# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with OpenAI Codex, an AI system, under the direction of the
# author, who is responsible for its content.
"""Second integer implementation of the continuous certificate.

Shared input: the rational Fourier table and coefficients. This is a cross-check
of implementation, not independent mathematical review or a Lean proof.
"""
from pathlib import Path
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import hashlib, json, time
import numpy as np
from numba import njit
P=Path(__file__).resolve().parent
p=json.loads((P/'inputs.json').read_text())
V=int(p['scale']);G=int(p['grid']);R=int(p['R']);alpha=int(p['alpha'])
v=np.fromfile(P/'kernel_lower.bin',dtype='<u4').astype(np.int64)
assert len(v)==R+1 and hashlib.sha256((P/'kernel_lower.bin').read_bytes()).hexdigest()==p['table_sha256']
W=np.array(p['weights'],dtype=np.int64);hh=np.array(p['h'],dtype=np.int64);B=np.array(p['cob_knots'],dtype=np.int64)
I,J=np.triu_indices(7,1);I=I.astype(np.int64);J=J.astype(np.int64)
assert np.all(v>=0) and np.all(v<=V)
assert np.all(W>=0) and np.all(W[1]>=W[0]) and np.all(W[2]>=W[0])
assert np.all(hh>=0) and np.all(hh[1]>=hh[0]) and not B.sum(axis=0).any()
assert not B[:,:,0].any() and not B[:,:,-1].any()
for t,cap in enumerate((2000000,4000000,8000000)):
 for k in range(1,7): assert sum(int(W[t,e]) for e in range(21) if J[e]-I[e]==k)<=cap
budget=sum(-min(0,int(row.min())) for row in B)
assert alpha*R>=(int(hh[1].sum())+budget)*G and V%G==0 and V%2048==0
# Python-integer preflight bounds, including every non-cancelled intermediate.
ms=int(np.max(np.abs(v[2:]-v[:-2])));ws=sum(int(x) for x in np.max(W,axis=0));pb=int(np.max(abs(B)));hr=int(hh.sum())
sb=2*pb*(V//2048);bo=pb*V+sb*R;pressure=alpha*(V//G)
aff_bound=ws*(2*V+ms*(2*R+6*512+2))+12*bo+12*sb*R+12*pressure*R+2*hr*V
basic_bound=16*(ws*V+6*R*pressure+12*pb*V+hr*V)
assert max(aff_bound,basic_bound)<2**63
print(json.dumps(dict(status='PASS_INT64_PREFLIGHT',bound=max(aff_bound,basic_bound))),flush=True)
logs=np.zeros(R+2,dtype=np.int64)
for k in range(2,R+2):logs[k]=logs[k//2]+1
rmq=np.zeros((int(logs[R+1])+1,R+1),dtype=np.int64);rmq[0]=v
for k in range(1,len(rmq)):
 jump=1<<(k-1);length=R+2-(1<<k)
 rmq[k,:length]=np.minimum(rmq[k-1,:length],rmq[k-1,jump:jump+length])
kinds=np.empty((128,21),dtype=np.int64);gtypes=np.empty((128,6),dtype=np.int64);rhs=np.empty(128,dtype=np.int64)
for m in range(128):
 rhs[m]=2*sum(int(hh[(m>>i)&1,i]) for i in range(7))*V
 for e in range(21):kinds[m,e]=((m>>int(I[e]))&1)+((m>>int(J[e]))&1)
 for i in range(6):gtypes[m,i]=((m>>i)&1)+((m>>(i+1))&1)
@njit(cache=True)
def bv(B,pos,typ,x,V):
 if x<=12288 or x>=12288+13*2048:return 0
 k=(x-12288)//2048;r=(x-12288)%2048
 return (B[pos,typ,k]*(2048-r)+B[pos,typ,k+1]*r)*(V//2048)
@njit(cache=True)
def bm(B,pos,typ,base,lo,hi,V):
 a=bv(B,pos,typ,lo,V);b=bv(B,pos,typ,hi,V)
 if base>=0:a-=bv(B,pos,base,lo,V);b-=bv(B,pos,base,hi,V)
 ret=min(a,b)
 for j in range(14):
  x=12288+j*2048
  if lo<x<hi:
   z=bv(B,pos,typ,x,V)
   if base>=0:z-=bv(B,pos,base,x,V)
   ret=min(ret,z)
 return ret
@njit(cache=True)
def ba(B,pos,typ,lo,hi,V):
 mid=(lo+hi)//2;s=0
 if 12288<mid<12288+13*2048:
  k=(mid-12288)//2048;s=(B[pos,typ,k+1]-B[pos,typ,k])*(V//2048)
 off=min(bv(B,pos,typ,lo,V)-s*lo,bv(B,pos,typ,hi,V)-s*hi)
 for j in range(14):
  x=12288+j*2048
  if lo<x<hi:off=min(off,bv(B,pos,typ,x,V)-s*x)
 return s,off
@njit(cache=True)
def run(rmq,logs,I,J,W,hh,B,kinds,gtypes,rhs,R,V,G,alpha,budget):
 slo=np.zeros((240,6),dtype=np.int64);shi=slo.copy();slo[0,:]=13926;shi[0,:]=R
 top=1;seen=0;leaves=0;basic=0;affine=0;maxstack=1;pressure=alpha*(V//G)
 h1=np.sum(hh[0]);h2=np.sum(hh[1]);lo=np.zeros(6,dtype=np.int64);hi=lo.copy()
 ls=np.zeros(21,dtype=np.int64);hs=ls.copy();deg=np.zeros(7,dtype=np.int64)
 ks=ls.copy();ko=ls.copy();bs=np.zeros((6,3),dtype=np.int64);bo=bs.copy();lin=np.zeros(6,dtype=np.int64)
 while top:
  top-=1;lo[:]=slo[top];hi[:]=shi[top];seen+=1;total=np.sum(lo)
  if total*pressure>=(h2+budget)*V:leaves+=1;basic+=1;continue
  for i in range(6):hi[i]=min(hi[i],R-total+lo[i])
  deg[:]=0;base=total*pressure
  for e in range(21):
   l=0;h=0
   for i in range(I[e],J[e]):l+=lo[i];h+=hi[i]
   h=min(h,R-total+l);last=max(l,h-1);ls[e]=l;hs[e]=last;k=logs[last-l+1]
   kval=min(rmq[k,l],rmq[k,last-(1<<k)+1]);base+=W[0,e]*kval
   i1=2*(W[1,e]-W[0,e])*kval;i2=(W[2,e]-W[0,e])*kval
   if J[e]==I[e]+1:
    i=I[e];base+=bm(B,i,0,-1,lo[i],hi[i],V)
    i1+=2*bm(B,i,1,0,lo[i],hi[i],V);i2+=bm(B,i,2,0,lo[i],hi[i],V)
   inc=min(i1,i2);deg[I[e]]+=inc;deg[J[e]]+=inc
  penalty=0
  for i in range(7):penalty+=min(0,deg[i]-2*(hh[1,i]-hh[0,i])*V)
  if 2*(base-h1*V)+penalty>=0:leaves+=1;basic+=1;continue
  width=0;split=-1
  for i in range(6):
   if hi[i]-lo[i]>width:width=hi[i]-lo[i];split=i
  if width<=512:
   for e in range(21):
    mid=(ls[e]+hs[e])//2;s=0 if mid<=0 or mid>=R else rmq[0,mid+1]-rmq[0,mid-1]
    off=9223372036854775807
    for k in range(ls[e],hs[e]+1):off=min(off,2*rmq[0,k]-s*(k+1 if s>=0 else k))
    ks[e]=s;ko[e]=off
   for i in range(6):
    for t in range(3):bs[i,t],bo[i,t]=ba(B,i,t,lo[i],hi[i],V)
   intercept=0
   for i in range(6):lin[i]=2*pressure+2*bs[i,0];intercept+=2*bo[i,0]
   for e in range(21):
    intercept+=W[0,e]*ko[e]
    for i in range(I[e],J[e]):lin[i]+=W[0,e]*ks[e]
   val=intercept
   for i in range(6):val+=lin[i]*(lo[i] if lin[i]>=0 else hi[i])
   if val-2*h1*V+penalty>=0:leaves+=1;affine+=1;continue
   allpass=True
   for m in range(128):
    intercept=0
    for i in range(6):
     t=gtypes[m,i];lin[i]=2*pressure+2*bs[i,t];intercept+=2*bo[i,t]
    for e in range(21):
     t=kinds[m,e];intercept+=W[t,e]*ko[e]
     for i in range(I[e],J[e]):lin[i]+=W[t,e]*ks[e]
    val=intercept
    for i in range(6):val+=lin[i]*(lo[i] if lin[i]>=0 else hi[i])
    if val<rhs[m]:allpass=False;break
   if allpass:leaves+=1;affine+=1;continue
  if width<=1:return -1,seen,leaves,basic,affine,maxstack
  if top+2>=240:return -2,seen,leaves,basic,affine,maxstack
  mid=(lo[split]+hi[split])//2
  slo[top,:]=lo;shi[top,:]=hi;slo[top,split]=mid;top+=1
  slo[top,:]=lo;shi[top,:]=hi;shi[top,split]=mid;top+=1
  maxstack=max(top,maxstack)
 return 1,seen,leaves,basic,affine,maxstack
start=time.time();res=run(rmq,logs,I,J,W,hh,B,kinds,gtypes,rhs,R,V,G,alpha,budget)
out=dict(status='PASS_COB_CONTINUUM' if res[0]==1 else 'FAIL',nodes=int(res[1]),leaves=int(res[2]),basic=int(res[3]),affine=int(res[4]),max_stack=int(res[5]),elapsed_seconds=time.time()-start,int64_bound=max(aff_bound,basic_bound),table_sha256=p['table_sha256'])
(P/'python_verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2),flush=True)
if res[0]!=1:raise SystemExit(1)
