# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with AI systems (OpenAI Codex and Claude, Anthropic), under
# the direction of the author, who is responsible for its content.
"""Rational cell enclosure using an explicit local derivative bound.
No numerical optimization or floating point is used for deciding inequalities.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json, hashlib, time
import numpy as np
P=Path(__file__).resolve().parent;p=json.loads((P/'inputs.json').read_text());H=p['grid'];V=p['scale'];R=p['R'];t0=time.time()
a=[F(z,10**6) for z in p['window_coefficients']]
assert sum(abs(z) for z in a)<1
def ab(q,n):
 s=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0));r=F((-1)**n,(2*n+1)*q**(2*n+1));return min(s,s+r),max(s,s+r)
a0,b0=ab(5,70);c0,d0=ab(239,20);pl=16*a0-4*d0;pu=16*b0-4*c0
unit=10**40;pil=F((pl*unit).__floor__(),unit);piu=F((pu*unit).__floor__()+1,unit)
assert 3<pil<piu<F(22,7)
assert piu*F(H-1,2*H)<pil/2
Q=2**70
def dyadlo(x):return F((x*Q).__floor__(),Q)
def dyadhi(x):return F((x*Q).__floor__()+1,Q)
def sinpoly(x,n):return sum((F((-1)**k,factorial(2*k+1))*x**(2*k+1) for k in range(n)),F(0))
def cospoly(x,n):return sum((F((-1)**k,factorial(2*k))*x**(2*k) for k in range(n)),F(0))
st=[];ct=[]
for j in range(H//2):
 r=F(2*j+1,2*H);xl=pil*r;xu=piu*r
 st.append((dyadlo(sinpoly(xl,10)/piu),dyadhi(sinpoly(xu,11)/pil)))
 ct.append((dyadlo(cospoly(xu,10)),dyadhi(cospoly(xl,11))))
assert all(0<s[0]<s[1] for s in st)
vals=np.empty(R+1,dtype='<u4');radd=F(1,2*H)
for k in range(R+1):
 t=F(2*k+1,2*H)
 rat=1/t+sum((aj*(-1)**j*t/(t*t-j*j) for j,aj in enumerate(a,1)),F(0))
 der=-1/(t*t)-sum((aj*(-1)**j*(t*t+j*j)/(t*t-j*j)**2 for j,aj in enumerate(a,1)),F(0))
 j=k%H;neg=False
 if j>=H//2:j=H-1-j;neg=True
 sl,su=st[j];cl,cu=ct[j]
 if neg:cl,cu=-cu,-cl
 dl=min(rat*cl,rat*cu)+min(der*sl,der*su)
 du=max(rat*cl,rat*cu)+max(der*sl,der*su)
 # |K''| <= pi^2, since f>=0, integral f=1 and |u|<=1/2.
 derivative_bound=min(piu,max(abs(dl),abs(du))+piu*piu*radd)
 low=max(F(0),abs(rat)*sl-derivative_bound*radd)
 vals[k]=(low*low*V).__floor__();assert 0<=vals[k]<=V
vals.tofile(P/'kernel_lower.bin');np.save(P/'kernel_lower.npy',vals.astype(np.int64))
p['table_sha256']=hashlib.sha256(vals.tobytes()).hexdigest();p['table_method']='local derivative; exact rational';(P/'inputs.json').write_text(json.dumps(p,indent=2))
info=dict(status='PASS_RATIONAL_LOCAL_DERIVATIVE_TABLE',R=R,grid=H,scale=V,pi_lower=str(pil),pi_upper=str(piu),hash=p['table_sha256'],elapsed_seconds=time.time()-t0)
(P/'kernel_build.json').write_text(json.dumps(info,indent=2));print(json.dumps(info,indent=2))
