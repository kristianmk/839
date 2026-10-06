# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with OpenAI Codex, an AI system, under the direction of the
# author, who is responsible for its content.
"""Rational adaptive interval proof of a two-sinc majorant and pair margins."""
from fractions import Fraction as F
from pathlib import Path
from math import factorial
import json,time,numpy as np
P=Path(__file__).resolve().parent
p=json.loads((P/'inputs.json').read_text());kb=json.loads((P/'kernel_build.json').read_text())
a=[F(x,10**6) for x in [193305,-23105,29166,13952,-21009,41052]]
pl=F(kb['pi_lower']);pu=F(kb['pi_upper'])
d=F(17,20);gamma=F(607,1000);c=F(67,20)
def cosb(j,u):
 t=(2*j*u)%2
 if t>1:t=2-t
 sg=1
 if t>F(1,2):t=1-t;sg=-1
 lo=sum((F((-1)**k,factorial(2*k))*(pu*t)**(2*k) for k in range(14)),F(0))
 hi=sum((F((-1)**k,factorial(2*k))*(pl*t)**(2*k) for k in range(13)),F(0))
 return (lo,hi) if sg>0 else (-hi,-lo)
def sincb(t):
 t=abs(t);assert t<1
 lo=sum((F((-1)**k,factorial(2*k+1))*(pu*t)**(2*k) for k in range(12)),F(0))
 hi=sum((F((-1)**k,factorial(2*k+1))*(pl*t)**(2*k) for k in range(13)),F(0))
 assert 0<lo<=hi
 return lo,hi
Lip=F(22,7)*(4*gamma*d+2*sum((j*abs(x) for j,x in enumerate(a,1)),F(0)))
stack=[(F(0),F(1,2),0)];nodes=0;leaves=0;maxdepth=0;t0=time.time();target=F(1,10000)
while stack:
 l,r,dep=stack.pop();nodes+=1;m=(l+r)/2
 fu=F(1)
 for j,aj in enumerate(a,1):
  low,up=cosb(j,m);fu+=aj*(up if aj>=0 else low)
 s1,_=sincb(d*(m-F(1,2)));s2,_=sincb(d*(m+F(1,2)))
 lower=gamma*(s1+s2)**2-fu-Lip*(r-l)/2
 if lower>=target:leaves+=1;maxdepth=max(maxdepth,dep)
 else:
  if dep>=25:raise RuntimeError(f'Cannot verify cell {l},{r}')
  stack.extend([(m,r,dep+1),(l,m,dep+1)])
_,su=sincb(d);L=2*gamma*(1+su)/d;assert 2*L<c
vals=np.fromfile(P/'kernel_lower.bin',dtype='<u4');end=(d*p['grid']).__floor__()
bet=F(int(vals[:end+1].min()),p['scale'])
x=F(sum(p['h'][0]),10**6);y=F(sum(p['h'][1]),10**6)
assert min(bet-x, 4*bet-y, 4*bet-x-y)>0
# At |K|=sqrt(beta) all pair eigenvalues lie below c.
assert bet<(c-2)**2/4 and bet<(c-1)*(c-2)/2 and bet<(c-1)**2
out=dict(status='PASS_MAJORANT_AND_PAIR_BOUNDS',nodes=nodes,leaves=leaves,max_depth=maxdepth,uniform_majorant_margin=str(target),norm_upper=str(L),norm_upper_decimal=float(L),twice_norm_below_clip_margin=str(c-2*L),near_pair_K_squared_lower=str(bet),near_pair_K_squared_decimal=float(bet),simple_pair_margin=str(2*bet-2*x),mixed_pair_margin=str(4*bet-x-y),double_pair_margin=str(8*bet-2*y),seconds=time.time()-t0,scope='Reference check in exact rational interval arithmetic. The majorant inequality, the Fourier transform of the majorant and the bound for close pairs are also proved in the Lean development, which is the proof of record.')
(P/'majorant_result.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
