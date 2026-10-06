# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with OpenAI Codex, an AI system, under the direction of the
# author, who is responsible for its content. It was changed with Claude (Anthropic) to read the
# result of the C++ verifier (cpp_verification.json).
"""Exact scalar assembly and consistency checks of the first certificate. A reference program: the
statements it checks are also proved in the Lean development (lean/Distinct839), the proof of record."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal,localcontext
import hashlib,json
import numpy as np
P=Path(__file__).resolve().parent;p=json.loads((P/'inputs.json').read_text());k=json.loads((P/'kernel_build.json').read_text());m=json.loads((P/'majorant_result.json').read_text())
a=[F(x,10**6) for x in p['window_coefficients']];pl=F(k['pi_lower']);pu=F(k['pi_upper'])
base=F(4,3)+sum((x*x/2 for x in a),F(0));coeff=sum((F((-1)**j,j*j)*x-x*x/F(4*j*j) for j,x in enumerate(a,1)),F(0))
CU=base+max(coeff/pl**2,coeff/pu**2);C=F(p['energy_cap']);assert CU<C
assert sum(abs(x) for x in a)<1
x=F(sum(p['h'][0]),10**6);y=F(sum(p['h'][1]),10**6);alpha=F(p['alpha'],10**6);b=6*alpha;c=F(p['clip_c'])
assert x==F(1087,20000) and y==F(69433,10**6)
assert m['status']=='PASS_MAJORANT_AND_PAIR_BOUNDS'
L=F(m['norm_upper']);assert 2*L<c
beta=F(m['near_pair_K_squared_lower']);assert min(beta-x,4*beta-y,4*beta-x-y)>0
assert beta>=F(8824337,134217728)
assert beta<(c-2)**2/4 and beta<(c-1)*(c-2)/2 and beta<(c-1)**2
rh=6*c-7-c*c+x-2*y;rk=4*c-2-c*c-2*x;nu=2*c-3+x-y;assert min(rh,rk,nu)>0
num=3-C+y-x-b;den=2-2*x+y;q=num/den;old=F(328367,391502);orig=F(16260119298029,19426831050000)
assert q==F(1645064,1960733) and q>old and den>0
W=np.array(p['weights'],dtype=np.int64);B=np.array(p['cob_knots'],dtype=np.int64);I,J=np.triu_indices(7,1)
assert not B.sum(axis=0).any()
A=np.cumsum(B,axis=0)[:5];omega=F(sum(int(r.max()-r.min()) for r in A),10**6);assert omega==F(7941,500000)
assert all(sum(int(W[t,e]) for e in range(21) if J[e]-I[e]==s)<=cap for t,cap in enumerate((2000000,4000000,8000000)) for s in range(1,7))
v=np.fromfile(P/'kernel_lower.bin',dtype='<u4')
assert len(v)==p['R']+1
# Exact endpoint checks: K(0)=1, K(j)=a_j/2 for j=1,...,6, and K(j)=0 thereafter.
for j in range(p['R']//p['grid']+1):
 exact=F(1) if j==0 else (a[j-1]/2 if j<=6 else F(0))
 for cell in [j*p['grid']-1,j*p['grid']]:
  if 0<=cell<len(v):assert F(int(v[cell]),p['scale'])<=exact**2
sha=hashlib.sha256((P/'kernel_lower.bin').read_bytes()).hexdigest();assert sha==p['table_sha256']==k['hash']
cr=json.loads((P/'cpp_verification.json').read_text());pr=json.loads((P/'python_verification.json').read_text())
assert cr['status']==pr['status']=='PASS_COB_CONTINUUM'
keys=['nodes','leaves','basic','affine','max_stack']
for key in keys:assert cr[key]==pr[key]
assert pr['table_sha256']==sha
assert cr['leaves']*2-1==cr['nodes']
def dec(z):
 with localcontext() as ctx:
  ctx.prec=60;return str(Decimal(z.numerator)/Decimal(z.denominator))
res=dict(status='PASS_FINITE_CERTIFICATE_AND_EXACT_ASSEMBLY',q=str(q),q_decimal=dec(q),percentage=dec(100*q),previous_q=str(old),previous_percentage=dec(100*old),gain_percentage_points=dec(100*(q-old)),gain_per_million=dec(10**6*(q-old)),original_q=str(orig),gain_from_original_percentage_points=dec(100*(q-orig)),x=str(x),y=str(y),alpha=str(alpha),b=str(b),boundary_oscillation_bound=str(omega),total_boundary_constant=str(6*y+omega),energy_cap=str(C),energy_upper=str(CU),numerator=str(num),denominator=str(den),clip_c=str(c),norm_upper=str(L),near_pair_beta=str(beta),high_multiplicity_coefficient=str(rh),off_line_pair_coefficient=str(rk),excess_multiplicity_coefficient=str(nu),counters={key:cr[key] for key in keys},table_hash=sha,lean_status='PROVED_IN_LEAN: lean/Distinct839 and lean/Solution839.lean; this program is a reference check',scope='Reference check in exact rational arithmetic: the scalar assembly of the constant from the certificate data, and the agreement of the result files of the C++ and the Python verifier, which share the kernel table and the mathematical specification. The proof of record is the Lean development. No claim of independent review or of a proof of the Riemann hypothesis.')
(P/'assembly.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
