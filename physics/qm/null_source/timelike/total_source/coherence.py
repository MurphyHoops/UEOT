"""Exact finite-support Fock selection rules, no Fock cutoff."""
import itertools
import sympy as s
from common import *
dim=8;d=4
vac=(0,)*dim
def basis(i):
 t=list(vac);t[i]=2;return tuple(t)
A1={basis(i):s.Rational(1,2) for i in range(4)}
A2={basis(i):s.Rational(1,2) for i in range(4,8)}
def add(*states):
 out={}
 for state in states:
  for k,v in state.items():out[k]=s.simplify(out.get(k,0)+v)
 return {k:v for k,v in out.items() if v!=0}
def act(state,i,creation):
 out={}
 for k,v in state.items():
  n=k[i]
  if n==0 and not creation:continue
  kk=list(k);kk[i]+=1 if creation else -1
  out[tuple(kk)]=out.get(tuple(kk),0)+v*s.sqrt(n+1 if creation else n)
 return out
def inner(left,right):return s.simplify(sum(s.conjugate(v)*right.get(k,0) for k,v in left.items()))
ops=list(itertools.product(range(dim),(False,True)))
assert inner(A1,A1)==inner(A2,A2)==1 and inner(A1,A2)==0
assert all(sum(k)==2 for state in (A1,A2) for k in state)
count=0
for op in ops:
 st=act(A1,*op);assert inner(A2,st)==0;count+=1
 for op2 in ops:
  assert inner(A2,act(st,*op2))==0;count+=1
def X(state):
 return add(*(act(act(state,i,cr),i,cr) for i,cr in ops))
quartic=inner(A2,X(X(A1)))
assert quartic==4*d
q=s.symbols("q",real=True)
assert s.factor(s.diff((1-q)**8*q**2,q))==2*q*(q-1)**7*(5*q-1)
assert above(WEIGHT,0) and below(WEIGHT,".001")
finish("coherence.py",{
 "proof":"COHERENCE.md","oscillators":8,"degeneracy":4,
 "linear_and_quadratic_exact_selection_checks":count,
 "quartic_matrix_element":str(quartic),"thermal_block_weight":outward(WEIGHT),
 "complete_W2_and_total_energy_spectral_law_preserved":True,
 "each_species_thermal_marginal_preserved":True,
 "positive_normal_Hadamard_states":True,"stationary_not_generally_KMS":True,
 "internal_O2_twirl_difference_nonzero":True,
 "autonomous_local_preparation_supplied_by_state_definition":False
},("COHERENCE.md",))
