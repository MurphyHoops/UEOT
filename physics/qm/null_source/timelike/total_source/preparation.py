"""Exact four-state dilation and resource identities."""
import sympy as s
from mpmath import iv
from common import *
t=s.symbols("t",real=True);w=s.symbols("w",positive=True)
U=s.eye(4);U[1,1]=s.cos(t);U[1,2]=-s.sin(t);U[2,1]=s.sin(t);U[2,2]=s.cos(t)
assert s.simplify(U.T*U-s.eye(4))==s.zeros(4)
initial=s.diag(w,w,0,0)
out=s.simplify(U*initial*U.T)
shell=s.Matrix([[out[i,j]+out[i+2,j+2] for j in range(2)] for i in range(2)])
assert s.simplify(shell-s.diag(w*(1+s.sin(t)**2),w*(1-s.sin(t)**2)))==s.zeros(2)
memory=s.Matrix([[sum(out[2*i+k,2*j+k] for k in range(2)) for j in range(2)] for i in range(2)])
memory[0,0]+=1-2*w
assert s.simplify(memory-s.diag(1-w*s.sin(t)**2,w*s.sin(t)**2))==s.zeros(2)
J=s.zeros(4);J[2,1]=s.I;J[1,2]=-s.I
assert s.trace(initial*J)==0 and s.trace(initial*J*J)==w
x=s.symbols("x",positive=True)
f=(1+x)*s.log(1+x)+(1-x)*s.log(1-x)-x*x
assert s.simplify(s.diff(f,x,2)-2*x*x/(1-x*x))==0
entropy=2*WEIGHT*iv.ln(2)
hm=-WEIGHT*iv.ln(WEIGHT)-(1-WEIGHT)*iv.ln(1-WEIGHT)
assert above(hm-entropy,0)
finish("preparation.py",{
 "proof":"PREPARATION.md","explicit_unitary_positive_unpostselected_dilation":True,
 "free_energy_preserved":True,"shell_entropy_reduction_c_equals_w":outward(entropy),
 "actual_memory_entropy_c_equals_w":outward(hm),
 "mutual_information_c_equals_w":outward(hm-entropy),
 "instantaneous_control_energy_variance":"lambda(t)^2*w",
 "instantaneous_control_power_variance":"lambda_prime(t)^2*w",
 "zero_memory_internal_H_implies_zero_local_stress":False,
 "actual_local_gate_and_controller_total_source_closed":False
},("PREPARATION.md","COHERENCE.md"))
