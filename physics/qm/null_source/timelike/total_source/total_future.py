"""Actual dilation difference and endpoint factorization."""
import sympy as s
from common import *
t=s.symbols("t",real=True);w=s.symbols("w",positive=True)
U=s.eye(4);U[1,1]=s.cos(t);U[1,2]=-s.sin(t);U[2,1]=s.sin(t);U[2,2]=s.cos(t)
out=U*s.diag(w,w,0,0)*U.T
sx=s.Matrix([[0,1],[1,0]]);sy=s.Matrix([[0,-s.I],[s.I,0]]);sz=s.diag(1,-1)
swap=s.kronecker_product(s.eye(2),sx)
diff=s.simplify(out-swap*out*swap)
assert s.simplify(diff-(w*s.sin(t)**2*s.kronecker_product(s.eye(2),sz)+w*s.sin(t)*s.cos(t)*s.kronecker_product(sy,sy)))==s.zeros(4)
assert s.simplify(diff*diff-w*w*s.sin(t)**2*s.eye(4))==s.zeros(4)
endpoint=s.simplify(diff.subs(t,s.pi/2))
assert endpoint==s.kronecker_product(s.eye(2)/2,2*w*sz)
B=s.Matrix(2,2,s.symbols("b0:4"));C=s.Matrix(2,2,s.symbols("c0:4"))
assert s.simplify(s.trace(endpoint*s.kronecker_product(C,B))-s.trace(2*w*sz*B)*s.trace(C/2))==0
finish("total_future.py",{
 "proof":"TOTAL_FUTURE.md","main_endpoint_c_equals_w":True,
 "actual_joint_difference_factorization":"delta_rho_shell tensor I_memory/2",
 "general_c_full_joint_trace_distance":"2*sqrt(w*c)",
 "endpoint_full_joint_trace_distance":outward(2*WEIGHT),
 "future_total_noise_difference_equals_shell_under_stated_contract":True,
 "individual_joint_states_assumed_product":False,
 "actual_memory_marginal_assumed_I_over_2":False,
 "old_bare_background_and_response_assumed_valid_with_memory":False,
 "gate_era_common_on_shell_total_history_closed":False
},("TOTAL_FUTURE.md","PREPARATION.md","PRESSURE_NOISE.md"))
