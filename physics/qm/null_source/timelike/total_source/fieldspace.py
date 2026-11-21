"""Compute the controller field-space curvature, without old project imports."""
from common import *
import sympy as sp
x,y,z=sp.symbols("x y z",real=True)
f=sp.symbols("F",positive=True);k=sp.Function("k")(x)
coords=(x,y,z);g=sp.diag(f**2,1+k,1-k);ginv=g.inv()
Gamma=[[[sp.simplify(sum(ginv[a,e]*(sp.diff(g[e,c],coords[b])+sp.diff(g[e,b],coords[c])-sp.diff(g[b,c],coords[e])) for e in range(3))/2) for c in range(3)] for b in range(3)] for a in range(3)]
# R^1_(2 1 2); convention R(X,Y)Z=...
r=sp.diff(Gamma[1][2][2],coords[1])-sp.diff(Gamma[1][1][2],coords[2])
r+=sum(Gamma[1][1][e]*Gamma[e][2][2]-Gamma[1][2][e]*Gamma[e][1][2] for e in range(3))
section=sp.simplify(g[1,1]*r/(g[1,1]*g[2,2]))
expected=sp.diff(k,x)**2/(4*f**2*(1-k**2))
assert sp.simplify(section-expected)==0
finish("fieldspace.py",{
 "proof":"FIELDSPACE.md","mixed_sectional_curvature":str(expected),
 "kinetic_eigenvalues":["F^2","1+kappa","1-kappa"],
 "dynamic_nonconstant_coupling_is_not_flat_target_relabeling":True,
 "pure_orthogonal_target_P_or_S_QND_allows_probe_gain":False,
 "quantum_full_QFT_controller_renormalization_closed":False},("FIELDSPACE.md",))
