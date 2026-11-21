"""Exact total covariance conservation for a real internal source transfer."""
from common import *
import sympy as sp
z,v,d,m=sp.symbols("z v d m",real=True)
vt=(1-z)**2*(v+d)+z**2*v+2*m**2*z*(1-z)
vr=z**2*(v+d)+(1-z)**2*v+2*m**2*z*(1-z)
cov=z*(1-z)*(2*v+d-2*m**2)
assert sp.expand(vt+vr+2*cov-(2*v+d))==0
assert sp.simplify(vt.subs(z,1)-v)==0
assert sp.simplify(vr.subs(z,1)-(v+d))==0
vv=4*R*L+4*R**2;mu=L+2*R;dd=exact(3)/16
mid=(2*vv+dd)/4+mu**2/2
midcov=(2*vv+dd-2*mu**2)/4
assert above(mid,1) and below(midcov,0)
finish("rotation.py",{
 "proof":"ROTATION.md","total_variance_identity":"V_T+V_R+2Cov=2V+3/16",
 "target_variance_at_half_rotation":outward(mid),
 "target_reservoir_covariance_at_half_rotation":outward(midcov),
 "complete_total_stress_operator_preserved_by_constant_O4_rotation":True,
 "all_total_stress_moments_and_defined_influence_preserved":True,
 "old_two_field_static_geometry_claimed_four_field_solution":False,
 "autonomous_local_rotation_device_built":False},("ROTATION.md",))
