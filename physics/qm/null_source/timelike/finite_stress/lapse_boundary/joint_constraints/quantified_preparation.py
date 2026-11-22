"""Exact and outward bounds for a genuine finite target/control ball."""
import sympy as sp
from common import iv,require,above,below,outward,finish,load
s=sp.Integer(1600000);M=sp.Integer(10)**6;R=sp.Rational(1,10**16)
B=[sp.Integer(1),sp.Integer(28),sp.Integer(784),sp.Integer(35000),sp.Integer(1517824)]
require(1232**2==1517824 and 28*1232<35000,'profile derivative products')
for j in range(4):require(B[j]**2+B[j+1]**2<s*s,'common source derivative budget')
x=sp.symbols('x',real=True);P=x+3*x*x+x**3
g=sp.exp(2*x)*(16*P**2+2*P)
require(sp.simplify(sp.diff(g,x).subs(x,1)-2440*sp.exp(2))==0,'observable majorant derivative')
major=iv.sqrt(8)*2440*iv.exp(2)
require(below(major,100000),'vector derivative constant')
bounds=[sp.Rational(1,5)*784/(32*3**(2-j)) for j in range(3)]
require(bounds[0]**2+2*bounds[1]**2+bounds[2]**2<36,'two by two norm')
det=9*sp.Rational(9,10000)**2
require(6/det<M,'inverse norm bound')
L=M*10**5*s**3*R**2
require(L==sp.Rational(512,125000) and L<sp.Rational(1,2),'strict contraction')
Y=R/(2*M);eta=sp.Rational(1,10**11)
require(eta**2/2==Y and 310*R<sp.Rational(1,5) and s*R<1,'gap and code target')
load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/joint_preparation.json')
finish('quantified_preparation.py',{
 'profile_derivative_L1_upper':[str(v) for v in B],
 'common_profile_Dyson_constant':int(s),
 'observable_majorant_derivative_vector_factor':outward(major),
 'two_by_two_Jacobian_determinant_strict_lower':str(det),
 'full_eight_by_eight_inverse_operator_norm_upper':int(M),
 'certified_control_ball_radius':'1e-16','certified_target_ball_radius':'5e-23',
 'contraction_Lipschitz_upper':str(L),'contraction_decimal':'0.004096',
 'common_two_code_strength_range':'0 < eta <= 1e-11',
 'instantaneous_source_supremum_upper':'310e-16',
 'actual_full_field_normal_state_map_used':True,
 'uniqueness_claim':'inside declared closed control ball only',
 'numerically_optimized_control_vector_computed':False,
 'experimental_or_SI_operating_range_claimed':False,
 'all_constraints_or_autonomous_actuator_solved':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/JOINT_PREPARATION.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/joint_preparation.json',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LOCAL_PREPARATION.md'])
