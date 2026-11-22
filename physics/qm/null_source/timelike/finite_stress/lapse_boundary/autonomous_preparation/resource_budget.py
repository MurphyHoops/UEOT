"""Sharp global derivatives, reference moment budget and one fixed instance."""
import sympy as s
from common import finish,require,iv,outward,above,below,load,box
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
ab=load(P+'collision.json')
y=s.symbols('y',real=True);Ppoly=y**4-6*y**3+6*y**2;q=y**3-10*y**2+24*y-12
require(s.expand(s.diff(Ppoly,y)-Ppoly+y*q)==0,'exact bump second derivative critical polynomial')
require(q.subs(y,4)==q.subs(y,6)==-12,'negative convex interval endpoints')
require(s.expand(s.diff(q,y,2)-(6*y-20))==0 and s.diff(q,y).subs(y,6)==12,'unique root on y>=4')
require(q.subs(y,s.Rational(20,3))==-s.Rational(4,27),'left root enclosure')
require(q.subs(y,s.Rational(67,10))==s.Rational(663,1000),'right root enclosure')
def taylor6(x):return sum(x**j/s.factorial(j) for j in range(7))
require(taylor6(s.Rational(73,50))>s.Rational(43,10),'positive exponential lower bound for R1')
require(taylor6(s.Rational(8,3))>14,'positive exponential lower bound for R2')
require(s.Rational(173,100)**2<3<s.Rational(1733,1000)**2,'rational sqrt3 enclosure')
r1sq=(36+24*s.Rational(1733,1000))/(25*s.Rational(43,10))
require(r1sq<s.Rational(85,100)**2,'global R1<.85')
require(Ppoly.subs(y,s.Rational(67,10))/(5*14)<7,'global R2<7')
a=iv.mpf(4)/5;R1=iv.mpf(17)/20;R2=iv.mpf(7);rs=iv.mpf(1)/5
c1=R1*iv.pi/(4*iv.sqrt(3)*a)
c2=(R2+R1**2/a)*iv.pi/(4*iv.sqrt(3)*a)
bo=R1/(2*iv.sqrt(a));le=5*R1*rs**3*(iv.mpf(5)/4)/(32*a**(iv.mpf(7)/2))
require(below(c1,'.5') and below(c2,'4.5') and below(bo,'.48') and below(le,'.003'),'sharp all-mode bounds')
q1=iv.exp(iv.pi/(4*iv.sqrt(3)))*iv.sqrt(27)/2
require(below(q1,'4.1'),'stronger reference first norm moment')
coefficient=iv.mpf(95)/2*iv.sqrt(iv.mpf(25)/176+iv.mpf(4)/25)+41*iv.sqrt(3)/50+iv.mpf(41)/20*iv.sqrt(iv.mpf(25)/176+iv.mpf(12)/25)
require(below(coefficient,30),'uniform square-root resource scaling coefficient')
require(below(iv.mpf('4.1')*(iv.mpf('.48')+5*iv.mpf('4.5'))+iv.mpf('.003'),95),'residual localization coefficient')
require(below((iv.mpf('4.5')*iv.mpf('4.1')+2*iv.mpf('.5')**2*40)/2,'19.2250000001'),'connection coefficient')
M=iv.mpf(10)**12;delta=iv.mpf('2.5e-6')
eps=30/iv.sqrt(M)+10/M
simple=10*delta+60/(M*delta)+11/M
dcl=box(ab['classical_binary_contrast_lower_bound_interval'])
gain=dcl-2*eps
require(above(gain,'.00233999998'),'strict actual contrast for final fixed instance')
require(below(eps,simple),'refined budget improves independent simple budget')
source=iv.sqrt(3)/50+eps
require(below(source,'.034672'),'source state-distance budget')
mean=s.Rational(25,2)*10**12+s.Rational(73,50)
variance=48*10**12+s.Rational(701,250)
finish('resource_budget.py',{
 'final_fixed_example':{'M':'1e12','delta':'2.5e-6','v':'5','X0':'-3/2','T':'1/2','sigma':'1/10'},
 'rprime_global_upper_bound':'.85','rsecond_global_upper_bound':'7',
 'squeeze_derivative_norm_bounds':{'c1':outward(c1),'c2':outward(c2)},
 'frequency_derivative_bound_interval':outward(bo),'subtracted_vacuum_force_bound_interval':outward(le),
 'reference_q1_bound_interval':outward(q1),
 'square_root_resource_coefficient_interval':outward(coefficient),
 'simple_vector_error_bound_interval':outward(simple),
 'final_vector_error_bound_interval':outward(eps),
 'actual_binary_contrast_lower_bound_interval':outward(gain),
 'total_H_mean_exact_rational':str(mean),'total_H_variance_exact_rational':str(variance),
 'total_H_mean_decimal_components':['1.25e13','1.46'],
 'total_H_variance_decimal_components':['4.8e13','2.804'],
 'low_source_half_trace_distance_from_free_upper_bound_interval':outward(source),
 'M1_p10_original_example_closed':False,
 'optimal_resource_lower_bound_claimed':False,
 'uniform_finite_energy_classical_limit_claimed':False,
 'SI_calibration':False
},inputs=[P+'collision.json',P+'COLLISION.md'])
