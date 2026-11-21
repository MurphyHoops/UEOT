"""Curvature-contact algebra and a controlled renormalized density row."""
import sympy as s
import mpmath as mp
from common import finish,require,iv,outward,above,below
x,y,z=s.symbols('x y z',real=True);tr=x+y+z;norm=x*x+y*y+z*z
riem=12+4*norm;ric=tr*tr+(2-x)**2+(2-y)**2+(2-z)**2;scalar=6-2*tr
require(s.expand(riem-2*ric+scalar**2/3-2*(norm-tr*tr/3))==0,'pure lapse Weyl invariant')
ell,ns,V,gamma,lam=s.symbols('ell ns V gamma lam',positive=True)
C=ns*ell*(ell-3)/(360*V);coef=s.Rational(8,3)*ell*(ell-3)
require(s.simplify(C/coef-ns/(960*V))==0,'universal Weyl logarithm')
require(coef.subs(ell,8)==s.Rational(320,3),'m3 Weyl contact')
eps,h,dh=s.symbols('eps h dh')
N=1+eps*h
r2=36*N-24*eps*dh+4*eps**2*dh**2/N
require(s.simplify(s.diff(r2,eps,2).subs(eps,0)*lam/(72*V)-lam*dh*dh/(9*V))==0,'R2 lapse contact')
K=1000;yy=iv.mpf('1.3');c=iv.mpf(2)/(9*(2*iv.pi**2))
H=sum((iv.mpf(1)/j for j in range(1,K+1)),iv.mpf(0))
static=c*(H-1-iv.mpf(1)/(3*K))
sub=-2*c*yy**2*(sum((1/(iv.mpf(2*j)*((2*j)**2+yy**2)) for j in range(2,K)),iv.mpf(0))
                 +iv.mpf(2)/3/(2*K*((2*K)**2+yy**2)))
renK=static-c*H+sub # gamma_R=0 in this explicitly stated example.
tail=c*yy**2*(iv.mpf(1)/(12*K**3)+iv.mpf(1)/(8*K**2))
edge=c/(3*K)
lo=(renK+edge-tail).a;hi=(renK+edge).b
mp.mp.dps=100
cc=mp.mpf(2)/(9*2*mp.pi**2);zz=mp.mpc(0,'1.3')
dig=cc*(-1+mp.digamma(2)-(mp.digamma(2-zz/2)+mp.digamma(2+zz/2))/2)
require(abs(mp.im(dig))<mp.mpf('1e-90'),'real imaginary-frequency response')
digiv=iv.mpf(str(mp.re(dig)))
require(bool(digiv.a>=lo) and bool(digiv.b<=hi),'digamma inside analytic tail enclosure')
finish('weyl_response.py',{'harmonic':3,'finite_mode_cutoff':K,
 'example_frequency':'1.3 i','finite_gamma_R':0,
 'renormalization_scheme':'gamma_W,K=gamma_R-n_s H_K/(960 V)',
 'renormalized_density_row_enclosure':outward(iv.mpf([lo,hi])),
 'finite_K_renormalized_row':outward(renK),
 'subtracted_tail_upper_bound':outward(tail),'static_edge_correction':outward(edge),
 'digamma_regression_decimal':mp.nstr(mp.re(dig),50),
 'digamma_regression_precision_digits':100,
 'infinite_row_enclosure_uses_analytic_tail_not_digamma_rounding':True,
 'independent_finite_Weyl_coupling_required':True,
 'all_FLRW_mean_data_determine_Weyl_coupling':False,
 'full_gravitational_response_inverse_constructed':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SPATIAL_NOISE.md'])
