"""Massless field on the isotropic sandwich. All quantities use pulse-width units."""
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import roots_legendre, spherical_jn

G_PROBE = 0.5
FLAT = 64/(75*np.pi**2)


def profile(u):
    u = np.asarray(u, dtype=float)
    # Avoid powers at the endpoints of the bump (and zero times infinity).
    z = np.divide(1., 1-u*u, out=np.zeros_like(u), where=np.abs(u)<1)
    f = np.where(z>0, np.exp(1-z), 0.)
    return f, z


def curvature(u, amplitude, xi):
    f,z = profile(u)
    grad = -2*u*(z*z*f)
    second = f*((2*u*z*z)**2 - 2*z*z - 8*u*u*z**3)
    a2 = amplitude**2
    return a2*((1-2*xi)*grad**2-2*xi*f*second)/(1-2*xi*a2*f*f)


def jacobi(amplitude, xi):
    def rhs(u,y):
        k = curvature(u,amplitude,xi)
        p,v,q,w = y
        return v,-k*p,w,-k*q
    sol = solve_ivp(rhs,(-1,1),(1,0,0,1),method="DOP853",
                    atol=2e-15,rtol=4e-14,dense_output=True,max_step=.035)
    if not sol.success:
        raise ArithmeticError(sol.message)
    return sol.sol


def correction(amplitude, xi, sol, order):
    t,w = roots_legendre(order)
    p,v,q,r = sol(t)
    assert np.min(p)>0 and np.max(abs(p*r-q*v-1))<2e-13
    d = t[:,None]-t
    # b(t,s)=q(t)p(s)-p(t)q(s). Remove the Hadamard pole before integrating.
    b = q[:,None]*p - p[:,None]*q
    off = d!=0
    density = np.diag(curvature(t,amplitude,xi)/6)
    density[off] = (d[off]-b[off])/(b[off]*d[off]**2)
    weights = w*(1-t*t)**3
    return -(weights@density@weights)/(4*np.pi**2)


def volterra_correction(amplitude,xi,order):
    # Independent triangular quadrature. Directly integrate (d-B)/(B d^2)
    # using B/d = b(1), b(r)=r-d^2 integral_0^r (r-v)K b(v) dv.
    t,w=roots_legendre(order)
    d=(1-t[:,None])*(1+t[None,:])/2
    s=t[:,None]
    high=s+d
    weights=w[:,None]*w[None,:]*(1-s)/2*(1-s*s)**3*(1-high*high)**3
    # Fixed-step RK4 for the correction j=(r-b(r))/d^2; j''=K(s+dr)(r-d^2 j).
    j=np.zeros_like(d)
    v=np.zeros_like(d)
    steps=2*order
    h=1/steps
    for n in range(steps):
        r=n*h
        k0=curvature(s+d*r,amplitude,xi)
        kh=curvature(s+d*(r+h/2),amplitude,xi)
        k1=curvature(s+d*(r+h),amplitude,xi)
        a=k0*(r-d*d*j)
        vb=v+h*a/2
        b=kh*(r+h/2-d*d*(j+h*v/2))
        vc=v+h*b/2
        c=kh*(r+h/2-d*d*(j+h*vb/2))
        vd=v+h*c
        e=k1*(r+h-d*d*(j+h*vc))
        j+=h*(v+2*vb+2*vc+vd)/6
        v+=h*(a+2*b+2*c+e)/6
    return -2*np.sum(weights*j/(1-d*d*j))/(4*np.pi**2)


def events(phase, visibility):
    x,y = visibility*np.cos(phase), visibility*np.sin(phase)
    return {"X":[(1+x)/2,(1-x)/2], "Y":[(1+y)/2,(1-y)/2]}


def row(amplitude, xi, template_mean):
    sol=jacobi(amplitude,xi)
    dv=correction(amplitude,xi,sol,80)
    finer=correction(amplitude,xi,sol,128)
    independent=volterra_correction(amplitude,xi,48)
    assert max(abs(dv-finer),abs(finer-independent))<1e-10
    variance=FLAT+finer
    assert variance>0
    mu=amplitude*template_mean
    phase=2*G_PROBE*mu
    visibility=np.exp(-2*G_PROBE**2*variance)
    p=events(phase,visibility)
    ref=events(0,visibility)
    for basis in p:
        assert abs(sum(p[basis])-1)<1e-15 and min(p[basis])>=0
    c=complex(2*p["X"][0]-1,2*p["Y"][0]-1)
    assert abs(c/(2*ref["X"][0]-1)-np.exp(1j*phase))<1e-14
    assert events(0,1)=={"X":[1,0],"Y":[.5,.5]}
    return dict(A=amplitude,xi=xi,mu=mu,variance=variance,curvature_noise_correction=finer,
                quadrature_80_128_difference=abs(finer-dv),independent_noise_difference=abs(independent-finer),
                p_exit=float(sol(1)[0]),p_prime_exit=float(sol(1)[1]),visibility=visibility,
                probabilities=p,same_geometry_reference=ref,
                Y_plus_minus_flat_noise=p["Y"][0]-events(phase,np.exp(-2*G_PROBE**2*FLAT))["Y"][0])


def main():
    if not __debug__:
        raise RuntimeError("enable assertions")
    mean=quad(lambda t:(1-t*t)**3*profile(t)[0],-1,1,epsabs=2e-14,epsrel=2e-14)[0]
    # Independent flat-space spectral integral of k |Fourier chi|^2/(4 pi^2).
    flat_quad=quad(lambda k: (96*spherical_jn(3,k)/k**3)**2*k/(4*np.pi**2),
                   0,400,epsabs=2e-14,epsrel=1e-13,limit=300)[0]
    assert abs(flat_quad-FLAT)<1e-11
    rows=[row(a,xi,mean) for xi in (0.,1/6) for a in (.25,-.25,0.,.125)]
    for start in (0,4):
        plus,minus,empty,held=rows[start:start+4]
        assert plus['variance']==minus['variance']
        assert np.allclose(plus['probabilities']['Y'],minus['probabilities']['Y'][::-1],atol=1e-15,rtol=0)
        assert empty['probabilities']['Y']==[.5,.5] and abs(empty['variance']-FLAT)<1e-12
        assert held['mu']*2==plus['mu'] and plus['Y_plus_minus_flat_noise']>0
    assert rows[4]['variance']<rows[0]['variance']
    # A separate unit-area, centre-clock comparison for a gate of duration .2.
    # Positive smooth weights of any shape are covered by this low-frequency bound.
    duration=.2
    kmax=.55
    flat_floor=(np.pi**2/4-1)/(4*np.pi**2*duration**2)
    curvature_cap=kmax/(24*np.pi**2*(1-kmax*duration**2/6))
    contrast_cap=np.exp(-(flat_floor-curvature_cap)/2)
    raw_gap=(1-contrast_cap)*np.sin(.25*profile(.1)[0])/2
    assert raw_gap>.045 and curvature_cap<.00234
    narrow=dict(duration=duration,variance_lower=flat_floor-curvature_cap,
                contrast_upper=contrast_cap,Y_plus_ideal_probability_gap_lower=raw_gap)
    print(json.dumps(dict(baseline="3346989339cfbfa2322812448cee336c8633ff89",g=G_PROBE,
                          outcome_order=["+","-"],template_mean=mean,flat_variance=FLAT,
                          flat_spectrum_check=flat_quad,narrow_point_gate=narrow,rows=rows,
                          contract_sha256=hashlib.sha256(Path(__file__).with_name('CONTRACT.md').read_bytes()).hexdigest()),
                     indent=2,allow_nan=False))


if __name__=='__main__':
    main()
