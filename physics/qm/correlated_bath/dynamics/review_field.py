"""Independent interval check of the cylinder probe, using integrated complex pulses."""
import json
from fractions import Fraction
from pathlib import Path

from mpmath import iv

iv.dps = 65
I = iv.mpc(0, 1)
kappa = iv.sqrt(5)/2
L = 2*iv.pi/kappa
ell = L/160
radius = L/6+4*ell
lam = iv.mpf(3)/10
n, c = iv.mpf(1)/2, iv.mpf(1)/4
old = json.loads((Path(__file__).resolve().parents[1]/"field"/"observed.json").read_text())


def sinc(x):
    return iv.sin(x)/x


# Solve the first cosine-mode matching equation for the satellite weight.
first_box = sinc(kappa*ell)**4
p = (1-iv.mpf(3)/5*iv.sqrt(iv.mpf(3)/4)/first_box)/(1-iv.cos(kappa*L/6))


def mode(j):
    if j == 0:
        return iv.mpf(1), iv.mpf(1)
    k = j*kappa
    profile = sinc(k*ell)**4*(1+p*(iv.cos(k*L/6)-1))
    w = iv.sqrt(1+k*k)
    return w, profile*iv.sqrt(2/w)


def pulse(w, g, start, duration):
    return -I*g*duration*sinc(w*duration/2)*iv.exp(I*w*(start+duration/2))


def abs2(z):
    return z.real**2+z.imag**2


def tails(M, coupling):
    power = (1/(kappa*ell))**8
    H = power/(5*kappa**3*M**10)
    return 12*coupling**2*H, 8*coupling**2*H, 16*coupling**2*power/(9*kappa**2*M**9)


def dyadic(z):
    sign, man, exp, _ = z
    return (-1)**sign*Fraction(man)*Fraction(2)**exp


def contained(case, key, interval):
    lo, hi = map(dyadic, old[case][key]["dyadic"])
    a, b = map(dyadic, interval._mpi_)
    assert lo <= a <= b <= hi, (case, key)


def run(case, a, b, opposite):
    phi, Q, E = (iv.mpf(0) for _ in range(3))
    for j in range(641):
        w, g = mode(j)
        A = pulse(w,g,0,a)
        B = pulse(w,g*(-1)**j if opposite else g,a,b)
        phi += 4*lam**2*(A.real*B.imag-A.imag*B.real)
        Q += 2*lam**2*abs2(B)
        E += w*lam**2*(abs2(A)+abs2(B))
        if j == 0:
            B0 = B
        if j == 1:
            # |(B0 +/- B1)/sqrt(2)|^2 weighs the occupied normal modes.
            Q += 2*lam**2*((n+c)*abs2(B0+B)+(n-c)*abs2(B0-B))
            contained(case, "two_mode_phase", phi)
            low = phi
        if j == 160:
            contained(case, "160_shell_phase", phi)
    ph_err, q_err, e_err = tails(640, lam)
    ph = phi+iv.mpf([-1,1])*ph_err
    atten = Q+iv.mpf([0,1])*q_err
    energy = E+iv.mpf([0,1])*e_err
    coherence = iv.exp(-atten)*iv.sin(ph)
    for key, val in (("field_phase",ph), ("damping_exponent",atten),
                     ("signed_imag_coherence",coherence), ("bare_energy_gain",energy),
                     ("phase_tail_upper",tails(160,lam)[0])):
        contained(case,key,val)
    if opposite:
        assert 0 in ph and 0 in coherence and low > iv.mpf(".0013")
    else:
        assert ph > iv.mpf(".209") and coherence > iv.mpf(".145")
    show = lambda x: float(x.mid)
    print(case, "two_mode_phi,full_phi,Q,Im_z,E", *map(show,(low,ph,atten,coherence,energy)))


if __name__ == "__main__":
    assert 0 < p and p < 1
    assert L/2-2*radius > iv.mpf(2)/5
    w, g = mode(1)
    assert iv.mpf(3)/2 in w and iv.mpf(3)/5 in g
    run("timelike_access",iv.mpf(2)/3,iv.mpf(3)/4,False)
    run("spacelike",iv.mpf(1)/5,iv.mpf(1)/5,True)
    print("L,R,p,spacelike_margin",*[float(x.mid) for x in (L,radius,p,L/2-2*radius-iv.mpf(2)/5)])
    for M in (96,160,640):
        print("M, tail bounds (phi,Q,E), lambda=.3",M,*[float(x.b) for x in tails(M,lam)])
    print("PASS, 14 interval containment checks, matched g, and causal support")
