"""Equal charge/Yukawa rule, two-channel fit obstruction, torus transition checks."""
import cmath
import json
import math
from fractions import Fraction as F


def matter(N, families, k):
    beta_L = 11-F(families*(N+1),3)-F(3,6)
    beta_C = F(11*N,3)-2*families
    assert families+N*(2*k-families)==0 and beta_L>0 and beta_C>0
    up, down = F(N+1,2*N), -F(N-1,2*N)
    plus, minus = F(1,2*N)-F(1,6), F(1,2*N)+F(1,6)
    scalars = {-F(2,3),F(1,3)}
    for charge in (up,down):
        assert plus-charge in scalars and charge-minus in scalars
    assert up-down==1 and (N*down).denominator==1
    assert F(1,2*N)-F(1,2)==down and F(1,2*N)+F(1,2)==up
    assert all((x+t).denominator==1 for x in scalars for t in [F(2,3),-F(1,3)])
    return dict(N=N,quark_charges=[str(up),str(down)],b_C=str(beta_C),b_L=str(beta_L),
                color_center_charge_residue=str(down%1),baryon_base_charge=str(N*down))


def wilson(z_d,z_s):
    target=[z_d,z_s]
    strength=4*sum(map(abs,target))
    assert strength>0
    ub=1/math.sqrt(2)
    u=[(cmath.sqrt(z/strength)/ub).conjugate() for z in target]+[ub]
    assert abs(sum(abs(t)**2 for t in u)-1)<1e-13
    def C(i,j):
        return strength*(u[i]*complex(u[j]).conjugate())**2
    assert max(abs(C(2,i)-z) for i,z in enumerate(target))<1e-13
    cycle=C(0,1)*C(1,2)*C(2,0)
    assert abs(cycle.imag)<1e-13 and cycle.real>=0
    return strength,cycle.real


def main():
    candidates=[matter(3,3,1),matter(5,5,2)]
    ms,md=17.7683,.5050
    sd_s,sd_d=math.hypot(.0051,.0032),math.hypot(.0021,.0010)
    ratio=ms/md
    errors=[ratio*abs(sd_s/ms-sd_d/md),ratio*(sd_s/ms+sd_d/md)]
    # Two distinct unseen s-channel NP coefficients, identical trained d channel.
    fits=[wilson(.3+.4j,z) for z in [.2-.1j,-.7+.6j,0j]]
    m=1
    cocycle=lambda y:cmath.exp(2j*math.pi*m*y)
    assert abs(cocycle(.37+1)-cocycle(.37))<1e-14
    print(json.dumps(dict(candidates=candidates,mixing_frequency_ratio=ratio,
        linearized_ratio_sd_unknown_cross_correlation=errors,arbitrary_amplitude_witnesses=fits,
        torus_unit_flux=m),indent=2))


if __name__=="__main__":
    main()
