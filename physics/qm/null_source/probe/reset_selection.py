"""Energy reset bound and a zero-energy real simulation of the archived weak-field record."""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

import numpy as np

SELECTION = Path(__file__).resolve().parents[2] / "operational_closure/selection"
sys.path.insert(0, str(SELECTION))
import network as net


def certifies(energy, gaps, other_tv, radius):
    if len(energy) != 2 or len(gaps) != 2 or min(gaps) <= 0 or min(energy) < 0 or other_tv < 0:
        raise ValueError("need two nonnegative energy bounds, two positive gaps and nonnegative TV")
    slack = radius - other_tv
    return slack > 0 and sum(e/d for e,d in zip(energy,gaps)) < slack**2


def degenerate_control(inputs):
    # At weak lambda the three exponents shrink by 10^-4. Use archived interval midpoints.
    qa,qb,c = [float(sum(map(F,inputs[key]))/20000) for key in ('Q_left','Q_right','cross')]
    logical = np.indices((2,2)).reshape(2,4).T
    dl,dr = np.moveaxis(logical[:,None,:]-logical[None,:,:],-1,0)
    rho = np.zeros((16,16))
    rho[np.ix_([0,3,12,15],[0,3,12,15])] = np.exp(-qa*dl**2-qb*dr**2-c*dl*dr)/4
    target = net.probabilities(rho)

    # The retained phase rebit on each side costs zero for either of its levels.
    tau = (np.eye(4)-np.kron(net.J,net.J))/4
    state = net.reference_state(tau)  # after local Bell-pair preparation
    H = np.kron(np.diag([0,1,1,1]),np.eye(2))  # local order: link data, phase flag
    gap_count = np.linalg.eigvalsh(H)
    assert (gap_count==0).sum()==2 and min(gap_count[gap_count>0])==1
    vacuum = np.diag([1,0,0,0])
    reset_marginal = np.kron(vacuum,np.eye(2)/2)
    assert np.trace(H@reset_marginal)==0
    assert np.trace(tau@np.kron(net.J,net.J)) == -1
    assert np.abs(np.linalg.eigvalsh(tau-np.eye(4)/4)).sum()/2 == .5

    # A fair classical bit flips BOTH phase angles. The even/odd Bell coherences
    # are cos(l+r) and cos(l-r), matching the target at all 18 settings.
    even,odd = np.arccos(np.exp([-qa-qb-c,-qa-qb+c]))
    left,right = (even+odd)/2,(even-odd)/2
    def rotated(obs,angle):
        u=np.diag([1,np.exp(1j*angle)])
        m=u.conj().T@obs@u
        return np.array([np.kron(o.real,net.I)+np.kron(o.imag,net.J) for o in m])
    tables = [net.born(state,rotated(net.AXES,s*left),net.BSM,rotated(net.CHARLIE,s*right))
              for s in (-1,1)]
    simulated = (tables[0]+tables[1])/2
    error = np.max(abs(simulated-target))
    assert error<2e-15
    return net.score(simulated),float(error)


def main():
    if not __debug__:
        raise RuntimeError("enable assertions")
    receipt=json.loads((SELECTION/"source_review.json").read_text(),parse_float=F)
    weak=receipt["lambda_0_003"]
    root=json.loads((SELECTION.parent/"source_result.json").read_text())
    radius=F(root["excluded_real_neighborhood_TV_radius"])
    assert F(root["weak_lambda"])==F("0.003") and radius==F("1e-7")
    assert 33*radius<weak["sufficient_all_branch_margin_lower"] and radius<F("7e-5")
    assert radius<weak["sufficient_extra_uniform_TV_radius_lower"]
    gaps=(F(1),F(2))
    energy=tuple(d*F('8e-16') for d in gaps)
    other=F('5e-8')
    assert sum(e/d for e,d in zip(energy,gaps))==F('4e-8')**2
    assert certifies(energy,gaps,other,radius)
    assert not certifies((F('1e-12'),F('2e-12')),gaps,other,radius)
    (t, branches),error=degenerate_control(receipt["scientific_inputs"])
    np.testing.assert_allclose(branches,list(map(float,weak["T_b"])),rtol=0,atol=2e-12)
    print(f"E1 weak radius={float(radius):g}; delta_reset<=4e-8; other_TV<=5e-8; total<=9e-8: inside")
    print("Each energy/gap=1e-12: inconclusive")
    print(f"Degenerate ground: energies=(0,0); real separable distance=0.5; T={t:.12f}; 288-cell max error={error:.2g}")


if __name__=='__main__':
    main()
