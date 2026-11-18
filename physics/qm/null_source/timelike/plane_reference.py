"""Local reference stress on the original isotropic plane wave, and a finite-sphere causal control."""
from fractions import Fraction as F
from pathlib import Path
import json

import sympy as s

HERE=Path(__file__).resolve().parent


def plane():
    U,v,x,y, V,z,X,Y=s.symbols("U v x y V z X Y",real=True)
    left,right=(U,v,x,y),(V,z,X,Y)
    h=s.Function("h")
    p2=h(U).diff(U)  # affine Brinkmann du = p² dU
    slope=(h(U)-h(V))/(U-V)
    flat=-(U-V)*(v-z)+((x-X)**2+(y-Y)**2)/2
    sigma=slope*flat
    grad=s.Matrix([sigma.diff(t) for t in left])
    eta=s.Matrix([[0,-1,0,0],[-1,0,0,0],[0,0,1,0],[0,0,0,1]])
    assert s.factor((grad.T*eta*grad)[0]-2*p2*sigma)==0
    mixed=s.Matrix(4,4,lambda i,j: -sigma.diff(left[i],right[j]))
    rhs=p2*h(V).diff(V)*slope**2
    assert all(mixed[1,j]==mixed[j,1]==0 for j in (1,2,3))
    det=-mixed[0,1]*mixed[1,0]*mixed[2:,2:].det()
    assert s.factor(det+rhs)==0
    # sqrt(Delta)=slope/(p(U)p(V)); Box of any one-null-coordinate function vanishes.
    density_inv_metric=p2*eta
    b=s.Function("b")(U)
    assert sum(s.diff(sum(density_inv_metric[i,j]*b.diff(q) for j,q in enumerate(left)),t)
               for i,t in enumerate(left))==0
    p=s.Function("p")(U)
    K=-s.diff(p.diff(U)/p**2,U)/p**3
    ric=-2*s.diff(s.log(p),U,2)+2*s.diff(s.log(p),U)**2
    assert s.simplify(ric-2*K*p**4)==0
    # Full Ricci-Hessian-squared counterterms also involve Riemann_ambn Ric^mn.
    # In Brinkmann coordinates curvature has only R_uiuj, while Ric^ab is proportional to vv.
    base=json.loads((HERE.parent/'probe/observed.json').read_bytes())
    row=next(r for r in base['rows'] if r['A']==.25 and r['xi']==0)
    assert row['probabilities']['Y'][0]>.59 and row['variance']>0
    return dict(vacuum_hadamard_remainder="zero on a convex Rosen chart for the specified pullback",
                renormalization="Minkowski vacuum normalized; measured G; cosmological term zero",
                original_probe_Y_plus=row['probabilities']['Y'][0],scope="source-only mean equation; original isotropic sandwich")


def monitor():
    radius, half=F(25,64), F(1,128)
    first, last, report=F(1,32), F(3,16), F(3,8)
    # arcsin(1/sqrt(3)) > .60 from alternating Taylor bound for sine.
    x=F(3,5)
    assert (x-x**3/6+x**5/120)**2<F(1,3)
    assert radius+half+last < x
    assert radius-half > report
    assert radius-half+first > report
    # All points in the detector are causally too late to affect the central collection.
    # Homogeneity of the empty core and transfer in the actual apparatus are separate conditions.
    return dict(max_eta_plus_chi=str(radius+half+last),min_arrival_eta=str(radius-half+first),
                geometry_received_eta=str(report),initial_chi_margin=str(radius-half-report),
                earliest_common_report_if_inward="after monitor signals arrive; no positive-flag conditioning")


if __name__=="__main__":
    print(json.dumps(dict(plane=plane(),monitor=monitor()),indent=2))
