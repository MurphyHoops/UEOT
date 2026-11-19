"""Independent algebra review of the physical-interval dynamics and local RSET.

The tensor formulas are transcribed from Anderson--Eaker (1999), Eqs. 10--14,
and independently reduced using c=cos(2 eta), s=sin(2 eta). This script does
not certify propagated modes, infinite spectral sums or backreaction.
"""
import argparse
import json
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent


def review():
    if not __debug__:
        raise RuntimeError("Algebra review requires assertions; do not use -O")
    c, s, L = sp.symbols("c s L", real=True)
    a = sp.sqrt(3*c)
    def D(f):
        return -2*s*sp.diff(f,c)+2*c*sp.diff(f,s)-2*s/c*sp.diff(f,L)
    def reduce(f):
        f = sp.expand(f)
        return sp.factor(f.subs(s**6,(1-c*c)**3)
                          .subs(s**4,(1-c*c)**2).subs(s*s,1-c*c))
    derivatives = [a]
    for _ in range(4):
        derivatives.append(sp.simplify(D(derivatives[-1])))
    a1,a2,a3,a4 = derivatives[1:]
    h = a1/a
    H1 = reduce(-36*a3*a1/a**6 + 72*a2*a1*a1/a**7 + 18*a2*a2/a**6
                + 36*a1*a1/a**6 - 18/a**4)
    T1 = reduce(-36*a4/a**5 + 144*a3*a1/a**6 - 216*a2*a1*a1/a**7
                + 108*a2*a2/a**6 + 72*a2/a**5 - 72*a1*a1/a**6)
    H3 = reduce(3*a1**4/a**8 + 6*a1*a1/a**6 + 3/a**4)
    T3 = reduce(12*a2*a1*a1/a**7 - 12*a1**4/a**8
                + 12*a2/a**5 - 12*a1*a1/a**6)
    # Multiply both stress components by pi^2 until the final displayed formula.
    rho = reduce((-H1/6+H3)/2880 - H1/1728
                 + (H1*(2+L)/32 - sp.Rational(9,4)
                    *(a1*a1*a2/a**7+a1*a1/a**6))/36)
    trace_AE = reduce((-T1/6+T3)/2880 - T1/1728
                      + (T1*(2+L)/32 - sp.Rational(9,8)
                         *(4*a3*a1/a**6-10*a2*a1*a1/a**7+3*a2*a2/a**6
                           +4*a2/a**5-6*a1*a1/a**6+1/a**4))/36)
    pressure = reduce((rho-trace_AE)/3)
    expected_rho = ((168+180*L)*c*c-110-135*L)/(8640*c**6)
    expected_p = ((160+300*L)*c*c-240-405*L)/(8640*c**6)
    assert reduce(rho-expected_rho) == 0
    assert reduce(pressure-expected_p) == 0
    assert reduce(D(rho)+3*h*(rho+pressure)) == 0
    assert reduce(H1-6*(4*c*c-3)/c**6) == 0
    assert reduce(2*sp.diff(rho,L)-H1/576) == 0
    # In the physical interior, the transformed equation is Legendre's equation.
    k,w,w1,w2 = sp.symbols("k w w1 w2", real=True)
    def DL(f):
        return (-2*s*sp.diff(f,c)+2*c*sp.diff(f,s)
                +2*c*w1*sp.diff(f,w)+2*c*w2*sp.diff(f,w1))
    v = sp.sqrt(c)*w
    nu = (k-1)/2
    residual = DL(DL(v))+(k*k+c**-2)*v
    residual = residual.subs(w2,(2*s*w1-nu*(nu+1)*w)/c**2)
    assert reduce(residual) == 0
    # Ferrers Wronskian in x is 1/(1-x^2); transformed Wronskian is 2.
    assert sp.simplify(c*(2*c)/c**2-2) == 0
    # A useful check on identifying a finite-rank shell against a stiff source.
    f = 1/c-c/2
    g = c**-3
    relative = sp.simplify(f/g)
    assert sp.simplify(relative-(c*c-c**4/2)) == 0
    assert sp.diff(relative,c).subs(c,1) == 0
    assert sp.diff(relative,c,2).subs(c,1) == -4
    return {
        "schema": "ueot-dynamic-independent-algebra/1",
        "reference_base": "987dd4ccc58d0086cc1305e99b5cdb67f8127fde",
        "H1_energy": str(H1),
        "H1_trace_AE": str(T1),
        "H3_energy": str(H3),
        "pi_squared_rho_analytic": str(rho),
        "pi_squared_pressure_analytic": str(pressure),
        "L": "log(3*c*mu**2/4)+2*EulerGamma; c=cos(2*eta)",
        "local_tensor_conservation": "exact symbolic identity",
        "scale_derivative": "d rho/d log(mu)=H1_energy/(576*pi**2)",
        "Legendre_degree": "(k-1)/2",
        "physical_fundamental_solutions": "sqrt(cos(2eta))*FerrersP_or_Q(nu,sin(2eta))",
        "physical_fundamental_Wronskian_eta": 2,
        "shell_to_stiff_ratio": str(relative),
        "near_turning_point_first_derivative_of_ratio": 0,
        "near_turning_point_second_derivative_of_ratio": -4,
        "scope": "local analytic terms and exact physical-interval identities only",
        "certifies_dynamic_mode_sum": False,
        "sources": ["https://arxiv.org/pdf/gr-qc/9906055", "https://dlmf.nist.gov/14.2"]
    }


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    data=review()
    path=HERE/"algebra.json"
    if args.write:
        path.write_text(json.dumps(data,indent=2,ensure_ascii=False)+"\n")
    if args.check:
        assert data==json.loads(path.read_text())
        print("PASS independent local RSET, scale covariance and Legendre identities")
    else:
        print(json.dumps(data,indent=2,ensure_ascii=False))
