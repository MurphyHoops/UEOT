"""Distinguish free spectra with interior, exterior and independently prepared thermal data."""
from fractions import Fraction as Fr
import json
from mpmath import iv
import sympy as s
from anomaly import q, interval

# Free real conformal scalars, two-component Weyl fermions, independent Maxwell fields.
ANOMALIES=s.Matrix([[1,s.Rational(11,2),62],[1,3,12]])  # 360 a_E and 120 c_W


def thermal(beta, nmax=32):
    # Independent physical oscillators. The conformal inverse temperature is dimensionless.
    b=q(beta)
    x=iv.exp(-b)
    sums=[q(0) for _ in range(3)]
    for n in range(1,nmax+1):
        e=q(n)
        f=e+q(Fr(1,2))
        sums[0]+=n*n*e/(iv.exp(b*e)-1)
        sums[1]+=2*n*(n+1)*f/(iv.exp(b*f)+1)
        sums[2]+=2*(n*n-1)*e/(iv.exp(b*e)-1)
    # For n>=1 all three terms <= 8 n^3 exp(-beta*n)/(1-exp(-beta)).
    m=nmax+1
    ratio=(q(Fr(m+1,m))**3)*x
    assert ratio<1
    remainder=8*m**3*x**m/((1-x)*(1-ratio))
    return [(v+iv.mpf([0,remainder.b]))/(2*iv.pi**2) for v in sums]


def energy(counts, coeff):
    return sum(k*v for k,v in zip(counts,coeff))


def main():
    cold_a=s.Matrix([11,0,0])
    cold_b=s.Matrix([0,2,0])
    difference=ANOMALIES*(cold_a-cold_b)
    assert list(difference)==[0,5]
    mu=q(Fr(7565,26208))
    tide=48*mu**2*(q(2)**-6-q(3)**-6)
    outside=(q(Fr(5,120))*tide)/(16*iv.pi**2)
    assert outside>0
    direction=s.Matrix([48,-20,1])
    assert ANOMALIES.rank()==2 and ANOMALIES*direction==s.zeros(2,1)
    first, second = (48,0,1),(0,20,0)
    design=thermal(3)
    response=energy(first, design)-energy(second,design)
    assert 0 not in response
    # Fit the exterior/interior ambiguity at one temperature. Common anomaly scores are 110 and 60.
    # The two exact rational rows restrict any integer spectrum with these scores to k=0 or 1.
    assert ANOMALIES*s.Matrix(first)==ANOMALIES*s.Matrix(second)==s.Matrix([110,60])
    observed=energy(second,design)+iv.mpf([-1,1])*q('0.001')
    estimated_k=(observed-energy(second,design))/response
    assert 0 in estimated_k and 1 not in estimated_k
    hold=thermal(4)
    bands=[energy(n,hold)+iv.mpf([-1,1])*q('0.001') for n in (first,second)]
    assert bands[0]>bands[1] or bands[1]>bands[0]
    return dict(exterior_trace_difference_11_scalars_minus_2_Weyl=interval(outside),
                exterior_areal_radii=[2,3],finite_source_GM="7565/26208",
                heat_row_at_beta3=[interval(v) for v in design],
                thermal_3_difference=interval(response),integer_family_fit=interval(estimated_k),
                thermal_4_heldout_48scalars_1vector=interval(bands[0]),
                thermal_4_heldout_20weyl=interval(bands[1]))


if __name__=="__main__":
    print(json.dumps(main(),indent=2))
