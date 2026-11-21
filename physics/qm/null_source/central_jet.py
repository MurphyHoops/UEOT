"""Cross-check the first dynamical readouts of the compact scalar initial slice."""
import sympy as s
from geometry.sphere import flux

r = s.symbols("r", positive=True)
for amp in (1, -1):
    psi = s.expand(1+flux(r,amp)/r+(1-r*r)**9/s.Integer(72))
    normal_field = s.Integer(amp)*(1-r*r)**4/psi**s.Rational(5,2)
    pi0 = normal_field.subs(r,0)
    # Radial Laplace-Beltrami at a regular center with vanishing first spatial derivative.
    lap = 3*s.diff(normal_field,r,2).subs(r,0)/psi.subs(r,0)**4
    volume_acc = -2*pi0**2                         # Raychaudhuri at K_ij=0; 4 pi G=1
    cubic = lap - volume_acc*pi0                    # differentiate scalar wave equation
    f0 = s.Rational(73,72)
    assert s.simplify(volume_acc+2/f0**5)==0
    assert s.simplify(cubic/pi0 - (3*(-8+5/(24*f0))/f0**4+2/f0**5)) == 0
    print(f"A={amp:+d}, Pi={float(pi0):+.9f}, V''/V={float(volume_acc):+.9f}, phi'''={float(cubic):+.9f}")
