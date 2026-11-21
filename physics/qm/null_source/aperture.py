"""Exact transverse source checks for the metric convention used by weak_lens.py."""
import sympy as s

u, v, x, y = s.symbols("u v x y", real=True)
H = s.Function("H")(u, x, y)
field = s.Function("field")(u, x, y)
coords = (u, v, x, y)
g = s.Matrix([[-H, -1, 0, 0], [-1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
gradient = s.Matrix([field.diff(q) for q in coords])
kinetic = (gradient.T * g.inv() * gradient)[0]
assert (gradient[0]*gradient[1] - g[0,1]*kinetic/2
        == (field.diff(x)**2 + field.diff(y)**2)/2)
assert sum(s.diff(j, q) for j, q in zip(g.inv()*gradient, coords)) == field.diff(x, 2)+field.diff(y, 2)

r, a, b = s.symbols("r a b", positive=True)
cut = s.log(b/r)/s.log(b/a)
assert cut.subs(r, a) == 1 and cut.subs(r, b) == 0
assert s.simplify(s.integrate(r*cut.diff(r)**2, (r, a, b)) - 1/s.log(b/a)) == 0

# Area coordinate makes both radial flux and the smooth taper polynomial.
q = s.symbols("q", real=True)
eta = 1-10*q**3+15*q**4-6*q**5
assert [eta.subs(q, 0), eta.subs(q, 1)] == [1, 0]
assert s.factor(eta.diff(q)) == -30*q**2*(q-1)**2
area_coordinate = (r**2-a**2)/(b**2-a**2)
mass = (a**2+(b**2-a**2)*s.integrate(eta, (q, 0, area_coordinate)))/2  # integral of r*eta(r)
assert s.simplify(mass.diff(r)-r*eta.subs(q, area_coordinate)) == 0
assert s.simplify(mass.subs(r, a)-a**2/2) == 0
assert s.simplify(mass.subs(r, b)-(a**2+b**2)/4) == 0
# For 4 pi G=1 and central density rho, H'=4*rho*mass/r. Core and exterior limits.
rho = s.symbols("rho", positive=True)
slope = 4*rho*mass/r
assert s.simplify((slope.diff(r)+slope/r)/2-2*rho*eta.subs(q, area_coordinate)) == 0
assert s.simplify(slope.subs(r, a)-2*rho*a) == 0
assert s.simplify(slope.subs(r, b)-rho*(a**2+b**2)/b) == 0
print("PASS: scalar stress, transverse wave equation, sharp annular bound, finite-flux dust metric")
