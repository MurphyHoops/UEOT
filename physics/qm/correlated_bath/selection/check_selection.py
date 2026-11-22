"""Exact finite witnesses for the selection adjudication. Run with the supplied venv."""
import unittest

from sympy import I, Matrix, Rational, diag, eye, kronecker_product as tensor
from sympy import simplify, sqrt, symbols, zeros

half = Rational(1, 2)
unit = eye(2)
x = Matrix([[0, 1], [1, 0]])
y = Matrix([[0, -I], [I, 0]])
z = diag(1, -1)
p0, p1 = (unit + z) / 2, (unit - z) / 2


class SelectionWitnesses(unittest.TestCase):
    def test_path_of_real_and_complex_controls(self):
        t = symbols("t", real=True)
        rotation = Matrix([[1-t*t, -2*t], [2*t, 1-t*t]]) / (1+t*t)
        for generator in (rotation, diag(1, I) * rotation * diag(1, -I)):
            self.assertEqual(simplify(generator.H * generator), unit)
            path = generator * p0 * generator.H
            self.assertEqual(path.subs(t, 0), p0)
            self.assertEqual(path.subs(t, 1), p1)
            self.assertEqual(simplify(path**2 - path), zeros(2))

    def test_discrete_swap_and_mixed_midpoint(self):
        self.assertEqual(x * p0 * x, p1)
        midpoint = (p0 + p1) / 2
        self.assertEqual(midpoint.trace(), 1)
        self.assertEqual(midpoint.det(), Rational(1, 4))
        self.assertEqual((p0 * midpoint).trace(), half)
        self.assertEqual((p0 * p1).trace(), 0)

    def test_hidden_extension_with_entangled_reference(self):
        # Visible qubit + hidden scalar, tensored with an untouched realisation of R=C^2.
        bell = Matrix([1, 0, 0, 1])
        visible = bell * bell.H / 2
        source = diag(visible, zeros(2))
        weights = [Rational(2, 5), Rational(3, 5)]
        continued = zeros(6)
        for effect, correction, weight in zip((p0, p1), (unit, x), weights):
            branch = tensor(correction * effect, unit)
            # Hidden weight w_y uses a CP branch with Kraus sqrt(w_y) I_R.
            extended = diag(branch, sqrt(weight) * unit)
            expected = branch * visible * branch.H
            self.assertEqual(extended * source * extended.H, diag(expected, zeros(2)))
            self.assertEqual(expected.trace(), half)
            continued += extended.H * extended
        self.assertEqual(continued, eye(6))

    def test_real_composite_invisible_coordinate(self):
        j = Matrix([[0, -1], [1, 0]])
        witness = tensor(j, j)
        plus, minus = (eye(4) + witness) / 2, (eye(4) - witness) / 2
        for projector in (plus, minus):
            self.assertEqual(projector.T, projector)
            self.assertEqual(projector**2, projector)
            self.assertEqual(projector.trace(), 2)
        delta = (plus - minus) / 2
        for a in (unit, x, z):
            for b in (unit, x, z):
                self.assertEqual((tensor(a, b) * delta).trace(), 0)
        self.assertEqual(((plus * plus / 2).trace(), (plus * minus / 2).trace()), (1, 0))

    def test_restricted_effects_and_tomography(self):
        visibility = half
        effects = [unit] + [(unit + visibility * axis) / 2 for axis in (x, y, z)]
        local = Matrix.hstack(*(e.reshape(4, 1) for e in effects))
        products = [tensor(a, b).reshape(16, 1) for a in effects for b in effects]
        self.assertEqual(local.rank(), 4)
        self.assertEqual(Matrix.hstack(*products).rank(), 16)
        e = effects[-1]
        self.assertEqual(((e*p0).trace(), (e*p1).trace()), (Rational(3, 4), Rational(1, 4)))
        # A Bell projector gives 1 on the Bell ray and 1/2 on |00>.
        bell = Matrix([1, 0, 0, 1])
        projector = bell * bell.H / 2
        self.assertEqual((projector**2).trace(), 1)
        self.assertEqual((projector * tensor(p0, p0)).trace(), half)


if __name__ == "__main__":
    unittest.main(verbosity=2)
