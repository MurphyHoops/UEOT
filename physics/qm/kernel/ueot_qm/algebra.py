"""Small exact complex matrices over Q(i); no floating-point coercions.

Positive semidefiniteness is decided by every principal minor.  The public
positivity/density checks deliberately support dimensions 1 through 4 only.
This is an executable finite-dimensional calculation, not a Lean proof.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Iterable


MAX_PSD_DIMENSION = 4


def rational(value: int | Fraction) -> Fraction:
    """Accept an exact integer or Fraction, and reject floats and strings."""
    if not isinstance(value, (int, Fraction)):
        raise TypeError("an exact int or Fraction is required")
    return Fraction(value)


@dataclass(frozen=True, slots=True, eq=False)
class QComplex:
    """A Gaussian rational with exact real and imaginary parts."""

    real: Fraction = Fraction(0)
    imag: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, "real", rational(self.real))
        object.__setattr__(self, "imag", rational(self.imag))

    @staticmethod
    def coerce(value: QComplex | int | Fraction) -> QComplex:
        if isinstance(value, QComplex):
            return value
        return QComplex(rational(value))

    def __add__(self, other: QComplex | int | Fraction) -> QComplex:
        other = self.coerce(other)
        return QComplex(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self) -> QComplex:
        return QComplex(-self.real, -self.imag)

    def __sub__(self, other: QComplex | int | Fraction) -> QComplex:
        return self + -self.coerce(other)

    def __rsub__(self, other: QComplex | int | Fraction) -> QComplex:
        return self.coerce(other) - self

    def __mul__(self, other: QComplex | int | Fraction) -> QComplex:
        if isinstance(other, Matrix):
            return NotImplemented
        other = self.coerce(other)
        return QComplex(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    __rmul__ = __mul__

    def conjugate(self) -> QComplex:
        return QComplex(self.real, -self.imag)

    def abs2(self) -> Fraction:
        return self.real * self.real + self.imag * self.imag

    def __truediv__(self, other: QComplex | int | Fraction) -> QComplex:
        other = self.coerce(other)
        denominator = other.abs2()
        if not denominator:
            raise ZeroDivisionError("division by zero Gaussian rational")
        numerator = self * other.conjugate()
        return QComplex(numerator.real / denominator, numerator.imag / denominator)

    def __rtruediv__(self, other: QComplex | int | Fraction) -> QComplex:
        return self.coerce(other) / self

    def __bool__(self) -> bool:
        return bool(self.real or self.imag)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, QComplex):
            return self.real == other.real and self.imag == other.imag
        if isinstance(other, (int, Fraction)):
            return not self.imag and self.real == other
        return NotImplemented

    def __hash__(self) -> int:
        return hash(self.real) if not self.imag else hash((self.real, self.imag))


Scalar = QComplex | int | Fraction


@dataclass(frozen=True, slots=True, init=False)
class Matrix:
    """An immutable nonempty rectangular matrix of Gaussian rationals."""

    rows: tuple[tuple[QComplex, ...], ...]

    def __init__(self, rows: Iterable[Iterable[Scalar]]) -> None:
        data = tuple(tuple(QComplex.coerce(x) for x in row) for row in rows)
        if not data or not data[0]:
            raise ValueError("matrix dimensions must be positive")
        if any(len(row) != len(data[0]) for row in data):
            raise ValueError("matrix rows must have equal lengths")
        object.__setattr__(self, "rows", data)

    @property
    def nrows(self) -> int:
        return len(self.rows)

    @property
    def ncols(self) -> int:
        return len(self.rows[0])

    @property
    def shape(self) -> tuple[int, int]:
        return self.nrows, self.ncols

    @property
    def is_square(self) -> bool:
        return self.nrows == self.ncols

    def __getitem__(self, index):
        if isinstance(index, tuple):
            i, j = index
            return self.rows[i][j]
        return self.rows[index]

    def __iter__(self):
        return iter(self.rows)

    def __add__(self, other: Matrix) -> Matrix:
        if not isinstance(other, Matrix):
            return NotImplemented
        if self.shape != other.shape:
            raise ValueError("matrix shapes differ")
        return Matrix(
            [self[i, j] + other[i, j] for j in range(self.ncols)]
            for i in range(self.nrows)
        )

    def __neg__(self) -> Matrix:
        return self * -1

    def __sub__(self, other: Matrix) -> Matrix:
        return self + -other

    def __mul__(self, scalar: Scalar) -> Matrix:
        scalar = QComplex.coerce(scalar)
        return Matrix([entry * scalar for entry in row] for row in self.rows)

    __rmul__ = __mul__

    def __truediv__(self, scalar: Scalar) -> Matrix:
        return self * (QComplex(1) / scalar)

    def __matmul__(self, other: Matrix) -> Matrix:
        if not isinstance(other, Matrix):
            return NotImplemented
        if self.ncols != other.nrows:
            raise ValueError("matrix product dimensions do not match")
        return Matrix(
            [
                sum((self[i, k] * other[k, j] for k in range(self.ncols)), QComplex())
                for j in range(other.ncols)
            ]
            for i in range(self.nrows)
        )

    def adjoint(self) -> Matrix:
        return Matrix(
            [self[j, i].conjugate() for j in range(self.nrows)]
            for i in range(self.ncols)
        )

    def trace(self) -> QComplex:
        if not self.is_square:
            raise ValueError("trace requires a square matrix")
        return sum((self[i, i] for i in range(self.nrows)), QComplex())

    def determinant(self) -> QComplex:
        """Exact Gaussian elimination, including row-swap signs."""
        if not self.is_square:
            raise ValueError("determinant requires a square matrix")
        work = [list(row) for row in self.rows]
        answer = QComplex(1)
        n = self.nrows
        for column in range(n):
            pivot = next((r for r in range(column, n) if work[r][column]), None)
            if pivot is None:
                return QComplex()
            if pivot != column:
                work[column], work[pivot] = work[pivot], work[column]
                answer = -answer
            value = work[column][column]
            answer *= value
            for row in range(column + 1, n):
                factor = work[row][column] / value
                for j in range(column + 1, n):
                    work[row][j] -= factor * work[column][j]
                work[row][column] = QComplex()
        return answer

    def is_hermitian(self) -> bool:
        return self.is_square and self == self.adjoint()

    def is_psd(self) -> bool:
        """Check all principal minors; dimensions above 4 are unsupported."""
        if not self.is_square:
            return False
        require_small_dimension(self.nrows)
        if not self.is_hermitian():
            return False
        for size in range(1, self.nrows + 1):
            for indices in combinations(range(self.nrows), size):
                minor = Matrix([self[i, j] for j in indices] for i in indices)
                value = minor.determinant()
                if value.imag or value.real < 0:
                    return False
        return True

    def is_density(self) -> bool:
        return self.is_psd() and self.trace() == 1


def require_small_dimension(dimension: int) -> None:
    if not isinstance(dimension, int) or not 1 <= dimension <= MAX_PSD_DIMENSION:
        raise ValueError(f"supported Hilbert dimensions are 1..{MAX_PSD_DIMENSION}")


def zeros(nrows: int, ncols: int | None = None) -> Matrix:
    ncols = nrows if ncols is None else ncols
    if not isinstance(nrows, int) or not isinstance(ncols, int) or nrows < 1 or ncols < 1:
        raise ValueError("matrix dimensions must be positive integers")
    return Matrix([0] * ncols for _ in range(nrows))


def identity(dimension: int) -> Matrix:
    if not isinstance(dimension, int) or dimension < 1:
        raise ValueError("matrix dimension must be a positive integer")
    return Matrix([int(i == j) for j in range(dimension)] for i in range(dimension))


def diagonal(entries: Iterable[Scalar]) -> Matrix:
    entries = tuple(QComplex.coerce(x) for x in entries)
    return Matrix(
        [entries[i] if i == j else 0 for j in range(len(entries))]
        for i in range(len(entries))
    )


def outer(ket: Iterable[Scalar]) -> Matrix:
    """Return |ket><ket|; normalization is the caller's explicit choice."""
    vector = tuple(QComplex.coerce(x) for x in ket)
    return Matrix([x * y.conjugate() for y in vector] for x in vector)


def real_trace(matrix: Matrix) -> Fraction:
    value = matrix.trace()
    if value.imag:
        raise ValueError("expected an exactly real trace")
    return value.real


def validate_density(state: Matrix, dimension: int | None = None) -> Matrix:
    if not isinstance(state, Matrix):
        raise TypeError("state must be a Matrix")
    if dimension is not None and state.shape != (dimension, dimension):
        raise ValueError("state dimension does not match the instrument")
    if not state.is_density():
        raise ValueError("state must be Hermitian, PSD, and trace one")
    return state


def hermitian_vector(matrix: Matrix) -> tuple[Fraction, ...]:
    """Real coordinates: diagonal, then upper-triangle real/imag pairs."""
    if not matrix.is_hermitian():
        raise ValueError("real Hermitian coordinates require a Hermitian matrix")
    result = [matrix[i, i].real for i in range(matrix.nrows)]
    for i in range(matrix.nrows):
        for j in range(i + 1, matrix.ncols):
            result.extend((matrix[i, j].real, matrix[i, j].imag))
    return tuple(result)


def linear_coordinates(
    basis: Iterable[tuple[Fraction, ...]], target: tuple[Fraction, ...]
) -> tuple[Fraction, ...] | None:
    """Solve target=sum(c_i*basis_i) exactly; basis must be independent.

    None means target is outside the span.  A dependent input basis is an
    error rather than an arbitrary choice of a nonunique coordinate vector.
    """
    basis = tuple(tuple(rational(x) for x in vector) for vector in basis)
    target = tuple(rational(x) for x in target)
    width = len(basis)
    if any(len(vector) != len(target) for vector in basis):
        raise ValueError("real coordinate dimensions differ")
    if not basis:
        return () if not any(target) else None
    augmented = [
        [basis[j][i] for j in range(width)] + [target[i]]
        for i in range(len(target))
    ]
    pivot_rows = []
    row = 0
    for column in range(width):
        pivot = next((r for r in range(row, len(target)) if augmented[r][column]), None)
        if pivot is None:
            raise ValueError("basis vectors must be linearly independent")
        augmented[row], augmented[pivot] = augmented[pivot], augmented[row]
        divisor = augmented[row][column]
        augmented[row] = [x / divisor for x in augmented[row]]
        for r in range(len(target)):
            if r != row and augmented[r][column]:
                factor = augmented[r][column]
                augmented[r] = [a - factor * b for a, b in zip(augmented[r], augmented[row])]
        pivot_rows.append(row)
        row += 1
    if any(not any(record[:width]) and record[-1] for record in augmented):
        return None
    return tuple(augmented[r][-1] for r in pivot_rows)


def matrix_payload(matrix: Matrix) -> list:
    """Canonical JSON-compatible exact entries, used for context hashes."""
    return [
        [
            [z.real.numerator, z.real.denominator, z.imag.numerator, z.imag.denominator]
            for z in row
        ]
        for row in matrix.rows
    ]
