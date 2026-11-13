"""Finite labelled Kraus tests for the persistent-bath research iteration.

All outcomes, including failure, are retained.  Floating-point validation is a
numerical guard, not a proof of complete positivity for an experimental device.
The carrier must contain all persistent memory when composition is used.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, Mapping
import numpy as np


def adjoint(a):
    return np.asarray(a).conj().T


def trace_norm(a):
    return float(np.linalg.svd(a, compute_uv=False).sum())


def psd_sqrt(a, tol=1e-12):
    vals, vecs = np.linalg.eigh((a + adjoint(a)) / 2)
    if vals.min() < -tol:
        raise ValueError("matrix is not positive semidefinite")
    return (vecs * np.sqrt(np.maximum(vals, 0))) @ adjoint(vecs)


@dataclass(frozen=True)
class FiniteTest:
    din: int
    dout: int
    branches: Mapping[Hashable, tuple[np.ndarray, ...]]

    def completeness_residual(self):
        total = np.zeros((self.din, self.din), complex)
        for ks in self.branches.values():
            for k in ks:
                if k.shape != (self.dout, self.din):
                    raise ValueError("Kraus input/output type mismatch")
                total += adjoint(k) @ k
        return float(np.linalg.norm(total - np.eye(self.din), 2))

    def validate(self, tol=1e-11):
        if self.din < 1 or self.dout < 1 or not self.branches:
            raise ValueError("nonempty finite carriers and outcomes required")
        residual = self.completeness_residual()
        if residual > tol:
            raise ValueError(f"incomplete test: residual {residual}")
        return residual

    def blocks(self, rho, reference_dim=1):
        if rho.shape != (self.din * reference_dim,) * 2:
            raise ValueError("input/reference type mismatch")
        ref = np.eye(reference_dim)
        ans = {}
        for label, ks in self.branches.items():
            z = np.zeros((self.dout * reference_dim,) * 2, complex)
            for k in ks:
                kr = np.kron(k, ref)
                z += kr @ rho @ adjoint(kr)
            ans[label] = z
        return ans

    def choi_blocks(self):
        # Input-major Choi convention: vec(K) in column order.
        ans = {}
        for label, ks in self.branches.items():
            z = np.zeros((self.din * self.dout,) * 2, complex)
            for k in ks:
                v = k.reshape(-1, order="F")
                z += np.outer(v, v.conj())
            ans[label] = z
        return ans

    def then(self, continuations: Mapping[Hashable, "FiniteTest"]):
        if set(continuations) != set(self.branches):
            raise ValueError("one complete continuation is required per outcome")
        dims = {t.dout for t in continuations.values()}
        if len(dims) != 1:
            raise ValueError("use explicit terminal embeddings for differing outputs")
        new = {}
        for y, ks in self.branches.items():
            t = continuations[y]
            if t.din != self.dout:
                raise ValueError("conditional-composition type mismatch")
            for z, ls in t.branches.items():
                new[(y, z)] = tuple(l @ k for k in ks for l in ls)
        return FiniteTest(self.din, dims.pop(), new)

    def parallel(self, other: "FiniteTest"):
        return FiniteTest(
            self.din * other.din,
            self.dout * other.dout,
            {(y, z): tuple(np.kron(k, l) for k in ks for l in ls)
             for y, ks in self.branches.items()
             for z, ls in other.branches.items()},
        )

    def coarse_grain(self, label_map):
        new = {}
        for y, ks in self.branches.items():
            new.setdefault(label_map[y], []).extend(ks)
        return FiniteTest(self.din, self.dout,
                          {y: tuple(ks) for y, ks in new.items()})

    def discard(self):
        new = {}
        for y, ks in self.branches.items():
            new[y] = tuple(k[j:j+1, :] for k in ks for j in range(self.dout))
        return FiniteTest(self.din, 1, new)

    def with_binary_effect(self, effect):
        if effect.shape != (self.dout,) * 2:
            raise ValueError("effect carrier mismatch")
        roots = (psd_sqrt(effect), psd_sqrt(np.eye(self.dout) - effect))
        return FiniteTest(self.din, self.dout,
                          {(y, bit): tuple(root @ k for k in ks)
                           for y, ks in self.branches.items()
                           for bit, root in enumerate(roots)})


def identity_test(d):
    return FiniteTest(d, d, {"id": (np.eye(d, dtype=complex),)})


def frame(d):
    """d^2 legal pure preparations/effects and their Hermitian duals."""
    units = np.eye(d, dtype=complex)
    rho = [np.outer(v, v.conj()) for v in units]
    dual = [x.copy() for x in rho]
    labels = [("diag", j) for j in range(d)]
    for j in range(d):
        for k in range(j+1, d):
            x = np.outer(units[j], units[k]) + np.outer(units[k], units[j])
            y = -1j * np.outer(units[j], units[k]) + 1j * np.outer(units[k], units[j])
            for phase, z in ((1, x), (1j, y)):
                v = (units[j] + phase * units[k]) / np.sqrt(2)
                rho.append(np.outer(v, v.conj()))
                dual.append(z)
                labels.append(("real" if phase == 1 else "imag", j, k))
            dual[j] -= (x + y)/2
            dual[k] -= (x + y)/2
    return labels, np.asarray(rho), np.asarray(dual)


def probabilities(test, preparations, effects):
    labels = list(test.branches)
    ans = np.zeros((len(labels), len(effects), len(preparations)))
    for r, rho in enumerate(preparations):
        blocks = test.blocks(rho)
        for y, label in enumerate(labels):
            for q, effect in enumerate(effects):
                ans[y, q, r] = float(np.trace(effect @ blocks[label]).real)
    return labels, ans


def reconstruct_blocks(p, input_duals, output_duals, x, reference_dim=1):
    """Linear inversion, including an arbitrary explicitly supplied reference."""
    din = input_duals.shape[-1]
    dout = output_duals.shape[-1]
    ans = [np.zeros((dout*reference_dim,) * 2, complex) for _ in p]
    for r, dual in enumerate(input_duals):
        weighted = (np.kron(dual, np.eye(reference_dim)) @ x).reshape(
            din, reference_dim, din, reference_dim)
        coefficient = np.einsum("irij->rj", weighted)
        for y in range(len(p)):
            image = sum(p[y, q, r] * out for q, out in enumerate(output_duals))
            ans[y] += np.kron(image, coefficient)
    return ans


def weighted_diamond_bound(delta, input_duals, output_duals):
    wi = np.array([np.linalg.norm(x, 2) for x in input_duals])
    wo = np.array([trace_norm(x) for x in output_duals])
    return float(np.einsum("r,q,yqr->", wi, wo, np.abs(delta)))


def labelled_choi_distance(test1, test2):
    if (test1.din, test1.dout, set(test1.branches)) != (
            test2.din, test2.dout, set(test2.branches)):
        return float("inf")
    a, b = test1.choi_blocks(), test2.choi_blocks()
    return max(float(np.linalg.norm(a[y] - b[y])) for y in a)
