# JC9 — A fixed quadratic actuator cannot reproduce the whole pure history

## 1. Exact contract

At a finite common field cutoff, put the **whole retained body** and an
apparatus in a normal joint state with finite second moments.
Allow arbitrary apparatus dimension within this finite covariance
calculation and any normal, even non-Gaussian apparatus state.
Let their total Hamiltonian be fixed, autonomous and quadratic,
including possible linear terms. Suppose the entire body marginal is
required to equal the specified pure Gaussian externally driven state
at every time of a connected interval, including its flat beginning.

This is stronger than reproducing an endpoint or a mixed reduced
history. It is the exact pure-history replacement that is tested here.

## 2. Short proof

A normal joint state with a pure body marginal is a product of that
pure marginal and some apparatus state. Therefore its centered
body–apparatus covariance vanishes at every time of the supposed
history, even if their means are nonzero.

For a fixed quadratic total Hamiltonian, write its constant linear
Hamiltonian generator in blocks \(A_{SS},A_{SE},A_{ES},A_{EE}\).
The body covariance must satisfy
\[
 \dot V_S=A_{SS}V_S+V_SA_{SS}^T
       +A_{SE}V_{ES}+V_{SE}A_{SE}^T
       =A_{SS}V_S+V_SA_{SS}^T .                                 \tag{1}
\]
Linear terms affect means but not this covariance equation.
At the flat beginning the target covariance has \(\dot V_S=0\).
Thus \(A_{SS}V_S(0)+V_S(0)A_{SS}^T=0\). Uniqueness of the constant
linear equation (1) makes \(V_S(t)=V_S(0)\) throughout.

The actual AQ target is not constant: if it remained the free incoming
covariance in a normal mode with frequency \(k\), then for
\(\mu(t)=\sigma r(t)\)
\[
 \dot V_{qp}=V_{pp}-(k^2+\mu(t))V_{qq}
            =-\mu(t)/(2k),
\]
which is nonzero when the ramp is active. This is a contradiction.
The new local pulse target also has a flat initial covariance and
a nonzero terminal dipole response, so the same argument excludes its
exact entire pure history in this actuator class.

## 3. What was and was not excluded

The conclusion holds at each finite common cutoff where the target
history is nontrivial. A full-field analogue additionally requires the
well-defined tested second moments and uniqueness of the autonomous
linear classical flow; it cannot be obtained by assuming bare
\(H_0\) graph regularity that the preparation does not possess.

The argument does not assume a Gaussian apparatus. It does not exclude
mixed intermediate body states, approximation with a declared error,
only matching an endpoint, explicitly time-dependent controls, or
nonquadratic interactions. In particular a dynamical actuator field
multiplying \(\Phi_+^2\) is a cubic interaction and lies outside the
excluded fixed-total-quadratic class.

The task therefore cannot close by merely relabeling the prescribed
pure quadratic history as an autonomous Gaussian device. A surviving
construction must state which of the above conditions changes, derive
its actual reduced state, and include the actuator and interaction
stress and the transfer-noise correlations in SOURCE_ACCOUNTING.md.
This entry supplies a rejection test, not that surviving construction.
