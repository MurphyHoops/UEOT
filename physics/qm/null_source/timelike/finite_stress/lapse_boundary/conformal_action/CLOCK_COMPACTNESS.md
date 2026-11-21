# C. Why tight test families cannot repair the original zero kernel

This page applies to the ORIGINAL frozen minimal-coupling model,
using the already accepted INTERIOR_COLLAPSE theorem. It does not
assume the new curvature coupling.

## C1. Uniform convergence on a relatively compact family

Let T_K:L¹(J;H)->H have norm at most one and T_K X->0 for every
fixed X. In the previous model
T_K X=integral U_K(u_i,u)X(u)du. If C is relatively compact in L¹,
then sup_{X in C}||T_KX||->0.

Proof: take a finite epsilon-net {X_j}. The operator bound gives
sup_C||T_KX||<=epsilon+max_j||T_KX_j||. First take K large for
the finite set, then epsilon->0. Consequently every precompact
sequence X_K still has T_KX_K->0. More generally,
S_KY->SY in L¹ implies T_K S_KY->0.

For the original physical kernel use the correctly weighted test
X=f_kappa Phi. Fixed smooth clock changes include their Jacobian.
Fixed or strongly convergent endpoint/unitary identifications that
yield L¹ convergence are covered. A singular clock or nonprecompact
test may evade the theorem; this is a changed physical comparison,
not evidence that the original gate passed.

## C2. A concrete resource/tightness criterion

It suffices that X_K have common compact time support, uniformly
bounded L¹ norm, uniformly continuous translations in L¹, and
finite-rank projections P_m increasing to I such that

    sup_K||(I-P_m)X_K||_L¹ -> 0.

To prove it, truncate with P_m, then replace the finite-dimensional
waveforms by averages on a fixed fine time mesh. Translation
continuity bounds the common approximation error. The mesh averages
belong to a bounded finite-dimensional set, hence have a finite net.
Adding the two approximation errors proves precompactness.

A uniform L¹ derivative bound supplies temporal continuity.
A declared positive compact-resolvent reference B and uniform
integral ||B^(1/2)X_K(u)||du bound supply Hilbert-space tail tightness.
This B is a waveform/resource norm; it is NOT automatically the
Hamiltonian or energy of a physical apparatus.

## C3. Two ways a proposed repair spends the missing compactness

In a scalar example, T_nX=integral_0^{2pi} e^{int}X(t)dt.
For a fixed trigonometric bump chi=(1-cos t)/(2pi), T_nchi=0
for integers n>=2. The moving X_n=e^{-int}chi instead has T_nX_n=1.
Its temporal derivatives cannot be uniformly L¹ bounded.

In H=ell², the functionals X-><e_n,X> tend to zero on every fixed
vector while X_n=e_n is detected with unit amplitude. Here finite-rank
tail tightness fails. These examples diagnose comparison resources;
they are not implementations in the old gravity model.

The old adapted section U_K(u,u_i)psi tautologically cancels evolution.
Its normalization alone says nothing about a preparer or a physical
test that survives the same comparison. A successful alternative must
state which tightness property fails, what action changes, or what
new physical clock/observable is being implemented.
