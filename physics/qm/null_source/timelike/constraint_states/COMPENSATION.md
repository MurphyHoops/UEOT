# Exact fixed-mean compensation and its quantum marginal cost

The positive-tail obstruction is reused from correlated_static, not counted
as a new discovery. The new results here are the exact constrained optimum,
its equality condition, its quantum marginal gap, and an attainable NOON
thermal-shell construction.

## 1. Fixed spectral law and fixed finite mean

Let A>=0 and B>=0 strongly commute on different source/apparatus factors.
Let the full source marginal be rho, with finite second A moment. Set
E=Tr R(A+B)>=Tr rho A. Choose C>=0 so that
\[
 E=\langle\max(A,C)\rangle_\rho ,
 \quad b_C=(C-A)_+,\quad h_C=(A-C)_+ .
\]
For E above the source mean this C exists; it is unique on the increasing
part of the mean function. At E equal to the source mean take C=0.
Define
\[
 V_C={\rm Var}_\rho[\max(A,C)]
     =\langle h_C^2\rangle-\langle h_C\rangle^2 .
\]
Since A=C+hC-bC and hC bC=0, equal total means imply the exact gap identity
\[
 \boxed{ {\rm Var}_R(A+B)-V_C
  =\langle(B-b_C)^2\rangle_R+2\langle h_CB\rangle_R\ge0. }
\]
One way to derive it is to expand T^2-TC^2, subtract
2C times the zero expectation of T-TC, then use hC bC=0.
Equality requires B=bC on the support of R. It is NOT obtained by setting
B=(E-A), which becomes negative in the unbounded source tail.

The relaxed spectral optimization is thus solved by
T*=max(A,C). Any finite C retains positive variance if the source law has
nonzero probability above every finite energy. No finite positive apparatus
budget can produce a sharp finite total energy with that marginal.

## 2. Full quantum marginal is an extra constraint

A fixed energy probability law is weaker than a fixed density operator.
For equality, R must be supported on ker(B-bC). Its invariance under
exp[it(B-bC)] implies
\[
                  [\rho,b_C]=0 .
\]
Conversely, if a normal trace-class rho commutes with the bounded bC, it
can have support only in its point spectral subspaces: diagonalize the
positive compact rho; each nonzero eigenspace is finite dimensional and
invariant under bC, and diagonalize bC there. Write rho as blocks rho_b.
An apparatus with orthogonal energy eigenvectors |b> then realizes
\[
       R=\sum_b\rho_b\otimes|b\rangle\langle b|,\qquad
       B|b\rangle=b|b\rangle .
\]
This sum is normal and preserves the entire rho. The designed apparatus
is an algebraic resource construction, not a local field implementation.

There is also a quantitative quantum gap. Let X=B-bC and assume finite
moments permitting the partial-trace commutator (or its bounded cutoff
limit). Trace norm contractivity and Cauchy–Schwarz give
\[
 \|[\rho,b_C]\|_1
 =\|{\rm Tr}_B[R,X]\|_1
 \le 2\sqrt{\langle X^2\rangle_R}.
\]
Hence
\[
 \boxed{{\rm Var}_R(A+B)\ge
       V_C+\tfrac14\|[\rho,b_C]\|_1^2.}
\]
A nonzero commutator therefore separates even the infimum from the
spectral optimum. A pure coherent source admits only product extensions,
which is a useful counterexample to a spectrum-only optimality claim.

## 3. Attainable full thermal-shell example

For the accepted k=2 NOON pair, let A=Omega N, Omega=sqrt(3)/A_radius.
Both rho+ and rho- commute with N. Their number law is exactly
\[
 p_n={n+7\choose7}(1-q)^8q^n,\quad q=n_{\rm th}/(1+n_{\rm th}).
\]
At C=Omega k, k a nonnegative integer, an apparatus with k+1 levels
Omega*k,...,Omega,0 realizes the optimum while retaining all N=2 NOON
coherence. In particular no dephasing inside the degenerate block occurs.

For dimensionless clipping X_k=max(N,k), put
\[
 e_k=8n_{\rm th}+\sum_{j=0}^{k-1}(k-j)p_j,\quad
 s_k=8n_{\rm th}+72n_{\rm th}^2+
          \sum_{j=0}^{k-1}(k^2-j^2)p_j,\quad
 v_k=s_k-e_k^2 .
\]
These are exact finite-prefix formulas for the infinite distribution,
not a Fock cutoff. Mean apparatus energy is Omega(e_k-8n_th);
the minimum variance is Omega^2 v_k. The checker evaluates k=0,1,2,4,
and uses an independent analytic tail identity for the same moments.
The dimensionless resource curve belongs to this shell only; the complete
zero-mode source marginal need not commute with its compensator.

A ground-state energy shift of a semibounded apparatus can be absorbed
into the fixed c-number/total budget. A genuinely unbounded-below
compensator, a time-dependent interaction, or a changed full marginal is
a different contract.

## 4. Fixed integer total-energy budgets

For a directly specified budget E=L*Omega, integer L>=1 and 8*n_th<1,
the optimum lies between L-1 and L. Set
U_L=E(N-L)_+, V_L=E(N-L)_+^2 and p_<L=Pr(N<L). Then
\[
 {C_L\over\Omega}=L-U_L/p_{<L},\qquad
 {{\rm Var}_{\min}\over\Omega^2}=V_L+U_L^2/p_{<L}.
\]
Only L+1 apparatus levels are needed and its mean is
(L-8*n_th)*Omega. The saved certificate includes L=1,2,4 and verifies the
total-mean and variance identities symbolically. These rows should not be
confused with the earlier integer-threshold rows, whose total means are
slightly larger than the threshold.

For fixed 0<q<1, the large-L behavior follows by retaining the full
geometric upper tail, not just its first term:
\[
 {{\rm Var}_{\min}(L\Omega)\over\Omega^2}
 \sim{(1+q)(1-q)^5\over7!}L^7q^{L+1}.
\]
This vanishing spectral optimum requires unbounded apparatus budget.
For a fixed nonstationary complete quantum marginal, Tr rho A^2<infinity
instead gives [rho,bC]->-[rho,A] in trace norm as C->infinity. Indeed the
tail commutator norm is at most 2*sqrt(<(A-C)_+^2>).
The corresponding quantum gap can remain strictly positive. It and the
Fisher/virial bounds are independent lower bounds to be maximized, not added.
