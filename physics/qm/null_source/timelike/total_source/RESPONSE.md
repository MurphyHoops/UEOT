# Conditional complete causal response and its initial-surface boundary

This page uses the original BARE TWO-FIELD response P and its frozen causal
inverse G. It is not the response of an expanded carrier/controller model.
The two NOON states have the same W2, so this mean-response operator is
common to them on the original static background.

## 1. What a noise difference predicts under a joint-initial-state contract

Assume a valid absolute constrained baseline exists and that the complete
initial contribution (including source cross correlations) is the same in
the comparison. In the specified linear Gaussian stochastic model put
\[
 q_c(t)=\int_0^tG(t-s)\cos(\Omega s)ds,\quad
 q_s(t)=\int_0^tG(t-s)\sin(\Omega s)ds.
\]
With Delta N_pp=Dp cos Omega(t-t'), the induced difference is
\[
 \Delta{\rm Cov}_u=A^4D_p(q_cq_c'+q_sq_s'),\quad
 \Delta{\rm Cov}_{R^{(3)}}=144D_p(q_cq_c'+q_sq_s').
\]
Primes on the two factors here denote the second time argument, not
derivatives; delta R^(3)=-12u/A^2 on the fixed physical slicing.
For a real test w the added curvature variance is
144Dp[(int w qc)^2+(int w qs)^2], strictly positive exactly when its
response vector is nonzero. This is not yet a relational detector record.

CONSTRAINTS.md shows the present independently noisy homogeneous baseline
does not satisfy the absolute linear density constraint. Thus the theorem
above has an explicit currently unmet premise for that baseline. A mere
source-kernel subtraction cannot supply it.

## 2. The full inverse retains its unstable poles

In Laplace space
\[
 \widehat q_c={s\over(s^2+\Omega^2)P(s)},\qquad
 \widehat q_s={\Omega\over(s^2+\Omega^2)P(s)}.
\]
The zeros of 1/P at the thermal forcing poles can cancel those bare poles,
but they do not make either transform zero. If sigma_F is the frozen fast
positive root, its residues are
\[
 r_c={\sigma_F\over(\sigma_F^2+\Omega^2)P'(\sigma_F)},\quad
 r_s={\Omega\over(\sigma_F^2+\Omega^2)P'(\sigma_F)} .
\]
Their added metric amplitude variance is
A^4 Dp/[(sigma_F^2+Omega^2)P'(sigma_F)^2]>0.
No fast-pole deletion, order reduction, or long-time stability assumption
is inserted into this calculation.

The previously certified T=1/(24A) and K0<4.2e-14 give, on this short window,
|qc|<=K0 and |qs|<=Omega T K0. Therefore the square root of ADDED pointwise
curvature variance is bounded by
12 sqrt(Dp) K0 sqrt[1+(Omega T)^2].
It is not the difference of the two standard deviations. Proper duration
is 1/24 in model units. Neither the tiny conditional bound nor the existence
of a nonzero test is an instrument calibration.

## 3. Finite initial forcing is not an all-past smooth preparation

G is C1 with G(0)=G'(0)=0. The convolution identities
qc'=G-Omega qs, qs'=Omega qc imply qc^(j)(0)=0 for j<=2 and
qs^(j)(0)=0 for j<=3. However the full UV symbol has
\[
 P(s)\sim-{s^4\log s\over24\pi^2A^2}\quad(s\to+\infty),
\]
because the exact spectral weights have mu_k~1/(24 pi^2 A^2 k).
Consequently
\[
 \widehat q_c\sim-{24\pi^2A^2\over s^5\log s},\qquad
 \widehat q_s\sim-{24\pi^2A^2\Omega\over s^6\log s}.
\]
Taylor-Laplace asymptotics then exclude qc in C5 and qs in C6 at the
zero-extended initial surface. These are mathematical finite-initial
responses, not the former C-infinity flat-past Hadamard geometry family.
Smoothing the measurement window does not smooth the physical source onset.
Adding a smooth homogeneous mode does not repair this boundary regularity.

For context on intrinsic/induced fluctuations and the dependence on an
initial state, see Hu-Roura-Verdaguer, arXiv:gr-qc/0402029. Their framework
does not remove the explicit model constraints established here.
