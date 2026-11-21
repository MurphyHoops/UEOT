# Rare preparation repair: exact operational reduction

## R1. Input and scope

Use precisely the finite-K C5/C9 preparations of
[CORRELATED_GAUSSIAN](../joint_feedback/CORRELATED_GAUSSIAN.md), with the original
complete finite-K unitary and fixed bulk embedding. The C9 numbers p=p_K,
r=r_K and b=b_K are selected once for the declared original low input.
They are held fixed when discussing the channel on another shared low input;
the original mean/current tuning is not asserted for that other input.
Every statement below retains the failure record and the same reference.

Let V=V_{0,K} be the C5 fixed-profile isometry from the low Hilbert space
into the complete bulk slice. Let T=exp(ib kappa^2/2). The normalized odd
branch channel E_1 is the actual isotropic single-odd-mode branch of C9.
For any normal low-plus-reference density omega, define

    rho_0 = (V tensor I) omega (V* tensor I)
    rho_1 = (E_1 tensor id)(omega)
    rho_rep = (1-p)[(1-r)rho_0+r T rho_0 T*]
              +p[(1-r)rho_1+r T rho_1 T*].

All odd outputs are orthogonal to the all-even ranges of V and TV.
The controlled source factors are unitary at each kappa, hence

    V* T V = z I,    z = integral |g(kappa)|^2 exp(ib kappa^2/2) d kappa.

## R2. Exact trace distance, including a shared reference

Put c=(1-p)r and q=1-|z|^2. If q>0, Z=(TV-zV)/sqrt(q) is an isometry
orthogonal to V. In the orthogonal (V,Z) representation the even part of
rho_rep-rho_0 is the following scalar matrix tensored with omega:

    M = [[c |z|^2-p-c, c z sqrt(q)],
         [c conjugate(z) sqrt(q), c q]].

Its trace is -p and determinant is -c(p+c)q. Its trace norm is therefore
sqrt[p^2+4c(p+c)q]. The odd positive block has trace p. The q=0 case follows
directly or by continuity. With D_tr(A,B)=||A-B||_1/2, this proves exactly

    delta_K = (p+sqrt[p^2+4c(p+c)(1-|z|^2)])/2,
    p <= delta_K <= p+(1-p)r <= p+r.

The formula is independent of the shared normal low/reference density.
It does not compare arbitrary, independently chosen extensions of two
marginals. For the actual C9 choice, p~1/(2 log K), r=(log K)^(-2).
When nu=0, b=0 and delta=p. When fixed nu is nonzero,
b~-nu(log K)^3/4. Since g is smooth and supported away from kappa=0,
repeated integration by parts in the nonstationary phase gives
|z|=O_N(|b|^(-N)) for every N; consequently delta~1/(2 log K).

## R3. Actual evolution, adaptive histories, and success/failure

The same complete unitary preserves delta exactly at every finite K and
at any allowed common time. Every same normal CPTP history channel
contracts it, including finite adaptive interventions, an untouched
reference and the full classical success/failure output. Thus every
event probability differs by at most delta, and a bounded real payoff of
norm M has expectation difference at most 2 M delta.

Let A,B be subnormalized success outputs with s=Tr A>0, t=Tr B>0.
The failure block is retained in the full record. Contractivity gives

    ||A-B||_1 + |s-t| <= 2 delta.

If s>=t, the triangle inequality applied at denominator s gives

    ||A/s-B/t||_1 <= [||A-B||_1+s-t]/s.

Interchanging A,B covers the other order. Therefore

    D_tr(A/s,B/t) <= min(1, delta/max(s,t)).

A persistent conditioned distinction requires success probability of
order delta or smaller. Discarding failure records is not a uniform
operational recovery. These statements do not construct an autonomous
local probe or its total stress.

## R4. Square-root and prepared-GNS transfer, with an elementary proof

For positive trace-class A,B, set X=sqrt(A)-sqrt(B), S=sgn X.
Their square roots and X_+,X_- are Hilbert-Schmidt. Products below are
trace class. Trace duality, cyclicity and S X=|X| give

    ||A-B||_1 >= Tr S(A-B)
               = Tr |X|(sqrt(A)+sqrt(B)).

After subtracting Tr X^2, the remainder is

    2 Tr X_+ sqrt(B) + 2 Tr X_- sqrt(A) >= 0.

The nonnegative traces are well-defined by Hilbert-Schmidt duality.
Thus the standard square-root inequality is proved here:

    ||sqrt(A)-sqrt(B)||_2^2 <= ||A-B||_1.

No uninspected external theorem is required. For any same-cutoff bounded
R_K,

    ||R_K sqrt(rho_rep,K)-R_K sqrt(rho_0,K)||_2
       <= ||R_K|| sqrt(2 delta_K).

In the predecessor's prepared-readout test N4,
R_K[f,B]=integral f(u) U_K(u_i,u) B U_K(u,u_i) du, ||B||<=1,
so ||R_K||<=||f||_1. The repaired and ground Hilbert-Schmidt sequences are
Cauchy if and only if each other and have the same limit whenever either
exists. Full bounded CQ cutoff gaps differ by at most delta_K+delta_L.

This closes the rare-repair comparison for the actual sequence. It does
not prove the ordinary-time R_K sequence Cauchy, does not control
unbounded moments, and does not infer a generator limit from trace
distance. In fact C9's rare branch can change unbounded clock resources
while this bounded operational distance tends to zero.

## R5. What the executable checks establish

The paired script checks the exact 2 by 2 characteristic polynomial,
the distance interval algebra, a noncommuting matrix realization with
an entangled shared input, and deterministic success/failure and
square-root examples. The infinite-dimensional proof is R1-R4; these
checks are algebra and regression checks, not machine formalization.
