# A — Complete-record stability for simultaneous dynamics

Date: 2026-11-12 (Asia/Shanghai). Author: native research agent A.
Working baseline: main `cb17211653fde30aa50e0e9848798a6a5b3b3f12`,
v31.12 / Kernel 1.12 / book 3.9. Core is a read-only dependency; GI is excluded.
This document contains new paper proofs for the next physical increment.
It does not claim new Lean or device evidence.

## 1. Shared physical model and exact operational types

The selected complex system is
`S=C^2 tensor l^2(N_0)`, with `G=n+P_e` and spectral carrier
`P_M=1_{G<=M}`, of dimension `2M+1`. The reference R is arbitrary finite
positive-dimensional complex space, initially correlated or entangled with S,
and never acted on. All persistent physical memory must be included in S.
The flag and detector auxiliaries used in this model are actually reset and
prepared independently. One-slot channel equality alone is not used to identify
processes that reuse an omitted hidden environment.

The final shared subfamily is the canonical self-adjoint quadrature model

`X=a+a†`, `U_x=exp[-i x (sigma_x tensor X)]`,
`V_0=exp[-i phi P_e]`, `phi=pi/3`.

`x` is a dimensionless integrated coupling, with independently declared design
range `[-1/10,1/10]`. The exact self-adjoint generator is defined by spectral
calculus, equivalently as `X direct_sum -X` in the sigma_x basis, with domain
`D(X) direct_sum D(X)`. It agrees on the finite Fock core with the simultaneous
red-plus-blue expression `A+B`. A pair of separated red and blue exponentials
is a different operation and is not substituted here.

At each source slot, independently prepare/read the same three-state flag as
the preceding chapter. With `q in [12/25,13/25]` and `s=1-q/2`, the events are

`K_0=sqrt(s(1-q)) V_0`, `K_1=sqrt(sq) U_x`, `K_f=sqrt(1-s) I`.

At most two source slots are run; f stops the process. All seven terminal
records `f,0f,1f,00,01,10,11` and the terminal SR state are kept. Acceptance is
the last four records. Since every unitary path has identity adjoint product,
the source acceptance effect is derived as `s^2 I`. Thus the complete conditional
target `T_q,x` is CPTP, with zero original-failure blocks still retained in its
record alphabet. The raw source remains a distinct CPTP process with nonzero
failure probability.

The physical compiler uses the same actual gates and the legal frozen policy:
first label-one weight `1/2`, then `312/625` after 0 and `313/625` after 1. Its
record law is

`Q00=Q11=313/1250`, `Q01=Q10=312/1250`, `E_Q[number of ones]=1`.

Weights depend only on allowed past labels and calibration data, not true x,
an unobserved Kraus index or a future result. Every observation fibre has one
common weight. Shared actual gates preserve the old full-CQ robust path error
`sup_q D(T_q,x,C_x)=1/50`; no new minimax theorem is inferred for arbitrary
smaller calibration sets.

The finite calculation uses the **true Galerkin generator**
`H_K=J_K† (sigma_x tensor X) J_K` and `U_K,x=exp(-i x H_K)`.
It is a finite mathematical predictor of the physical process. Its laboratory
availability as an action is not assumed, and a finite matrix exponential is
not declared a physical device implementation by definition.

## 2. General finite-tree stability theorem

### P-OPT-05 / Statement A.1 — Unnormalized-prefix composition

Fix a finite rooted control/stopping tree. At each nonterminal visible history
h, exact and comparison instruments have the same finite outcome set and the
same legal policy. Let their normal CP event maps be `E_h,o` and `F_h,o`, with
the sum over o trace preserving. If an action coin is not recorded, sum its
weighted CP events inside each visible outcome; if it is recorded, include it
in that outcome label. Coarse-graining never hides a label that belongs to the
declared comparison output.

The common physical carrier may be a separable infinite-dimensional Hilbert
space, but R is finite and untouched. Finite approximants are embedded by a
specified isometry. A normal CPTP extension of an approximant outside its
reachable support may be used for the proof; its behaviour there is neither
queried by the finite process nor asserted to be the physical oscillator.

For a common initial density rho define only the **F-prefix** states:

`sigma_empty=rho`, `sigma_ho=F_h,o(sigma_h)`, `m_h=Tr sigma_h`.

Each `sigma_h` is positive and unnormalized. Define the local complete-output
discrepancy

`d_h(sigma_h) = (1/2) sum_o ||E_h,o(sigma_h)-F_h,o(sigma_h)||_1`.

Then the complete terminal CQ outputs obey

`D(Omega_E(rho), Omega_F(rho)) <= min(1, sum_(h internal) d_h(sigma_h))`.

All failure, leakage, early-stop and final records are included. The theorem
does not require state-independent event probabilities, a scalar acceptance
effect, or normalized intermediate states. It does require complete instruments,
a fixed finite tree and the same permissible control rule in both processes.

### Proof

Let `C_h^E` be the exact continuation from a state at history h to the common
terminal record space, with h already included in every final record. At a leaf
it is the canonical labelled embedding; at an internal node it is the sum of
the labelled continuations after its complete instrument. Finite induction
shows that every continuation is normal CPTP.

Expanding once and recursing on the F-prefix part gives the exact identity

`Omega_E(rho)-Omega_F(rho)`
` = sum_(h internal) sum_o C_ho^E((E_h,o-F_h,o)(sigma_h))`.

This is a fixed-direction hybrid expansion: F before each discrepancy, E after
it. It is not legitimate to replace `sigma_h` by whichever process's normalized
state happens to have a smaller energy estimate.

Every local difference is Hermitian trace class, possibly of nonzero trace.
For such X, positivity and trace preservation give

`||C(X)||_1 <= ||C(X_+)||_1+||C(X_-)||_1`
`             =Tr X_+ + Tr X_- = ||X||_1`.

Applying this fact to each term, the triangle inequality and orthogonality of
the outcome record blocks give the displayed bound. Both terminal outputs have
trace one, giving the cap one. This directly proves the needed trace-class
case; it is not an unannounced extension of a finite Lean declaration. ∎

### Legal randomized actions and zero prefixes

If `w_a(v(h))` is the common probability for action a on an observation fibre,
convexity gives

`d_h(sigma_h) <= sum_a w_a(v(h)) d_h,a(sigma_h)`.

Equivalently use the unnormalized action prefix `tau_h,a=w_a sigma_h`. The local
bound is homogeneous: `d_h,a(tau_h,a)=w_a d_h,a(sigma_h)`. If either mass is zero,
the positive state is zero and its contribution is zero; no state is normalized.
If a normalized local error bound `epsilon_h` is valid on the actual F-prefix
input family, its contribution is `m_h epsilon_h`, not `epsilon_h` and not an
unjustified function of the exact process's global mean.

Stopping is part of the fixed policy/instrument. A sum of accepted event maps
alone is not substituted for a complete instrument. For general postselection,
the existing success-probability and sharp conditionalization bounds must be
applied after the complete-output estimate.

## 3. Source-derived Galerkin defect, with the correct mass factor

For B's more general real-parameter model

`H=omega n+Delta P_e+gA+hB`,
`A=a sigma_+ + a† sigma_-`, `B=a† sigma_+ + a sigma_-`,

take the stated self-adjoint realization and true compression `H_M=J_M†HJ_M`.
Physical pulse durations satisfy `t>=0`; signs reside in the real couplings.
Every finite carrier lies in its needed domain. Define the residual from the
source, not as an input error field,

`R_M=H J_M-J_M H_M=(I-P_M)H J_M`.

Only the blue term crosses a G-cutoff. Direct action on the boundary gives

`R_M† R_M = h^2 W_M`,
`W_M=(M+1)|g,M><g,M|+M|g,M-1><g,M-1|`.

For `M=0`, omit the second term; a ket with negative oscillator number is never
introduced. Diagonal and red terms preserve G and have no boundary residual.

Let tau be an unnormalized positive finite input of mass m, including R, and
let `tau(s)=(exp(-isH_M) tensor I_R) tau (exp(isH_M) tensor I_R)`. Duhamel, with
the true unitary on the left, implies

`||(U(t)J_M-J_M U_M(t)) tensor I_R sqrt(tau)||_2`
` <= |h| integral_0^t sqrt(Tr[(W_M tensor I_R) tau(s)]) ds`.

A purification of mass m has norm sqrt(m); its subnormalized trace distance
is at most sqrt(m) times its vector difference. Consequently

`d_unitary(tau) <= |h| integral_0^t`
`                  sqrt(m Tr[(W_M tensor I_R) tau(s)]) ds`.

This expression is linear under scaling tau by a nonnegative scalar. Exact
common readout/reset after the pulse contracts the same complete labelled
error. Prefix-by-prefix substitution into A.1 gives the full finite-tree bound.
Boundary occupation and quadrature of this integral need actual computed or
rigorous upper bounds if it is used as a certificate. A floating integral with
an unchecked solver tolerance does not by itself certify the theorem's bound.

The two sides may have unequal later prefix probabilities. A.1 still uses
the finite reference prefixes consistently and compares all signed local
trace differences, so state-dependent readout does not break the theorem.
It does invalidate the simpler fixed-Q word calculation below unless that
word law is independently source-derived.

## 4. Finite Duhamel remainder without an infinite Dyson claim

### Supporting proof for P-MICRO-07 / Statement A.2 — Low-support Galerkin comparison

Write `H=H0+hB`, where `H0=omega n+Delta P_e+gA` strongly preserves every G
spectral carrier. Assume the exact self-adjoint realization is established.
Start in `P_N`, choose a nonnegative integer L, and set `K=N+2L`. For a fixed
unitary word, let x be the sum of absolute blue interaction areas across its
simultaneous-drive segments. Any phase kicks or other explicitly admitted
G-preserving unitaries occur identically in the two words.

Define

`c_j(x,N)=x^j/j! product_(k=1..j) sqrt(N+2k-1)`, `c_0=1`.

For the exact word U and the corresponding word U_K of true Galerkin
exponentials,

`||(U J_N-J_K U_K J_(N->K))|| <= 2 c_(L+1)(x,N)`.

The same operator norm bound holds after tensoring any finite identity. It
gives complete joint-state trace distance at most `min(1,2c_(L+1))` on every
normalized input supported in `P_N tensor I_R`.

### Finite-expansion proof and the key direction

For one segment start with the exact Duhamel identity

`U(t)=U0(t)-i h integral_0^t U(t-s) B U0(s) ds`.

Apply it repeatedly to the leftmost true U, exactly L+1 times. Before the j-th
B from the right, the vector is in `P_(N+2j-2)` because the intervening U0
preserves G. Its B norm is at most `sqrt(N+2j-1)` times the preceding norm.
After j terms its support is at most `N+2j`.

All coefficient terms through order L agree exactly with the Galerkin
expansion: every intermediate support remains in K, and H0 and its finite
restriction agree there. Each final remainder has L+1 interactions on the
right and a true or finite unitary on the left. The latter has norm one and
requires no energy or support assertion about the exact evolved state.
The ordered simplex integral of the absolute scalar couplings is at most
`x^(L+1)/(L+1)!`. Each remainder is bounded by `c_(L+1)`, and their difference
by twice that value.

Every finite iteration applies Duhamel to a finite-support vector in the common
operator domain. No infinite-series convergence, interchange of limits, or
hard support property for the true evolved state is needed. For a finite word,
apply the same expansion along its ordered segments; inserted common
G-preserving kicks do not change these support or norm estimates. Equivalently
sum the multinomial allocations of L+1 interactions among segments. ∎

The finite-remainder improvement was proposed by A during this iteration and
independently checked by B. Its use of Duhamel and finite Galerkin projection
is standard mathematical machinery; this is a project bridge with its stated
domain, not a new natural law.

### Complete-Q word form for the shared source/compiler

For the shared compiler the word probabilities Q are independent of the quantum
state, true x and its fitted value. With j=L+1 define `d_j(z)=min(1,2c_j(z,N))`.
On any supported input, the complete CQ error between the exact and finite
compiler at the *same* area x is bounded by

`epsilon_G(x) <= (Q01+Q10)d_j(|x|)+Q11 d_j(2|x|)`.

The word 00 has no driven pulse and contributes zero. This weighted expression
is stronger than replacing every word by the worst two-drive word. Its
argument x is the actual area used in the nominal calculation. If calibration
uses a grid representative, its independently bounded displacement must first
be accounted for; an unobserved true value is not handed to the simulator.

For the frozen principal example, `N=4095`, `L=40`, `K=4175`, and `|x|<=1/10`.
C supplies the independent rational enclosure and joins it to calibration.
The numerical finite witness may use smaller explicitly stated cutoffs; it
does not masquerade as numerical execution of a dimension-8351 calculation.

## 5. Calibration mismatch through an exact conserved form

### Supporting proof for P-ROB-04 / Statement A.3 — Common-area stability for the quadrature subfamily

For a normalized input with `Tr G rho_S<=E`, the form inequality

`X^2 <= 4n+2I <= 4G+2I`

gives `Tr X^2 rho_S<=4E+2`. Here `Tr X^2 rho` means the positive quadratic-form
expectation. Finite mean n places any purification in `D(I tensor X)`; it does
not require `D(X^2)`.

The force unitary has the spectral form

`U_x=P_+ tensor exp(-ixX)+P_- tensor exp(ixX)`.

It strongly commutes with the spectral projections of `I tensor X`. The phase
gate acts on the spin alone. Hence every exact word made from either the true
or nominal forces and those phase gates preserves `D(X)`, the quadratic-form
domain of the positive operator `X^2`, and the norm `||X psi||`. This is stronger than commuting formal unbounded expressions on
an unspecified common core.

For a single force and a purified input, spectral calculus gives

`||(U_x-U_y)psi|| <= |x-y| ||X psi||`.

Telescope a word with k force calls, using nominal exact prefixes and true exact
suffixes. Each prefix retains the same `X^2` form expectation and the suffix is
unitary. Its joint-state discrepancy is at most `k|x-y|sqrt(4E+2)`.
Both processes have exactly the same complete record law Q, so

`D(C_x(rho),C_y(rho)) <= min(1,|x-y|sqrt(4E+2))`.

For `E<=1`, the uniform bound is `sqrt(6)|x-y|`. The physical low-G spectral
filter retains the bound `E<=1` on pass, so it can be used without resetting or
discarding the reference. The mass of that pass branch may be retained for a
sharper estimate or conservatively bounded by one. ∎

### C-MICRO-03 — The finite model need not conserve X^2

At K=1 use basis `(g0,g1,e0)`. The compressed simultaneous generator couples
g1 and e0, while `J_K†X^2 J_K=diag(1,3,1)`. Indeed, the red term sends e0 to
g1 and back. Its vacuum action vanishes. The blue term sends g0 to e1, which
lies outside `G<=1`, and has no retained matrix elements. Thus

`H_1=[[0,0,0],[0,0,1],[0,1,0]]`,
`U_1,x |e,0> = cos(x)|e,0> - i sin(x)|g,1>`.

The full oscillator form has `X^2=a^2+(a†)^2+2n+1`. The two-step off-diagonal
matrix elements have no endpoint within a fixed spin's retained n=0,1 range;
the compressed form is consequently the stated diagonal matrix. Starting
from e0, the finite evolution has X-form expectation `1+2sin^2(x)`. In the
exact infinite model the same initial state has moment one, and strong
commutation with X preserves it. For every x not an integer multiple of pi,
the two moments differ. ∎

This counterexample refutes inheriting this exact form invariant through this
Galerkin compression; it does not refute its trace-distance approximation or
the exact model's invariant. In particular, A.3 may not be applied directly to
Galerkin prefixes. The valid triangle chain compares true and nominal **exact**
models first, then separately pays the nominal Galerkin approximation error.

## 6. One complete preparation/calibration/prediction chain

Retain the actual low-spectral filter `P_N`, its pass label, and failure map

`rho -> tau_vac tensor Tr_S[(I-P_N)rho(I-P_N)]`.

The reference on failure is conditioned by that observed event and never
replaced by an unconditional or fresh reference state. Its mass remains in
the disjoint `prep_fail` output block. The ideal target has zero mass there.
Let `delta_N=1-s_N<=1/(N+1)` and use the inherited sharp preparation bound

`f(delta)=(sqrt(4delta-3delta^2)+delta)/2`.

Suppose independent calibration produces an admitted joint parameter set and
a nominal xhat, with a valid bound `|x-xhat|<=Delta_x` over that whole set.
All means, common gates, readout assumptions and allowed records remain as
declared; the data analysis must not read an inaccessible true parameter.

Let the final predictor apply the physical filter map in its mathematical
output model and on pass simulate the fixed policy with true finite
Galerkin gates at xhat. The ideal complete conditional source target and
that predictor obey the sufficient uniform bound

`epsilon_total <= f(1/(N+1)) + 1/50 + sqrt(6)Delta_x + epsilon_G(xhat)`.

The four terms refer respectively to actual filter failure/disturbance,
the legal path-law mismatch, the independently bounded calibration error,
and the finite prediction error. The initial filter is charged once.
Instrument/readout/model imperfections need their own errors in the same
metric; they are not set to empirical zero.

Operationally, a real matched physical compiler at the unknown true x still
uses the common real gate; it is not asked to implement the finite Galerkin
matrix or the fitted nominal Hamiltonian. The last two terms certify the
finite model's predictive accuracy for that real process under the stated
ideal-device and calibration assumptions. Computational executability is
not itself physical action realizability.

When comparing successful outputs after additional state-dependent acceptance,
use the complete-output bound and its separate positive-success contract.
The present source's scalar effect explains why its specified conditional
target is CPTP; it does not eliminate general posterior amplification.

## 7. Evidence, provenance, and remaining routes

The new general finite-tree identity and its trace-class contraction proof are
paper mathematics. A separately authored finite checker tests the exact hybrid
identity with state-dependent outcome probabilities, an untouched entangled
reference, early stopping, hidden Kraus refinements, zero prefixes, and negative
controls. Its numerical passes do not prove the universal theorem. No Lean
theorem or hardware observation is claimed in this note.

The primary standard background for CP instruments and trace-norm reasoning
is John Watrous, *The Theory of Quantum Information*, author-hosted text:
https://johnwatrous.com/wp-content/uploads/TQI.pdf and the author's book page
https://cs.uwaterloo.ca/~watrous/TQI/. The contraction needed here is also
proved directly above, including normal trace-class maps.

Full finite-OPT axiomatization, independent complex-sector selection,
measurement actualization versus environment equivalence, unrestricted
controllers, infinite reference systems and unbounded stopping remain separate
responsibilities. This approximate simultaneous-dynamics bridge does not
reinterpret the old hard-support counterexample as a new result or remove the
long-term field, particle, gravity and empirical tasks.
