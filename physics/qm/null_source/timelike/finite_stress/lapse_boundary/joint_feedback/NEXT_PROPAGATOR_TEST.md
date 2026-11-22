# Next acceptance: original joint histories and prepared records

**Status: OPEN, not executed.** This is the next-test contract reached after the
17 scientific entries. It is not an eighteenth scientific certificate, a new
continuum theorem, or an autonomous device construction.

The initial state is now concrete: CORRELATED_GAUSSIAN C5 supplies a normal bulk
limit, and C9 supplies a specified initial-current/clock-mean repair with the same
limit. Its divergent covariant form, clock variance and initial curvature remain
accepted failure results. The next question is whether the original **complete**
propagation has a common limit, and what a legitimate prepared record in that
limit would mean.

## N1. Fix the original comparison before taking a limit

Use the fixed no-chirp bulk reference from CORRELATED_GAUSSIAN C5,
\[
{\cal H}_{\rm bulk}=L^2((0,\infty),d\kappa)
 \otimes{\cal H}_{\rm zero}\otimes{\cal F}_\omega .
\]
The comparison with the actual bulk Jost representation, if used, is its one
fixed unitary identification. Retain the selected positive-half-line ordering
and principal boundary realization, original nonzero \(U_0\), AE prescription,
and all coefficients of JOINT_CUTOFF J1–J3.

The original \(W_K\) in RELATIONAL_DOMAIN R4 is independent of the \(u\) clock.
From the already constructed finite-\(K\) complete propagator define
\[
{\cal U}_K(u,v)
 =j_K[W_K\bar U_K(u,v)W_K^\dagger],
\]
where \(j_K\) extends by the identity on the fixed tail Fock factors. This does
not assert a strong limit of \(W_K\). Keep the original covariant derivative
\(P_\kappa-(A_K+Q_K)\), the complete source/dilation terms and the original
counterterms. A new subtraction requires its own action and renormalization
argument; it cannot be introduced as a favorable state-dependent expectation.

Fix the C5 real compact profile and regular low state once, or its fully specified
C9 preparation rule. Neither the mixing weights nor the phase may be reset
during evolution. The conditional Gaussian ground bundle is an initial-state
construction, not an invariant subspace of the full generator. Do not replace
the propagator by a projection onto that bundle, or by a rule forcing the packet
to remain inside its initial compact support.

## N2. The common two-sided propagator gate

Choose a fixed \(u\)-clock interval \([u_i,u_i+T]\), \(T>0\), in a common
negative-\(g_K\) clock patch for sufficiently large \(K\). This is not the old
conformal-time window relabelled as a quantum proper-time interval.

Let \({\cal D}\) be a countable dense subset of compact smooth geometry functions,
zero-mode Schwartz functions and finite-mode Hermite tensors. The sufficient
acceptance target is, for every \(\psi\in{\cal D}\),
\[
\lim_{M\to\infty}
\sup_{\substack{K,L\ge M\\0\le t\le T}}
\left[
 \|({\cal U}_L-{\cal U}_K)(u_i+t,u_i)\psi\|
+\|({\cal U}_L^\dagger-{\cal U}_K^\dagger)
       (u_i+t,u_i)\psi\|
\right]=0.                                                       \tag{N1}
\]
Uniform unitary bounds extend this dense-set control to every vector. Both
directions give a unitary, strongly continuous limit; two-time propagation is
then recovered by composition. This criterion is sufficient, not a declaration
that it has been proved or that every possible physical topology must satisfy it.

One concrete proof route is a summable bound on the **whole** dyadic blocks
\(2^n\le K,L\le2^{n+1}\), on the same interval. Comparing only the two block
endpoints is insufficient. Before estimating the differences, establish the
complete weak Duhamel comparison and its reverse on the transported
\(Q/Q^*\) classes. Existing finite-\(K\) constants in ALL_SIGN_EVOLUTION are not
uniform cutoff bounds.

The comparison must retain possible cancellations and oscillatory integrals
between the source, dilation, AE and covariant derivative terms. Divergence of
\(\bar H_K\psi\), or a failure of exact cutoff intertwining, does not on its own
decide N1. Conversely, a forward weak limit alone need not give a unitary limit
or a valid advanced pullback.

## N3. A positive two-time kernel retaining the clock correlation

For the same finite-\(K\) density \(\rho_K\), form
\[
{\cal K}_K(u,v)
 ={\cal U}_K(u,u_i)\rho_K{\cal U}_K(v,u_i)^\dagger .                \tag{N2}
\]
The common preparation makes its tested sesquilinear form positive. On the
already justified finite-cutoff weak domains it has the two branch identities
\[
(-i\partial_u+H_{{\rm bulk},K}(u)){\cal K}_K=0,\qquad
i\partial_v{\cal K}_K+{\cal K}_K H_{{\rm bulk},K}(v)=0.             \tag{N3}
\]
The next deliverable is a common cutoff limit of these **combined tested**
identities, with positivity and nonzero normalization retained. It must not
split them into two separately divergent clock/generator moments and discard
their cross term.

The original relation
\[
f{\cal C}_Kf=P_u+H_{{\rm rel},K},\qquad f=\kappa^{-1/2},
\qquad \chi=\kappa^{1/2}\Psi
\]
is a congruence, not a unitary equivalence. Transport N2–N3 back with the original
weights, endpoint map and observable domains. The conserved reduced slice norm
is already available for the declared finite-\(K\) quantization; identification
with a positive original-constraint rigging quotient and a common full-field
domain remains a separate requirement. If a global group average is requested,
its self-adjoint constraint/clock endpoint domain must also be specified from
the original problem.

On a common second-moment domain,
\[
\operatorname{Var}(P_u+H_K)
=\operatorname{Var}(P_u)+\operatorname{Var}(H_K)
 +2\operatorname{Cov}_{\rm sym}(P_u,H_K).
\]
The accepted \(K^2/\log K\) lower bound for the candidate's clock-generator
variance does not supply this full expression. In a rigged physical state the
individual moments may themselves require testing. Neither a successful N3
limit nor a choice of clock correlation would erase the separately established
failure of the candidate to recover the fixed target's finite initial curvature.

## N4. First readout: bounded, on the actual joint \(u\) clock

Start with one bounded original geometry record, for example
\[
B(\kappa)=\frac{\kappa^2}{1+\kappa^2},\qquad
R_K[f,B]=\int f(u)\,
 {\cal U}_K(u,u_i)^\dagger B\,{\cal U}_K(u,u_i)\,du ,
\quad f\in C_c^\infty((u_i,u_i+T);\mathbb R).                      \tag{N4}
\]
Here \(0\le B\le1\) and \(\|R_K\|\le\|f\|_1\). A normalized real \(f\)
fixes a model readout; it does not define a calibrated physical clock or probe.
Transport any chosen original observable with the same endpoint maps.

A legitimate first record is the common GNS vector of this same prepared
operator. Under N1 and \(\rho_K\to\rho_\infty\) in trace norm, bounded-record
means and finite products have a common limit. For an explicit Hilbert-space
comparison one may use the Hilbert–Schmidt vectors
\(R_K\sqrt{\rho_K}\); their limit retains the positive Gram matrix.
A smaller first acceptance may be proved directly on the prepared orbit,
without claiming N1 on the full Hilbert space. Set
\(\Omega_K=\sqrt{\rho_K}\), and bound
\[
\begin{split}
e_0&=\|\Omega_L-\Omega_K\|_2,\\
e_1&=\sup_u\|({\cal U}_L-{\cal U}_K)\Omega_K\|_2,\\
e_2&=\sup_u\|({\cal U}_L^\dagger-{\cal U}_K^\dagger)
                      B{\cal U}_K\Omega_K\|_2 .
\end{split}
\]
Then the norm difference of the prepared readout vectors is at most
\(\|f\|_1(e_0+e_1+e_2)\). This direct route is the first bounded-record
calculation to attempt; N2 is the stronger full-propagator gate. The third term
retains the reverse evolution on the actual prepared orbit, rather than
assuming it from forward convergence. Selected-record convergence does not
prove N1, an original-constraint rigging limit, or an autonomous instrument.

A concrete rejection route is to fix a self-adjoint
\[
A=f_0(\kappa)\otimes\operatorname{Re}{\cal W}_{M_0}(\xi),
\quad \|A\|\le1,
\]
where \(f_0\), finite mode count \(M_0\) and Weyl parameter \(\xi\) do not change
with \(K\). Let
\(a_K(u)=\operatorname{Tr}\rho_K{\cal U}_K(u,u_i)^\dagger
 A{\cal U}_K(u,u_i)\).
A certified gap \(|a_L(u_*)-a_K(u_*)|\ge\epsilon>0\) at one **fixed**
\(u_*>u_i\), for arbitrarily large \(K,L\), rejects the common state-history
limit for this preparation and therefore N1 in this reference. A gap only at
\(u_K\downarrow u_i\) rejects a uniform window containing the initial slice,
but need not reject a positive-time limit with an initial layer. The known
initial curvature divergence does not provide either gap without a uniform
Taylor remainder or a complete time-integrated estimate.

## N5. The stronger stress/charge and instrument gate

After the bounded joint test, derive a joint advanced/Duhamel pullback for one
specific stress/constraint-charge readout. Its source, preparation and boundary
contributions must be combined into one vector on the same normal/GNS state
before taking the cutoff limit; all cross Gram blocks and finite-cutoff Ward
defects remain. Unbounded stress/current convergence requires additional domain
and uniform-integrability estimates, not just trace convergence of \(\rho_K\).

ADVANCED_CUTOFF and PREPARED_LIMIT establish this structure on the actual
**external classical** background. Their weighted resolvents and proper-clock
test pair cannot be substituted for a quantum joint-clock map. In particular,
derive the joint lapse/clock map, ordering and endpoint response before using a
proper-time stress test. INTERIOR_LAPSE's four homogeneous interior blocks do
not already give quantum initial-state blocks, all spatial constraints, or a
joint advanced propagator.

Both branches' density, propagator and final pairing remain those of
COHERENT_TRANSPORT T1. If the physical past changes, retain the actual first and
second preparation Duhamel insertions from T4. A canonical endpoint connection
alone does not supply the physical preparation or enforce its initial
constraint column.

An autonomous-instrument claim additionally requires a specified local
controller/probe coupling, with its interaction stress, complete success/failure
output and calibration included in the same total source. The combined system
must pass the corresponding tests; an added apparatus does not inherit a test
of the earlier system for free. N4 is a mathematical bounded record, not such
a device.

## N6. Alternative scalar clock: the earlier gate stays open

Changing to the existing scalar-clock sector does not bypass the original
domain problem. First select the original whole-\(\kappa\) realization
\(\bar R_\Theta\) from physical boundary/preparation data, then establish
\(\mu_{\rm old}\ll\nu_{\bar R_\Theta}\) on the two fixed target energy bands.
A positive finite-width resolvent or nonempty positive spectral projection is
not this absolute-continuity gate. Complete source coherence and preparation
remain further conditions even if the radial law passes.

## Source and review responsibility

This plan uses JOINT_CUTOFF J1–J11, CORRELATED_GAUSSIAN C1/C5–C9,
COHERENT_TRANSPORT T1–T6, ADVANCED_CUTOFF, PREPARED_LIMIT, and the frozen
RELATIONAL_DOMAIN, ALL_SIGN_EVOLUTION and PHYSICAL_SLICE.
Three native read-only agents independently sharpened the propagation, physical
state and readout clauses. No new computation, achieved cutoff rate, physical
rigging limit or instrument is asserted. The outcome of N1–N6 remains OPEN.
