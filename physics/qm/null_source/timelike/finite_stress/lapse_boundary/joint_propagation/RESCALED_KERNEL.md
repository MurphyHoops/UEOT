# Normal rescaled two-time kernels and complete bounded records

## K1. The actual limit and its generator

Use the complete propagation theorem INITIAL_LAYER, with
epsilon_K=log(K)/K and V_K(s)=Ucal_K(u_i+epsilon_K s,u_i).
Uniformly on compact rescaled time pairs,

    V_K(s)->F_s=exp[is/(2kappa)],
    V_K(s)*->F_s*,
    Ucal_K(u_i+epsilon_K s,u_i+epsilon_K t)->F_{s-t}

strongly on every fixed bulk vector. F_s is a strongly continuous
unitary group with maximal multiplication generator
H_layer=-1/(2kappa), domain D(kappa^-1). This identifies the derived
layer group, not the original full constraint or a limit of its domains.

For ANY normal initial densities rho_K->rho_infinity in trace norm,

    K_K(s,t)=V_K(s)rho_K V_K(t)*
       ->K_infinity(s,t)=F_s rho_infinity F_t*

uniformly in trace norm on compact s,t windows. To prove this first
replace rho_K by rho_infinity. Approximate the latter in trace norm by
a fixed finite-rank operator. A rank-one |x><y| has error at most
||(V_K(s)-F_s)x||||y||+||x||||(V_K(t)-F_t)y||.
The trace-norm tail costs at most twice its norm. This proof works
with any fixed untouched reference as well, by strong convergence of
V_K tensor I and finite-rank approximation on the enlarged Hilbert space.

The actual C5 and C9 sequences satisfy the hypotheses. For a declared
regular low mixture, purification and INITIAL_LAYER give
O((log K)^-1/2+K^-1/2) for C5; RARE_PREPARATION adds O(1/log K) for
C9. No derivative of C9's large rare phase is taken. General normal
inputs have convergence without that moment-dependent rate.

## K2. Positivity and the exact rescaled test normalization

For finitely many s_j,x_j,

    sum_ij <x_i,K_K(s_i,s_j)x_j>
       =||sqrt(rho_K) sum_j V_K(s_j)*x_j||^2 >=0.

The limiting kernel has the same positivity and normal trace-one
diagonals. For a fixed test Phi(s) smooth/compact in s and compact
in kappa away from zero, put f_kappa=kappa^-1/2 and

    T_K^layer Phi=integral V_K(s)* f_kappa Phi(s) ds.

The family f_kappa Phi(s) is integrable and H-valued. Uniform strong
adjoint convergence and domination give T_K^layer Phi->T_infinity^layer
Phi. Therefore the state-independent form <T_K Phi,T_K Psi> and
prepared form <T_K Phi,rho_K T_K Psi> converge. The limiting T has dense
range, by narrow time bumps and the dense compact-kappa/source core;
with trace-one rho the prepared positive form is nonzero.

This is a FIXED RESCALED test. In the original u variable it is

    phi_K(u)=epsilon_K^-1 Phi((u-u_i)/epsilon_K).

The factor is the integration Jacobian, not the square-root Jacobian of
a clock L^2 coordinate change. The test's support shrinks to the initial
slice. No fixed-original-u N3 test convergence is inferred.

## K3. Original endpoint weights and the effective constraint

Let R=kappa^1/2, f_kappa=R^-1. Define the raw prepared kernel only as
a tested form,

    Gamma_K(s,t)=f_kappa K_K(s,t) f_kappa.

Its reduced recovery extends to the normal operator

    R Gamma_K(s,s) R=V_K(s)rho_K V_K(s)*,
    Tr[R Gamma_K(s,s) R]=1.

The same holds in the limit. This uses multiplication on stated
domains and extension of the recovered form, not unbounded cyclic
trace manipulations. An arbitrary normal rho need not make the raw
flat-measure Gamma trace class.

The raw PROPAGATOR G_infinity(s,t)=f_kappa F_{s-t} f_kappa obeys

    G_infinity(s,t) kappa G_infinity(t,r)=G_infinity(s,r).

This identity must not be applied to the prepared density kernel:
multiplying two such kernels introduces rho^2.

The explicit bulk kernel satisfies, on compact-kappa tests,

    (-i partial_s-1/(2kappa))K_infinity(s,t)=0,
    i partial_t K_infinity(s,t)-K_infinity(s,t)/(2kappa)=0.

The right multiplier acts on the right. The endpoint congruence gives

    R(P_s-1/(2kappa))R = kappa P_s-1/2.

The finite-K ORIGINAL constraint after u=u_i+epsilon_K s pulls back to

    C_K=epsilon_K^-1 R[P_s+epsilon_K H_K(u_i+epsilon_K s)]R.

Accordingly C_layer=kappa P_s-1/2 is the combined tested limit of
epsilon_K C_K after pullback, not of the unscaled original constraint.
Multiplying by this nonzero scalar preserves finite-K homogeneous
solutions, but it matters for contact/source normalization.
The derivative passes in an integrated distributional equation along
the convergent exact orbit. No strong common-domain operator limit or
separate unbounded clock/source-moment convergence is asserted here.

The local state-independent quotient for this explicit layer constraint
again completes to the same weighted bulk slice Hilbert space.
The three physical/feature/GNS completions remain distinct as in
LOCAL_CONSTRAINT.

## K4. Finite instruments, full failure outputs and raw operations

Fix a finite sequence of normal CP instruments on the bulk physical
slice, with fixed rescaled times and all outcomes/failure outputs kept.
The two-time unitary channels converge in trace norm on each fixed
trace-class input. A telescoping estimate and contraction of each
CP operation give convergence of the complete CQ history state to the
same operations interleaved with F_{s-t}. Finite adaptive protocols
are included by acting on the accumulated CQ register. An untouched
normal reference may be retained throughout. No diamond-norm or
operator-norm convergence is claimed.

For finitely many bounded Kraus branch products B_alpha,K, strong
convergence and the square-root inequality imply

    B_alpha,K sqrt(rho_K)->B_alpha,infinity sqrt(rho_infinity)

in Hilbert--Schmidt norm. Hence all finite Gram matrices, branch
densities and probabilities converge. A normalized selected branch
converges if its limiting probability is positive; vanishing-probability
branches require separate control. The same-K C9/C5 full-record
distance is still at most delta_K before any limit. K-dependent
instrument definitions require their own convergence.

The raw slice Hilbert space has inner product integral kappa<psi,psi>.
Its isometry into the bulk space is R. A bounded physical Kraus M
therefore transports to f_kappa M R with weighted adjoint
f_kappa M* R and the same weighted norm. This need not be bounded in
flat kappa measure. Probabilities are computed from the recovered
normal operator R Gamma R.

These are complete abstract instruments on the physical completion.
They do not construct a local autonomous interaction, controller
stress, preparation energy balance or an experimental calibration.

## K5. The actual bounded readout, on the stated clock

For fixed h in C_c^infinity((0,S)) and bounded A, define

    R_K^layer[h,A]=integral h(s)V_K(s)* A V_K(s)ds.

It converges strongly to the corresponding F_s expression, and
R_K^layer sqrt(rho_K) converges in Hilbert--Schmidt norm. This is
the original test f_K(u)=epsilon_K^-1 h((u-u_i)/epsilon_K), rather
than the old fixed interior test f.

For B(kappa)=kappa^2/(1+kappa^2), F_s*BF_s=B. Thus

    R_K^layer[h,B]sqrt(rho_C9,K)
      ->(integral h) B sqrt(rho_infinity).

On the fixed regular low family this has O((log K)^-1/2) error:
B Psi_C5,K is the same comparison family with profile Bg, so the
Heisenberg error is bounded by ||B||e_K[g]+e_K[Bg].
The C5 isometry tail gives an O(K^-1/2) square-root error, and the
C9 addition is at most ||h||_1 sqrt(2 delta_K).
Source-only bounded records likewise commute with F_s.
A quiet diagonal readout is therefore compatible with the nontrivial
coherence record of BOUNDED_WITNESS.

## K6. No trace-normal preparation can repair the original uniform gate

For s!=0 the multiplication function exp[is/(2kappa)] has countable
kappa level sets of measure zero, so F_s has no point spectrum,
even with source multiplicity. If a nonzero positive trace-class rho
commuted with F_s, a positive eigenvalue of rho would give a nonzero
finite-dimensional eigenspace invariant under F_s. A unitary on that
space has an eigenvector, contradiction. Therefore

    ||F_s rho F_s*-rho||_1>0

for every normal density, without a state-independent positive bound.

This gives an actual cross-cutoff prepared-history gap. For ANY
rho_K->rho_infinity in trace norm, take K=N^2, L=N and
t_N=s epsilon_{N^2}. At the same original time,

    U_K rho_K U_K* -> F_s rho_infinity F_s*,
    U_L rho_L U_L* -> rho_infinity,

since t_N/epsilon_N=2s/N->0. Their trace-norm gap tends to the strictly
positive quantity above. Further preparation tuning with a normal
trace limit cannot restore the declared uniform initial-slice history
gate in this frozen model/reference.

Isolated fixed positive original-u times, selected noncompact readouts, other
topologies and action-derived changes remain separate questions.
Strong propagation and trace-normal kernel convergence cannot be
differentiated to obtain finite variance, QFI or stress. SNAPSHOT_SPECTRUM
gives the actual C9 failure of moment convergence; its mixed-state
variance bound is not a QFI lower bound.

## K7. Follow-on result on the original clock

INTERIOR_COLLAPSE subsequently proves that the fixed original-clock
state-independent and normally prepared vector-test kernels tend to
zero. Thus the original nonzero N3 gate is rejected; only the explicitly
rescaled kernel constructed here remains a positive normalized limit.
That theorem does not decide the selected noncompact N4 readout.
