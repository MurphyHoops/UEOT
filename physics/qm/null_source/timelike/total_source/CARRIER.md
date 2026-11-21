# A real internally degenerate carrier: complete future factorization

## 1. Local free-field action, nonzero carrier source

Introduce a separate complex scalar doublet Psi=(Psi0,Psi1) with m>0,
minimal coupling, and common U(2)-invariant renormalization:
\[
 S_C=-\int\sqrt{-g}\sum_{a=0}^1
    [\nabla_\mu\Psi_a^*\nabla^\mu\Psi_a+m^2|\Psi_a|^2]\,d^4x.
\]
Its local stress follows by metric variation. With E_a=(Box-m^2)Psi_a,
\[\nabla^\mu T^C_{\mu\nu}=\sum_a(E_a^*\partial_\nu\Psi_a+E_a\partial_\nu\Psi_a^*).\]
The free field equations therefore give conservation; the common quantum
renormalization is required to preserve this Ward identity.
On the static compact S3 it has an invariant Hadamard vacuum. Take the same
normalized smooth positive-frequency one-particle orbital f for each
internal value, |f,a>=a_a^dagger(f)|0>. Smooth spectral coefficients ensure
the finite-particle state has the same Hadamard singularity.

This is a real carrier, not a zero-stress qubit. On the static background
its excess Hamiltonian mean is
sum_(k,m) sqrt[m^2+(k^2-1)/A^2] |f_km|^2>=m.
For the uniform k=1 orbital, the excess is m and the excess density is
m/(V0 A^3). Its vacuum RSET and all stress fluctuations are also retained.
No cancellation with an unchosen counterterm is assumed.

## 2. The complete representation sector, not a one-particle truncation

Let H_V be the ENTIRE fundamental isotypic sector of the carrier Fock
representation:
\[
                   {\cal H}_V\simeq{\mathbb C}^2\otimes{\cal M}.
\]
The multiplicity space M contains every orbital and every allowed
fundamental copy, including the singlet pair dressing produced by a common
metric history. No projection back to a one-particle state is performed.

The local total carrier stress, common free propagation and relative
metric unitary commute with U(2). Schur's lemma therefore gives on this
sector T_C=I2 tensor t_C and B_C=I2 tensor b_C, with the usual smeared
domains understood for unbounded stress. This is an INTERNAL representation
decomposition, not a local spacetime tensor factor.

Uniformly extend the explicit shell-memory dilation as U_x tensor I_M.
It acts on the entire multiplicity and commutes with the static free carrier
Hamiltonian. Equivalently, within this sector the global Noether generators
Q_ab act as |a><b| tensor I_M, so
J=i(|A+><A-| tensor Q10-|A-><A+| tensor Q01)
has the required block action. These are global charges and global shell
projectors. This is not a localized interaction or an autonomous controller;
any internal reference that implements it remains an actual resource.

## 3. The actual correlated output on the gravitational observable algebra

Start from rho_th tensor |0><0|_internal tensor sigma_M. The actual gate
output is varrho_s,internal,plus/minus tensor sigma_M, with all correlations
of PREPARATION.md retained. On the future invariant algebra
A_s tensor I_internal tensor B_M its restriction is exactly
rho_s,plus/minus tensor sigma_M.

For no later direct shell-carrier coupling and a common U(2)-invariant
carrier theory, this proves for EVERY 0<c<=w, not only c=w,
\[
 \langle T_{\rm tot}\rangle_\pm=\langle T_s\rangle_\pm+\langle T_C\rangle,
 \quad N_{{\rm tot},\pm}=N_{s,\pm}+N_C,\quad
 \Pi_{{\rm tot},\pm}=\Pi_{s,\pm}+\Pi_C ,
\]
where Pi includes the common mean-response/contact prescription.
The absolute connected shell-carrier stress cross covariance vanishes in
this invariant future algebra. The carrier noise itself does not vanish.

Each full influence, rather than only its difference, factors:
\[
            F_{{\rm tot},\pm}=F_{s,\pm} F_C .
\]
Common independent original zero/higher modes may be included as the
additional F0 Frest factors. This strengthens the abstract-memory endpoint
theorem by adding an explicit carrier symmetry and input contract; it is
not a claim about arbitrary memories or gate-era observables.

## 4. A nonzero full future contrast exists for a sufficiently small pulse

Use the balanced family in HISTORY_WITNESS.md with variable epsilon.
For every sufficiently small positive epsilon,
beta_shell=epsilon beta1+O(epsilon^2) with beta1!=0 and F0=1.
For the massive carrier, conformally rescaled modes have compact smooth
scattering potential
V_C=a''/a-m^2(a^2-A^2) relative to
omega_C,k^2=k^2-1+m^2 A^2>0.
For fixed finite m,A, all the needed L1 derivative norms of V_C are O(epsilon).
The same Volterra/integration-by-parts proof gives beta_C,k=O(epsilon/omega_C,k^2)
uniformly in k and a Hilbert-Schmidt norm tending to zero. The number-preserving
part converges strongly to identity. Thus a natural relative implementer
can be chosen strongly continuous at epsilon=0; on the fixed normal carrier
state its expectation tends to 1. Arbitrary common implementer phases do not
alter the modulus limit.

It follows that some epsilon0>0 gives |F_C|>1/2 for 0<epsilon<epsilon0.
The original rest overlap is also nonzero there. Hence the complete
free-field-plus-actual-carrier FUTURE influence contrast is nonzero for a
nonempty small-epsilon interval. This is an existence result: no numerical
epsilon0 is certified, and the bare-field 2.04e-10 bound at epsilon=.001
must not be quoted as an expanded-carrier bound.

Shale implementability and the natural implementer are discussed in
Bruneau-Derezinski, arXiv:math-ph/0511069, section 3.1.
Compact-Cauchy Hadamard representation equivalence is also discussed in
Junker-Schrohe, arXiv:math-ph/0109010, Theorem 4.7(ii); it is not a generic
claim that arbitrary raw canonical slicings have unitary evolution.

## 5. What must be recomputed for gravity

The carrier mean, vacuum counterterms and Pi_C change the common total model.
The original bare A, P, K0 and static pure-pressure formula do not
automatically apply to its on-shell solution. One must solve the expanded
mean/constraints, choose joint gravity data, recompute the response, and
construct the local preparation controller. Equal carrier source between
two internal encodings does not authorize removing the carrier. No such
on-shell or gate-era completion is claimed here.
