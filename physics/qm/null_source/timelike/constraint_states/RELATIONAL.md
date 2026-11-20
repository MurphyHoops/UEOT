# A complete relational source history, and its normal finite-resolution encoding

This is a declared constrained source/reference model. It does not supply
the Einstein Hamiltonian, momentum constraints, a gravity action or the
stress of a physical clock. Its purpose is to construct the precise
alternative left open by QUANTUM_FLOOR and ZERO_VIRIAL, without calling a
nonnormal kinematic distribution a normal density matrix.

## 1. Physical Hilbert space

For any self-adjoint H on the source Hilbert space, introduce
H_kin=L2(R,dt) tensor H_source, P_t=-i d/dt, and
C=P_t+H (a fixed constant can be subtracted throughout).
Distributional solutions are
\[
                \Psi_\psi(t)=e^{-iHt}\psi .
\]
They have infinite kinematic norm on the full time axis. Define their
physical inner product by
\[
 \langle\Psi_\phi,\Psi_\psi\rangle_{\rm phys}
 =\langle\phi,\psi\rangle
 =\langle\Psi_\phi(t),\Psi_\psi(t)\rangle
\]
at any t. Its completion is exactly H_source. Normal density matrices on
this physical Hilbert space and all bounded source effects are then
well-defined. Evaluation at t is a unitary reduction map. The relational
effect at reading t is e^{iHt} O e^{-iHt} on H_phys, so probabilities and
all products of bounded relational observables agree with the original
source evolution. The original source's Hadamard correlators are recovered
when the corresponding smeared field forms are defined on their domains.

This elementary construction is the linear-clock case of the standard
group-averaging/Page–Wootters/Dirac-observable relation, not a derivation
of quantum mechanics from Core. Primary reference: Hoehn, Smith and Lock,
arXiv:1912.00033, especially Sections IV–V and the physical-inner-product
discussion. No ordinary trace over a nonexistent normalized kinematic
history is used.

## 2. A normal encoding with explicit absolute correlations

Let G multiply g in L2(R,dg), and choose the clock coordinate
T=i d/dg, so [T,G]=i. Put
\[
 f_\sigma(g)=(2\pi\sigma^2)^{-1/4}e^{-g^2/(4\sigma^2)},\quad
 U=e^{-iHT},\quad
 V_\sigma\psi=U(f_\sigma\otimes\psi).
\]
In the source spectral representation,
\[
          (V_\sigma\psi)(g,E)=f_\sigma(g+E)\psi(E).
\]
Thus V is an isometry. With C=G+H,
\[
 U^\dagger C U=G,\quad
 \langle C\rangle=0,\quad {\rm Var}C=\sigma^2 .
\]
For every source density with finite required moments, the complete
geometry/source energy block is explicitly
\[
 \langle G\rangle=-\langle H\rangle,\quad
 {\rm Var}G={\rm Var}H+\sigma^2,\quad
 {\rm Cov}_{sym}(G,H)=-{\rm Var}H.
\]
It is an actual positive normal joint state, not merely an assigned
positive covariance. The energy probability law and energy-degenerate
NOON coherence are exactly preserved. The G marginal is identical for
the two NOON inputs because their H spectral laws coincide.

The bare source marginal, however, is the channel
\[
 \rho(E,E')\longmapsto
 e^{-(E-E')^2/(8\sigma^2)}\rho(E,E').
\]
It changes cross-energy coherence. For the original zero mode, centered
T has Var(T)=1/(4sigma^2). Bare Q covariance consequently acquires
\[
 \Delta{\rm Cov}(Q_j,Q_k)
       ={ \langle P_jP_k\rangle\over4A^6\sigma^2}.
\]
No new claim of preserving the original bare W2 is made. The sigma->0
family has no normal trace-class limit preserving that marginal; the
physical Hilbert construction above is a different normalization, not
that nonexistent limit.

## 3. Dressed observables and their exact source recovery

For any bounded source observable O define
\[
 O_D=U(I\otimes O)U^\dagger .
\]
Then [C,O_D]=0 in the strong bounded-operator sense and
\[
 V_\sigma^\dagger O_D V_\sigma=O,\qquad
 V_\sigma^\dagger O_{1D}\cdots O_{mD}V_\sigma=O_1\cdots O_m .
\]
Thus the complete dressed algebra recovers the source state exactly.
For the zero mode Q_D=Q-T P/A^3, with the displayed canonical convention.
This is an explicit operator-algebra alternative, not evidence that
Q_D is a realizable local gravitational detector.

Fourier transforming the clock gives the equivalent time-envelope
\[
 V_\tau\psi(t)=g_\tau(t)e^{-iHt}\psi,\quad
 g_\tau(t)=(2\pi\tau^2)^{-1/4}e^{-t^2/(4\tau^2)},\quad
 \sigma=1/(2\tau).
\]
Its constraint variance is 1/(4tau^2). The ideal clock's conditional source
at any t is exactly e^{-iHt}rho e^{iHt}; the unconditional source is the
Gaussian time average. The two statements are not interchangeable.

## 4. Same-energy preparation intertwiners

If a common source/memory unitary W commutes with its complete free H,
then (I tensor W)V=VW for both encodings. Consequently it acts on one
common constrained history and preserves its constraint residual.
The accepted finite-shell NOON gate, with its complete source--memory
output starting from a pure memory, has this property for the explicitly
degenerate abstract memory Hamiltonian. The final reduced memory is not
assumed pure; its correlations and entropy remain included.
All its earlier entropy and transient interaction obligations remain.

The statement is algebraic and post-gate. It does not construct a cap-local
autonomous gate, prove a common preparation geometry, or assign zero stress
to the memory. A real carrier changes H, its mean source and the needed
clock budget; the bare numerical bounds must then be recomputed.

## 5. A new normal source family with identical full stress records

The fixed-bare-marginal exclusions must not be overextended. Define
\[
 \rho_{\sigma,\pm}={\cal D}^0_\sigma(\rho_z)\otimes\rho_{h,\pm},
 \quad {\cal D}^0_\sigma(\rho_z)
   =\int p_\sigma(t)e^{-itH_0}\rho_z e^{itH_0}\,dt ,
\]
where H0=S/(2A^3) and p_sigma is centered Gaussian with variance
1/(4sigma^2). The accepted high input commutes with its static high
Hamiltonian, so this is exactly the bare marginal of the full-H normal
encoding above. Every sigma>0 gives a positive normal trace-one state
with all finite-mode moments finite. PP and symmetrized QP are unchanged,
while QQ gains the displayed smooth zero-mode constant. Its Hadamard
singularity is unchanged. This is a new preparation input, not an assertion
that the old bare W2 was preserved.

Let M={P1,P2}' be the algebra of bounded operators decomposable in the
joint zero-mode momentum representation, with the full high-mode algebra
retained. For every O in M,
\[
                    {\cal D}^{0*}_\sigma(O)=O .
\]
In the free minimal massless theory, the homogeneous zero-mode field is
Y0[Qj+I_g(eta)Pj]. Every derivative stress tensor and its products are
independent of Qj; their bounded records belong to M. The same holds for
relative free propagators on the previously admissible FLRW histories.
Consequently all defined smeared stress moments, all bounded source
stress records, and the complete prescribed-history influence are
EXACTLY identical throughout this sigma family. Use the same canonical
initial frame, renormalization and phase prescription; no new infinite
determinant or instrument is asserted.

This gives a genuine normal Hadamard source alternative at the same exact
deterministic static mean geometry. It shows that a fixed-bare-state
quantum floor is not universal across the entire stress/influence
equivalence class. It does not solve the total source/quantum geometry
constraint: G remains a coded reference, not a radius operator, and a
physical preparation of this global dephasing still has to be supplied.
The sigma->0 limit has divergent QQ and no normal trace-norm limit;
source-algebra equivalence is not permission to call that endpoint a
normal full field state.
