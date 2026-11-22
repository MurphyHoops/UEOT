# AN. Smooth mass-source counterterms, lapse contacts and the common CTP state

## AN1. Which sources are varied

Use the local AL candidate with real smooth mass-squared scalar sources
\(s_\chi(t,y),s_s(t,y)\); the latter couples equally to \(\phi,\psi\).
They are diagnostic source profiles held fixed as coordinate scalar
functions when varying the metric or lapse. If a physical controller makes
\(s_i\) depend on the lapse or other fields, its chain-rule terms and stress
must be added. This entry does not turn an external profile into an
autonomous apparatus.

The background mass Hessian changes by
\(\operatorname{diag}(s_\chi,s_s,s_s)\).
Relative to AL at zero sources, the one-loop local polynomial is exactly
\[
 P_s=s_\chi(a+3\alpha\chi^2+\eta S)
    +s_s[2b+2\eta\chi^2+(3\beta+\kappa)S]
    +\tfrac12s_\chi^2+s_s^2,\qquad S=\phi^2+\psi^2,          \tag{AN.1}
\]
\[
 F_s=\zeta_\chi s_\chi+2\zeta_s s_s,\qquad
 G_s=s_\chi+2s_s,\qquad \zeta_i=\xi_i-\tfrac16 .
\]
Its heat density is
\[
 (16\pi^2)^{-1}[P_s+RF_s-\Box G_s/6].
\]
Thus a closed constant-coupling matter potential is not yet a renormalized
generating functional for its mass insertions. Source squares, curvature
terms, composite-field mixing and source endpoint terms must be fixed.

For a representative real counterterm action write
\[
 S_s^{\rm ct}=c_{\rm ct}\int\sqrt{-g}
                        [P_s+RF_s-\Box G_s/6].             \tag{AN.2}
\]
The symbol \(c_{\rm ct}\) includes the divergent normalization and
effective-action sign; independent finite coefficients remain independent
renormalization inputs.

## AN2. Explicit source and mixed lapse columns

With the static \(h\), zero shift and closed spatial slice convention of AK,
\[
 \frac{\delta S_s^{\rm ct,bulk}}{\delta N}
 =c_{\rm ct}\sqrt h[P_s+R_hF_s-2\Delta_hF_s].                \tag{AN.3}
\]
For a source variation \(\sigma_i\), the mixed column is
\[
 c_{\rm ct}\sqrt h[
   (\partial_iP_s)\sigma_i+
      \zeta_i^{\rm eff}(R_h\sigma_i-2\Delta_h\sigma_i)],
 \qquad
 (\zeta_\chi^{\rm eff},\zeta_s^{\rm eff})=(\zeta_\chi,2\zeta_s),          \tag{AN.4}
\]
where
\[
 \partial_\chi P_s=a+s_\chi+3\alpha\chi^2+\eta S,\quad
 \partial_sP_s=2b+2s_s+2\eta\chi^2+(3\beta+\kappa)S .
\]
These are source-containing operators. In particular, the source insertions
mix the controller quadratic field with the source/probe quadratic fields.
The local Laplacian of a nonconstant source variation cannot be removed by
the homogeneous spatial integral.

The direct bulk source Hessian is the local kernel
\[
 \frac{\delta^2 S_s^{\rm ct,bulk}}
      {\delta(s_\chi,s_s)\delta(s_\chi,s_s)}
  =c_{\rm ct}N\sqrt h
       \begin{pmatrix}1&0\\0&2\end{pmatrix}\delta^{(4)}.     \tag{AN.5}
\]
This is the direct variation of the local counterterm. The full
state-dependent influence Hessian contains additional connected
correlations and does not equal this matrix.

The total derivative gives the finite-time action
\[
 S_s^{\rm ct,end}=\frac{c_{\rm ct}}6
        \left[\int dV_h\,\dot G_s/N\right]_{t_i}^{t_f}.      \tag{AN.6}
\]
For example its source/lapse mixed variation is
\[
 -\frac{c_{\rm ct}}6
 \left[\int dV_h\,\partial_t(\sigma_\chi+2\sigma_s)
                         \delta N/N^2\right]_{t_i}^{t_f}.
\]
The source profiles can be compactly supported inside the interval, in
which case this particular endpoint term vanishes, but that is a support
condition rather than permission to discard the term before variation.
The \(RF_s\) boundary completion still depends on the selected metric
boundary problem.

## AN3. Tree contact and the two CTP branches

For homogeneous sources in the actual finite-cutoff canonical problem,
\[
 H_K(N,s)=N[H_K+s_\chi O_{\chi,K}+s_sO_{s,K}],
 \quad O_{s,K}=\tfrac12\int(\phi_K^2+\psi_K^2)dV.
\]
At \(N=1,s=0\), the tree mixed contacts are
\[
 C_{N s_\chi}=O_{\chi,K},\quad C_{N s_s}=O_{s,K},
 \quad C_{NN}=C_{s_i s_j}=0.                               \tag{AN.7}
\]
The separated pulses in AM produce the correct initial covariance block;
they do not include by themselves every contact of this overlapping
lapse-times-mass parameterization.

For a general common-history expansion
\(H[J]=H_0+J^aO_a+\frac12J^aJ^bC_{ab}+\cdots\), fix one initial
\(\rho\) and assume the displayed operator words and time integrals exist.
Then the exact CTP trace has the connected derivatives
\[
 \delta_{+a}\log Z=-i\langle O_a\rangle,\quad
 \delta_{-a}\log Z=+i\langle O_a\rangle,
\]
\[
 \delta_{+a}\delta_{+b}\log Z
   =-\langle T\,\Delta O_a\Delta O_b\rangle
                         -i\langle C_{ab}\rangle\delta,
\]
\[
 \delta_{-a}\delta_{-b}\log Z
   =-\langle\bar T\,\Delta O_a\Delta O_b\rangle
                         +i\langle C_{ab}\rangle\delta,
 \qquad
 \delta_{+a}\delta_{-b}\log Z
      =\langle\Delta O_b\Delta O_a\rangle.                  \tag{AN.8}
\]
The signs here use Hamiltonian derivatives; action counterterms are
translated with their corresponding action-to-Hamiltonian sign.
Finite cutoff alone does not supply the moment hypotheses for every normal
state. AM's Gaussian original-point derivatives satisfy the stated domain
condition. General evolving unbounded words require separate control.

The symmetric noise is
\[
 N_{ab}=\tfrac12\langle\{\Delta O_a,\Delta O_b\}\rangle,\quad
 N(f,f)=\|O_f^{\rm centered}\sqrt\rho\|_{\rm HS}^2\ge0.       \tag{AN.9}
\]
The contacts in (AN.5), (AN.7) and AL's \(R^2\) Hessian contribute to the
real response/action variation. They are not independent stochastic
noise kernels. The direct local counterterm in the action has only
same-branch bulk Hessians of opposite signs; this does not set the
full mixed-branch covariance to zero.

## AN4. Positivity, external-source Ward identity and preparation terms

A real source-only c-number counterterm multiplies the exact CTP trace by
\(\exp(iS_{\rm ct}[J_+]-iS_{\rm ct}[J_-])\).
This is a diagonal phase change of every history Gram matrix. It preserves
positivity, normalization and \(|Z|\); it cannot cancel a positive
divergent variance by decree. Field-dependent counterterms instead change
the actual Hamiltonian or composite insertion. Their effect must be
recomputed in the same chosen preparation, as AM's raw/Wick comparison
demonstrates.

With the scalar sources transformed under diffeomorphisms, the off-shell
Ward identity contains their work terms:
\[
 \nabla^\mu T_{\mu\nu}
  =\sum_A{\cal E}_A\nabla_\nu\varphi_A+
          {\cal E}_{s_\chi}\nabla_\nu s_\chi+
          {\cal E}_{s_s}\nabla_\nu s_s.                    \tag{AN.10}
\]
On the matter equations with nonconstant prescribed sources, those
external-work terms remain. An autonomous controller must contribute the
compensating equations and stress. At zero sources, the same complete
matter action recovers its own on-shell conservation condition.

The formulas (AN.8) assume a fixed \(\rho\) in a specified common canonical
Hilbert space. If the proposed boundary preparation is
\(\rho[g_i,s_i]\), its first and second variations produce additional
initial blocks. The identity \(\operatorname{Tr}\delta\rho=0\) does not
set those blocks to zero. A metric-dependent mode projector also needs
its variation. Neither effect is replaced by an independent geometric
record chosen after the matter state.

## Acceptance and next gate

Accepted at the stated finite-cutoff / one-loop levels: the actual
source-functional counterterm basis, direct source/lapse/endpoint columns,
and their distinction from same-state CTP noise and initial variations.
Open: the positive normal interacting continuum state, joint smooth-source
propagators, source/metric projector transport, complete renormalized stress
noise and all local Ward/Einstein constraints.

The next construction must freeze these counterterms and the preparation
together, take actual smooth histories and prove the joint limit. It may
not substitute formal polynomial closure, a positive matrix at each cutoff,
or source-only phase renormalization for that limit.
