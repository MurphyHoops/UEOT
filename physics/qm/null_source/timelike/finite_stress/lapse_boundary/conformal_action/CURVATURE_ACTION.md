# A. General curvature coupling, full endpoint and contact rows

This is a NEW matter model. The previous minimal-coupling AE coefficients,
incoming state and common mean history are not imported into it.

## A1. One local action and its scalar boundary term

Use ds²=a²(-N²deta²+dOmega_3²), a=A exp(u), D=N^{-1}d/deta,
kappa=Du, chi=Dkappa. For n_s real fields, orthonormal real S³ modes
have k=1,2,..., degeneracy k² per field. Q=sum q_r²/2, q=a phi.
Set beta=1-6xi and R=6a^{-2}(chi+kappa²+1).

Starting from -1/2 integral sqrt(-g)[(nabla phi)²+xi R phi²], the
q kinetic rewrite contributes -[kappa Q]. For the induced-metric/scalar
Dirichlet classical problem the nonminimal boundary term is

    S_xi,boundary=-xi integral_boundary epsilon sqrt(|h|) K_out sum phi².

Here epsilon=n_out²=-1 on spacelike ends and K_out=+/-3kappa/a.
Its value is +6xi[kappa Q]. Thus the NET matter endpoint is

    -beta[kappa Q].

The resulting bulk Lagrangian is

    L_m,beta=sum (Dq)²/2 - sum(k²-beta)q²/2
               +beta(chi+kappa²)Q.

For arbitrary beta its first-derivative representative, including the
above endpoint, is

    L_m,raw=sum(Dq)²/2-beta kappa DQ+beta kappa²Q
               -sum(k²-beta)q²/2.                         (A1)

At beta=0 both chi Q, kappa²Q AND the net endpoint vanish.
The k=1 modes become positive oscillators of frequency one, replacing
the old free zero modes. This is a change of dynamics and preparation.

The boundary sign follows the scalar-tensor variational principle of
Dyer--Hinterbichler, arXiv:0809.4033v2, §5.2 eqs.(5.5)-(5.6); their
inward-spacelike normal convention equals epsilon K_out here.
Jacobson--Satz, arXiv:1308.2746v2, shows that quantum bulk/boundary
renormalization is an additional issue. Its Euclidean determinant
boundary conditions are not automatically our real-time CTP gluing law.

## A2. The actual constraint modification

Let the complete geometric representative be
L_g=g chi²/2+A_kappa chi+L_0, with g nonzero for this section.
Keep kappa as an Ostrogradsky coordinate, p=Dq in the bulk frame:

    P_kappa=g chi+A_kappa+beta Q,
    C_beta=kappa P_u+(P_kappa-A_kappa-beta Q)²/(2g)
                 +H_beta-beta kappa²Q-L_0,
    H_beta=sum[p²+(k²-beta)q²]/2.                          (A2)

The difference from beta=1 at the SAME geometric coefficients is

    Delta C=[(1-beta){P_kappa-A_kappa,Q}
                    +(beta²-1)Q²]/(2g)
                 +(1-beta)(kappa²+1)Q.                  (A3)

Thus one action change supplies the linked geometry derivative,
quartic and quadratic terms. Subtracting only a scalar or Wick
contraction would not be this action. No claim is made that the
old minimal AE counterterm coefficients remain appropriate.

Endpoint transport is
P_kappa,raw=P_kappa-beta Q, p_raw=p-beta kappa q.
The raw source constraint is
H_beta,raw+beta kappa D_raw+(beta²-beta)kappa²Q,
where D_raw=sum{q,p_raw}/2. At beta=0 raw and bulk agree.
For beta nonzero this is only a canonical identity at finite K;
an infinite-mode implementer cannot be assumed.

## A3. Retained lapse, physical metric row and contacts

In configuration polarization (A1) is

    L_eta = sum q'²/(2N) - beta u' Q'/N
                + beta u'² Q/N - N V_beta(q).

Hence its exact lapse row is

    Gamma_N=-sum(Dq)²/2+beta kappa DQ-beta kappa²Q-V_beta.

At fixed q the u Euler row is
Gamma_u=N beta[D²Q-2chi Q-2kappa DQ].
Variation at fixed physical phi additionally has sum q Gamma_q.
This distinction disappears only on the matter equations, with the
same endpoint/initial kernel transported.

The local velocity/lapse Hessian contains

    L_NN=[sum q'²-2beta u'Q'+2beta u'²Q]/N³,
    L_N,u' = beta(Q'-2u'Q)/N²,
    L_u',u'=2beta Q/N,
    L_N,q'_r=-(q'_r-beta u'q_r)/N²,
    L_u',q'_r=-beta q_r/N,
    L_q'_r,q'_s=delta_rs/N.

These determine the derivative-delta contacts; varying V_beta and Q
supplies the position contacts. The script verifies the complete
single-mode polynomial Hessian and additivity gives every finite K.
For beta=0 the configuration lapse contact is sum q'²/N³,
although the phase-space action p q'-N H_conf has zero EXPLICIT
second lapse derivative. Integrating out p restores the configuration
contact. They must not be added twice.

CTP uses S[+]-S[-], independent N_+,N_- before variation, one initial
density, and the transported final gluing. Vanishing classical matter
trace at beta=0 does not remove the quantum anomaly.

## A4. Scope

These are exact finite-mode algebra and a classical local four-dimensional
matter action with its declared boundary variational problem.
The following pages choose a finite anomaly-compatible homogeneous
geometry representative and quantize it. They do not constitute a
complete four-dimensional quantum-gravity renormalization proof.

Sources inspected:
https://arxiv.org/abs/0809.4033
https://arxiv.org/abs/1308.2746
