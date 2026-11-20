# The pulse itself has a nonzero total-source obligation

The free-out covariance and noise are conserved, but this does not close the measurement interval. The same actual short Gaussian pointer channel gives an explicit obstruction.

Use the convention \(\Box u_{\rm ret}=f\), with \(u_{\rm ret}=G_{\rm ret}f\) and vanishing incoming data. The pointer momenta commute with their coupling and have centered independent Gaussian distributions. Consequently the exact nonselective target mean change at every intermediate time is
\[
\Delta\langle T_{ab}\rangle=2sT_{ab}[u_{\rm ret}].
\]
The classical identity \(\nabla^aT_{ab}[u]=(\Box u)\nabla_bu\) therefore yields
\[
\nabla^a\Delta\langle T_{ab}\rangle
 =2sf\nabla_bu_{\rm ret}.
\]
The script verifies the identity on arbitrary nontrivial \(u(t,x)\), including energy and momentum components; its covariant form follows directly by the scalar derivative commutator.

After the pulse \(f=0\), the displacement agrees, up to propagator sign convention, with the out \(u=Ef\); all stress and noise formulas above are unchanged. During the pulse, the interaction, pointer and controller must carry the opposite divergence. Inserting only the computed target source into Einstein's equation would violate its Bianchi identity.

On the old static background, the Killing-energy ledger is
\[
\Delta E_{\rm target}=-2s\int\sqrt{-g}\,
             f\,\partial_\tau u_{\rm ret}.
\]
The already certified \(8.31\,10^{-14}<\Delta E_{\rm target}<1.88\,10^{-11}\) makes the work nonzero. Equal source momentum before and after a QND operation does not remove this work. Nor does a small numerical energy change remove the exact conservation requirement.

This is the specified scalar-source Gaussian pointer model. The finite kinetic field-probe model has its own force \(O_\chi\partial_b\chi\), computed from the same coupled Green kernel. Neither the final POVM nor the target conditional instrument determines the entire apparatus energy ledger. Completing the target channel and its free-out Ward identity is a necessary intermediate result; completing the total physical history still requires a dynamical apparatus source.

## The same Cauchy state throughout the pulse

The forced static mode equation is q_k''+omega_k^2 q_k=-b_k t'/A^2, with retarded data. Its oscillator-energy amplitude is bounded by ||t'||_1 |b_k|/A^2, including the zero mode by its zero-frequency limit. Parseval therefore bounds the added target energy at **every** pulse time by
\[
 \Delta E(\eta)\le{\|t'\|_1^2\over4v_m A^3V_0}<1.88\,10^{-11}.
\]
Let r_eta denote the complete Cauchy displacement vector (u_k,A^2 u'_k). For each field its actual covariance is
\[
 \Gamma_\eta=\Gamma_{\rm free,\eta}+s r_\eta r_\eta^T.
\]
This includes both normal derivatives and all zero/high covariance terms. The same pointer momentum is used at every time, not a fresh displacement drawn separately on each slice.

Specifically, P_i(eta)=P_i-Y_0 t(eta) xi_i with Var(xi_i)=s. Thus
\[
 \delta\mu(\eta)={A^4t(\eta)^2\over2Cw_{\rm ptr}}
 \le{8A^4\over\pi^2Cw_{\rm ptr}}<2.4\,10^{-19},
\]
\[
 \Delta\operatorname{Var}S_0=2\mu\,\delta\mu+(\delta\mu)^2,\qquad
 E_{0,\rm transient}\le {4A\over\pi^2w_{\rm ptr}}<1.35\,10^{-13}.
\]
The pulse source law returns to the original one when t vanishes. With k_eta,eta'=sY_0^2 t(eta)t(eta'), its exact nonselective multitime covariance is
\[
 \operatorname{Cov}(S_0(\eta),S_0(\eta'))
 =\operatorname{Var}S_0+{4\mu k_{\eta,\eta'}\over C}
                    +{4k_{\eta,\eta'}^2\over C^2}.
\]
The momenta at these times commute, but they do not commute with the final pointer coordinate: [P_i(eta),Y_j,out]=i delta_ij Y_0 t(eta). This nonselective spectral process must not be relabeled as a simultaneously observed history conditional on a final flag.

For the convention L_int=-sum_i xi_i f phi_i, T_int=-sum_i xi_i f phi_i g. The combined target-plus-interaction mean Ward defect is -2s u_ret partial_b f. Its opposite remains the controller's responsibility. No target-only work formula closes that controller equation.
