# Exact conditional local noise of the actual two-flag state

The nonselective kernel in LOCAL_TENSOR.md does not determine every conditional noise by itself. Here the actual fixed preparation and specified reader do determine it. No new mode integration is needed to obtain the exact finite-integral representation.

For each latent \(p\) and fine Kraus integration variable \(Y\), the two fields have a common connected Wightman kernel
\[
W_c=W_0+s\,u\otimes u-c\otimes c/V
\]
with the original commutator retained, and means \(m_i=p_iq+r_ic\). The definitions of \(V,\delta,c,u,r_i\) are those in CONDITIONAL_TENSOR.md. The smooth difference terms preserve Hadamard form. The complete conditional state is the posterior mixture of these Gaussian blocks.

Define
\[
X=(|p|^2,\ p\cdot r,\ |r|^2),\qquad
{\cal B}=(T[q],\ 2B_T(q,c),\ T[c]).
\]
Let \(N_G\) be the stress-noise kernel of two independent centered Gaussian fields with connected kernel \(W_c\). Let \(K_{fg}\) be the symmetrized covariance of the linear polarized operators \(L[\varphi,f]\) and \(L[\varphi,g]\) for one such centered field; take \(K_{qc}\) symmetrically in \(q,c\). Wick's rule is applied only inside these Gaussian blocks.

The exact complete flag noise is then
\[
N_b=N_G+E_bX_1K_{qq}+2E_bX_2K_{qc}+E_bX_3K_{cc}
 +\sum_{j\ell}\operatorname{Cov}_b(X_j,X_\ell)
                   {\cal B}_j\otimes{\cal B}_\ell.
\]
The last term carries the actual between-\(p\), between-record and cross-species correlations. Zero/high quantum correlations are already in \(W_c\). No Gaussian approximation is made to the whole CQ mixture.

## One Rice integral generates all remaining moments

For each of the two radial values \(R\), choose coordinates with \(p=\sqrt{CR}\,e_1\); this is a change of integration coordinates in an internally invariant stress expression, not an angular twirl of the preparation. Let \(N\sim N(0,\delta I_2)\). Then
\[
X_1=CR,\quad X_2={\sqrt R\,N_1\over\beta\delta},\quad
X_3={|N|^2\over\beta^2C\delta^2}.
\]
The sign of \(\beta\) is retained in \(X_2\).

Write \(P_b(R;\delta)\) for the Rice integral in CONDITIONAL_TENSOR.md. Define
\[
Z_b(R;t,z)=E\!\left[e^{tN_1+z|N|^2}
                  e_b(|\sqrt R\,e_1+N|)\right].
\]
Completing the Gaussian square gives the exact identity, for \(z\) near zero,
\[
\delta_z={\delta\over1-2\delta z},\qquad
Z_b={\exp(\delta_z t^2/2)\over1-2\delta z}\,
 P_b((\sqrt R+\delta_z t)^2;\delta_z).
\]
Only its derivatives \(t,z,tt,tz,zz\) at zero, together with the two known \(R\) values, are needed for \(E_bX\) and \(\operatorname{Cov}_bX\). Average the two radial contributions with their original weights \(1/2\), then divide by the actual flag probability \(p_b\). The script checks the square completion and all unweighted Gaussian moment limits.

For later numerical evaluation, the Rice density can be written using the scaled Bessel function \(I_{0e}\):
\[
{r\over\delta}\exp[-(r-\sqrt R)^2/(2\delta)]I_{0e}(r\sqrt R/\delta).
\]
This avoids exponential overflow at the present large \(R/\delta\). No such numerical integration is claimed in this certificate.

All needed moments are finite for the actual bounded latent means and finite Gaussian pointer variance, with \(p_b>0.49\). This does not assert that the Hadamard condition alone guarantees all fourth moments for arbitrary states.

Finally, propagate \(W_0,u,c,q\) through the same branch KG map and waiting/shear schedule. The coefficient moments \(E_bX,\operatorname{Cov}_bX\) stay those of the original actual readout. This gives the full local conditional target-noise kernel on each prescribed future geometry. Its numerical local metric response and the probe/reader/controller total noise are separate tasks.

## The response input from the same actual state

The nonlocal stress commutator needs only the complete two-point function, even for this non-Gaussian CQ state, because the commutator of quadratic fields reduces using the CCR. Set
\[
 S_{\Sigma,b}=2\operatorname{Re}W_c+E_bX_1\,q\otimes q
 +E_bX_2(q\otimes c+c\otimes q)+E_bX_3\,c\otimes c .
\]
The two-field stress commutator is 4i times the appropriate two stress differential operators acting on E(x_1,y_1) S_Sigma,b(x_2,y_2), followed by the coincidence restrictions. Its precise meaning is the difference of valid Hadamard products W^2-W_op^2 with the corresponding mean terms, not a separately postulated multiplication of arbitrary distributions E and S. The script checks 2(W^2-W_op^2)+4mn(W-W_op)=4iE(S+mn).

This gives the actual nonlocal Kubo input. The retarded extension, contact/seagull terms, variations of shared local counterterms, gauge constraints and the inverse coupled Einstein operator are not calculated by this identity.
