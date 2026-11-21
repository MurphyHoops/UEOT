# Both actual flags, not only their average, retain anisotropy

This sharpens LOCAL_TENSOR.md on the same static out slice. No new state, angular randomization, high reset or latent-variable readout is introduced.

Let \(\beta=-1/(\sqrt{2\pi^2}A^2)\), \(v=X_0/4\),
\(V_z=v+w_h+w_{\rm ptr}\), \(V=\beta^2V_z\), and \(\delta=V_z/C\). Here \(v\) is the within-\(p\) Gaussian quantum variance; the between-\(p\) CQ variation is not inserted into \(V\). Put
\(c(x)=\operatorname{Cov}_{\rm sym,within-p}(\phi_i(x),A_i)\), \(A_i=\beta P_i+H_i\), \(u=Ef\), and \(s=1/(4\beta^2w_{\rm ptr})\).
The homogeneous profile \(q(x)\) is the mean field per unit \(p_i\).

For the fine integration variable \(Y\), each Gaussian block has
\[
m_{i,p,Y}=p_iq+cr_i,\quad r_i=(Y_i-\beta p_i)/V,\qquad
C_{\rm cond}=C_0+suu-cc/V.
\]
The continuous \(Y\) is only a Kraus integration variable. The physical reader produces the two smooth flags directly.

For the radial effect \(e_b=m_b^2\), define
\[
P_b(R)=E_{\zeta\sim N(0,\delta I_2)}
 e_b(|\sqrt R\,e_1+\zeta|),\quad
p_b=\tfrac12[P_b(1)+P_b(1+\sqrt3/2)].
\]
Equivalently, this is a one-dimensional Rice integral with density
\[
{r\over\delta}\exp[-(r^2+R)/(2\delta)]I_0(r\sqrt R/\delta).
\]
The actual angular prior need not be uniform or observed; radiality makes the probability depend only on \(R\).

Gaussian integration by parts gives
\[
E[(r_1^2+r_2^2-2/V)e_b]
 ={4\over\beta^2C}[RP_b''(R)+P_b'(R)].
\]
The \(T[q]\) and polarized \(B_T(q,c)\) terms have zero spatial traceless part, since \(q\) is spatially homogeneous. The reference covariance stress is isotropic. Hence the exact conditional anisotropy is
\[
p_b\pi_b=2sp_b\pi[u]+D_b\pi[c],\quad
D_b={4\over\beta^2C}E_R[RP_b''(R)+P_b'(R)].
\]

## The soft-reader score bound

For the Gaussian displacement \(\zeta\), the radial Laplacian score is
\(Q=(|\zeta|^2-2\delta)/(4\delta^2)\), with \(EQ=0\) and \(EQ^2=1/(4\delta^2)\).
On either ring, subtract the correct constant flag value. Its squared difference is bounded by its absolute difference, whose expectation is at most \(\varepsilon_{\rm tail}\). Cauchy–Schwarz gives
\[
|D_b|\le{2\sqrt{\varepsilon_{\rm tail}}\over\beta^2V_z},\qquad
{|D_b|\over2sp_b}
 \le{4w_{\rm ptr}\sqrt{\varepsilon_{\rm tail}}\over p_bV_z}
 \le{4\sqrt{\varepsilon_{\rm tail}}\over1/2-\varepsilon_{\rm tail}}.
\]
This proof uses the actual short-probe high noise in \(\delta\) and the actual pointer variance in \(s\). They are not interchangeable.

The high part of the covariance profile is
\[
c_h=-{1\over2A^2}\sum_{km}(2n_k+1)b_{km}\widehat t(\omega_k)
                    \sin(\omega_k\eta)Y_{km}.
\]
Its zero part is spatially constant. Parseval and \(\|t'\|_1\le8/\pi\) give
\[
{\int|Dc|^2\over\int|Du|^2}
 <{32(1+2n)^2\over V_0}<70.
\]
In physical units \(\|\pi[f]\|_{L^1}=\sqrt{2/3}\,A\int|Df|^2\). Combining these inequalities,
\[
{\|\pi_b-\Delta\pi_{\rm ns}\|_{L^1}\over
  \|\Delta\pi_{\rm ns}\|_{L^1}}<6\,10^{-7},
\]
and therefore, for **each** of the two actual flags,
\[
\|\pi_b\|_{L^1}>
 (1-6\,10^{-7})\sqrt{2/3}\,{A\over2w_{\rm ptr}}
 >1.35\,10^{-13}.
\]

Both branch sources, not merely one, thus require a nonhomogeneous metric or explicit anisotropic device compensation for exact pointwise mean closure. These are small model-unit lower bounds. They neither prove detectability nor invalidate the controlled averaged approximation, and are not asserted at every later time.

## The complete mean tensor of each actual flag

This also controls energy, momentum and trace, once the large homogeneous posterior source is kept explicitly. Write c=beta v q+c_h. Define d_b=D_b/p_b and Gamma_b=4 E_R[R P_b'(R)]/(beta p_b). With t_hom(mu_b) denoting the homogeneous comparison tensor at the **actual** posterior mean mu_b, retaining the original high reference,
\[
 t_b-t_{\rm hom}(\mu_b)
 =2sT[u]+(\Gamma_b+2\beta v d_b)B_T(q,c_h)+d_bT[c_h].
\]
The comparison tensor is not a high-state reset and is not asserted to solve Einstein's equation.

For h=(sqrt(3)-1)/4-delta_r, 0.18<h<0.2, and delta>=1/2500, h^2>2 delta. Gaussian tail integration gives
\[
 |P'_b(R)|\le{(h+\delta/h)\varepsilon_{\rm tail}\over2\sqrt R\,\delta},
 \qquad |RP_b''+P_b'|\le{h^2\varepsilon_{\rm tail}\over4\delta^2}.
\]
For the second inequality the radial Laplacian score is nonnegative on |N|>=h, and its tail integral is h^2 epsilon_tail/(4 delta^2). Together with delta<1/2400, p_b>0.499, |beta|>3.3e-11, beta^2 C>0.69, these yield |Gamma_b|<1e-4, |d_b|<1e-12, and |beta|v<0.06.

The covariance high-profile energy obeys
\[
 E[c_h]\le{(1+2n)^2\|t'\|_1^2\over8A^3V_0}<3\,10^{-15}.
\]
In the orthonormal-component Frobenius norm, integral ||T[c_h]||=2E[c_h], and integral ||B_T(q,c_h)||<=sqrt(2E[c_h]/A^3). Combining with the already computed nonselective mean gives, for each actual flag,
\[
 \int\|t_b-t_{\rm hom}(\mu_b)\|_F\,dV<3.77\,10^{-11}.
\]
This does not count the finite change mu_b-mu as a small perturbation. It is a complete mean-tensor bound on the same static out slice; future local geometry and device compensation remain to be solved.
