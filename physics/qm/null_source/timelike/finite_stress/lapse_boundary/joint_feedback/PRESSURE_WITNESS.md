# Actual incoming pressure witness and the fixed-geometry-law rejection

This is an actual-source calculation at \(K=131072\), not a static-vacuum substitution. The source is the same transported rank-two thin state in the quiet mean history. The result concerns its raw finite-\(K\) stress under the original positive-\(\kappa\), \(u\)-clock joint generator. Geometric AE terms and the joint continuum problem have not been equated to this source-only quantity.

## P1. One fixed history and a useful relative remainder

Use QUIET_WINDOW's once selected \(c=e^{-20000}\) and
\[
 u(\eta)=U(-ce^{s\eta},b(c)e^{r\eta}),\quad u(0)=0,\quad h_i=u'(0)>0.
\]
The fixed input enclosures give
\[
 1.9<s<2.1,\quad 900000<r<937000<10^6,\quad
 80000<A<10^5,\quad 0<p=4n<0.08 .
\tag{P1}
\]
Here \(\eta\) denotes conformal time, not the ordering parameter. Let \(W_s=w_4(s)<200\), \(W_f=w_4(r)<10^{26}\), and
\(C_0=2\,10^{20}\,6400/[2(1-0.128)]<e^{80}\).
The already proved fixed-point estimate is uniform under the smaller once selected amplitude:
\[
 \|v\|_{E_4}\le C_0r_{\rm seed}^2,\quad
 r_{\rm seed}\le(W_s+1.1W_f)c<2\,10^{26}c.
\]
At the initial unit coefficient radius, the root condition gives
\(|b-c|\le\|v\|_{E_4}\). Multiplication of that scalar correction by the fast linear mode costs \(W_f\). Therefore, for all the incoming past,
\[
 u_L=c(e^{r\eta}-e^{s\eta}),\qquad
 \|u-u_L\|_{E_4}\le C_0r_{\rm seed}^2(1+W_f)<e^{300}c^2.
\tag{P2}
\]
In particular \(\|u\|_{E_4}<e^{62}c\) and \(h_i<10^6c\).
This relative estimate is used only at the initial slice and in its incoming construction; it is not extended unchanged to the quiet future endpoint.

Set \(V=u''+(u')^2\), \(V_L=c(r^2e^{r\eta}-s^2e^{s\eta})\). The Banach algebra and derivative bounds give
\[
 \|V\|_{E_1}<e^{63}c,\qquad
 \|V-V_L\|_{E_1}<e^{301}c^2 .
\tag{P3}
\]

## P2. Use the exact Jost product in its proved Wiener domain

Let \(W_k=|F_k|^2=2\omega_k|v_k|^2\), with the same incoming normalization as NONLINEAR_HISTORY/KERNELS. Its exact positive-frequency recursion gives
\[
 W_k=1+2(\Theta^2+4\omega_k^2)^{-1}V+\sum_{j\ge2}W_{j,k},\qquad
 \|W_{j,k}\|_{E_1}\le\frac{\|V\|_{E_1}^{j}}{2\omega_k^{2j}}.
\]
This is the coefficient Wiener norm, not a bound obtained by discarding the oscillations in a time-domain \(C^0\) Volterra integral. In particular \(\Theta:E_1\to A\) is bounded.

The linear term for the actual fixed geometry is
\[
 W_{L,k}=2c\left[
  \frac{r^2e^{r\eta}}{r^2+4\omega_k^2}
 -\frac{s^2e^{s\eta}}{s^2+4\omega_k^2}\right].
\]
Writing \(R_{W,k}=W_k-1-W_{L,k}\), (P3) and the geometric Born tail prove
\[
 \|R_{W,k}\|_{E_1}<e^{302}c^2/\omega_k^2 .
\tag{P4}
\]
An explicit sufficient bound, also checked by the script, is
\[
 \omega_k^2\|R_{W,k}\|_{E_1}
 \le \tfrac12\|V-V_L\|_{E_1}
   +\frac{\|V\|_{E_1}^2}{2(1-\|V\|_{E_1}/3)}.
\]
The loose denominator only enlarges the correct estimate for \(\omega_k^2\ge3\).

For one real oscillator,
\[
 \left\langle\frac{\{\phi,P\}}2\right\rangle_{\rm vac}
 =\frac{W_k'/2-h_iW_k}{2\omega_k}.
\]
Put \(N_k=W_k'(0)/2-h_iW_k(0)\). The exact linear coefficient is
\[
 N_{L,k}=-4c\omega_k^2
 \left[\frac r{r^2+4\omega_k^2}
             -\frac s{s^2+4\omega_k^2}\right].
\tag{P5}
\]
Indeed \(N_k-N_{L,k}=R_{W,k}'/2-(h_i-c(r-s))-h_i(W_k-1)\).
The same estimates give the safe uniform bound
\[
 |N_k-N_{L,k}|<e^{305}c^2 .
\tag{P6}
\]
No mode ODE is integrated.

## P3. Retain both species, all degeneracies, and the actual thin occupations

Both source branches have all high modes in the same incoming vacuum. The occupied branch has total occupation two in the eight \(k=2\) oscillators. Its quadratic mean changes the \(k=2\) degeneracy weight from \(4\) to \(6\); averaging with probability \(p\) gives \(4+2p\). The NOON sign does not change this quadratic mean.

Consequently
\[
 \langle D_\Omega\rangle_{\rm old}
 =-4c\sum_{k=2}^{K}(k^2+2p\,\delta_{k2})\omega_k^3
 \left[\frac r{r^2+4\omega_k^2}
             -\frac s{s^2+4\omega_k^2}\right]+\mathcal R_K ,
\quad |\mathcal R_K|<e^{400}c^2 .
\tag{P7}
\]
For the last bound, \(\sum_{k=2}^Kk^2\omega_k<\sum_{k=1}^Kk^3=[K(K+1)/2]^2\); the extra occupied contribution is smaller than one times the bound (P6). The large, explicit exponent leaves a checked margin.

The sign can be certified without enumerating the \(1.5\,10^{15}\) real modes. In the upper half of the \(k\)-sum,
\[
 \omega_k\ge k/2,\qquad
 \frac r{r^2+4\omega_k^2}>
 \frac{900000}{10^{12}+4K^2}>8\,10^{-7}.
\]
Thus the negative fast term has magnitude at least \(6.25\,10^{-9}K^6c\).
The positive slow term is at most \(3c[K(K+1)/2]^2\); an additional \(36c\) safely bounds the occupied branch contribution. At the actual \(K=131072\), exact integer arithmetic and the outward remainder give
\[
 \boxed{\langle D_\Omega\rangle_{\rm old}<-10^{22}c,\qquad
       -\langle D_\Omega\rangle_{\rm old}/h_i>10^{16}.}
\tag{P8}
\]
This tiny unscaled expectation is not set to zero. Dividing by the equally small fixed expansion is part of the actual relational equation.

## P4. The same geometry probability law permits no entangled repair of this initial source row

This subsection fixes the N4/N6 two-packet \(\kappa\) law, but permits arbitrary normal joint extensions of it and the same complete raw thin source marginal. Required weighted moments/domain regularity remain part of the contract.

Let \(P_M=P_0+P_2\) be the rank-two source support. The two zero-mode annuli are disjoint; their actual free transport only multiplies by momentum phases and performs the same finite scaling, so they remain orthogonal. Since \(D_\Omega\) contains no zero-mode coordinate or momentum, cross-branch compression vanishes. On this exact support,
\[
 P_MD_\Omega P_M=d_{\rm vac}P_M+d_{\rm exc}P_2,\quad
 d_{\rm vac}<-10^{22}c,\quad |d_{\rm exc}|<100c .
\tag{P9}
\]
The vacuum inequality follows from P3 with no occupied term. For the extra branch use \(d_{\rm exc}=2\omega_2N_2\), (P5), \(r>900000\), \(s<3\), and (P6); these give \(|N_2|<5c\), already much stronger than the displayed bound.

Any joint extension has support in \(I_G\otimes P_M\), hence \(\tau=P_M\tau P_M\). Write \(I_1=\operatorname{Tr}\tau\), \(t_2=\operatorname{Tr}(\tau P_2)\), with \(0\le t_2\le I_1\). For the fixed two-packet law, Jensen within the two packets gives \(i_s\ge2\), \(i_l\ge1\). With \(w=h_i/(2R-h_i)\),
\[
 I_1\ge(1-w)\frac2{h_i}+\frac wR
       =\frac2{h_i}-\frac1R>\frac3{2h_i}.
\tag{P10}
\]
The actual preparation has \(R>1\), \(h_i<1/2\). Thus
\[
 |t_2-p/h_i|\le I_1+h_i^{-1}\le5(I_1-h_i^{-1}),
\]
\[
 \operatorname{Tr}(\tau D_\Omega)
        -h_i^{-1}\operatorname{Tr}(\sigma D_\Omega)
 < -\tfrac12\,10^{22}c\,(I_1-h_i^{-1}) .
\tag{P11}
\]
This proof does not assume a product state or set a cross covariance to zero.

Using the exact raw pressure row W8, the resulting initial pressure derivative exceeds the prescribed-history derivative by a strictly positive amount. Safe bounds in the declared model units are
\[
 \delta\langle p_s\rangle'_u>10^{-6}
 \quad\hbox{for the actual product N4/N6 preparation},
\]
\[
 \delta\langle p_s\rangle'_u>10^{-7}
 \quad\hbox{for every stated regular joint extension with the same two-packet law}.
\tag{P12}
\]
These are \(u\)-derivatives of raw finite-cutoff pressure, not SI units, a metric error, or an experimentally calibrated signal. The domain is finite initial \(Q_3\) comparison energy with the fixed thin marginal: that marginal supplies all higher source moments, so RAW_WARD's cutoff proof supplies the pressure derivative for every such joint extension. No unrestricted trace manipulation or general claim about all normal states is used.

## P5. Scope and continuation

This closes the missing actual-source coefficient in the earlier raw pressure comparison and in the phase-current counterexample. It excludes keeping this source marginal and this two-packet geometry law while restoring the old raw pressure row by entanglement alone. Other geometry laws, altered sources, other clocks, the quantum AE/geometric row, and a complete normal joint continuum solution remain to be examined.
