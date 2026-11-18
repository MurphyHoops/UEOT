## The common multitime source with a persistent bath

### Source, records and quantifiers

The same two-mode environment is retained until each branch actually stops. The system S is a qubit; the initial state $\rho_{SR}$ is arbitrary, and the finite-dimensional reference R is never acted on during the dynamics. Set $\hbar=1$ and $H_S=0$, and fix the source below:

$$
\begin{aligned}
H_\lambda&=I_S\otimes H_E+\lambda Z\otimes B,
&H_E&=n_1+\frac32n_2,\\
B&=(a_1+a_1^\dagger)+\frac35(a_2+a_2^\dagger),
&\lambda&\in[1/5,2/5],\\
\rho_{SRE}(0)&=\rho_{SR}\otimes|00\rangle\langle00|_E,
&(t_1,t_2,t_3)&=(2/3,3/4,1/2).
\end{aligned}
$$

After every joint evolution, apply the complete two-branch instrument $F=\operatorname{diag}(\sqrt{1/8},\sqrt{1/4})$ and $P=\operatorname{diag}(\sqrt{7/8},\sqrt{3/4})$. Failure stops immediately and retains its actual unnormalized SR state. Pass branches receive $R_y(\pi/2)$, $R_x(\pi/3)$ and I, respectively. Every terminal record f,pf,ppf,ppp is retained. Distance is half the sum of the trace norms of the record-block differences; E is discarded only at the stipulated terminal output. Complex Hilbert space, the Born rule, CP operations, oscillator dynamics and vacuum preparation remain independent physical inputs, not structures uniquely derived from Core.

**P-MICRO-08 (A complete persistent Gaussian-bath process on a common domain).** We first construct a legitimate common source and then derive its full multitime response. General finite Gaussian states specify the scope of the analytic formula only. Every executed, calibrated and numerically certified source in this section starts in the frozen vacuum above.

### Field bounds and a common self-adjoint domain

For finitely many positive-frequency modes, define $a(g)=\sum_k g_k^*a_k$ and $b_g^2=\sum_k|g_k|^2/\omega_k$. Cauchy–Schwarz and the CCR give, initially on finite Fock vectors,

$$
\begin{aligned}
\|a(g)\psi\|&\le b_g\|H_E^{1/2}\psi\|,\\
\|a(g)^\dagger\psi\|^2
&=\|a(g)\psi\|^2+\|g\|_2^2\|\psi\|^2,\\
\|(a(g)+a(g)^\dagger)\psi\|
&\le2b_g\|H_E^{1/2}\psi\|+\|g\|_2\|\psi\|.
\end{aligned}
$$

The spectral inequality $\sqrt{x}\le\epsilon x+(4\epsilon)^{-1}$ turns the last line into an arbitrarily small relative $H_E$ bound plus a bounded term. The field therefore has relative bound zero. The system operator is bounded, so Kato–Rellich gives a self-adjoint realization on $\mathbb C^2\otimes D(H_E)$. A compact finite-coupling set and a positive frequency lower bound make these estimates uniform. Here completing the square also constructs the unitary explicitly. With $\omega=(1,3/2)$ and $c=(1,3/5)$, the $Z$-sector $z=\pm1$ satisfies

$$
\begin{aligned}
U_z(t)&=e^{i\phi(t)}D(z\alpha(t))e^{-itH_E},\\
\alpha_k(t)&=\frac{\lambda c_k}{\omega_k}(e^{-i\omega_kt}-1),\\
\phi(t)&=\sum_k\left(\frac{\lambda c_k}{\omega_k}\right)^2
[\omega_kt-\sin(\omega_kt)],\\
D(\zeta)&=\exp\!\left[\sum_k(\zeta_ka_k^\dagger-\zeta_k^*a_k)\right].
\end{aligned}
$$

The identity $a_kD(\zeta)=D(\zeta)(a_k+\zeta_k)$ shows that finite displacement preserves $D(H_E)$; the additional field terms are controlled by the preceding bound. This explicit unitary agrees with the self-adjoint source, rather than defining dynamics through an unproved formal series.

### Energy with complete stopping records

Dilate the instruments into a finite record register. After a branch stops, let its bath evolve freely until the common horizon $T=23/12$. This padding changes neither its terminal record nor its SR output. System and record operations preserve total number $N=n_1+n_2$, and the live-branch coupling operator has norm at most one. Put $\gamma=\|c\|_2=\sqrt{34/25}$. Vacuum evolves into finitely many displacement histories with the required number moments. Differentiation on this actual domain and Cauchy–Schwarz give

$$
\left|\frac{d}{dt}\langle N\rangle\right|
\le2|\lambda|\gamma\sqrt{\langle N\rangle},
\qquad
\sqrt{\langle N(t)\rangle}\le|\lambda|\gamma t.
$$

The zero initial value is handled by first regularizing with $\sqrt{\langle N\rangle+\epsilon}$ and then taking $\epsilon$ to zero. This is a complete-record, unconditioned energy bound. Dividing a branch by a small acceptance probability does not preserve it without a cost. For a separately declared finite-energy Gaussian preparation, the right-hand side becomes $\sqrt{\langle N(0)\rangle}+|\lambda|\gamma t$; this does not extend the present truncation or numerical certificate to nonvacuum input.

### Complete history pairs for a correlated Gaussian preparation

For a system eigenvalue history $s=(z_1,\ldots,z_n)$, let $R_j=\operatorname{diag}(e^{-i\omega_kt_j})$. Starting at $\beta_0=0,\theta_0=0$, recurse

$$
\begin{aligned}
\beta_j&=R_j\beta_{j-1}+z_j\alpha(t_j),\\
\theta_j&=\theta_{j-1}+\phi(t_j)
+\operatorname{Im}\langle R_j\beta_{j-1},z_j\alpha(t_j)\rangle,\\
W_s&=U_{z_n}(t_n)\cdots U_{z_1}(t_1)
=e^{i\theta_s}D(\beta_s)e^{-iH_ET_n}.
\end{aligned}
$$

The second line retains the exchange phase from Weyl multiplication. After noncommuting intermediate operations, this phase generally cannot be discarded.

Use quadratures $r=(q_1,p_1,q_2,p_2)$, with $q_k=(a_k+a_k^\dagger)/\sqrt2$, $p_k=(a_k-a_k^\dagger)/(i\sqrt2)$ and $\Omega=\bigoplus_{k=1}^2\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Let d be the mean and V the symmetric covariance, with $V+i\Omega/2\succeq0$. V is the full matrix and may contain intermode correlations. The Gaussian characteristic function and history-pair factor are

$$
\begin{aligned}
\xi(\zeta)&=\sqrt2(\operatorname{Im}\zeta_1,-\operatorname{Re}\zeta_1,
\operatorname{Im}\zeta_2,-\operatorname{Re}\zeta_2)^T,\\
\chi_\sigma(\zeta)&=\operatorname{Tr}[\sigma D(\zeta)]
=e^{i\xi(\zeta)^Td-\frac12\xi(\zeta)^TV\xi(\zeta)},\\
F_{s,r}&=\operatorname{Tr}(W_s\sigma_EW_r^\dagger)\\
&=e^{i[\theta_s-\theta_r+\operatorname{Im}\langle\beta_r,\beta_s\rangle]}
\chi_\sigma\!\left(e^{i\omega T_n}(\beta_s-\beta_r)\right).
\end{aligned}
$$

This follows from cyclicity of the trace, the Weyl phase in $D(-\beta_r)D(\beta_s)$, and free rotation. No product decomposition of a correlated initial bath is made, and no conditional bath is assumed Gaussian.

For terminal record h, let $M_{h,j}$ denote the actual failure operator or rotated pass operator, and define $A_{h,s}=M_{h,n}\Pi_{z_n}\cdots M_{h,1}\Pi_{z_1}$. The full output is

$$
\rho_h^{SR}=\sum_{s,r}F_{s,r}
(A_{h,s}\otimes I_R)\rho_{SR}(A_{h,r}^\dagger\otimes I_R).
$$

This is the expansion of the actual joint operator $\sum_sA_{h,s}\otimes W_s$ followed by a partial trace, so it is CP; $(F_{s,r})$ is also a positive Gram matrix. Summing outcomes successively and using $F^\dagger F+P^\dagger P=I$ proves unit total trace and causal prefix constraints. The reference is retained throughout. Iterating $(3/4)I\preceq P^\dagger P\preceq(7/8)I$ bounds surviving mass and yields $27/64\le\Pr(ppp)\le343/512$. This neither makes the accepted effect scalar nor makes normalized postselection linear.

Even vacuum does not support a single-Gaussian conditional closure. After the first pass with Bell input, the bath marginal mixes opposite coherent states with weights 7/13 and 6/13. With $\mu=\sqrt2|\alpha_1(t_1)|$, its displacement-aligned fourth cumulant is $\mu^4(-2+8/169-6/28561)$, strictly nonzero for nonzero displacement. Gaussian preparation and fully Gaussian conditional dynamics are therefore different assumptions.

## Genuine finite propagation error and parameter stability

### Finite Duhamel expansion and the all-input lift

**P-MICRO-09 (An all-input finite approximation of the same persistent source).** Let $P_K$ project onto occupation at most K in each mode, let $J_K$ be its inclusion, and use the actual compression $H_{\lambda,K}=J_K^\dagger H_\lambda J_K$. Free bath evolution and every dilated record operation preserve total number. In the interaction picture including these operations, write the field as $\widetilde V(s)$. On total number at most $k-1$, its norm is bounded by $\gamma(\sqrt{k-1}+\sqrt{k})$.

The essential Duhamel orientation keeps true propagation on the left:

$$
W(T,0)=I-i\lambda\int_0^T W(T,s)\widetilde V(s)\,ds.
$$

Expand the left suffix only finitely many times. In the order-j remainder, the true unitary remains to the left of every field factor, while the right-hand input has finite support originating in vacuum. Each field increases total number by at most one. Thus every term through order K stays inside $N\le K$, itself contained in the rectangular carrier $P_K$; the first K terms of the infinite and finite sources agree exactly. Projections in the finite remainder cannot increase norms. With $\lambda_{\max}=2/5$, the ordered time-simplex volume bounds the two order-$K+1$ remainders separately:

$$
\begin{aligned}
x&=\lambda_{\max}\gamma T,
&c_j&=\frac{x^j}{j!}\prod_{k=1}^j(\sqrt{k-1}+\sqrt{k}),\\
\|(W-J_KW_KJ_K^\dagger)\psi_{\rm vac}\|
&\le c_{K+1}+c_{K+1},
&d_K&=\min\{1,2c_{K+1}\}.
\end{aligned}
$$

No convergence of an infinite Dyson series is assumed, and no uncontrolled infinitely evolved state is placed to the right of a field operator. Purify an arbitrary input and retain every instrument record in the dilation. The operator estimate is unchanged by tensoring the identity on any reference. Pure-state trace distance is at most the corresponding vector distance; discarding E and unused dilation registers then gives

$$
\sup_{\rho_{SR},\,\dim R<\infty}
\frac12\sum_h\left\|
(\Phi_{\lambda,h}\otimes\operatorname{id}_R)(\rho_{SR})-
(\Phi_{\lambda,K,h}\otimes\operatorname{id}_R)(\rho_{SR})
\right\|_1\le d_K,
\qquad d_{20}<0.00001344.
$$

This is an analytic statement for arbitrary SR input, not an extrapolation from numerical Bell-input agreement. The same bound applies when the first two durations are interchanged, with the same total exposure and legal system operations.

### Boundary residuals on actual finite prefixes

A small initial tail does not establish accurate propagation by a compressed generator. Here only creation operators cross the rectangular boundary. The two outgoing faces are orthogonal, hence

$$
\begin{aligned}
\mathcal R_K&=H_\lambda J_K-J_KH_{\lambda,K},\\
\mathcal R_K^\dagger\mathcal R_K
&=\lambda^2(K+1)I_S\otimes
\left[\Pi_{n_1=K}+\frac9{25}\Pi_{n_2=K}\right].
\end{aligned}
$$

Let $\sigma_h$ be the actual unnormalized live prefix of the same finite model, with mass $m_h$, and let $\sigma_h(s)$ be its local finite evolution. After purifying a subnormalized state, the Duhamel vector-defect integral must be multiplied by its norm $\sqrt{m_h}$ to bound trace distance. Contractivity of the true complete suffix and telescoping over the tree give

$$
r_h(s)=\operatorname{Tr}\!\left[
(\mathcal R_K^\dagger\mathcal R_K\otimes I_R)\sigma_h(s)\right],
\qquad
D_{\rm full}\le\sum_{h\,\mathrm{live}}\int_0^{t_h}\sqrt{m_h r_h(s)}\,ds.
$$

The occupations and masses must belong to the actual finite prefixes, not be replaced by infinite-source occupations. This formula can sharpen the result, but ordinary numerical quadrature is not called an interval certificate here. The uniform certificate actually used is $d_K$ above.

The frozen vacuum has zero initial tail; no mode is deleted and no Trotter split is used. Changing the preparation requires separate initial-tail and propagation costs; correlated modes cannot be replaced by a freshly prepared product vacuum. Mode deletion should switch off its coupling on the same Hilbert space and bound the coupling difference on the actual retained initial state and finite domain. Device preparation, control, leakage, effective-model and readout errors still require independent evidence.

### Parameter stability is first proved in the infinite source

For $\lambda,\widehat\lambda\in[1/5,2/5]$, compare the same controller and stopping rules. The parameter Duhamel formula inserts $(\lambda-\widehat\lambda)Z\otimes B$ with a true infinite-source prefix on its right. Its energy estimate must therefore come from the infinite source, rather than an assumed invariant of the finite compression. For a normalized purified prefix,

$$
\begin{aligned}
\|B\psi(t)\|&\le\gamma\left(\sqrt{\langle N\rangle}
+\sqrt{\langle N\rangle+1}\right)
\le\gamma(1+2\lambda_{\max}\gamma t),\\
D_{\rm full}(\Phi_\lambda,\Phi_{\widehat\lambda})
&\le|\lambda-\widehat\lambda|
\int_0^T\gamma(1+2\lambda_{\max}\gamma t)\,dt\\
&=|\lambda-\widehat\lambda|
[\gamma T+\lambda_{\max}\gamma^2T^2]
<\frac{51}{10}|\lambda-\widehat\lambda|.
\end{aligned}
$$

The bracket is approximately $4.2336426708$. The rational estimate $\gamma<7/6$ bounds it by $38111/9000<51/10$. We retain the previously frozen $51/10$. Parameter stability is established first; finite truncation and numerical-representation errors are added afterwards. It does not authorize silent changes of frequencies, relative couplings, preparation or control permissions.

## Memory controls and physical numerical representation

### A strict memory witness for the fixed three-slot source

**C-QMEM-01 (Equal single-slot channels do not determine a multitime process).** Repreparing vacuum after every slot defines a different process. Its isolated single-slot channel equals the true source for every input and reference, because that slot still starts from the same vacuum and undergoes the same evolution. Yet for the same three-slot Bell input at $\lambda=3/10$, the event “record ppp and $X_S\otimes X_R=+1$” has the strict interval witness

$$
p_{\rm reset}-p_{\rm persistent}
>0.03164037538529123569>\frac3{100},
\qquad
D_{\rm full}(\Phi_{\rm reset},\Phi_{\rm persistent})>\frac3{100}.
$$

This uses 80-digit interval history pairs and an independently propagated sequence of reset Schur channels, with exact dyadic endpoints retained. An event gap bounds trace distance directly; interval diagonalization of a trace norm is unnecessary, and no different causal-break protocol is substituted. The complete distance approximately $0.1012518562$ remains a floating diagnostic. Omitting the exchange phase causes approximately $0.0502254699$ error. Vacuum has exactly zero initial tail above K=0, but its propagation error at $\lambda=0.4$ is approximately $0.2389578616$. These controls identify the consequences of separate omissions; they do not replace the strong standard baseline.

### Why interval Choi bounds control arbitrary reference inputs

**P-NUM-01 (From interval Choi bounds to a physical terminal instrument).** With normalized Bell vector $|\Omega_2\rangle=(|00\rangle+|11\rangle)/\sqrt2$, define the four normalized Choi blocks in output-S followed by input-reference order:

$$
J_h=(\Phi_h\otimes\operatorname{id}_2)
(|\Omega_2\rangle\langle\Omega_2|),
\qquad
J_h\succeq0,
\qquad \sum_h\operatorname{Tr}_{\rm out}J_h=I_2/2.
$$

For generator parameter 3/10 and calibration-only nominal parameter 0.299314119192, independent 80-digit interval formulas enclose every entry for both timing orders. Each timing separately certifies the actually stored binary64 matrices from the Weyl and K20 Galerkin implementations, giving eight certificates. Convert the stored matrices to exact rationals and Hermitianize them, calling them $Q_h$. Entrywise intervals bound Frobenius error, and each block has dimension four, so

$$
\begin{aligned}
e&:=\sum_h\|Q_h-J_h\|_1
\le2\sum_h\|Q_h-J_h\|_F<10^{-12},\\
\frac12\|\mathcal Q-\Phi\|_\diamond
&\le\frac{d_{\rm in}}2\sum_h\|Q_h-J_h\|_1=e,
\qquad d_{\rm in}=2.
\end{aligned}
$$

The second line follows directly by vectorization. Any unit rank-one input $|u\rangle\langle v|$ with an arbitrary reference can be written as $(I\otimes A)|\Omega_2\rangle\langle\Omega_2|(I\otimes B^\dagger)$, with $\|A\|,\|B\|\le\sqrt2$. Left and right multiplication therefore increase each block trace norm by at most two. A singular-value decomposition extends the bound to any trace-class input, proving the diamond inequality. This certifies the stored linear map for every reference input; it does not extrapolate one floating Bell-input agreement.

The intervals compare the exact infinite source directly with the actual stored matrices. For the Galerkin backend, this fixed-nominal-parameter difference already contains truncation and floating matrix-exponential errors; it is not merely a rounding estimate. In contrast, $d_{20}$ is an independent analytic bound uniform over the entire frozen parameter interval.

### Exact CP/TP repair and its term-by-term cost

The raw $Q_h$ need not be positive or trace preserving. Choose rational $\delta=10^{-10}$ and $a=(1+20\delta)^{-1}$, and define

$$
\widetilde Q_h=Q_h+\delta I_4,
\qquad
R=I_2/2-a\sum_h\operatorname{Tr}_{\rm out}\widetilde Q_h.
$$

Each block has operator error at most $e<\delta$, hence $\widetilde Q_h\succeq0$. Trace-norm contractivity of partial trace on Hermitian inputs bounds the aggregate marginal error by $e<2\delta$. The four added $\delta I_4$ blocks contribute $8\delta I_2$ after partial trace. Therefore

$$
a\sum_h\operatorname{Tr}_{\rm out}\widetilde Q_h
\preceq a(1/2+10\delta)I_2=I_2/2,
\qquad R\succeq0.
$$

Set $J_h^{\rm rep}=a\widetilde Q_h$ for every block, then add $|0\rangle\langle0|_{\rm out}\otimes R$ only to the existing f block. Every block is positive and the total output marginal is exactly $I_2/2$, defining a CP/TP terminal instrument. Matrices, a, delta and R are all stored as exact Fractions. Trace preservation and Hermiticity are verified entrywise with rational arithmetic. Separate review additionally checked all 504 principal minors of the eight certificates' blocks and residuals exactly.

To expose the repair cost, let $\Delta_h=Q_h-J_h$ and $s=\sum_h\operatorname{Tr}\Delta_h$, so $|s|\le e$. Since $R\succeq0$ and $\sum_h\operatorname{Tr}J_h=1$, term-by-term triangle bounds give

$$
\begin{aligned}
\sum_h\|J_h^{\rm rep}-J_h\|_1
&\le ae+(1-a)+16a\delta+\operatorname{Tr}R,\\
\operatorname{Tr}R&=1-a(1+s+16\delta),\\
\sum_h\|J_h^{\rm rep}-J_h\|_1
&\le ae+2(1-a)-as\\
&\le2ae+40a\delta
=a(40\delta+2e)<10^{-8},\\
\frac12\|\Phi^{\rm rep}-\Phi\|_\diamond&<10^{-8}.
\end{aligned}
$$

The term $16a\delta$ comes from four four-dimensional blocks; $2(1-a)=40a\delta$ comes from normalization scaling. No input-dimension factor is missing. This is explicitly paid physicalization, rather than treating raw “nearly CP” matrices as CP.

The repaired object is a terminal prediction instrument for one fixed policy. It is not claimed implementable at each original early stopping time, nor to repair a complete process tensor for all counterfactual interventions. Its changed failure block is included in the error bound. A later floating contraction for arbitrary input requires its own rounding budget; the fixed Bell-input Pauli readout here can instead be evaluated exactly from the rational matrices.

The frozen calibration certificate retains the conservative budget

$$
\varepsilon_{\rm CQ}
=\frac{51}{10}r_\lambda+d_{20}+\varepsilon_{\rm phys},
\qquad
\varepsilon_{\rm tester}
=\varepsilon_{\rm CQ}+\frac12r_\eta,
\qquad \varepsilon_{\rm phys}=10^{-8}.
$$

At the current nominal parameter the interval certificate already directly bounds the infinite-source-to-repaired-predictor difference. Paying $d_{20}$ again is a conservative reserve, not a second independent discovery of the same error. The term $r_\eta/2$ applies only to the declared complete binary terminal detector model, not to arbitrary device SPAM.

Standard persistent joint evolution and the same Gaussian influence functional predict the same physics. This section connects explicit premises, complete records, actual finite propagation and auditable numerical representation, without claiming additional empirical advantage over standard quantum theory. Infinite modes, local field theory, energy exchange and thermalization retain separate UV/IR, representation, causal-composition and limit obligations.
