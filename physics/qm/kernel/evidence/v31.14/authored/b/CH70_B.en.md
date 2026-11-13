## The common multitime source with a persistent bath

The same two-mode environment is retained through all live slots. The system is a qubit S, while the finite-dimensional reference R is never acted on. With hbar=1 and H_S=0, let

$$
H_\lambda=n_1+\frac32n_2+
\lambda Z\otimes\left[(a_1+a_1^\dagger)+\frac35(a_2+a_2^\dagger)\right],
\qquad\lambda\in[1/5,2/5],
$$

acting on rho_SR tensor |00><00|_E. Slot durations are (2/3,3/4,1/2). Each joint evolution is followed by F=diag(sqrt(1/8),sqrt(1/4)) or P=diag(sqrt(7/8),sqrt(3/4)). A failure stops and retains its actual unnormalized SR state. Pass branches receive Ry(pi/2), Rx(pi/3), and I, respectively. All records f,pf,ppf,ppp remain in the output. The noncommuting intermediate rotations prevent this process from being identified by its isolated single-slot decoherence curve. Complex Hilbert space, the Born rule, CP operations, Fock dynamics and vacuum preparation remain independent physical inputs.

**P-MICRO-08 (A complete persistent Gaussian-bath process on a common domain).** For finitely many positive-frequency modes, the linear field has relative bound zero with respect to the free bath Hamiltonian. The frozen compact parameter set therefore has a common self-adjoint domain. In the Z-sector z=+/-1 the present source is explicitly

$$
U_z(t)=e^{i\phi(t)}D(z\alpha(t))e^{-itH_E},\quad
\alpha_k(t)=\frac{\lambda c_k}{\omega_k}(e^{-i\omega_kt}-1),
$$

$$
\phi(t)=\sum_k\left(\frac{\lambda c_k}{\omega_k}\right)^2
[\omega_kt-\sin(\omega_kt)].
$$

For a system eigenvalue history s, write W_s=exp(i theta_s)D(beta_s)exp(-iH_E T_s). Composition requires both displacement and Weyl exchange phase:

$$
\beta_j=R_j\beta_{j-1}+z_j\alpha(t_j),\qquad
\theta_j=\theta_{j-1}+\phi(t_j)+
\operatorname{Im}\langle R_j\beta_{j-1},z_j\alpha(t_j)\rangle.
$$

If A_(h,s) is the system history operator built from the actual instrument, rotations and spectral projectors, then

$$
\rho_h^{SR}=\sum_{s,r}\operatorname{Tr}(W_s\sigma_EW_r^\dagger)
(A_{h,s}\otimes I_R)\rho_{SR}(A_{h,r}^\dagger\otimes I_R).
$$

For a general finite Gaussian initial state, its full mean and covariance determine the pair factor through its characteristic function. Mode correlations and exchange phases are retained. Only the initial bath is assumed Gaussian; a conditional bath is not projected back onto one Gaussian. The actual joint-unitary construction establishes positivity, while successive uses of F†F+P†P=I establish complete probabilities and causal prefix constraints.

The executed and calibrated certificate uses the frozen vacuum only. Even here, after the first pass with Bell input the bath marginal is a mixture of opposite coherent states with weights 7/13 and 6/13. Its displacement-aligned fourth cumulant is nonzero, disproving closure by a single conditional Gaussian. The accepted effect is also nonscalar. Operator inequalities establish only the uniform bounds

$$
27/64\le\Pr(ppp)\le343/512.
$$

## Genuine finite propagation error and parameter stability

**P-MICRO-09 (An all-input finite approximation of the same persistent source).** Let P_K project onto occupancy at most K in each mode, and use the actual Galerkin generator H_(lambda,K)=P_K H_lambda P_K. Put gamma=sqrt(34/25), T=23/12 and x=(2/5)gamma T. For every rho_SR, finite reference and complete terminal record,

$$
D_{\rm full}(\Phi_\lambda,\Phi_{\lambda,K})
\le\min\left\{1,
\frac{2x^{K+1}}{(K+1)!}
\prod_{k=1}^{K+1}(\sqrt{k-1}+\sqrt{k})\right\}.
$$

The proof uses a finite Duhamel expansion. Free bath evolution and system operations preserve total number. Starting from vacuum, the first K interaction orders lie in the finite carrier, so the two expansions agree term by term. The remainder keeps true propagation as a unitary suffix on the left; each coupling on its right acts only on controlled finite support. No convergence of an infinite Dyson series is assumed, and a small initial tail does not replace propagation error. Interval arithmetic gives the uniform K=20 bound 0.00001344.

The boundary defect also has the explicit form

$$
(HJ-JH_K)^\dagger(HJ-JH_K)
=\lambda^2(K+1)I_S\otimes
\left[\Pi_{n_1=K}+\frac9{25}\Pi_{n_2=K}\right].
$$

Integrating this residual against actual finite-model prefix masses and top-level occupancies can sharpen the bound. Unverified numerical quadrature is not a rigorous certificate. Initial-state truncation, mode deletion, time discretization and effective-model error remain separate terms. The frozen vacuum has zero initial tail, no mode is deleted, and no Trotter split is used; these terms vanish only within the stipulated mathematical source.

Parameter stability is first proved in the infinite source. Complete-record energy obeys sqrt(<N(t)>) <=(2/5)gamma t. Consequently the same controller satisfies

$$
D_{\rm full}(\Phi_\lambda,\Phi_{\widehat\lambda})
\le\left[\gamma T+\frac25\gamma^2T^2\right]
|\lambda-\widehat\lambda|
<\frac{51}{10}|\lambda-\widehat\lambda|.
$$

The previously frozen 51/10 constant is retained. Interchanging the first two durations preserves T and therefore preserves both constants. It does not authorize an unannounced change of vacuum, frequencies, relative couplings or instrument implementation.

## Memory controls and physical numerical representation

**C-QMEM-01 (Equal single-slot channels do not determine a multitime process).** The true source and a bath-reset replacement have exactly identical isolated first-slot channels for every input and reference. For the same complete three-slot Bell output at lambda=0.3, 80-digit interval evaluation proves that the event `ppp and X_S tensor X_R=+1` has probability gap greater than 0.03164037538529123569, hence strictly D_full>3/100. The full trace-distance value approximately 0.1012518562 is separately labeled a floating diagnostic. Omitting the Weyl exchange phase causes a difference of approximately 0.0502254699. A separate control has exactly zero initial vacuum tail above K=0, yet its propagation error at lambda=0.4 is approximately 0.2389578616. These controls address memory replacement, phase omission and invalid tail reasoning; they do not replace the strong standard baseline.

**P-NUM-01 (From interval Choi bounds to a physical terminal instrument).** For the generator parameter 3/10 and the calibration-only nominal value 0.299314119192, all four normalized Choi blocks are enclosed by 80-digit interval history-pair evaluation, for both the original and permuted timings. The stored binary64 representations of both the Weyl implementation and the independent K20 Galerkin implementation obtain an all-input half-diamond error below 10^-12. The argument uses entrywise interval enclosures and the d_in=2 Choi norm inequality; one floating Bell-input agreement is not promoted into an all-input theorem.

Raw rounded matrices need not be exactly CP or TP. Add delta I4 to every block, with delta=10^-10, and multiply by a=(1+20delta)^-1. Let R=I2/2-a sum_h Tr_out(J_h^raw+delta I4), and add |0><0| tensor R to the existing f block. Every entry is stored as an exact rational. Positivity follows from the certified perturbation bound, while trace preservation is checked by exact rational arithmetic. The physicalization cost is explicitly bounded:

$$
\frac12\|\Phi^{repair}-\Phi\|_\diamond
\le a(40\delta+2\times10^{-12})<10^{-8}.
$$

This is a terminal prediction instrument for a fixed policy. It does not repair a full process tensor under every counterfactual intervention, and it does not identify the modified failure block with the unchanged microscopic F event. Any subsequent floating matrix contraction needs a further rounding budget; the supplied rational Bell-input Pauli readout can instead be evaluated exactly.

Standard persistent joint evolution and the same Gaussian influence functional predict the same physics. This section supplies a reproducible connection between source, approximation and representation, without claiming additional predictive advantage over standard quantum theory. Infinite modes, local field theory, energy exchange and thermalization retain their own domain, UV/IR, causality and limiting responsibilities.
