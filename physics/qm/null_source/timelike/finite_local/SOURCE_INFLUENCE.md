# Exact non-Gaussian source influence on prescribed homogeneous histories

This is the next closed subproblem after the 29-check source/instrument stage. It supplies an exact matter influence factor, with a controlled second-cumulant approximation. It does not supply a probability law for geometry or solve its initial constraints.

## One fixed state and two histories

Use the same canonical zero-mode pair (Q_i,P_i), the same fixed preparation, C=2pi^2 M2, and S0=(P_1^2+P_2^2)/C. On a prescribed FLRW history with lapse N(t)>0 and scale a(t)>0,
\[
 H_0[g](t)={N(t)\over2a(t)^3}(P_1^2+P_2^2).
\]
Take a common finite initial/final interval and fixed canonical Cauchy identifications. The histories agree in the preparation neighborhood; no separate state is chosen on either branch. For a standard closed-time-path construction one can also choose a common final neighborhood. The phase integral is
\[
 I_g=\int_{t_i}^{t_f}{N(t)\over a(t)^3}dt
     =\int{dt_{\rm proper}\over a^3}.
\]
It is invariant under endpoint-preserving time relabeling. For infinite intervals the corresponding phase difference must exist; such limits are not assumed here.

Here phi_0=Y_0 Q, P_i=a^3 N^{-1} dQ_i/dt, and the trace uses one fixed L2(d^2Q) representation. If history-dependent canonical variables such as a*phi are used instead, their endpoint transformations/phases must be included. One cannot trace different representations as if they were a single fixed state.

All these zero Hamiltonians strongly commute. Therefore
\[
 U_0[g]=e^{-i C S_0 I_g/2},\qquad
 {\cal F}_0[g_+,g_-]
 =\operatorname{Tr}\rho_0 U_0[g_-]^\dagger U_0[g_+]
 =E_{\rho_0}e^{-i\nu S_0},
 \quad \nu={C\over2}(I_+-I_-).
\]
The trace identity does not assume that rho_0 is diagonal in momentum. It only uses the spectral law of S0 in the one actual incoming state.

This follows the conventional influence-functional/closed-time-path setup, not a new definition of quantum gravity; see Hu and Verdaguer, *Stochastic Gravity: Theory and Applications*, [arXiv:0802.0658](https://arxiv.org/abs/0802.0658), especially Sec. 4. The explicit source evaluation and bounds below are for the present model.

## Exact evaluation, to all source cumulants

Set r=v/C, L=1+sqrt(3)/4, and alpha=sqrt(3)/4. A fixed displacement radius R with the actual Gaussian width gives
\[
 \chi_R(\nu)={1\over1+2ir\nu}
 \exp\!\left[-{iR\nu\over1+2ir\nu}\right].
\]
Consequently
\[
 {\cal F}_{0,\rm quiet}=\chi_L,\qquad
 {\cal F}_{0,\rm two}
 =\chi_L\cos\!\left({\alpha\nu\over1+2ir\nu}\right).
\]
The general spectral trace identity applies to every normal source state, but the displayed chi_R requires the stated fixed-width Gaussian-displacement preparation. It is not a fidelity or an already measured metric probability. Gamma candidates and the mean-restored D-clock output have different source laws and require their own spectral average; matching first/second field moments or restoring the source mean does not justify reusing chi_R.

These formulas hold for both the uniform-angle comparison and the explicit original-A-matched two-center alternative: the S0 law depends only on displacement radius. The original historical angular pair with identical S0 laws still has identical entire zero-sector influence.

For real nu, the denominator never vanishes and chi_L is nonzero. Positivity of the spectral measure gives
\[
 {\cal F}_0[g,g]=1,\quad
 {\cal F}_0[g_-,g_+]=\overline{{\cal F}_0[g_+,g_-]},\quad
 |{\cal F}_0|\le1.
\]
For any finite list of histories their influence matrix is positive semidefinite, by its Gram representation. This is an exact average over one static source parameter S0, not fresh independent noise at every time. Histories with the same I_g have identical zero-sector evolution. It does not make their high modes or local metric observables identical.

The actual source contribution obeys rho_0=p_0=M2 S0/(2a^6), with the conserved tensor J already defined in INVARIANT_PREPARATION.md. Its separated-point nonlocal stress commutator is zero in this homogeneous sector; local/contact mean responses from the geometry dependence of J are retained. This does not say that the complete field commutator or high-mode response vanishes.

## A controlled Gaussian approximation, not a global ordering

Choose the logarithm continuously from nu=0. The relative log is
\[
 \Delta\log{\cal F}_0
 =-{3\nu^2\over32}+i{3r\nu^3\over8}
   +\left({9r^2\over8}-{3\over1024}\right)\nu^4+O(\nu^5).
\]
Thus with F=exp(i Gamma), the leading relative imaginary action is +3nu^2/32, in agreement with Delta Var S0=3/16. The first mean-response term is unchanged. The nonzero cubic and quartic terms prevent an exact Gaussian replacement.

An explicit error follows without truncating an infinite mode sum. Put w=alpha nu/(1+2irnu). For |nu|<=1, |w|<=alpha<1/2. The Euler product for cos gives negative even coefficients for log cos, so
\[
 |\log\cos w+w^2/2|
 \le-\log\cos|w|-|w|^2/2
 \le{|w|^4\over8(1-|w|^2/2)}
 \le{|w|^4\over7}.
\]
Also
\[
 {|w^2-\alpha^2\nu^2|\over2}
 \le2\alpha^2r|\nu|^3(1+r|\nu|).
\]
Hence
\[
 \left|\Delta\log{\cal F}_0+{3\nu^2\over32}\right|
 \le{3r\over8}|\nu|^3(1+r|\nu|)
       +{9\over1792}|\nu|^4.
\]
On |nu|<=0.1 and the actual fixed parameter boxes this is less than 5.03e-7. The domain is a **history phase difference**, equivalently |I_+-I_-|<=0.2/C for each fixed parameter choice. It is not a metric-norm, stability or experimental-precision bound.

Smaller second source variance does not order the entire influence at all separations. Indeed
\[
 \lim_{|\nu|\to\infty}
 \left|{{\cal F}_{0,\rm two}\over{\cal F}_{0,\rm quiet}}\right|
 =\cosh\!\left({\alpha\over2r}\right)>1.
\]
The relative factor is therefore not itself the characteristic function of an independent positive random source, or an independent CP dephasing channel. Positive ordering of second noise kernels does not imply an all-orders decomposition as quiet source plus independent noise. Each complete influence still has modulus at most one. The reversed relative ordering in this limit may concern extremely small absolute amplitudes; no observable effect size is claimed.

## The actual ideal-short nonselective state: a restricted exact extension

For the original zero/high product input, the ideal short pointer's nonselective out state is
\[
 \rho_{\rm out}=\int d\nu_{\rm ptr}(\xi)
 \big[W_0(\xi)\rho_0W_0^\dagger(\xi)\big]\otimes
 \big[W_h(\xi)\rho_hW_h^\dagger(\xi)\big],
 \quad W_0(\xi)=e^{-i\beta\xi\cdot P}.
\]
This generally is not a product state. However W0 commutes with every bounded f(S0), and Wh does not depend on P. For any bounded high observable B_h,
\[
 \Phi^*[f(S_0)\otimes B_h]
 =f(S_0)\otimes\Phi_h^*(B_h).
\]
The S0/high subalgebra therefore remains statistically independent for this input, even while genuine Q/high correlations remain.

The two future histories start at the same post-readout Cauchy slice t_star; the preparation, short pulse and reader are one common already completed past. Repeating the pulse separately on two different geometry histories would not define the same rho_out. A future pair of homogeneous free histories has relative operator B0(S0) tensor B_h whenever its common high relative evolution is defined. On the same actual nonselective state,
\[
 {\cal F}_{\rm target,out}
 ={\cal F}_{0,\rm prior}\,{\cal F}_{h,\rm out}.
\]
The high out state and high factor are identical for the two compared preparations. Summing every annulus outcome gives this same nonselective channel, without discarding a record. Thus
\[
 {\cal F}_{\rm target,two,out}
 =\cos\!\left({\alpha\nu\over1+2ir\nu}\right)
    {\cal F}_{\rm target,quiet,out}.
\]
The multiplication identity is valid even if the common high factor is zero. Common purely geometric renormalization phases, when defined, cancel in the comparison.

This does not construct the absolute infinite-mode high influence. It does not extend automatically to individual flags, record-dependent geometries, nonhomogeneous histories, or a generic finite kinetic poststate. Conserved P alone is insufficient for that factorization, and the finite-probe second/fourth-moment convergence theorem is not an all-orders influence theorem.

## Remaining physical closure

The source distribution now has an exact history-level influence factor and an explicit small-phase Gaussian error, rather than only a noise covariance. A gravitational action/initial state and a legitimate approximation or probability construction are still needed to turn it into geometry predictions. The full-AE initial-constraint obstruction remains: a nonzero source realization cannot be inserted into frozen initial geometric data merely because its influence factor is known. High modes, apparatus/controller influence, full local Ward identities and calibrated gravitational observables retain their stated responsibilities.
