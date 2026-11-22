# JC14 — Full source phase, normal CTP kernel and actual mean-force limit

## The result being proved

For the fixed ESU dipole-source family \(h=b\epsilon+b'\zeta\), \(\|u\|=\|(\epsilon,\zeta)\|\le10^{-4}\), the same finite-mode Hamiltonians with the declared scalar counterterm converge to actual phased unitaries and their adjoints. This supplies a normal same-input CTP kernel, including its phase. The AP-vacuum kernel is real analytic in this finite set of source parameters. We also prove uniform convergence of the renormalized mean source force and its integrated power. Arbitrary metric dependence and an autonomous four-dimensional actuator are outside this theorem.

The weighted endpoint Bogoliubov estimate in LOCAL_PREPARATION established covariance convergence but explicitly did not fix the scalar phase. This proof addresses that gap. It uses no predecessor scientific module, no numerical mode ODE, and no assumption that a stationary quadratic-Hamiltonian theorem proves a time-dependent phase limit. General quadratic Hamiltonian conventions can be compared with Dereziński, J. Math. Phys. 58, 121101 (2017), https://doi.org/10.1063/1.5017931 .

## 1. Finite-cutoff Gaussian equations with the actual phase

Work in the AP plus-field one-particle space; the spectator minus field is unchanged. Let D=sqrt(-Delta+1+mu), mu=1/5, and
\[
 B_h=\tfrac12D^{-1/2}(h\cdot Z)D^{-1/2},\qquad {\cal L}z=Dz+zD .
\]
With the common projection P_K on every factor,
\[
 H_K=d\Gamma(D+B_h)+\tfrac12(a^\dagger B_h a^\dagger+aB_ha)+C_K[h],
 \qquad C_K={{\cal H}_K|h|^2\over64}.
\]
Trace B_h,K=0 exactly on this dipole column. The evolved vacuum has the actual normalized form
\[
 \psi_K=c_K\exp(\tfrac12a^\dagger z_K a^\dagger)\Omega,\quad
 i\dot z_K={\cal L}z_K+B_h+B_hz_K+z_KB_h+z_KB_hz_K,
\]
\[
 i{\dot c_K\over c_K}=C_K+\tfrac12\operatorname{Tr}(B_hz_K).
\]
Initial z=0 and c=1 fix the phase. All products and traces in these equations are ordinary finite-mode ones at this stage.

## 2. A uniform Riccati contraction in a graph of the commutator

Use
\[
 X=\{z:\|z\|_X=\|z\|_{\rm HS}+\|[D,z]\|_{\rm HS}<\infty\}.
\]
The free group e^{-it L} is isometric in this norm. The neighboring-shell matrix elements of Z give, uniformly in K,
\[
 \|{\cal L}^{-1}B_h\|_{\rm HS}<|h|/5,\quad
 \|{\cal L}^{-1}B_h\|_X<2|h|/5,
\]
\[
 \|B_h\|\le |h|/2,\quad \|[D,B_h]\|\le |h|,\quad
 \|DB_h\|\le1.5|h|,\quad \|B_hD^{-1}\|_{\rm HS}\le2|h|.
\]
For example, the square of the first norm is the convergent sum of twice the neighboring-shell B matrix squares divided by Omega_k^2; it is bounded by |h|^2/25. The commutator multiplies each edge by omega_{k+1}-omega_k<1. The weighted operator bound follows by writing D^(1/2) Z D^(-1/2) on the two neighboring shells. These are operator and Hilbert--Schmidt estimates, not traces of an unbounded identity.

The linear solution can be integrated once by parts:
\[
 z_1=-i\int_{-\infty}^t e^{-i{\cal L}(t-s)}B_h(s)\,ds
 =-{\cal L}^{-1}B_h(t)+
 \int_{-\infty}^t e^{-i{\cal L}(t-s)}{\cal L}^{-1}\dot B_h(s)\,ds .
\]
The bump derivative bounds in QUANTIFIED_PREPARATION give
\(\int|h|\le29\|u\|\), \(\int|\dot h|\le812\|u\|\), and
\(\sup_t\|z_1\|_X\le650\|u\|\).
In the ball R=1300||u||<=.13 the nonlinear Volterra map has Lipschitz constant at most
\[
 44\|u\|(2+2600\|u\|)<.01.
\]
Its nonlinear part is bounded by \(44\|u\|(2R+R^2)\), so it maps the ball to itself. The solution is unique there and analytic in the eight real control parameters (and in their sufficiently small complex neighborhood).

The same estimates control the actual cutoff difference. B_K and [D,B_K] converge in operator norm because their two-shell band coefficients tend to zero. DB_K converges strongly with its adjoint; it is not asserted to converge in operator norm. The linear terms converge uniformly in X by the square-summable edge tails and dominated time integrals. Contraction then gives z_K to z uniformly in time in X.

## 3. The nonlinear phase remainder is trace class

Write r_z=z-z_1 and F=Bz+zB+zBz. It would be incorrect to assume Dz is Hilbert--Schmidt while the source is active. Instead,
\[
 DzB=zDB+[D,z]B
\]
shows that DF is Hilbert--Schmidt using only the X bound and bounded DB. For R<=.13 one obtains
\[
 \|DF(t)\|_{\rm HS}<4|h(t)|R,\quad
 \sup_t\|Dr_z(t)\|_{\rm HS}\le160000\|u\|^2 .
\]
Apply this identity first at finite cutoff. Strong/adjoint-strong DB_K convergence times a convergent Hilbert--Schmidt operator suffices for the limit; operator-norm convergence of DB_K is unnecessary. The Duhamel formula therefore proves actual uniform Dr_z,K convergence in Hilbert--Schmidt norm.

Now
\[
 B_hr_z=(B_hD^{-1})(Dr_z)
\]
is trace class and converges in trace norm uniformly under the time integral. In particular,
\[
 \left|\tfrac12\int\operatorname{Tr}(B_hr_z)\,dt\right|
 \le5\,10^6\|u\|^3.
\]
The divergent part of log c_K is entirely its quadratic part. SOURCE_HESSIAN proves that part converges with the same C_K. Thus
\[
 \log c[h]=\lim_K\log c_K[h]\big|_2
                   -{i\over2}\int\operatorname{Tr}(B_hr_z)\,dt
\]
exists with its actual, continuous phase. No arbitrary implementer phase is chosen after the limit.

Since ||z||<=.13<1, Hilbert--Schmidt convergence of z gives convergence of the Gaussian exponential and its norm; the convergent exponential log c supplies its nonzero scalar amplitude. Hence U_K Omega converges as a vector with the intended phase.

## 4. From a vacuum vector to full unitaries and CTP

The bounded classical symplectic perturbation has the strong cutoff limit already established in LOCAL_PREPARATION. Weyl intertwining therefore gives convergence of U_K on the dense span of coherent vectors, using the phased vacuum convergence above. Uniform unitarity extends it strongly to the whole Fock space. Reversing the time interval yields strong convergence of U_K dagger as well; the limits are mutual inverses. This is a unitary, not merely an isometry.

For every fixed normal density rho_in,
\[
 R_{\rm pre}[h_+,h_-]=U[h_+]\rho_{\rm in}U[h_-]^\dagger,\quad
 Z[h_+,h_-]=\operatorname{Tr}R_{\rm pre}
\]
is the trace-norm limit of the same finite-cutoff mixed initial block. The kernel satisfies Z[h,h]=1, branch conjugation, and positive Gram matrices. For the AP vacuum the contraction and trace estimates are locally uniform and analytic, so differentiating in the finite eight-control neighborhood is justified; the Hessian is SOURCE_HESSIAN.

An equivalent exact vacuum expression is
\[
 Z[h_+,h_-]=\overline{c[h_-]}\,c[h_+]\,
 \det(1-z[h_-]^\dagger z[h_+])^{-1/2}.
\]
The product inside the Fredholm determinant is trace class with operator norm
at most .13 squared. The square-root branch is continued from one at zero
controls. Actual Hilbert--Schmidt convergence gives determinant convergence.
Thus full-amplitude positivity follows from actual output-vector Gram
matrices, not only from the quadratic noise form.

This is norm-analyticity of the prepared vacuum vector and its finite
control derivatives. No operator-norm continuity or analyticity of the
whole unitary family is asserted; its number generator is unbounded.
For an arbitrary fixed normal input only continuity and the actual trace
limit follow automatically.

The operator result also allows composition with the earlier actual AQ preparation and its normal density. It transports the existence and positivity of that CTP kernel only. The AP vacuum spectral W_k, eight-control Jacobian, stationary Einstein datum and numerical budgets do not transfer to the AQ input. Analytic dependence for an arbitrary density is not claimed without the needed moments.

## 5. Actual renormalized mean force and power

For the normalized Gaussian write
\[
 \gamma=zz^\dagger(1-zz^\dagger)^{-1},\qquad
 \kappa=(1-zz^\dagger)^{-1}z=z+\gamma z.
\]
For a basis dipole a, the finite-mode mean of its quadratic source force is
\[
 \langle O_{a,K}\rangle
 =\operatorname{Tr}(B_a\gamma_K)
                +\operatorname{Re}\operatorname{Tr}(B_a\kappa_K).
\]
This formula fixes the convention for z and the anomalous covariance. The number term and the gamma z term converge in trace norm. For the r_z part, use the two Hilbert--Schmidt factors B_a D^-1 and Dr_z. The remaining linear term is exactly
\[
 \operatorname{Re}\operatorname{Tr}(B_a z_{1,K})
                  =-2\sum_{k<K}W_k I_{h_a}(\Omega_k,t).
\]
Adding the actual scalar derivative \({\cal H}_K h_a/32\) gives minus T_K h_a. Its uniform cutoff tail was proved explicitly in SOURCE_HESSIAN. Therefore the complete renormalized mean force
\[
 F_{a,K}=\langle O_{a,K}\rangle+{{\cal H}_K\over32}h_a
\]
converges uniformly on the compact time interval, including its nonlinear parts. Dominated convergence now legitimately gives
\[
 \lim_K\int\dot h\cdot F_K\,dt
    =\int\dot h\cdot F\,dt=E_{\rm excitation,final}\ge0.
\]
The last equality follows first from the exact finite-mode work identity and then the already proved final energy-graph limit. We have not inferred instantaneous power convergence merely from a finite final work value.

This mean limit does not define a sharp force variance. The local scalar subtraction affects the mean but not the divergent pair norm.

## 6. Active domains: a necessary limitation

If h(t) is nonzero, a second integration by parts in z_1 and the preceding Dr_z bound give
\[
 z(t)=-{\cal L}^{-1}B_h(t)+R(t),\qquad DR(t)\ {\rm Hilbert--Schmidt}.
\]
The leading neighboring-shell term implies
\[
 \operatorname{Tr}(D\gamma_K(t))
                    ={ |h(t)|^2\over64}\log K+O(1).
\]
The cross term is finite by the explicit two-Hilbert--Schmidt estimate
\[
 |\operatorname{Tr}(D z_0R^\dagger)|
 \le\|z_0\|_{\rm HS}\|DR\|_{\rm HS},\qquad z_0=-{\cal L}^{-1}B.
\]
The higher Gaussian powers are finite because Dz_0 is bounded and z is
Hilbert--Schmidt, so Dzz^\dagger is Hilbert--Schmidt; the remaining
resolvent factor is bounded by ||z||<1. Thus the active state is normal and Hadamard for its actual sourced equation, but is not in the form domain of the old AP excitation Hamiltonian. This is compatible with finite renormalized source energy. At the final, smoothly switched-off endpoint, LOCAL_PREPARATION gives all final AP energy moments and their actual weighted cutoff limits. Those endpoint results must not be advertised as a common old-energy graph throughout an active mass pulse.

## Decision and next gate

The prescribed source's complete phase, actual mixed-branch state, causal source Hessian and renormalized mean power are now constructed in the stated neighborhood. A source-only CTP kernel still omits controller stress. Its completion requires a real autonomous interaction with a controlled ultraviolet limit and joint constraint solution; CLOCK_ACTUATOR explores the finite-cutoff part of that problem.
