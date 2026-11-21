# Positive-time control for the actual joint preparations

The clock increment in this page is \(t=u-u_i\), not conformal or SI time. Fix any \(T_0>0\) contained in a compact nonzero-\(g_K\) interval. All coefficients, source states, packets and phases are selected once. The estimates use the complete original raw generator, not \(H_s\) alone.

## T1. A complete-generator Taylor residual

For a normalized compact-\(\kappa\), Schwartz-source initial vector \(\phi\), put
\[
 H_*=H(0),\quad v_1=-iH_*\phi,\quad
 v_2=(-iH_*'-H_*^2)\phi,\quad
 P_2(t)=\phi+tv_1+\tfrac12t^2v_2 .
\]
All finite compositions displayed here stay in the common test space. Direct substitution gives
\[
 r(t)=(i\partial_t-H(t))P_2(t)
 =-[H(t)-H_*-tH_*']\phi
 +it[H(t)-H_*]H_*\phi
 +\tfrac12t^2H(t)(iH_*'+H_*^2)\phi .
\tag{T1}
\]
Define, with suprema over \([0,T_0]\),
\[
 R_H=\tfrac12\sup\|H''(s)\phi\|
  +\sup\|H'(s)H_*\phi\|
  +\tfrac12\sup\|H(s)(iH_*'+H_*^2)\phi\|.
\]
These are finite norms of specified vectors and the original coefficients. Then \(\|r(t)\|\le R_Ht^2\). Weak Duhamel and the actual unitary give
\[
 \|U(t,0)\phi-P_2(t)\|\le R_Ht^3/3.
\tag{T2}
\]
Strong transport of raw snapshot operator domains is not required.

For the actual rank-two density decomposition with weights \(p_j\), partial trace and rank-one operator estimates imply
\[
 \|\sigma(t)-\sigma_0-t\sigma_1-\tfrac12t^2\sigma_2\|_1
 \le C_\sigma t^3 ,
\]
where one explicit valid constant is
\[
 C_\sigma=\sum_jp_j\left[
 (2+R_{H,j}T_0^3/3)R_{H,j}/3+
       \|v_{1,j}\|\|v_{2,j}\|+
                    T_0\|v_{2,j}\|^2/4\right].
\tag{T3}
\]
The first term bounds the true-versus-polynomial projector; the remaining terms retain its cubic and quartic products.

## T2. The weighted error needs its own form-norm proof

Use the fixed raw comparison space \(Q=Q_3\) after the fixed geometry phase has been removed, or its precisely conjugated domain before that removal. WEIGHTED_EVOLUTION proves
\[
 M_Q=\sup_{s,t\in[0,T_0]}\|U(t,s)\|_{Q\to Q}<\infty .
\]
Replace every Hilbert norm in \(R_H\) by the \(Q\) norm to define \(R_Q\). Core stability and smooth coefficients make it finite. The residual is a continuous \(Q\)-valued function; the \(Q\)-valued Bochner Duhamel integral is legitimate and weak uniqueness identifies it with the actual error. Therefore
\[
 \|U(t,0)\phi-P_2(t)\|_Q\le E_Qt^3,\qquad E_Q=M_QR_Q/3 .
\tag{T4}
\]
This step is not inferred from T2 or from unitarity in the Hilbert norm.

Let \(c_M=\|\kappa^{-1/2}\|_{Q\to\mathcal H}\), which is finite by E3, and
\(\beta_l=\kappa^{-1/2}v_l\), \(v_0=\phi\). Set
\[
 B_{\rm app}=\|\beta_0\|+T_0\|\beta_1\|+\tfrac12T_0^2\|\beta_2\|,
 \qquad B_{\rm ex}=c_MM_Q\|\phi\|_Q .
\]
The same projector argument, now genuinely weighted, gives
\[
 \|\tau(t)-\tau_0-t\tau_1-\tfrac12t^2\tau_2\|_1\le C_\tau t^3,
\]
\[
 C_\tau=\sum_jp_j\left[
 (B_{{\rm ex},j}+B_{{\rm app},j})c_ME_{Q,j}
 +\|\beta_{1,j}\|\|\beta_{2,j}\|+T_0\|\beta_{2,j}\|^2/4\right].
\tag{T5}
\]
The coefficients are the weighted polynomial-projector coefficients. Taking their trace also controls \(I(t)\). This is an initial expansion for the actual core preparations, not a new global differentiability theorem for all weighted states.

## T3. A strictly positive interval of generated correlations

Put
\[
 A_\sigma=\|\sigma_2\|_1/2+C_\sigma T_0,\quad
 A_\tau=\|\tau_2\|_1/2+C_\tau T_0,\quad
 L_\sigma=\|\sigma_1\|_1+A_\sigma T_0,
\]
\[
 C_\Delta=2A_\tau+I A_\sigma+|J_0|L_\sigma .
\]
Expanding \(\Delta(t)=\tau(t)-I(t)\sigma(t)\), while using the exact
\(\|\sigma(t)\|_1=1\), proves
\[
 \|\Delta(t)-t\Delta'_0\|_1\le C_\Delta t^2.
\]
For the same actual \(B_s\), \(c_s>0\), and
\(v_M=\operatorname{Var}(\kappa^{-1})>0\), every
\[
 0<t\le T_{\rm corr}:=
 \min\{T_0,c_sv_M/(2C_\Delta)\}
\]
satisfies
\[
 \operatorname{Tr}B_s\Delta(t)\ge \tfrac12c_sv_Mt>0.
\tag{T6}
\]
If a denominator vanishes its restriction is omitted. \(\Delta\) is a weighted correlation operator, not itself a normalized density or an apparatus readout.

## T4. A positive interval distinguishing the two phase preparations

For CLOSURE_COUNTEREXAMPLE, the two initial \(\sigma_0,\sigma_1\) agree.
Let \(d=|c_s\Delta J|>0\) and
\(C_\Sigma=C_{\sigma,+}+C_{\sigma,-}\). The actual bounded expectation difference is \(\tfrac12c_s\Delta J\,t^2+O(C_\Sigma t^3)\), so
\[
 0<t\le T_*:=\min\{T_0,d/(4C_\Sigma)\}
 \quad\Longrightarrow\quad
 D_{\rm tr}(\sigma_+(t),\sigma_-(t))\ge d\,t^2/8 .
\tag{T7}
\]
The certified \(d_0=10^{-9}h_i^{-2}\le d\) may replace \(d\) in both the radius and the lower bound. This is more than an initial-jet claim, but its vector-norm constants have not been reduced to a numerical experimental time radius.

## T5. The raw mean pressure also has a controlled interval

Any \(C^3\) bounded form \(O(t):Q\to Q^*\) can be handled with T4. Put
\(q_i=\|v_i\|_Q/i!\), \(o_l=\|O^{(l)}(0)\|_{\rm form}/l!\), \(i,l=0,1,2\), and
\[
 B_{{\rm app},Q}=\sum_{i=0}^2q_iT_0^i,\quad
 B_{{\rm ex},Q}=M_Q\|\phi\|_Q,\quad
 O_{\max}=\sup\|O(t)\|_{\rm form},\quad
 O_{3,\max}=\sup\|O'''(t)\|_{\rm form}.
\]
An explicit third-order remainder constant for its expectation is
\[
 C_O=\sum_jp_j\left[
 O_{\max}(B_{{\rm ex},Q}+B_{{\rm app},Q})E_Q
 +B_{{\rm app},Q}^2O_{3,\max}/6
 +\!\!\sum_{\substack{i,k,l\in\{0,1,2\}\\i+k+l\ge3}}
 q_iq_ko_lT_0^{i+k+l-3}\right]_j .
\tag{T8}
\]
The three terms bound the actual vector error, the operator Taylor error, and the finite polynomial tail separately.

Finite-\(K\) raw pressure \(p_s(u)\) is such a form. The phase pair has
\[
 \Delta\langle p_s\rangle''_0=
 -\frac{4\Delta J}{3V_0A^4}\langle D_\Omega\rangle_{\rm old}\ne0
\tag{T9}
\]
by PRESSURE_WITNESS. With \(d_p\) the absolute value of this coefficient and
\(C_p=C_{p,+}+C_{p,-}\), the same argument yields
\[
 |\Delta\langle p_s\rangle(t)|\ge d_pt^2/4,\qquad
 0<t\le\min\{T_0,d_p/(4C_p)\}.
\tag{T10}
\]
No full continuum geometry, all-mode tensor constraints, or apparatus is implied. These candidate-dependent positive windows are expressed in the chosen relational clock.
