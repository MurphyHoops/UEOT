# JC19 — Actual matter-plus-interaction mean repair at fixed cutoff

## Result and separation of the two contracts

Fix K>=2. For the same autonomous Hamiltonian in CLOCK_ACTUATOR there is some positive g_*(K) such that the actual eight-dimensional mean map has a local inverse for 0<g<g_*(K). The density includes the whole interaction in the declared matter split
\[
 T_m=T_{\rm body}-g_{\mu\nu}V_{\rm int};
\]
the free X/Y tensor remains separately retained. No sharp endpoint switch-off is assumed.

For K=64 and eta=10^-13, one can choose
\[
 0<g<\min\{g_*(64),10^{-40}\}
\]
and one common program u_g so that these actual eight matter-plus-interaction mean projections cancel the two code alternatives' common target, while the same complete instrument retains a binary gap greater than 2.69e-30. The threshold g_* is an existence result, not a numerical bound. Consequently this combined existence claim does **not** inherit the 1.02e81 energy upper bound of the distinct, explicitly fixed g=10^-40 record example. Each chosen positive g has finite energy, and smaller g costs more.

This is a closure of eight retained-matter mean conditions for a normal, generally non-Gaussian actual joint state at finite K. It is not a solution of the full apparatus constraints or an interacting continuum construction.

## 1. The actual mean map is defined before the limit

At the encoding time T=pi let
\[
 F_{g,K}(u)=
 \left(\left\langle A_a^{\rm body}+\int Z_aV_{\rm int}\,dV\right\rangle,
                 \langle P_a^{\rm body}\rangle\right)_{a=1}^4 .
\]
The state is the exact autonomous U_g(T,t_i) applied to its normal programmed initial vector. Only the initial coherent means depend on u; H_g itself does not. The potential contributes no T_0i on this zero-shift slice. All these expectations and their finite-u derivatives are defined on the energy form domain.

There is a uniform-in-g form bound for the interaction. Write
\(A=Y_0^2+Y_1^2\), \(B=g^2(F_0^2+F_1^2)\Phi_+^4\). Pointwise,
\[
 |V_{\rm int}|\le A/4+B/2,\qquad
 (Y_0^2+Y_1^2)/2+V_{\rm int}\ge A/8+B/12 .
\]
The latter follows by the square
\(3\sum_j[Y_j+(2g/3)F_j\Phi_+^2]^2/8\).
Thus the absolute dipole interaction form is bounded by 8 H_pos. The body A/P quadratics are also bounded forms of H_pos+1, with constants depending on fixed K but not on g. This bound is on the fixed ESU Hamiltonian, not arbitrary metric changes.

## 2. A genuine high-order approximation of the actual vectors

Use the comparison frame
\[
 {\cal U}_{u,g}(t)=U_{\rm controller,free}(t,t_i)
        W_{\rm in}(u/g)\otimes U_{\rm body,ref}(u;t,t_i).
\]
The X displacement is included and does not depend on u. As explained in CLOCK_ACTUATOR, the body reference vector has the source-only scalar counterterm phase explicitly removed so that its finite-K Hamiltonian shares the autonomous static constant.

In this frame the residual generator has a finite Taylor expansion
\[
 R_g(t,u)=gV_1(t,u)+\cdots+g^NV_N(t,u)+R_{N+1}(t,u;g).
\]
Every V_j is a finite-K polynomial in canonical variables, since the free controller and quadratic body evolutions transform those variables linearly. Each F_j and all its derivatives are bounded on the real line. Taylor's integral remainder therefore bounds the **global** residual on every Gaussian-polynomial reference vector by O(g^(N+1)); it is not merely an expansion near a classical coordinate value. The same assertion holds after a fixed canonical linear weight and after a u derivative, uniformly on the compact time interval and closed small u ball.

Starting from the fixed reference Gaussian chi_0, define successively
\[
 i\dot\chi_n=\sum_{j=1}^nV_j\chi_{n-j},\qquad
 \chi_n(t_i)=0,\quad n>=1 .
\]
Each chi_n is a polynomial times that fixed Gaussian with finite time-integrated coefficients; its program derivatives have the same property. Set
\(\Psi_N={\cal U}_{u,g}\sum_{n=0}^Ng^n\chi_n\).
Duhamel with the exact autonomous propagator gives
\[
 \|\Psi_g-\Psi_N\|\le C_{K,N}g^{N+1}.                            \tag{1}
\]

The program phase must be handled explicitly. At the common initial time each Y oscillator's coordinate/momentum displacement is a multiple of the same phase-space direction. These directions form a Lagrangian subspace, so
\(W_{\rm in}^\dagger\partial_{u_a}W_{\rm in}=L_a/g\)
with a fixed linear canonical generator, and no u/g^2 central term. Since the actual U_g is independent of u, differentiating the physical Duhamel formula differentiates only its residual and reference vector. The weighted remainder bound gives
\[
 \|\partial_u(\Psi_g-\Psi_N)\|\le C'_{K,N}g^N .                 \tag{2}
\]
No derivative of an unknown interacting propagator is assumed.

## 3. Energy-form interpolation converts norm control to stress means

All finite-g initial vectors and their program derivatives are in D(H_g). Exact autonomous energy-graph conservation and direct action on the Gaussian-polynomial parametrix give, uniformly in the chosen u ball,
\[
 \|(H_g+1)\Psi_g\|+\|(H_g+1)\Psi_N\|=O(g^{-2}),
\]
\[
 \|(H_g+1)\partial_u\Psi_g\|
       +\|(H_g+1)\partial_u\Psi_N\|=O(g^{-3}).
\]
These deliberately loose bounds retain the large controller energy. They do not assume that the interacting evolution preserves Schwartz space or that its high energy moments are uniformly small.

Let delta=Psi_g-Psi_N. Positivity gives
\[
 \|(H_g+1)^{1/2}\delta\|^2
     \le\|\delta\|\,\|(H_g+1)\delta\|.
\]
Together with (1)--(2), the quadratic-form bounds prove a mean error
O(g^((N-3)/2)) and a first-program-derivative error
O(g^((N-5)/2)). Taking N=7 suffices for convergence of the actual means and their derivatives.

After commuting the apparatus Weyl displacement past a body observable, the parametrix body means and derivatives differ from the prescribed-source ones by O(g). For the interaction contribution at T=pi, all F_j and all their jets at pi vanish. In the pulled-back operator gY_j is u_j Z cos(2T)+g upsilon_j, while F_j(gX) is F_j(pi+g xi). Global Taylor bounds make its Gaussian-polynomial expectation and its program derivative O(g^m) for every fixed m. The uniform interaction form bound above then transfers the result to the actual state without falsely declaring finite-g tails to be zero.

Hence
\[
 \boxed{F_{g,K}\longrightarrow F_{\rm ref,K}
                      \quad\hbox{in }C^1\hbox{ on the small control ball}.} \tag{3}
\]
The constants in (1)--(3) depend on K and are not evaluated here.

## 4. A quantified target ball with an unquantified coupling threshold

For every K>=2 the reference Jacobian consists of the same repeated 2 by 2 block as JOINT_PREPARATION. The first neighboring shell is present, so its strict determinant bound survives. K=1 has no such pair and is excluded. The QUANTIFIED_PREPARATION bounds are uniform under truncation:
\[
 \|J_K^{-1}\|<10^6,\quad
 r_0=10^{-16},\quad y_0=5\,10^{-23},\quad
 \|J_K^{-1}(DF_{\rm ref,K}-J_K)\|<.004096.
\]
At u=0 the entire input and Hamiltonian are SO(4) invariant. Thus
\(F_{g,K}(0)=0\) exactly, despite the clock's large homogeneous energy and finite-g interaction.

By (3), some g_*(K)>0 makes
\(\sup_{\|u\|\le r_0}\|DF_{g,K}-DF_{\rm ref,K}\|\le10^{-7}\).
The fixed-point map
\[
 {\cal T}_{g,y}(u)=J_K^{-1}\{y-[F_{g,K}(u)-J_Ku]\}
\]
then has Lipschitz constant at most .104096 and maps the r_0 ball into itself for ||y||<=y_0, since .5+.104096<1. It has a unique fixed point in that ball. This gives an actual state/program existence theorem with a definite target radius. It does not give a computable numerical value of g_* without further residual/moment estimates.

## 5. Same actual state, same retained record

The actual common preparation is body-parity even. A smooth momentum code changes no coordinate-only potential, so its common density increment is exactly eta^2 f_K^2/2 and its longitudinal mean increment is zero. Choose
\[
 y=(-\eta^2\mathbf d_K,0),\qquad
 \mathbf d_K=\tfrac12\int\mathbf Z f_K^2\,dV,\quad \|\mathbf d_K\|\le1/2 .
\]
For eta=10^-13 this is in the certified ball. Both code signs use the same u_g.

For K=64 and any g below both thresholds, the CLOCK_ACTUATOR reference estimates apply uniformly to that u_g. The actual complete Gaussian instrument has the same >2.69e-30 probability-gap bound. The actual post-preparation state is generally non-Gaussian; only the reference uses the erf formula.

The Hamiltonian, both code energy laws, controller state and all outcomes are retained. Parity maps the two code states into each other while acting trivially on the controllers. Consequently the controllers' reduced states and all parity-even full-stress statistics agree for the two signs. The positive probe record is not thereby a record of a gravitational stress difference.

## Next gate

This mean inverse includes the declared interaction split but omits the free controller tensor from the eight targets. Its response is not automatically small as g tends to zero. The full source, background constraints, actual program mixed block, a uniform interacting ultraviolet limit and a physical pointer remain necessary.
