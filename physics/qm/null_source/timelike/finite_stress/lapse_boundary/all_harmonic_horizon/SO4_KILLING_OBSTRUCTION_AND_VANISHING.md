# AH03 — Complete 15-Dimensional Conformal–Killing Obstruction Space on $S^3$ and $SO(4)$ Angular Momentum Audit

## 1. The 15 Geometric Constraint Obstructions on $(S^3, a(\tau)^2\gamma_{ij})$

On a closed 3-sphere spatial slice $(S^3, g_{ij} = a^2\gamma_{ij})$, the linearized ADM constraint operator $(D\mathcal{H}, D\mathcal{M}_i)$ has a finite-dimensional obstruction space determined by the kernel of its formal adjoint $(D\mathcal{H}, D\mathcal{M}_i)^*$ (Moncrief linearization-stability / York–Lichnerowicz decomposition):

1. **Homogeneous $\ell = 0$ scalar (`1` mode)**: constant lapse $N = 1$, matched dynamically by the sub-critical bounce Friedmann equation (`RC05`–`RC06`).
2. **Inhomogeneous $\ell = 1$ scalar densities (`4` modes, $Z_A = 2x_A$, $A = 1..4$)**: $-\Delta_{S^3} Z_A = 3 Z_A \implies (-\Delta_{S^3} - 3)Z_A \equiv 0$ (the Fischer–Marsden turnaround kernel).
3. **Proper conformal Killing vector momenta (`4` modes, $C_A^i = \nabla^i x_A$, $A = 1..4$)**: $\nabla_i C_{A,j} + \nabla_j C_{A,i} - \frac{2}{3}\gamma_{ij}\nabla_k C_A^k \equiv 0$, annihilating the trace-free conformal vector Laplacian.
4. **Rotational $SO(4)$ Killing angular momenta (`6` modes, $\xi_{AB} = x_A\partial_{x_B} - x_B\partial_{x_A}$, $1 \le A < B \le 4$)**: $\nabla_i \xi_{AB,j} + \nabla_j \xi_{AB,i} \equiv 0$ and $\nabla_i \xi_{AB}^i \equiv 0$. Unlike the $\ell = 1$ proper conformal scalars, $\xi_{AB}$ are **exact spacetime Killing vector fields** of $-d\tau^2 + a(\tau)^2\gamma_{ij}dx^i dx^j$ at **every** $\tau \in \mathbb{R}$, so by integration by parts on closed $S^3$,
   $$\int_{S^3} \xi_{AB}^i \nabla^j(\delta K_{ij} - \delta K\,g_{ij})\,d\mu_g = -\frac{1}{2}\int_{S^3} (\nabla^i\xi_{AB}^j + \nabla^j\xi_{AB}^i)(\delta K_{ij} - \delta K\,g_{ij})\,d\mu_g \equiv 0.$$
   Hence **all six $SO(4)$ Killing charges $J_{AB}^{\mathrm{tot}}(\tau) := \int_{S^3} \xi_{AB}^i \langle T_{0i}^{\mathrm{tot}}(\tau, x)\rangle\,d\mu_{S^3}$ must vanish identically** for any linearized ADM momentum-constraint solution to exist ($1 + 4 + 4 + 6 = 15 = \dim SO(5,1)$).

## 2. Exact All-Order Vanishing $J_{AB}^{\mathrm{tot}} \equiv 0$ on the Axisymmetric Readout Protocol

We audit every sector of the `renormalized_continuum` state $\Psi_{\mathrm{actual},\infty}$:

1. **Separable conformal spectator/program channels (`RC04`)**: For any real $\xi = 1/6$ massless field $\varphi(\tau, x) = a(\tau)^{-1}\tilde f(\tau) v(x)$ with a single spatial profile $v(x)$, the conformally improved momentum density on FRW satisfies
   $$a(\tau)^2 T_{0i}^{\mathrm{conf}}[\varphi] = \tilde f'(\tau)\tilde f(\tau)\,v\nabla_i v - \frac{1}{6}\partial_\tau(\tilde f^2)\nabla_i(v^2) = \frac{1}{6}\tilde f'(\tau)\tilde f(\tau)\,\nabla_i\bigl(v(x)^2\bigr),$$
   which is an **exact spatial gradient**. Integrating against $\xi_{AB}^i$ ($\nabla_i\xi_{AB}^i = 0$) yields $0$ identically for **any** spatial profile $v(x)$ (even non-axisymmetric).
2. **Axisymmetric code $\pm\eta f(x_4)$, antipodal beacon $B_{\mathrm{rec}}(x_4)$, pointer $\Psi_{\mathrm{ptr}}$, and matched 8-mean fixed point $\mathbf{u}^*$ (`RC08`–`RC09`)**: Because the target $\mathbf{y}$ is invariant under the orthogonal group $O(3)_{123}$ acting on $(x_1, x_2, x_3)$, uniqueness of the Banach fixed point $\mathbf{u}^* = (\mathbf{u}_0^*, \mathbf{u}_1^*)$ forces $\mathbf{u}_0^*, \mathbf{u}_1^* \in \mathbb{R}\mathbf{e}_4$. Thus the full interacting state $|\Psi_{\mathrm{actual},\infty}(\tau)\rangle$ is invariant under each coordinate reflection $R_A: x_A \mapsto -x_A$ ($A \in \{1, 2, 3\}$). Since every pair $1 \le A < B \le 4$ has $A \in \{1, 2, 3\}$ and $R_A$ flips $x_A$ while leaving $x_B$ fixed, $\mathcal{U}(R_A)^\dagger L_{AB}\mathcal{U}(R_A) = -L_{AB}$, proving $J_{AB}^{\mathrm{tot}}(\tau) \equiv 0$ **to all non-perturbative orders**.

## 3. Non-Zero Second-Order Rotational Torque for Non-Collinear Controls

Conversely, for general 3D targets with non-collinear controls $\mathbf{u}_0 \wedge \mathbf{u}_1 \neq 0$, driving the smeared body field via $V(\tau) = \frac{1}{2}\sum_{C=1}^4 (u_{0,C} F_0(\tau) + u_{1,C} F_1(\tau))\mathcal{O}_C$ ($\mathcal{O}_C := \int_{S^3} Z_C (\mathcal{K}_{\rho_0}\Phi_+)^2 d\mu_{S^3}$) generates via Heisenberg evolution $L'_{AB} = i[V, L_{AB}]$ and $[L_{AB}, \mathcal{O}_C] = i(\delta_{AC}\mathcal{O}_B - \delta_{BC}\mathcal{O}_A)$ a second-order $SO(4)$ torque:
$$J_{AB}^{(2)}(\mathbf{u}_0, \mathbf{u}_1) = \varkappa_{\mathrm{rot}}\,\bigl(u_{0,A} u_{1,B} - u_{0,B} u_{1,A}\bigr),$$
where for disjoint smooth gates $F_0(\tau) = \sin^6(4\tau)\mathbf{1}_{[0,\pi/4]}(\tau)$ and $F_1(\tau) = \sin^6(4(\tau - \pi/4))\mathbf{1}_{[\pi/4,\pi/2]}(\tau)$,
$$\varkappa_{\mathrm{rot}} = \sum_{k=1}^\infty w_{k,k+1}^{\rho_0}\,\sin\!\left(\frac{\Omega_{k,k+1}\pi}{4}\right)\left(\int_{-\pi/8}^{\pi/8} \cos^6(4\xi)\cos(\Omega_{k,k+1}\xi)\,d\xi\right)^2, \qquad \Omega_{k,k+1} = \omega_{+,k} + \omega_{+,k+1},$$
with positive Clebsch–Gordan pair weights $w_{k,k+1}^{\rho_0} = \frac{k(k+1)(k+2)}{6 V_0 \omega_{+,k}\omega_{+,k+1}}\,\hat\kappa_{\rho_0}(k)^2\hat\kappa_{\rho_0}(k+1)^2 > 0$. Because the six-fold smooth gate Fourier square decays as $O(k^{-12})$ (with tail above $k = 200$ bounded below $10^{-11}$), the modes within the gate bandwidth ($k \lesssim 8$, led by $k = 2, 3$ where $\sin(\Omega_{k,k+1}\pi/4) < 0$) yield $\varkappa_{\mathrm{rot}} < -2\times 10^{-4} \neq 0$, proving that general non-collinear 3D preparations **require** the 6-parameter rotational trim constructed in `AH04`.
