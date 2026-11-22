# JC8 — The source pulse's counterterm, net work and Ward noise

This entry includes the bookkeeping required by the actual local
preparations in LOCAL_PREPARATION.md and JOINT_PREPARATION.md.
It does not convert their prescribed source into a dynamical actuator.

## 1. Local source data before variation

In the original two-field basis put
\[
 {\cal M}^2=r\sigma_x+sP_+,\qquad P_+=(I+\sigma_x)/2 .
\]
Its eigenvalues are \(r+s,-r\), and
\[
 {\rm tr}{\cal M}^2=s,\qquad
 {\rm tr}({\cal M}^2)^2=2r^2+2rs+s^2 .                            \tag{1}
\]
For conformal scalars the new source part of the heat coefficient is
\(rs+s^2/2-\Box s/6\). The divergent \(Rs\) cross term cancels at
conformal coupling. A **finite** \(Rs\) term is an independent datum;
set its coefficient to zero relative to the covariant completion in
GROUND_DATUM.md. Extend its source-square finite datum using
\({\rm tr}({\cal M}^2)^2/2\), and retain derivative/source contacts
until variation is done.

Let \(H_K^{\rm harm}=\sum_{k=1}^K1/k\). In the inherited unit-sphere
Hamiltonian normalization the new logarithmic scalar counterterm is
\[
 \Delta C_K[s]=\frac{H_K^{\rm harm}}{16V_0}
                     \int(2rs+s^2)dV .                          \tag{2}
\]
For \(s=\mathbf h(t)\cdot\mathbf Z\),
\[
 \Delta C_K=\frac{H_K^{\rm harm}}{64}|\mathbf h(t)|^2,\qquad
 \mathbf h=b\boldsymbol\epsilon+b'\boldsymbol\zeta .               \tag{3}
\]
Although \(\int s=0\) for these profiles, the \(2rs\) term in (2)
must be kept before local source or metric variation.
Likewise the instantaneous \(2bb'\boldsymbol\epsilon\cdot
\boldsymbol\zeta\) term in (3) must not be dropped because a separate
integral happens to vanish. The local derivative of (2) is
\(H_K^{\rm harm}(r+s)/(8V_0)\).

Equations (1)–(3) identify the logarithmic local source subtraction
and finite source choices. They do not yet match every scalar
canonical cutoff phase to a full renormalized CTP determinant.

## 2. Finite-cutoff work identity and its actual endpoint limit

At each finite cutoff the source is flat off at both ends, and the
Hamiltonian is the same \(H_{r,K}\) there. Exact unitary evolution gives
\[
 W_K=\int dt\left[\int \dot s\,\langle\Phi_+^2/2\rangle_K\,dV
                          +\partial_tC_K\right]
     =\langle H_{r,K}\rangle_{\rm final}-e_K\geq0 .                 \tag{4}
\]
All compact derivative counterterms have zero endpoint difference.
The actual weighted Hilbert--Schmidt endpoint convergence in
LOCAL_PREPARATION.md proves
\[
 W_K\longrightarrow E_{\rm exc}
       ={\rm Tr}(D\beta\beta^\dagger)\geq0 .                       \tag{5}
\]
This is an actual net-work limit. It does not assume that the
instantaneous renormalized power has already been shown to admit a
dominated cutoff limit, and it does not prove the absolute CTP phase
limit.

For a small eight-control pulse, (5) has the positive quadratic
coefficients and nonzero energy variance in JOINT_PREPARATION.md.
Accounting only for the net mean work omits those fluctuations.

## 3. The external-source Ward deficit

For the retained field action with the prescribed source,
\[
 \nabla^\mu T^{\rm m}_{\mu\nu}
      =-B_s\,\partial_\nu s,\qquad B_s=[\Phi_+^2/2]_{\rm ren},
                                                                    \tag{6}
\]
with the source operator and stress defined in the same local
counterterm convention. With an additional time-dependent old mixing
one also retains \(-[\phi\psi]_{\rm ren}\partial_\nu r\).
This source-dependent conservation identity is standard for a
covariant external-potential action; see Moretti,
[gr-qc/9809006](https://arxiv.org/abs/gr-qc/9809006), Theorem 2.4(b).

For a real compact spacetime vector \(v\), define
\[
 D_v^{\rm m}=-T^{\rm m}(\nabla^{(\mu}v^{\nu)}),\qquad
 g=v^\nu\partial_\nu s .
\]
After centering, \(\delta D_v^{\rm m}=-\delta B_s(g)\).
Both are legitimate spacetime-smeared Wick vectors on the actual
prepared history. Their variance is
\[
 \operatorname{Var}D_v^{\rm m}
 =\|\delta B_s(g)\Omega\|^2=N_{B_s}(g,g)\geq0 .                    \tag{7}
\]
It is strictly positive for suitable \(v\) in an active source region:
choose a small real test where a nonzero two-mode product has nearly
constant phase, then divide by a nonzero component of \(\partial s\)
to realize that test as \(v\cdot\partial s\). Smooth dependence from
the nonzero lowest incoming mode makes this construction available
for the small pulses here. This is not a claim that every test has
strictly positive variance.

## 4. Necessary total-source correlation, not just mean compensation

Suppose a future joint model really supplies a total stress on the
same domain, with apparatus and interaction included in
\(T^{\rm e}=T^{\rm app}+T^{\rm int}\), and the operator Ward identity
\(\nabla(T^{\rm m}+T^{\rm e})=0\).
For any test with variance \(v_m>0\), it must have
\[
 \delta D_v^{\rm e}=-\delta D_v^{\rm m},\qquad
 \operatorname{Var}D_v^{\rm e}=v_m,\qquad
 \operatorname{Cov}_{\rm sym}(D_v^{\rm m},D_v^{\rm e})=-v_m .       \tag{8}
\]
Thus its transfer-noise block is
\[
 v_m\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
\]
with a zero total-transfer direction. A c-number apparatus mean, or
an independent apparatus noise with zero cross covariance, does not
satisfy this necessary condition.

Equation (8) is conditional on the specified retained Ward law being
realized in the joint model. A quantum actuator can change that law's
state and correlations; its actual interaction must then be derived
again. We have not constructed such a joint model, assigned its
positive energy budget, or solved the Einstein constraints. The
external pulse succeeds as a source-state preparation but remains
incomplete as a physical total-source device.
