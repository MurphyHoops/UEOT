# AK. Source-containing local counterterms and their lapse / endpoint columns

## AK1. The actual three-field Hessian

Consider a local three-scalar action with canonical kinetic terms and
\[
 V=\tfrac12\sum_{i=\chi,\phi,\psi}m_i^2\varphi_i^2
       +r(\chi)\phi\psi ,
\]
and independent nonminimal couplings \(\xi_iR\).
This section computes a one-loop background-field UV diagnostic. It
does not assume an exact normal interacting continuum state.

The extra mass Hessian is
\[
 \delta{\cal M}=
 \begin{pmatrix}
 r''\phi\psi&r'\psi&r'\phi\\
 r'\psi&0&r\\ r'\phi&r&0
 \end{pmatrix}.                                             \tag{AK.1}
\]
Let \({\cal M}_0=\operatorname{diag}(m_i^2+\xi_iR)\),
\(D=-(\nabla^2+E)\), \(E=-({\cal M}_0+\delta{\cal M})\).
For the same flat scalar bundle, subtracting the free operator's bulk
four-dimensional heat coefficient gives
\[
 \delta a_4=\frac1{16\pi^2}\left\{
 r^2+(r')^2(\phi^2+\psi^2)+\frac12(r'')^2\phi^2\psi^2
 +[m_\chi^2+(\xi_\chi-\tfrac16)R]F-\frac16\Box F\right\},
 \quad F=r''\phi\psi .                                      \tag{AK.2}
\]
Indeed the relevant coefficient is
\(\operatorname{tr}(E^2/2+RE/6+\Box E/6)\), and
\(\operatorname{tr}\delta{\cal M}=F\).
The convention and bulk formula are Eq. (2.2) and Eq. (4.28) of Vassilevich,
[hep-th/0306138](https://arxiv.org/abs/hep-th/0306138).
Terms independent of the interaction cancel.

In particular an \(r^2\) vacuum term alone misses source/probe-dependent
terms after the controller is local and fluctuating. This is an actual
Hessian distinction, not an assumed noise counterterm.

## AK2. Metric variation and the Ward identity

Write
\[
 P=r^2+(r')^2(\phi^2+\psi^2)+\tfrac12(r'')^2\phi^2\psi^2
        +m_\chi^2F,\qquad a=\xi_\chi-\tfrac16 .
\]
The representative local counterterm is
\[
 S_{\rm ct}=\kappa\int\sqrt{-g}\,[P+aRF-\Box F/6].
\]
Here \(\kappa\) absorbs the divergent coefficient and convention-dependent
effective-action sign. Finite coefficients of distinct local operators
are independent renormalization data; this expression does not require
them all to equal one finite \(\kappa\).

For signature \((-+++)\) and
\(T_{\mu\nu}=-2(\sqrt{-g})^{-1}\delta S/\delta g^{\mu\nu}\),
compactly supported bulk variation yields
\[
 T^{\rm ct}_{\mu\nu}
  =\kappa Pg_{\mu\nu}
     -2\kappa a[FG_{\mu\nu}+g_{\mu\nu}\Box F-\nabla_\mu\nabla_\nu F].
                                                               \tag{AK.3}
\]
The field Euler derivatives are
\[
 {\cal E}^{\rm ct}_A=\kappa(\partial_AP+aR\partial_AF),
\qquad
 \nabla^\mu T^{\rm ct}_{\mu\nu}
    =\sum_A{\cal E}^{\rm ct}_A\nabla_\nu\varphi_A.             \tag{AK.4}
\]
The identity follows by differentiating (AK.3), using the contracted
Bianchi identity and the scalar derivative commutator. The new stress is
conserved only together with the same complete modified field equations.
A separately added conserved-looking carrier does not replace this identity.

## AK3. Explicit lapse and mixed source columns

Restrict to a static spatial metric \(h_{ij}\), zero shift, closed \(S^3\),
and arbitrary positive lapse \(N(t,y)\). Then
\[
 R=R_h-2N^{-1}\Delta_hN .
\]
After spatial integration by parts, the bulk lapse column is
\[
 \boxed{\frac{\delta S_{\rm ct,bulk}}{\delta N}
   =\kappa\sqrt h\,[P+a(R_hF-2\Delta_hF)].}                  \tag{AK.5}
\]
Its mixed variation in a source/controller direction \(\eta\) is
\[
 \kappa\sqrt h\,[DP\,\eta+
        a(R_h\,DF\,\eta-2\Delta_h(DF\,\eta))].               \tag{AK.6}
\]
These are genuinely source-containing columns. The spatial Laplacian
cannot be deleted from a local constraint simply because its integral
against a constant homogeneous lapse is zero. In this restricted
static-\(h\) local bulk term alone the second lapse column is zero,
because the lapse dependence is linear after integration by parts.
This says nothing about the second derivative of the complete CTP
influence action or a dynamical metric.

## AK4. Finite-time endpoint and CTP signs

On a finite time interval with closed spatial slices,
\[
 \int dt\,dV_h\,N\Box F
  =-\left[\int dV_h\,\dot F/N\right]_{t_i}^{t_f}.
\]
Consequently
\[
 S_{\rm div}=\frac{\kappa}{6}
       \left[\int dV_h\,\dot F/N\right]_{t_i}^{t_f},
\]
\[
 \delta_NS_{\rm div}=-\frac{\kappa}{6}
       \left[\int dV_h\,\dot F\,\delta N/N^2\right]_{t_i}^{t_f},
\]
\[
 \delta_{N_1}\delta_{N_2}S_{\rm div}=\frac{\kappa}{3}
       \left[\int dV_h\,\dot F\,\delta N_1\delta N_2/N^3
       \right]_{t_i}^{t_f}.                                \tag{AK.7}
\]
Keep \(S_{\rm ct}[+]-S_{\rm ct}[-]\) and both lapses until variation and
the common initial density kernel / final gluing have been specified.
Dropping this total derivative prematurely loses endpoint and mixed
columns. The \(RF\) metric variation can require additional boundary
completion for a chosen boundary-value problem; (AK.7) is not claimed
to be the whole boundary action. A true physical boundary also requires
heat-kernel boundary coefficients. A finite artificial CTP time cut is not
silently identified with a separately imposed Dirichlet boundary.

## AK5. Linear coupling is UV simpler but unstable without a changed action

For \(r(\chi)=g\chi\), \(r''=0\), (AK.2) reduces to
\[
 \delta a_4=\frac{g^2}{16\pi^2}(\chi^2+\phi^2+\psi^2).
\]
The old \(r^2\) term supplies only the \(\chi^2\) part. Source and probe
mass terms remain required. Furthermore the naive cubic potential with
only positive quadratic masses is unbounded below:
constant \(\chi=\phi=t,\ \psi=-\operatorname{sgn}(g)t\) gives
\(O(t^2)-|g|t^3\to-\infty\). Coherent displacement of even the lowest
finite-cutoff modes already excludes a semibounded Hamiltonian for that
bare potential.

A concrete classical stability repair changes the action by
\[
 V_{\rm stab}=\tfrac12\eta\chi^2(\phi^2+\psi^2),\quad\eta>0 .
\]
For equal \(\phi,\psi\) mass \(m^2>0\), their lowest quadratic eigenvalue
is \(m^2+\eta\chi^2-|g\chi|\ge m^2-g^2/(4\eta)\).
Thus \(\eta\ge g^2/(4m^2)\), with positive controller mass, makes the
potential nonnegative; strict inequality gives a uniform source/probe gap.

This repair is not closed under its one-loop UV terms. The new Hessian
satisfies
\[
 \tfrac12\operatorname{tr}(\delta{\cal M})^2
 =g^2(\chi^2+\phi^2+\psi^2)+8g\eta\chi\phi\psi
 +4\eta^2\chi^2(\phi^2+\psi^2)+\eta^2\chi^4
       +\tfrac12\eta^2(\phi^2+\psi^2)^2,                    \tag{AK.8}
\]
and
\(\operatorname{tr}\delta{\cal M}=\eta(\phi^2+\psi^2+2\chi^2)\).
The \(\chi^4\) and \((\phi^2+\psi^2)^2\) operators, with their own
coefficients, are therefore needed already at this order, together
with the corresponding mass, curvature and total-derivative terms.

## Acceptance and next contract

Accepted: exact Hessian algebra; interaction-dependent one-loop bulk
counterterms; their local lapse, mixed and finite-time endpoint columns;
a cubic stability rejection and a specified classical stability repair.
This is not an exact interacting normal-state or quantum-gravity theorem.

A local candidate must next fix the full operator basis and finite
renormalization data, derive the complete causal CTP/Ward system on one
initial state, and control a positive normal preparation/instrument limit.
Hollands and Wald [gr-qc/0404074](https://arxiv.org/abs/gr-qc/0404074)
provide perturbative stress conservation under explicit time-ordered
product conditions; their formal series cannot stand in for convergence
or normal-state positivity of the present model.
The previous fixed-source independent-carrier exclusion does not reject
(AK.6): these columns contain the source. Their presence alone also does
not prove the geometric/source charge equality. Full unification remains open.
