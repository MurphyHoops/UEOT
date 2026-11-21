# B. A fixed finite anomaly-compatible homogeneous action

## B1. Prescription and one Casimir contribution

For n_s real massless conformal scalars choose the canonical trace
prescription

    T^a_a=n_s[Box R-E_4/2]/(2880 pi²)

on conformally flat backgrounds. Here E_4=Riem²-4Ric²+R² and the
closed unit S³ has V_3=2pi². This finite prescription matters:
a finite R² shift changes its Box R convention and the associated
Einstein-universe vacuum energy. We keep the canonical matter
prescription fixed and vary a separately named gravitational coupling.

In the retained conformal lapse variables,

    a⁴ E_4=24 chi(1+kappa²),
    a⁴ Box R=-6D²chi+12chi+36kappa²chi.

A homogeneous anomaly representative is

    L_an=-n_s chi²/480-n_s kappa⁴/720.                     (B1)

Its Euler_u row equals V_3 a⁴ T^a_a and its Hamiltonian is

    E_an=-n_s kappa⁴/240-n_s chi²/480
                          +n_s kappa Dchi/240.           (B2)

The source energy is H_c=dGamma(k)+E_c with E_c=n_s/240.
E_c is included ONCE. A normal-ordering convention alone would not
justify deleting either E_c or (B1).

This is an anomaly-compatible homogeneous representative for a selected
fixed-background prescription. The conformally invariant part is
encoded by the source spectrum/state; possible boundary/state local
terms require the same CTP prescription. We have not recovered a unique
four-dimensional effective action from its FLRW restriction.

## B2. A real R² coupling and all linked terms

Add [lambda/(72V_3)] integral sqrt(-g) R². Its homogeneous bulk is

    lambda(chi+kappa²+1)²/2.

The cross term is D F_lambda with
F_lambda=lambda(kappa+kappa³/3). Removing it requires transporting
the initial state, endpoint polarization and final gluing by the same
source-independent phase. This phase is a well-defined multiplication
unitary in geometry; it is not the divergent source Q endpoint.

After that transport, let a=Aexp(u). The complete geometric bulk is

    L_geom = 3V_3 a²(1-kappa²)/2 - V_3 U_0 a⁴
             +g chi²/2 +(lambda/2-n_s/720)kappa⁴
             +lambda kappa²+lambda/2,
    g=lambda-n_s/240.                                    (B3)

For g nonzero the symmetric u-clock generator has the form

    H(u)=alpha A_eta +[H_c+d0(u)]/kappa
                       +d1(u)kappa+d3 kappa³,
    alpha=1/(2g),
    d0=V_3U_0a⁴-3V_3a²/2-lambda/2,
    d1=3V_3a²/2-lambda,
    d3=n_s/720-lambda/2.                                 (B4)

A_eta is the same selected geometry principal ordering, eta>=-1/4;
its self-adjoint realization is specified in JOINT_CONTINUUM.
All coefficients are independent of the source cutoff K.
Keeping the old minimal AE logarithmic coefficients instead would be
a different model and would invalidate this construction.

## B3. Ward and lapse rows

For any N L(u,kappa,chi),
P_kappa=L_chi, P_u=L_kappa-DP_kappa,
Gamma_N=-(kappa P_u+chi P_kappa-L), Gamma_u=N(L_u-DP_u),
Theta=P_u delta u+P_kappa delta kappa.
The exact off-shell identity is
D E_geom+kappa (L_u-DP_u)=0.
All chi, lapse-derivative and mixed contacts are obtained by varying
this SAME action; N must not be fixed before variation.
The anomaly row and R² row are not independent noises or detachable
pressure corrections.

## B4. A useful independent de Sitter check

On a=A/cos(eta), N=1, kappa=tan(eta), chi=1+kappa²,
Dchi=2kappa chi,

    E_c+E_an=n_s(1+kappa²)²/480,
    rho_conf=n_s/(480 V_3 A⁴).

The trace gives p_conf=-rho_conf on this geometry.
A constant-curvature R² variation vanishes in four dimensions.
Thus the NEW conformal vacuum mean equations admit this explicit
closed de Sitter history when

    U_0=3/(2A²)-n_s/(480V_3 A⁴).

This checks both density and pressure, not just a scalar sum.
It is a NEW semiclassical fixed-background history; it is not yet
a statement that an arbitrary normal joint geometry state follows
that exact mean history.

## B5. What the prescription does not establish

The anomaly stress and Casimir convention are established background
QFT inputs. Canonically quantizing this reduced higher-derivative action
is an additional declared construction, not a proof of full quantum
gravity. Normality and unitary evolution do not imply a lower energy
bound. The nondegenerate energy-stability test must be checked separately,
and g=0 requires a new constrained reduction.

Primary sources:
Agullo--Nelson--Ashtekar, Phys.Rev.D91 064051, conformal trace discussion.
Dowker, https://arxiv.org/abs/2403.03817 (finite-scheme dependence).
Dyer--Hinterbichler, https://arxiv.org/abs/0809.4033 (boundary data).
