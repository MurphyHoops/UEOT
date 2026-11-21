# F. Critical action: a new constrained reduction with an admitted band

## F1. Eliminate the higher derivative by the FULL finite action change

At lambda*=n_s/240, g=0. After the same scalar R² endpoint transport,

    L_geom=B(u)kappa²+c kappa⁴+D(u),
    c=n_s/1440,
    B=lambda*-3V_3 a²/2,
    D=3V_3a²/2-V_3U_0a⁴+lambda*/2.                       (F1)

The lapse constraint and geometric momentum are

    P_u=2B kappa+4c kappa³,
    F(u,kappa,E)=3c kappa⁴+B kappa²+E-D=0.               (F2)

E is the FULL conformal energy of the admitted matter sector.
Writing a_c=3c, Delta=B²-4a_c(E-D),

    x_s=kappa_s²=(-B+s sqrt(Delta))/(2a_c),  s=+1 or -1,
    partial_kappa P_u=2s sqrt(Delta).                   (F3)

Fix a compact clock chart and a common energy band where Delta has a
strict positive lower bound and x_s has a strict positive lower bound.
The Legendre map is then locally invertible; the branch and expanding
sign are chosen ONCE. This is a new regular Dirac reduction. Neither
the previous g-nonzero Friedrichs theorem nor a division by g is used.

The selected reduced Hamiltonian is

    h(u,E)=-2B sqrt(x_s)-4c x_s^(3/2),
    partial_E h=1/kappa_s.                              (F4)

On the lower branch s=-1 with B<0, P_u<0 and h>0 on the admitted band.
This positive branch is not a proof of stability in other spacetime
modes, other clock charts or a uniquely prescribed Dirac quantization.

## F2. A normal physical Hilbert space and complete time weight

On a fixed spectral band B_E of H_c, define
H_phys=1_B_E(H_c)F and H_red(u)=h(u,H_c).
The diagonal bounded self-adjoint family gives

    U(u,v)=exp[-i integral_v^u h(w,H_c)dw].              (F5)

All normal states evolve normally. In compact S³ an upper-bounded
source energy band is FINITE dimensional. This space is not the old
independent L²(kappa) tensor Fock partition, nor the unrestricted field
CCR representation. Kappa(u)=kappa_s(u,H_c) is now a spectral observable.

Choose the reduced normal-form ordering
C_sel=R(u)[P_u+H_red(u)]R(u), R=sqrt(kappa(u)).
R and R^-1 are bounded on the admitted chart/band. Expanding it gives

    C_sel=kappa P_u-(i/2)partial_u kappa+kappa H_red.

The connection term cannot be dropped. Raw states are
Psi=R^-1 U psi_i, and
Gamma_raw(u,v)=R(u)^-1 U(u,i)rho U(v,i)*R(v)^-1.
Weighted diagonal trace is one, and weighted gluing uses kappa(v).
Fixed compact physical tests give a nonzero positive kernel by
continuity; an inverse-propagator test is unnecessary.

This explicitly declares reduce-then-quantize and its ordering.
It does not prove equivalence to an unspecified quantization of the
original nonlinear unreduced constraint.

## F3. Actual frozen-parameter window, recomputed for the NEW model

Only A and U_0 are reused as numerical parameters from the accepted
history.json; no old field mode or geometry solution is reused.
Choose J=[0.54,0.56], n_s=2, and total excitation energy 0<=E-E_c<=100.
The verifier uses 200 exact rational cells and outward intervals,
the complete finite action and the cancellation-stable lower root

    x_-=2(E-D)/[-B+sqrt(Delta)].

It bounds kappa, Delta, the energy ceiling and the model proper
duration integral a du/kappa. Every point in the stated energy band
and chart is included. No mode or geometry ODE is integrated.

For the isolated conformal source the common energy ceiling is finite,
E<=D+B²/(12c). Its finite-band restriction is essential. A different,
energy-conditioned clock is considered separately; it cannot silently
replace this common-u history.

## F4. Operator homogeneous compatibility and the mean-history scope

Since all operators above are functions of the same conserved E,
(F2) is a strong operator identity on H_phys, not just a mean match.
Differentiating it and using P_u=partial_kappa L gives
kappa partial_u P_u=partial_u L_geom, the corresponding u Euler row.
For time-dependent T(u)=E+f(u)A with commuting E,A, the row becomes

    kappa partial_u P_u=partial_u L_geom-f'(u)A,
    chi=kappa partial_u kappa
        =[q(1+x)-2r-f'(u)A/2]/[s sqrt(Delta)],
    q=3V_3a²/2, r=V_3U_0a⁴.                             (F6)

All source, apparatus and interaction energies must enter T before
solving the branch.

A useful exact rearrangement for no apparatus is, with
N_exc=E-E_c and y=(1+kappa²)/a²,

    a_c y²-(3V_3/2)y+V_3U_0+N_exc/a⁴=0.                (F7)

The canonical E_c=n_s/240 and the full finite R² constant combine
consistently. Dropping E_c by hand would not give this relation.
Vacuum gives the lower de Sitter root
y_-=[m-sqrt(m²-4a_cV_3U_0)]/(2a_c), m=3V_3/2.

The effective critical anomaly projections are
rho_an=a_c(1+kappa²)²/(V_3a⁴) and
p_an=rho_an/3-4a_c chi(1+kappa²)/(3V_3a⁴).
Together with radiation N_exc/(V_3a⁴), any admitted apparatus rows,
and U_0, they obey the same homogeneous constraint and Ward identity.
These are exact identities of this selected commuting reduced model.
They do not solve spatial metric modes or unrestricted quantum fields.

The finite R²/Box-R removal and linked Casimir shift agree with the
action structure in Barvinsky--Kamenshchik, hep-th/0605132, §4--5.
Their Euclidean density/instanton construction is not imported as
our real-time initial state. Their restriction to minisuperspace is
also retained here.
