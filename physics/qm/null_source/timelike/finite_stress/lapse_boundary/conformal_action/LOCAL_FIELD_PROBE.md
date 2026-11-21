# X. A local full-field probe, exact induced observable and retained control work

## X1. Actual coupled action and Green map

Take one source scalar phi and one probe scalar psi, both real
and conformally coupled, on a prescribed smooth background.
This is a new linear two-field comparison; it is not the
three-field nonlinear sigma apparatus or its geometry calibration.

 S0=-(1/2) integral sqrt(-g)[(grad phi)^2+R phi^2/6
                                      +(grad psi)^2+R psi^2/6],
 Sint=-integral sqrt(-g) r(x)phi psi.                    (X1)

The real smooth r has compact spacetime support. On the late
unit ESU slab P=-Box+R/6=partial_t^2+D^2. The exact coupled
operator is T_r=P I+R_r, R_r=[[0,r],[r,0]].
The fixed field rotation (phi+psi,phi-psi)/sqrt(2) diagonalizes
it into P+r and P-r, both normally hyperbolic. A unique coupled
advanced Green operator E_r^adv therefore exists.

For a probe spacetime test g supported after the coupling set,
the exact scattering pullback is

 (f_g,h_g)=(0,g)-R_r E_r^adv(0,g),
 U_r^dagger Q_p(g) U_r=Q_s(f_g)+Q_p(h_g).                 (X2)

The actual Cauchy map defines U_r below. This formula fixes the
observable selected by the interaction: f_g is not an arbitrary
chosen source charge. f_g and h_g-g are supported in
supp r intersect J^-(supp g). If this intersection is empty,
f_g=0 and this probe cannot supply a source record.

This applies the established Fewster--Verch scattering formula
with our P and signature convention. The minus sign and the
ADVANCED orientation are essential.

## X2. Full-field normality, complete instrument and calibration

Let the source be the late Hadamard Gaussian prepared in W
(or the ESU vacuum), and the probe initially an independent
ESU Gaussian vacuum. The actual doublet Cauchy evolution is
smooth and symplectic. On the future uncoupled slab the
propagated joint state is pure Hadamard relative to the free
doublet. The same Sobolev/smoothing argument in W proves
implementability on the FULL source times probe Fock space,
normality and every polynomial late free-energy moment.
The resulting unitary channel acts on arbitrary normal inputs
and references; the regularity/moment claims have the stated
Gaussian initial-state restriction.

Let the probe state have mean mu_g=<Q_p(h_g)> and
v_g=Var Q_p(h_g). Its induced source Weyl map is exactly

 (id tensor sigma_p)[U_r^dagger exp(it Q_p(g)) U_r]
       =exp(it mu_g-t^2 v_g/2) exp(it Q_s(f_g)).          (X3)

For the late probe Gaussian reader of width sigma in W,
the actual source instrument density is

 I_z(rho)=Tr_p[(I tensor M_z) U_r(rho tensor sigma_p)
                         U_r^dagger(I tensor M_z)],     (X4)

where M_z is the bounded Gaussian function of the actual
late Q_p(g). All z are retained. It is a normal complete CP
instrument, with a normal L1(R;trace-class) CQ output.
Its input-source effect density is

 E_z=(2pi nu_g^2)^(-1/2)
           exp[-(z-mu_g-Q_s(f_g))^2/(2nu_g^2)],
 nu_g^2=v_g+sigma^2.                                   (X5)

Thus its record is the source spectral law convolved with
exactly the probe and reader noises. The effective POVM does
NOT determine the post-state map: (X4) cannot be replaced
by the source Luders map sqrt(E_z)rho sqrt(E_z).
No QND claim follows. Joint source-probe backreaction during
U_r and all final outcomes remain in (X4).

## X3. A concrete nonzero transfer without a mode ODE run

Choose r(t,x)=lambda eta(t), spatially constant, with the exact
smooth pulse in W, duration T=.2 and lambda=.2.
This is a pointwise local Lagrangian over the ENTIRE compact
S3; it is not a small spatial detector. |r|<=.2<1 makes the
instantaneous two-field mode potentials k^2 plus/minus r
strictly positive for every k.

For the k=1 source/probe block, remove the known free rotation
R(t)=[[cos t,sin t],[-sin t,cos t]].
In interaction picture the off-diagonal 2 by 2 generator is

 B_sp(t)=[[sin t cos t,sin^2 t],
                       [-cos^2 t,-cos t sin t]],        (X6)

with norm one. Each interaction swaps source and probe.
Let L=|lambda| integral eta <= |lambda|T/2=.02.
For the late free-demodulated probe momentum, the source
row is (a_q,a_p), with first-order row
-lambda integral eta(t)(cos^2 t,cos t sin t)dt.
The actual source-row remainder is bounded by sinh(L)-L;
the probe self-row differs from (0,1) by at most
delta_even=cosh(L)-1.

On [3T/8,5T/8], eta>=exp(-4/3). Therefore

 |a_q| >= lambda (T/4)exp(-4/3)cos^2 T-[sinh L-L]>0.     (X7)

This certifies an ACTUAL nonzero finite-coupling record.
The input-source observable is a_q q_s+a_p p_s; it has
not been replaced by the pure q_s or by a stress charge.
The free-demodulated probe quadrature has a real smooth
late spacetime-test representative by the time-slice property.

For the initial probe vacuum,
(1-delta_even)^2/2 <= v_g <= (1+delta_even)^2/2.
With reader sigma=.1, add .01 to these endpoints to obtain
the exact certified interval for nu_g^2. This is a noise
variance in the chosen quadrature units, not a metric error.

## X4. Actual canonical cutoff convergence for this subcase

Spatially constant r(t) does not mix different S3 modes.
Hence the real finite-mode canonical scattering map, after
the free rotation is removed, is EXACTLY S_(k<=K) direct-sum
I_(k>K). It is a truncation of the actual full solution map,
not a modified spatial potential at the cutoff boundary.

The full beta is smoothing by X2, so beta_K -> beta in HS
and with every energy weight; alpha_K -> alpha strongly.
The positive-vacuum-overlap implementers consequently converge
strongly, and adjoints strongly, by the squeezed-vacuum and
Weyl coherent-vector argument in U.
Scalar phases cancel from channels and instruments.
Thus the actual canonical cutoff channels and complete bounded
instruments converge for every fixed normal input/reference.
For the k=1 readout the induced effect (X5) is already the
same at every K>=1, but the full source post-state still uses
the preceding channel limit.

This closes a cutoff gate for the spatially constant probe.
It does not prove W's general time-dependent lapse cutoff
limit or the same statement for general spatial r.
The physical cross-history scalar phase is addressed separately
in PROBE_PHASE, rather than inferred from channel convergence.

## X5. Retained lapse rows and total control work

Before setting the lapse to one, the interaction density is
-N sqrt(h)r phi psi. Hence

 Gamma_N,int=-sqrt(h)r phi psi,
 Gamma_r,int=-N sqrt(h)phi psi,
 Gamma_phi,int=-N sqrt(h)r psi,
 Gamma_psi,int=-N sqrt(h)r phi.                          (X8)

Its NN contact is zero, but Nr, Nphi and Npsi contacts are
nonzero. The full conformal source/probe rows are retained.
The interaction stress is T_int,mu nu=-g_mu nu r phi psi.
On the exact coupled equations, the improved total tensor obeys

 nabla^mu T_mu nu=-phi psi partial_nu r.                 (X9)

On ESU, H_r=H0,s+H0,p+integral r phi psi and
d<H_r>/dt=integral rdot <phi psi>.
The pointwise Ward equation is a classical local-action identity;
its quantum version requires the common local renormalization below.
The finite canonical cutoff has the exact integrated Hamiltonian
work identity. No arbitrary spatial cutoff is asserted to preserve
the unprojected pointwise local Ward equation.
The prescribed r supplies work. Deleting the probe or the
interaction energy would change the physical source.

At the quantum field level coincident T and phi psi must use
the SAME local renormalization. In Vassilevich's convention
D_Laplace=-(nabla^2+E), E=-R I/6-r sigma_x.
Relative to r=0, tr(E^2)/2 contributes r^2; the RE and total
derivative terms linear in r have zero internal trace. Thus

 delta a4=(4pi)^(-2) integral sqrt(g) r^2.               (X10)

An external-coupling vacuum functional/counterterm is needed.
A Lorentzian finite term c_r integral sqrt(-g)r^2 changes
both the phase and T_ct=c_r r^2 g, and contributes
2c_r r to the r equation. It cannot be deleted from either
the controller work or the gravitational source.

The terminal Gaussian reader acts only on the late probe.
Its nonselective action leaves the source marginal unchanged
at that final step, while increasing the total free-field
energy by <g_late,D g_late>/(8sigma^2).
Here g_late is the actual late one-particle quadrature profile,
not the induced f_g. In X3 it is a unit k=1 profile, so the
increase is 12.5 model energy units. The energy of a real
terminal controller has not been included.

Completed: a local covariant field interaction, its actual
full-field normal scattering and complete calibrated instrument,
a nonzero exact transfer and the constant-spatial cutoff limit.
Still open: an autonomous controller producing r, a physical
terminal reader, full stress-complete preparation, and joint
Einstein constraints/feedback. The fixed-background result is
not the nonlinear sigma model's old geometry calibration.

Primary sources actually checked:
Fewster--Verch, https://arxiv.org/pdf/1810.06512 ,
Eqs. 4.11, 5.2, 5.7--5.11 and Appendix D. Their polynomial
example explicitly leaves bounded effects to a completion;
the normal Fock and spectral-calculus instrument (X4) is
supplied here, not attributed to that polynomial algebra.
Vassilevich, https://arxiv.org/pdf/hep-th/0306138 ,
Eqs. 2.2 and 4.28 for the heat coefficient and E convention.
