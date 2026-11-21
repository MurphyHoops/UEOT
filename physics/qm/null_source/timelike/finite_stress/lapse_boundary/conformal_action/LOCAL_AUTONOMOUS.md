# I. Quantized homogeneous controller, source and probe from a local action

## I1. What is quantized, and what is not

Reuse the CLASSICAL local three-scalar action of total_source/AUTONOMOUS
and its nonflat field-space metric in FIELDSPACE:

 S=-1/2 integral sqrt(-g)[(grad chi)^2+(grad phi)^2+(grad psi)^2
                         +2 k_c(chi) grad phi.grad psi].

Its positive target metric has eigenvalues 1,1+k_c,1-k_c.
Here all three homogeneous scalar degrees of freedom are quantized
together. Their inhomogeneous modes and their loops are NOT included.
The n_s=2 conformal scalar sector and its declared anomaly remain a
separate sector. Thus this is the homogeneous quantum truncation of a
local covariant classical action, not a renormalized interacting
four-dimensional quantum field theory. A spatially homogeneous pulse
on S³ is not a bounded-spacetime-region probe coupling.

With V=2pi² and retained conformal lapse N, homogeneous Hamiltonian is
N K0/(V a²), where K0=-Delta_G/2 on L²(R³,sqrt(det G)d³X).
Select its nonnegative Friedrichs realization. Uniform ellipticity
and bounded smooth metric coefficients give the complete positive
form, including the source/controller/probe interaction.

Fix u_*=.55, a_*=Aexp(u_*), s_*=sqrt(V)a_*. Make the ONE fixed
canonical change Q=s_*X, P=pi/s_* and choose k_c(chi)=k(s_*chi).
Then K0=s_*² K and the complete conformal energy is

 T(u)=H_c+f(u)K, f(u)=exp[-2(u-u_*)].                    (I1)

There is no time-dependent field rescaling or dropped endpoint.
Every controller/source/probe energy is included before solving the
critical branch. Here K is conserved, T'=-2fK, and the scalar projections

 rho_app=p_app=fK/(V a⁴)

are stiff matter, not a proper-rest dust apparatus. With the conformal
source, rho=(H_c+fK)/(Va⁴), p=(H_c/3+fK)/(Va⁴); their Ward identity
rho_u+3(rho+p)=0 is exact. The critical chi row includes +fK in its
numerator in (F6). Primitive phase-space contacts are
S_NN=0, S_Nu=2fK delta, S_uu=-4NfK delta.
For prescribed paths the exact homogeneous influence is
Tr rho exp[-i H_c Delta tau_0-iK Delta tau_f]; all mixed covariances
of H_c and K must be retained. This is not a full spatial CTP kernel.

## I2. A fixed smooth coupling and a positive self-adjoint operator

Let b_L(x)=cos²(pi x/(2L)) for |x|<=L and zero outside, L=49.
Let r be the normalized even C-infinity mollifier proportional to
exp[-1/(1-x²)] for |x|<1, zero otherwise. Its derivative L1 norm is
less than 3 (r is unimodal, ||r'||1=2r(0)<3).
Choose k=.01(b_49*r), once and for all. Thus

 support k subset [-50,50], 0<=k<=.01, integral k=.49,
 k1=.01pi/98, k2=.01pi²/(2*49²), k3<=3k2.

The k3 bound uses the weak bounded second derivative of b_49 and r'.
The half-density unitary J=(1-k²)^(1/4) maps to flat L²(d³Q). There,

 K=H0+V_P(Q_chi), H0=(P_chi²+P_phi²+P_psi²)/2,
 V_P=[k²(P_phi²+P_psi²)-2kP_phi P_psi]/[2(1-k²)]+V_g,
 V_g=J''/(2J)
    =-(k'²+kk'')/[4(1-k²)]-3k²k'²/[8(1-k²)²].         (I2)

The potentially negative V_g does not negate positivity of the
unitarily transported Laplace-Beltrami operator. P_phi,P_psi commute
strongly with K. On compact bands |p_phi|<=p_s, |p_psi|<=p_r define
d0=1-k0², S=p_s²+p_r², P=p_s p_r, k0=.01, and

 Cg0=(k1²+k0k2)/(4d0)+3k0²k1²/(8d0²),
 Cg1=(3k1k2+k0k3)/(4d0)
       +(k1²+k0k2)k0k1/(2d0²)
       +3(k0k1³+k0²k1k2)/(4d0²)+3k0³k1³/(2d0³),
 C0=(k0²S+2k0P)/(2d0)+Cg0,
 C1=k1[k0S+(1+k0²)P]/d0²+Cg1.                          (I3)

These are uniform sup bounds on V_P and its clock-coordinate derivative.

## I3. An explicit normal incoming preparation

Use normalized cosine momentum packets of full width w:
phi_w(p)=sqrt(2/w)cos(pi(p-p0)/w) inside its band, zero outside.
The controller has p0=v=10000, initial center Q_chi=-100.
Its momentum phase is exp(100 i p_chi). Source states may be arbitrary
normal states on the two declared source momentum bands, including
coherences and arbitrary normal reference systems.

For the controller envelope,

 B0=2sqrt(2w)/pi, B1=2sqrt(2/w), B2=4pi sqrt(2)/w^(3/2).

B2 includes BOTH derivative jumps at the momentum edges.
For negative free time t, two integrations by parts bound the norm
inside the coupling support by
sqrt(50/pi)[B2/d(t)²+3|t|B1/d(t)³+3t²B0/d(t)^4],
where d(t)=50+p_min|t|. Cook integration therefore gives

 e_in=C0 sqrt(50/pi)/50
          [B2/p_min+3B1/(2p_min²)+B0/p_min³].          (I4)

It proves existence on this dense compact-momentum class of
Omega_in=strong-limit_(t->-infinity) exp(itK)exp(-itH0).
Isometry follows from the unitary approximants; extension by density
and time translation give K Omega_in=Omega_in H0 spectrally.
No asymptotic-completeness theorem is needed or claimed.

W_in applies Omega_in to source tensor the fixed controller/probe
packets. This is an isometric normal preparation, within e_in in
operator norm of the stated product preparation on the source code.
The correlations are small but not zero. W_in has NOT been produced
by an autonomous earlier physical device.

## I4. Actual propagation, finite passage and fixed probe phase

For the admitted total spectrum, actual u propagation is

 U=exp[-i Phi(K)], Phi(K)=integral_J h(u,E_c+f(u)K)du.   (I5)

The conformal source is in its vacuum in this apparatus example.
For a COMMON admitted K interval [K_-,K_+] with width W and midpoint K_*,

 tau_*=integral_J f/kappa(u,E_c+fK_*) du,
 B_Phi=integral_J sup f²/[2kappa³ sqrt(Delta)]du,
 e_geo=W² B_Phi/8.                                     (I6)

Spectral Taylor calculus gives operator norm error at most e_geo from
the scalar-phase times exp(-i tau_* K) comparison. The actual geometry
is not frozen: (I5) remains the exact unitary used in the instrument.

In the interaction picture of H0, compare V_P(Q_chi+tP_chi) to the
scalar-clock trial V_P(-100+vt). The spectral theorem and Lipschitz
bound C1, followed by Duhamel, give

 e_dyn <= tau_* C1 sqrt(pi²/w_chi²+tau_*² v_chi),
 v_chi=w_chi²[1/12-1/(2pi²)].                           (I7)

This is uniform on the complete source/probe momentum bands, including
references. It uses the actual controller variance, not a sharp clock.
If tau_*>.015 the trial crosses the whole support. Its phase is

 -(1/v)[A2(p_phi²+p_psi²)/2-A1 p_phi p_psi+Ag],
 A1=integral k/(1-k²) in [.49,.49/.9999],
 A2=integral k²/(1-k²), Ag=integral Vg.

Prepare the ONE probe momentum chirp
exp[i(tau_*+A2/v)p_psi²/2].
This cancels the trial free/self-quadratic probe phase for either
input code, leaving probe position shifted by -A1 p_phi/v.
Parameters and chirp are chosen once for the common band; no outcome
or source-dependent retuning occurs. The trial is used only for an
error estimate; reflection and every other channel in actual U remain.

For the cosine probe of width w_p, the one-sided position tail beyond
distance d is bounded by beta=16pi/[3(w_p d)^3].
It follows from the second-derivative-plus-edge norm and integration
of |x|^-4. Thus total probability errors are bounded by

 epsilon=beta+e_in+e_dyn+e_geo.                         (I8)

## I5. Two useful records, with a genuine total-energy-class calibration

SIGN example:
source bands [999,1001] and [-1001,-999], w_chi=10,
probe band [-50,50], w_p=100, threshold Q_psi=0.
Both source classes have the SAME total K spectral law for reflected
source input packets. The guaranteed displacement is d=.048951.
The common K band is [50449013,50552263].
The output contrast is >=1-2epsilon. This is a source-sign record,
not an energy record.

ENERGY example:
source LOW band [-1,1], HIGH band [999,1001],
w_chi=24 (9988<=p_chi<=10012), probe band [-110,110], w_p=220.
The same action and coupling are retained. Choose Q_psi<-.0245 as HIGH.
The probe distance from threshold is at least .02445 for either code.
The full incoming free-energy bands are

 B_low=[49880072,50126122.5],
 B_high=[50379072.5,50627122.5].

They are disjoint. Use their COMMON convex hull in (I6), including
both outcomes and all interactions. Spectral intertwining gives

 1_(B_high)(K) W_in=W_in P_high,
 1_(B_low)(K) W_in=W_in P_low.                           (I9)

Actual U commutes K, so this remains true immediately BEFORE readout.
This is a calibration of a pre-read TOTAL gravitating energy class
on the prepared range, not merely an arbitrary source-label proxy.
It is not a continuous-energy measurement or a record of the old
minimal-model C_source.

The uniform effect bound is ||E_read-P_high||<=epsilon.
It applies to every normal source-code state and normal reference.
Initial record contrast is at most 2e_in; the much larger final
contrast is generated during actual finite-u propagation. The
certificate checks the band admission and all terms with outward
interval arithmetic; no trajectory ODE is used.

## I6. Complete normal instrument and all retained energy

Let Pi project onto the admitted K hull, the stated source-band union
and probe momentum band. Do NOT project onto positive outgoing
controller momentum. Define F_high=Pi 1_(Q_psi<threshold) Pi and
F_low=I_Pi-F_high, L_j=sqrt(F_j). The complete instrument is

 rho -> sum_j |j><j| tensor L_j U W_in rho W_in* U* L_j.

It is normal and retains every record. It preserves the physical
band. L_j commute P_phi, so the complete source momentum law is
unchanged nonselectively; source coherences generally change.
The effects generally do NOT commute K: the terminal reader is an
abstract compressed joint observable, not an energy-conserving
autonomous device. Its work and its own gravitational source remain
open. Equation (I9) calibrates pre-read energy, not post-read conservation.

Because K intertwines with H0, all TOTAL energy moments on W_in are
finite and exactly the free-spectral moments of the three packets.
For a cosine packet, v2=w²(1/12-1/(2pi²)) and
v4=w⁴(1/80-1/(4pi²)+3/(2pi⁴)):
mean(p²/2)=(p0²+v2)/2,
var(p²/2)=p0²v2+(v4-v2²)/4.
Independent packet variances add; mixed code populations add their
between-code variance as well. These are not separate, independently
assigned interaction/kinetic noises. Stiff apparatus energy enters
rho,p and the SAME critical operator constraint throughout.

This closes a specified homogeneous normal quantum propagation and
calibrated bounded-record problem derived from a genuine local action.
It leaves autonomous preparation/readout, full interacting field
renormalization, spatial metric constraints and physical unification open.
