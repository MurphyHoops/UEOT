# W. A common smooth past, a normal outgoing field and complete Gaussian readout

## W1. A specified preparation history from the same local field action

V rejects imposing the unchanged old Cauchy vacuum directly on a
different static lapse. It does not reject actual preparation
through a smooth metric history. Here choose, once,

 N(t,x)=1+epsilon eta(t)Y3(x),
 eta in C_c^infinity((0,T)), real, 0<=eta<=1,
 |epsilon|<sqrt(V)/11, V=2pi^2.                           (W1)

An explicit nonzero pulse is
eta(t)=exp[4-1/(s(1-s))] for 0<s<1, and zero otherwise,
s=2t/T-1/2. Its support is [T/4,3T/4], a compact subset of
(0,T), and its maximum is one. Each endpoint is flat to every
order. For the concrete comparison take T=.02 model conformal
time and |epsilon|<=.08. Neither is an SI experimental claim.

All histories share the SAME open ESU past and future slabs.
The same single ESU vacuum density is specified in the past.
No branch-dependent vacuum replacement is made.

The spacetime g=-N(t,x)^2dt^2+h is smooth, globally hyperbolic,
with compact Cauchy surfaces and uniform positive lapse.
Because h is time independent, its extrinsic curvature is zero;
R=6-2N^(-1)Delta N even for time-dependent N.
The actual canonical action therefore gives

 qdot=N p, pdot=-Q(t)q,
 Q(t)=-div(N grad)+N-Delta N/3.                           (W2)

The positive form bounds of U apply at every time.
The smooth normally hyperbolic KG Cauchy problem has a unique
global evolution E_eta(t,s) preserving the real symplectic form.
Hyperbolic energy estimates make it and its inverse bounded
on each Sobolev Cauchy space H^(r+1/2) plus H^(r-1/2) over
a finite interval. This is the actual solution map of (W2),
not a chosen abstract state transporter.

## W2. Same past state, genuine full-field late Gaussian channel

The ESU vacuum is Hadamard on the common past neighborhood.
Propagation of the Hadamard wavefront condition through the
smooth KG equation gives a pure Hadamard state on each entire
prescribed spacetime. On the common late ESU slab, its covariance
differs smoothly from the ESU vacuum in all Cauchy blocks.

Encode the Cauchy data by D^(1/2)q,D^(-1/2)p, D=sqrt(-Delta+1).
Let S be the encoded E_eta(T,0), and P0^+,P0^- the ESU frequency
projections. Pout^+=S P0^+ S^(-1).
The smooth late covariance difference implies that
Pout^+-P0^+ is a smoothing operator. Consequently the actual
off-diagonal Bogoliubov part is

 beta=P0^- S P0^+
     =P0^-(Pout^+-P0^+)S P0^+.                           (W3)

Since S is bounded on every Sobolev level, this beta is smoothing.
Thus D^r beta and beta D^r are Hilbert--Schmidt for every r.
This step uses the actual classical evolution, not just the
existence of some Hadamard state on the endpoint metric.

Shale implementability supplies a full-Fock unitary V_eta
realizing this symplectic scattering map. Its scalar phase
does not affect the exact normal channel

 Phi_eta(rho)=V_eta rho V_eta^dagger.                     (W4)

The outgoing state is the normal pure Gaussian density of
V_eta|0_D>. The channel exists for every normal input,
including entangled reference inputs. Hadamard regularity and
the moment conclusions below are proved for the specified
past vacuum, not for every arbitrary normal density.

A chosen positive-vacuum-overlap phase can define a normal
Gram kernel between pulse labels. This is a convention for
implementers. It does not derive the physical cross-history
Einstein-CTP phase from local covariant counterterms.
The pointwise-in-time old canonical pair generator is generally
not HS; no informal Dyson series for that generator is used.

## W3. All polynomial late free-energy moments are finite

Let H0=dGamma(D), Nop=dGamma(I) on the common late ESU Fock space.
The outgoing occupation n and anomalous covariance m have smooth
kernels. In particular, every D-weighted trace or HS norm of
these kernels used below is finite.

For the pure Gaussian vector let Z be its symmetric squeezing
kernel. Z is HS, ||Z||<1, and

 <exp(s Nop)>
 = det(I-Z^dagger Z)^(1/2)
   /det(I-exp(2s)Z^dagger Z)^(1/2)<infinity               (W5)

for sufficiently small positive s.
This proves all number moments, not exponential H0 moments.

For any positive integer r, the n-particle sector inequality
(sum_j D_j)^r <= n^(r-1) sum_j D_j^r gives

 H0^r <= Nop^(r-1)dGamma(D^r).                           (W6)

Cauchy--Schwarz reduces its expectation to a number moment
and the second moment of dGamma(A), A=D^r. Wick's rule yields

 <dGamma(A)^2>
 = (Tr A n)^2+Tr(A^2 n)+Tr(A n A n)
                      +Tr(A m A^T m^dagger),            (W7)

which is finite by smoothing. To justify unbounded operations,
first use the free D spectral projections and commuting number
cutoffs. In the D eigenbasis the Wick terms are nonnegative
absolutely summable terms; pass to the limit by monotone
convergence and the uniform finite bounds. These are auxiliary
moment cutoffs, not dynamically truncated Hamiltonians.

Thus the actual outgoing vector belongs to every D(H0^p),
p a nonnegative integer. All finite positive energy moments
are finite. There is no claimed numerical uniform energy
budget for arbitrary pulse families, no exponential-energy
moment, and no sharp local stress-variance conclusion.
This gives a valid preparation control for the finite-energy
failure in V, on its explicitly stated prescribed geometry.

## W4. A complete normal Gaussian readout, with a source energy cost

For a real smooth one-particle vector f (species included in
the one-particle space), set
Q_f=(a(f)+a^dagger(f))/sqrt(2), and choose sigma>0.
The bounded Kraus density

 M_z=(2pi sigma^2)^(-1/4)
              exp[-(z-Q_f)^2/(4sigma^2)]                (W8)

satisfies integral_R M_z^dagger M_z dz=I by the spectral theorem.
For every Borel B the map

 I_B(rho)=integral_B M_z V_eta rho V_eta^dagger M_z^dagger dz (W9)

is a normal completely positive instrument; I_R is trace
preserving. Every outcome is retained in this nonselective
description, and arbitrary reference extensions are permitted.
For the centered Gaussian output the readout is a centered
normal distribution with variance Var_out(Q_f)+sigma^2.

The nonselective reader is exactly the Weyl dephasing channel

 rho -> integral exp(-i lambda Q_f)rho exp(i lambda Q_f)
           Normal(0,1/(4sigma^2))(d lambda).             (W10)

A Weyl displacement shifts a by a constant proportional to
lambda f. Smooth f and Gaussian lambda moments preserve
all polynomial H0 moments of this prepared output.
Averaging the linear energy shift to zero gives the exact
source energy increase

 Delta <H0> = <f,Df>/(8sigma^2).                          (W11)

For a unit k=1 mode and sigma=1, this is 1/8 in model energy
units. It is not zero and cannot be discarded from a total
apparatus/energy account. The equality is a mean source
cost of this mathematical reader, not a calibrated work cost
of a fully specified gravitational apparatus.

An abstract Gaussian pointer with coupling exp(-iQ_f P_pointer)
realizes the instrument. A local autonomous stress-complete
pointer, its coupling controller and the source of the lapse
pulse have not been supplied. W therefore closes a genuine
same-past field preparation and complete mathematical instrument,
not the complete material apparatus or Einstein feedback loop.

## W5. Exact remaining boundary and checked primary sources

The actual in/out KG map, Hadamard state, normal late channel,
energy-domain conclusion and instrument above are analytic
objects. This entry has not proved convergence of the specific
time-dependent canonical finite-mode Hamiltonian regulator
used in T; U's static proof cannot simply be applied pointwise.
It also has not proved a differentiable old-Fock Hamiltonian
at all intermediate times, a locally renormalized nonlinear
two-branch phase, all momentum/tensor constraints or a solution
for the classical/quantum metric rather than prescribing it.

Primary results actually read and applied with the hypotheses
in W1--W3:

- Bar--Ginoux--Pfaffle, https://arxiv.org/pdf/0806.1036 ,
  Theorems 3.2.11--3.2.12: global smooth Cauchy evolution.
- Gerard--Wrochna, https://arxiv.org/pdf/1209.2604 ,
  section 8.2: Hadamard propagation from a Cauchy neighborhood;
  section 8.1, Remark 8.2: compact-slice smoothing and Shale
  equivalence. Equation (W3) supplies the actual-map bridge.
- Junker--Schrohe, https://arxiv.org/pdf/math-ph/0109010 ,
  Theorem 4.7(ii): the compact-Cauchy pure-state unitary
  equivalence criterion, consistent with the explicit argument.

The certificate checks the explicit pulse and Gaussian
normalization/dephasing/energy identities. These finite algebraic
checks complement, and do not formalize, the PDE/microlocal proof.

For this particular reader the calibration identity is also exact:
the commuting law of the final Q_f and its record has
E[(z-Q_f)^2]=sigma^2. Hence
sigma^2 Delta<H0>=<f,Df>/8.
This is an identity of this instrument, not a universal lower
bound for all instruments. The sigma->0 limit is not a finite-energy
exact readout. The continuous classical record is a normal
L1(R;trace-class) CQ density; it is not a fictitious trace-class
operator made of delta-normalized position eigenstates.
