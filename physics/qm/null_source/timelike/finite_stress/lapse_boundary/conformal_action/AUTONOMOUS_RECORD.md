# AA. A finite-time source record in the actual full-field autonomous model

## AA1. Same Hamiltonian, explicitly different preparation

Use the exact self-adjoint H, actual H_K and counterterm scheme of Z,
with M=1, c_r=0 and r(x)=.2 exp[4-1/(x(1-x))] on (0,1), zero outside.
No prescribed r(t) is inserted.

This test changes Z5's outside-coupling packet to a packet already
inside the interaction region. Put b(x)=sqrt(630)x^2(1-x)^2 on (0,1),
zero outside. The k=1 source oscillator is the free coherent state
with <q_s>=+q0 or -q0, <p_s>=0, both quadrature variances 1/2.
The k=1 probe is vacuum. All k>=2 fields are in the true x-dependent
dressed vacuum W_tail(x)|0>. Denote the two full vectors by Psi_+,Psi_-.

Their common environment (controller, probe and all higher source/probe
modes) is a fixed normal vector. Thus the variable input system can
be the source k=1 mode, with a genuine Stinespring CP instrument for
arbitrary normal low-mode/reference inputs. The full source Fock space
is not asserted independent of the full probe/controller environment.

High modes are correlated with the controller; this is not X's product
preparation or a proof of autonomous preparation from a remote past.
The coherent +/- source states are not orthogonal.
The total-H spectral distributions of these two inputs are IDENTICAL:
joint parity of the two low modes connects them and commutes with H.
The following record measures source quadrature sign, not total energy
or a geometric constraint charge.

## AA2. Actual input domain and a uniform energy budget

The envelope and its first derivative vanish at both endpoints:
b is H2, with int b^2=1 and int |b'|^2=12.
The tail squeezing coefficients and their first two x derivatives
are square summable uniformly. On vacuum, A^2|0> is also finite.
Consequently W_tail,K|0> converges in C2 on this packet's support.
The actual finite-K vectors Psi_+,K/Psi_-,K converge strongly,
and H_K Psi_+,K / H_K Psi_-,K converge strongly. The already established
strong resolvent limit identifies the full inputs as elements of D(H).
No D(H^2) membership is used.

For y=1/[x(1-x)]>=4,
|r'|=.2 exp(4-y)y^2|1-2x| <=16*.2=:R1=3.2,
because y^2 exp(-y) decreases for y>=4.

The vacuum connection contribution to the kinetic energy is
sum_tail(theta'_j)^2/(4M), bounded by
R1^2 pi^2/[192M(1-r_*)^2]=pi^2/12.

An essential cancellation must be kept. The low dressed energy
expectation is 1+q0^2/2-E_ground,low. Its part of e_K is
E_ground,low-1+r^2/8. Their sum is q0^2/2+r^2/8;
the remaining vacuum-energy tail is nonpositive.
Therefore every actual K and both full inputs obey

 <H_K>, <H> <= Ebar
      =6+q0^2/2+r_*^2/8+R1^2 pi^2/[192(1-r_*)^2].      (AA1)

Take q0=1. Let e_abs be Z's proved uniform |e_K|,|e| bound.
Eplus=Ebar+e_abs+1 controls the actual low bare Hamiltonian
and controller kinetic energy throughout evolution by total-H
energy conservation.

## AA3. An energy-form Taylor estimate, with all high modes retained

Let P=p_probe,1, Q=q_probe,1, Zf=Q+r(x)q_s and F=sin(sP).
At every actual finite K,

 F'=i[H_K,F]=-(s/2){Zf,cos(sP)},
 Zf'=P+r p_s+{p_x,r'}q_s/(2M),

 {Zf,{Zf,sin(sP)}}=4 Zf sin(sP) Zf+s^2 sin(sP).

Zf' commutes with cos(sP), so the second weak commutator is

 F''=-s Zf' cos(sP)-s^2 Zf sin(sP) Zf
                                      -s^4 sin(sP)/4.  (AA2)

The low potential is [Zf^2+(1-r^2)q_s^2]/2. Hence

 <Zf^2> <=2Eplus,
 <q_s^2> <=2Eplus/(1-r_*^2),
 <P^2+p_s^2> <=2Eplus,
 <p_x^2> <=2M Eplus.

The controller anticommutator is bounded in its quadratic-form
expectation by Cauchy--Schwarz. No independent r'' cost appears.
These estimates give, uniformly in K and actual time,

 |d^2<F>/dt^2| <= Cs,
 Cs=|s|sqrt[2(1+r_*^2)Eplus]
       +[2|s|R1/sqrt(M(1-r_*^2))+2s^2]Eplus+s^4/4.     (AA3)

Here is the domain justification for using (AA3). At finite K,
the smooth semibounded elliptic Schroedinger Hamiltonian has its
usual smooth compact/oscillator operator core. Translation generated
by P changes H only by a linear low-mode form plus a scalar.
That linear term is infinitesimally H-bounded, so F preserves D(H).
The first commutator maps the H form domain continuously into Hilbert
space. Compute the second weak commutator on the operator core;
the identity i(<Hu,Gv>-<Gu,Hv>) extends it to D(H), and (AA3)
gives its continuous extension as an energy-bounded form.

Use R_epsilon=(I+epsilon(H_K+C0))^(-2), where H_K+C0>=0.
Sandwich F, its first commutator and this second form with R_epsilon.
R_epsilon commutes with H_K and contracts the positive form norm.
The squared resolvent maps Hilbert space into D(H_K^2), so the
regularized commutator products have the required operator domains.
The regularized bounded commutator identities give the fundamental-
theorem-of-calculus Taylor bound. Let epsilon decrease to zero,
using the same conserved energy bound. This proves

 |<F>_t-<F>_0-t<F>'_0| <= Cs t^2/2                    (AA4)

for these inputs without assuming D(H^2).

Finally use the moving initial vectors and actual U_K(t) strong limit.
F is bounded, all initial slopes are the same, and Ebar/Cs are uniform.
Thus the whole inequality (AA4) passes to the true full-field H.
No high-mode classical substitution or finite-matrix extrapolation
has occurred.

## AA4. A complete bounded record and one numerical positive time

The probe momentum Gaussian reader of width sigma, followed by
the stochastic binary score w(z)=[1+sin(sz)]/2, has a complete
binary effect on the probe

 E=[I+exp(-sigma^2 s^2/2)sin(sP)]/2.                    (AA5)

All z outcomes are retained before this optional complete two-outcome
postprocessing; there is no success-only filtering.
The two inputs have exactly the same initial outcome probability 1/2.
Their actual initial slope difference for F is

 (<F>_+'-<F>_-')_(t=0)
       =-2s q0 exp(-s^2/4) r_eff,
 r_eff=int |b(x)|^2 r(x) dx.

The central packet mass is exactly

 int_(1/4)^(3/4)630x^4(1-x)^4 dx=59123/65536.

On this interval r>=.2 exp(-4/3), so
r_eff>=r_lo=.2 exp(-4/3)59123/65536>0.
Combining BOTH Taylor remainders with (AA5) yields

 |p_+(t)-p_-(t)| >= exp(-sigma^2 s^2/2)
       [s q0 exp(-s^2/4)r_lo t-Cs t^2/2].              (AA6)

Select once q0=s=M=1, sigma=.1 and t_*=.0004.
The companion outward-interval certificate proves the bracket
positive and gives the actual numerical lower bound.
t_* is ESU model time, not seconds; this is a small contrast,
not a high-precision or optimized measurement.

## AA5. Momentum-reader energy, source scope and remaining gate

This is a P reader, so its backaction is derived anew.
For V_l=exp(-i l P), V_l^dagger Q V_l=Q+l and

 V_l^dagger H V_l=H+l Zf+l^2/2                         (AA7)

as a closed form. The r q_s contribution in Zf is essential.
The uniform <Zf^2> bound gives domain preservation.
Gaussian l of variance 1/(4sigma^2) therefore gives the exact
nonselective total-energy increase 1/(8sigma^2)=12.5.
The terminal mathematical reader still requires an external physical
energy supply; no energy-conserving realization of that reader is
asserted. The binary postprocessing adds no extra quantum operation.

Completed in ONE fixed model: semibounded autonomous full-field
evolution, legitimate correlated input, complete normal instrument,
actual finite-time source-sign probability separation, and total-system
reader energy backaction. Open: physical construction of the initial
correlations, pulse tracking from the outside packet, efficient finite
resource readout, local four-dimensional control/reader fields,
local stress/Hadamard properties of operator-valued control, and
self-consistent quantum Einstein constraints. Equal total-energy
spectral laws explicitly rule out interpreting this particular
contrast as a total-energy or geometry-charge calibration.
