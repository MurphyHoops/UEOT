# The full AE density constraint at the same static state

## 1. A degenerate first variation

Use the original two minimal massless fields, fixed M2/U0/AE prescription and
the common incoming-state/occupation transport of ../nonlinear_history/KERNELS.md.
Put a=A exp(u), h=Theta u and V=Theta^2 u+h^2. All formulas here refer to this
contract; changing occupation, controller energy, or a joint Cauchy state is an
additional source direction.

The bare energy of a mode is
e=[Theta^2 W/2-Theta(hW)+2 omega^2 W]/(2 omega).
Since W_1=2 V/(Theta^2+4 omega^2), its linear dynamic part vanishes:
(Theta^2/2+2 omega^2)W_1-Theta h=V-V=0.
The density subtraction coefficients E1,E3 and local H1,H3 have no linear
dynamic jet. The indispensable dynamic logarithm ell=ell0+2u gives
delta r_an=-u/32. Consequently
\[
 \delta\rho_{\rm geom}
 =-[6\rho_z+4\rho_{\rm vac}+4\rho_{\rm th}
       +(16\pi^2 A^4)^{-1}]u
 =-3(\rho+p)u=-3u/A^2 .
\]
The last equality uses BOTH frozen static Einstein equations. The Einstein
density side has the same variation. Thus the full first-order Hamiltonian
constraint for an additional source is
\[
                    \boxed{\xi_{\rho,\rm total}=0}.
\]
An independent density fluctuation cannot be accommodated by merely selecting
a different linear radius or fast/slow metric amplitude within this state
transport. This is an obstruction in the specified tangent space, not a ban
on every possible gravity/state initial condition.

An independent static check uses x=a^2 and
\[
 \rho(x)=U_0+M^2\mu/(2x^3)
       +[2B(x)-1/(4\pi^2)+Jn]/x^2,\quad
 B'(x)=-1/(64\pi^2x).
\]
Then x rho'(x)=-3(rho+p)/2, and at the static root
d[3/(2x)-rho(x)]/dx=0. The checker verifies the derivative identity rather
than fitting nearby parameter roots.

## 2. Necessary quadratic scale for changing the mean source

On the frozen complex E4 ball ||u||<=0.1 define
\[
 E(u;\delta m)=h^2+1-\tfrac23 a^2\rho(u)
              -\kappa\,\delta m\,e^{-4u},\qquad
 \kappa=M^2/(3A^4)>0.23.
\]
Here delta m is a change of the zero-mode mean parameter mu, not a measured
sharp value of an unmeasured quantum operator. On this ball E(0;0)=DE(0;0)=0.
The frozen analytic bounds give x rho_z<0.6, x U0<1.01, x>6e9, n<0.02,
a complete vacuum density bracket <7 and ||e2||<2 as follows.
These two bounds are derived within the original E4 analytic domain and
positive-frequency spectrum; they are not claims about arbitrary C4 functions.
For M=.11 and omega2^2=3, the frozen W-series estimates give
||W||<=1+M/[6(1-M/3)]<1.02 and
||Theta^2 W||<=2M/(1-M/3)<.23.
All nonzero frequencies exceed 1, so ||Theta W||<.23, while ||Theta h||<=.1.
The complete energy formula then gives
||e2||<(.23/2+.1*1.02+.1*.23+6*1.02)/(2sqrt(3))<2.
Also ||Theta V||<=.12, ||E1||<=.505 and
||E3||<=1/8+.0025+.11^2/8+.01*.11/4+.1*.12/4=.1322875<.133.
Together with the frozen subtracted mode-sum bound <1 and ||r_an||<1,
the density bracket is bounded by 1+.505+.133+1+4<7. Hence
\[
 \|E(u;0)\|\le1.01+\tfrac23[
 .6 e^{.4}+1.01e^{.2}
 +7e^{.2}/(2\pi^2x)+8n e^{.2}/(\pi^2x)]<3.
\]
Cauchy's estimate on the Banach-valued analytic map, with its constant and
linear terms zero, gives for t=||u||<=0.01
\[
 \|E(u;0)\|\le {3t^2\over(0.1)^2(1-10t)}.
\]
After evaluation at any chosen slice in the analytic domain, any compatible
datum with 0<t<=0.01 obeys
\[
 |\delta m|\le {3e^{4t}\over\kappa(0.1)^2(1-10t)}t^2
                      <1510t^2 .
\]
At t=0 the equation instead gives delta m=0 exactly; a strict 0<0 is not asserted.
If the entire old u00=0 incoming history must solve E identically, its constant
term already forces delta m=0; the finite-slice bound does not bypass this.
This is an E4-norm necessary bound; it is not a pointwise lower bound on a
metric signal, an existence theorem, or a stability theorem. A constant
nonzero delta m cannot share the unchanged all-past static solution without
additional state/geometry data. An initial-slice obstruction does not itself
construct a common past.

## 3. What a difference of noise kernels does not establish

For a classical/central random initial vector X with finite second moments,
L X=0 almost surely iff L E[X]=0 and L Sigma L^T=0. Positivity then also
forces the covariance of L X with every component to vanish.

A vanishing DIFFERENCE of density noise between two preparations does not
establish this absolute criterion for either preparation. The NOON direction
below removes a new density-noise difference, but leaves the full baseline
density noise, state-geometry correlations and quantum initial constraints
to be supplied. A positive auxiliary Gaussian covariance is not by itself a
legal joint quantum state. See RESPONSE.md and INITIAL_CORRELATIONS.md.

For the actual product zero/high input, even the spatially averaged density
has the strictly positive variance
\[
 {\rm Var}\,\bar\rho={M^4\over4A^{12}}{\rm Var}(S_0)
             +{6n(n+1)\over\pi^4 A^8}>0,\quad
 {\rm Var}(S_0)=4rL+4r^2+3/16 .
\]
The NOON off-diagonal changes neither term. Thus the specified homogeneous
linear random extension with only this geometric/state tangent has no
absolute constrained baseline: its independent density noise is nonzero
while the linear density constraint demands zero. This does NOT invalidate
the exact deterministic semiclassical mean solution, which has no stochastic
xi term. New state/device directions, nonlinear initial compensation or an
explicit quantum-geometric law are additional physical contracts.

The necessary E4 bound also does not give a metric lower bound for NOON:
that pair has delta m=0. In the original u00=0 incoming family, u,h tend to
zero in the static past. A fixed delta m !=0 would then leave
E -> -kappa delta m, ruling out an unchanged on-shell static past within
that family.

The relation to linearization stability of Einstein-static backgrounds is
contextual only; the identities above are derived for this specific AE model.
Reference: Losic and Unruh, arXiv:gr-qc/0408011.
