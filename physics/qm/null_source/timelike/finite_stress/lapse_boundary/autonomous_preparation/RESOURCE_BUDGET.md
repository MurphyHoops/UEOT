# AC. Sharper all-mode bounds and one fixed lower-cost instance

## AC1. Global derivative bounds proved without a numerical scan

Retain AB's r, v=5, X0=-3/2, T=1/2 and complete Gaussian P instrument.
Only the declared mass and initial width change between the two examples.

For y=1/[x(1-x)]>=4,
|r'|=(1/5)e^(4-y)y^(3/2)sqrt(y-4).
Its squared maximum occurs at y=3+sqrt(3) and equals
(36+24sqrt(3))e^(2-2sqrt(3))/25.
Use 1.73<sqrt(3)<1.733 and the positive Taylor lower bound
exp(1.46)>sum_(j=0)^6 (1.46)^j/j!>4.3.
It follows globally that ||r'||<.85.

Also r''=(1/5)e^(4-y)P(y),
P(y)=y^4-6y^3+6y^2.
The derivative with respect to y is -(1/5)e^(4-y)y q(y),
q(y)=y^3-10y^2+24y-12.
For y in [4,6], q''>0 and q(4)=q(6)=-12, hence q<0.
For y>=6, q'>=12, and
q(20/3)=-4/27<0<q(67/10)=663/1000.
Thus the only critical point on y>=4 is eta in (20/3,67/10).
The negative endpoint value of r'' is -6.4, and its positive maximum
is less than P(67/10)/(5 exp(8/3)).
P is increasing on this enclosing interval, and
exp(8/3)>sum_(j=0)^6 (8/3)^j/j!>14.
The resulting upper bound is <7. Therefore ||r''||<7 globally.

For a=1-r_*=4/5, these imply
c1=sup||theta'||_l2<.5,
c2=sup||theta''||_l2<4.5,
Bomega=sup_(k,sign)|omega_k'|<.48.
For example,
c2< [7+(.85)^2/a] pi/[4sqrt(3)a].
The differentiated vacuum sum satisfies
sup_K||e_K'|| <= 5(.85)r_*^3 zeta(5)/[32a^(7/2)]<.003, (AC1)
using zeta(5)<5/4. Define the scalar function
b(z)=[sqrt(1+z)+sqrt(1-z)-2]/2+z^2/8, so
e_K(x)=sum_(k<=K) k^3 b(r(x)/k^2).
Here b'(0)=b''(0)=b'''(0)=0. Taylor's theorem for b'(z),
with |b^(4)|<=15/[16a^(7/2)], gives (AC1).
This b is a scalar function, distinct from AB's number operator h.
It is a bound on the SAME subtracted e_K; no x-dependent vacuum
energy is discarded.

## AC2. Two independently checkable error bounds

AB's exact residual and endpoint correction are unchanged.
Using q1<5, q2<40 gives
||residual|| <=116 Delta_t+9/(M delta)+22/M.
The exact variance in AB implies
int_0^(1/2) Delta_t dt
 <=delta/(2sqrt(44))+sqrt(3)/(4Mdelta),
Delta_T<=delta/sqrt(44)+sqrt(3)/(Mdelta).
Adding the endpoint frame at c1 q1<=2.5 yields
epsilon <= (60.5/sqrt(44))delta
           +(31.5sqrt(3)+4.5)/(Mdelta)+11/M
        < 10delta+60/(Mdelta)+11/M.                    (AC2)

A further reduction uses the already proved q1<4.1, q2<40:
the localization coefficient is <95, the centered-derivative
coefficient is <2.05, and the connection contribution is
<19.225/M. The exact free variance and Jensen give
J=int_0^(1/2)Delta_t dt
 <=(1/2)sqrt(delta^2/44+1/(M^2delta^2)).
Therefore
epsilon <=95J+1.025sqrt(12)/(Mdelta)+2.05Delta_T+10/M.    (AC3)
For delta=5/(2sqrt(M)), M>=25/4, its coefficient of M^(-1/2)
is
(95/2)sqrt(25/176+4/25)
 +(41sqrt(3))/50
 +(41/20)sqrt(25/176+12/25) <30.
Thus
epsilon <30/sqrt(M)+10/M.                              (AC4)

The bounds are sufficient estimates for this family, not an optimized
physical lower limit. The limiting error tends to zero as M increases,
but its total energy grows as 12.5M; this is not a uniform finite-energy
classical-control limit.

## AC3. Fixed example used by the later apparatus entries

Select ONCE
M=10^12, delta=2.5*10^-6, v=5, X0=-3/2, T=1/2,
the same two coherent source codes and sigma=1/10.
Then epsilon<0.00003000001. The actual complete binary contrast obeys
d_actual>=d_cl-2epsilon>0.00233999998.                   (AC5)
The certificate uses the stronger actual interval for d_cl from AB.

The exact TOTAL spectral mean and variance of this preparation are
E_Z=1.25*10^13+1.46,
Var_Z=4.8*10^13+2.804.                                 (AC6)
More generally under this width scaling,
E_Z=25M/2+73/50 and Var_Z=48M+701/250.
Both quantities and the whole total-energy law are conserved by U_M.

These resources are finite and still large in model units.
No relation to laboratory kilograms, joules or seconds is supplied.
The mean energy cannot be omitted from a later gravitational source.
M=1,p=10 has not been verified; neither (AC4) nor this numerical example
changes that status. Geometry and local stress remain uncalibrated.

The actual k=1 source marginal's half trace distance from its free-evolved
coherent state is <=sqrt(3)/50+epsilon<.034672.
This allows a complete source-state change. It does not reinstate the
earlier fixed-bare-state extension that was excluded in the predecessor.
