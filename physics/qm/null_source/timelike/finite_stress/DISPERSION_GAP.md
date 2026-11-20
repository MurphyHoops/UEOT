# A nonzero classical-dispersion comparison cost

The following bounds apply to the declared model. The conditional-ratio
averages in sections 1-3 are probability-weighted diagnostics over the
conserved P spectral label. Section 5 separately proves a linear mean
of a declared comparison form. Neither is an already constructed
laboratory record.

## 1. Positivity forces a nonzero conditional kinetic fraction

At the critical point let h=(2-S-S*)/4, so 0<=h<=1 and 4gamma=q.
For a conditional normal geometry state sigma_P of finite <v>, define
\[
 m(P)={\langle\sqrt v\,h\,\sqrt v\rangle_P\over\langle v\rangle_P}.
\]
Negative mean H_P and the positive matter term give
\[
 m(P)\ge\inf_{v>0}
 \left[1-{3\over2U_0}v^{-2/3}
              +{|P|^2\over2V_0U_0}v^{-2}\right].
\]
For P nonzero the minimum is attained at
v^(2/3)=|P|/sqrt(V0), giving
\[
 m(P)\ge b(P):=[1-\sqrt{V_0}/(U_0|P|)]_+.
\tag{34}
\]
For P=0 use the bound zero. The inequality permits arbitrary geometry
correlations; it is not restricted to our packet ansatz.

The volume-reweighted density tau_P=sqrt(v) sigma_P sqrt(v)/<v>_P
is normal. Since h has no endpoint eigenvectors on the half line,
0<m(P)<1. We use conservative non-strict inequalities; no sharp optimum
or attainable lower bound is claimed.

## 2. Keep the complete Gaussian tail

Set r_crit=1/(M2 U0^2), r_hi=1+sqrt(3)/2 and choose zeta=10^-12.
In the upper-radius branch (probability 1/2), the Gaussian noise ball
\[
 |\xi|\le\sqrt{K_2}\,d_\xi,\qquad
 d_\xi=\sqrt{\log(1/\zeta)/\nu_0}
\]
has probability 1-zeta. The reverse triangle inequality gives
|P|/sqrt(K2)>=sqrt(r_hi)-d_xi. Thus on an event of probability
p_*=(1-zeta)/2,
\[
 b(P)\ge b_*=
 1-{\sqrt{r_{\rm crit}}\over\sqrt{r_{\rm hi}}-d_\xi}>0.
\tag{35}
\]
All events, including the complementary Gaussian tail, remain in the
state. Their contribution to this nonnegative diagnostic is only dropped
when establishing a lower bound. In particular
E_P m(P)>=p_*b_* and E_P m(P)^2>=p_*b_*^2.

## 3. Declare the reference before comparing it

Define a principal quadratic lattice-dispersion reference by
\[
 K_{\rm ref}=4\gamma\sqrt v\,(\arcsin\sqrt h)^2\sqrt v,\quad
 K_{\rm poly}=4\gamma\sqrt v\,h\sqrt v.
\tag{36}
\]
This is a specified bounded-function-of-h quadratic form. It is not
silently equated to a global self-adjoint canonical p_v^2, the old AE
Hamiltonian, or a measured metric error.

For 0<=x<=1,
\[
 (\arcsin\sqrt x)^2
 ={1\over2}\sum_{n\ge1}{(4x)^n\over n^2{2n\choose n}}.
\]
All coefficients are positive. Hence
Delta(x)=(arcsin sqrt(x))^2-x is convex and
\[
 \Delta(x)\ge p_4(x):={x^2\over3}+{8x^3\over45}+{4x^4\over35}.
\tag{37}
\]
Jensen for tau_P gives
\[
 d(P):={\langle K_{\rm ref}-K_{\rm poly}\rangle_P
                    \over4\gamma\langle v\rangle_P}
 \ge\Delta(m(P))\ge p_4(m(P)).
\]
For m(P)>0 the relative difference is d(P)/m(P). The lower-bound
function p4(x)/x extends continuously by zero at x=0; no zero limit
for the actual ratio d(P)/m(P) is inferred from m(P) tending to zero.
Both p4 and this extension of p4(x)/x are increasing on nonnegative x. Therefore
\[
 E_P d(P)\ge p_*p_4(b_*),\qquad
 E_P[d(P)/m(P)]\ge p_*p_4(b_*)/b_* .
\tag{38}
\]
The certificate evaluates these as outward intervals from frozen data.

Neither average in (38) can be replaced by a total-volume-weighted ratio
without another argument. There is also no conversion here into an
instrument signal-to-noise ratio.

## 4. Implication for this route

The critical finite-source construction passes its domain test, but it
cannot make the declared quadratic-reference difference arbitrarily
small while preserving the original P law and positive dust. In
addition, rho_c=U0 is a new macroscopic density relation. These facts
prevent signing off restoration of the old mean geometry or full GR/AE
history merely from normality and finite stress.

## 5. A genuine linear mean residual in the same state and time window

The ratio averages above are not needed to obtain a linear observable
bound. Positivity of the parity kinetic form gives, conditionally on P,
\[
 0\ge\langle H_P\rangle
 \ge-{3V_0\over2}\langle v\rangle_P^{1/3}
                  +{|P|^2\over2\langle v\rangle_P},
\]
so V(P)=<v>_P >= (P2/(3V0))^(3/4). Let
r_*=(sqrt(r_hi)-d_xi)^2. The same high-branch event in (35) now yields
\[
 \boxed{\langle\Delta K\rangle\ge
 q\,p_*\left({K_2r_*\over3V_0}\right)^{3/4}p_4(b_*)>0.}
\tag{38a}
\]
This is a genuine linear mean:
<Delta K>=q Tr[(sqrt(v) rho sqrt(v)) Delta(h)], finite whenever <v>
is finite. It does not interchange probability and volume weights.

Keep the same joint state, proper-dust lapse, and E (or p after the
normal clock lift); change only the kinetic comparison form.
Define only a Hermitian comparison form h_ref=h_poly-DeltaK; no new
self-adjoint reference dynamics is assumed. A changed state or clock
would be a different comparison contract. In the physical state,
E=-H_poly, so
\[
 \langle E+h_{\rm ref}\rangle=-\langle\Delta K\rangle.
\tag{38b}
\]
All premises (the full P law, negative spectral support and finite
volume) hold throughout each finite time window of the constructed
history. The same mean bound survives the normal clock average,
where <p+H_poly>=0. This is a uniform nonzero integrated constraint
mean for the declared quadratic reference form. It is not a local
Einstein/AE residual, an RMS bound, or a proof that the reference has
its own complete quantum dynamics.
