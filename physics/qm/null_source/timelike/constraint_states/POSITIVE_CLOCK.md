# A normal finite positive-energy clock without discarding the source tail

This construction supplies an explicit approximate source/clock constraint
model on the original static source Hilbert space. It is not an Einstein
history or a local autonomous apparatus. In particular it does not erase
the clock's positive mean energy, and it does not pretend the capped
generator is the original full local QFT dynamics.

## 1. A smooth bounded clock encoding

Subtract only the fixed static c-number from the full source Hamiltonian:
\[
 H=H_{\rm exc}=E_sS_0+\Omega N\ge0,\quad
 E_s=\pi^2M_2/A^3,\quad\Omega=\sqrt3/A .
\]
All other nonzero modes have their full vacuum state, not a numerical
cutoff; their excitation energy is zero on the given input. The full
operator and any later field insertion still include them.

Choose a smooth nonincreasing chi with chi=1 on (-infinity,0],
chi=0 on [1,infinity), and 0<=chi<=1. It can be fixed explicitly using
b(s)=exp(-1/s) for s>0 and zero otherwise,
chi(s)=b(1-s)/(b(s)+b(1-s)).
For Ec>0 and Delta>0 define
\[
 f(E)=E\ (E\le E_c),\qquad
 f(E)=E_c+\int_0^{E-E_c}\chi(u/\Delta)\,du\ (E>E_c).
\]
Then 0<=r(E)=E-f(E)<=(E-Ec)_+, f(E)<=Ec+Delta,
and f is C-infinity. There is no source spectral projection or
postselection; the high-energy tail is retained.

On L2(R_+,dp) choose the actual clock Hamiltonian P=p>=0.
Let h(k)>=0 be an even normalized smooth packet with support |k|<=2R.
Take E0=Ec+Delta+d, d>2R, and define
\[
             (V\psi)(p)=h(p+f(H)-E_0)\psi .
\]
Every translated packet lies strictly inside p>0, so V is an isometry
on the entire source Hilbert space. The clock energy has bounded support
\[
                  d-2R\le P\le E_0+2R .
\]
The joint state V rho V^dagger is positive, normal and includes every
source outcome. Its unconditional source energy spectral law is unchanged;
its full bare marginal generally is not.

The canonical covariant time POVM on the positive-energy clock gives
\[
 \langle t|V\psi\rangle
        =g(t)e^{-i(f(H)-E_0)t}\psi,\quad
 g(t)=(2\pi)^{-1/2}\int e^{ikt}h(k)\,dk .
\]
Thus at t=0, whenever g(0)>0, its conditional state is exactly the full
original rho. This is a conditional probability density, not a claim
that an exact time point has nonzero probability.

## 2. Two distinct errors, both kept

For the actual proposed constraint C=P+H-E0, translated packet coordinate
k is independent of the source energy law. With <k>=0 and Var(k)=sigma_k^2,
\[
 \boxed{\langle C\rangle=\langle r(H)\rangle,\qquad
        \langle C^2\rangle=\sigma_k^2+\langle r(H)^2\rangle.}
\]
The clock packet spread must not be confused with the much smaller source
tail error. The state is not an exact strong solution.

At a clock reading t with g(t)!=0, compare its conditional source with the
true original H evolution:
\[
 D(\rho_f(t),\rho_H(t))
 \le\min\{1,\ 2\sqrt{\Pr(H>E_c)},\
             |t|\sqrt{\langle r(H)^2\rangle}\}.
\]
Here D is half the trace norm. Purification and
|exp(-itr)-1|<=min(2,|t|r) prove this for mixed inputs.
At t=0 the first density-matrix derivative differs by at most
\(2\sqrt{\langle r^2\rangle}\) in trace norm.
For an unbounded observable O, an additional moment bound is required:
\[
 |\langle i[r,O]\rangle|
 \le2\sqrt{\langle r^2\rangle\langle O^2\rangle}.
\]
The trace-distance result alone is not a proof of all unbounded RSET
normal derivatives or the complete multi-time UV/Ward structure.

For any finite time-bin inside |t|<=T, the clock/source record has the same
time density |g(t)|^2 as its reference record using rho_H(t), and their
conditional bounded-observable statistics differ by at most the same
T*sqrt(<r^2>) bound. This compares the same coarsened history; it does not
claim that a finite time bin prepares precisely rho(0).

## 3. Explicit parameters and the complete original source tail

Use proper model units, not SI:
\[
 E_c=2E_s,\quad\Delta=E_s/100,\quad
 R=4,\quad d=9,\quad E_0=2.01E_s+9 .
\]
Let
\[
 h(k)=Z^{-1/2}(2/\pi)^{1/4}e^{-k^2}\chi(|k|/R-1).
\]
It equals the Gaussian on |k|<=R, vanishes outside |k|>=2R, and is
smooth even at zero because the cutoff is constant near zero.
\[
 Z\ge1-2e^{-32},\qquad
 \sigma_k^2\le {1\over4(1-2e^{-32})}.
\]
A lower bound follows by retaining the central Gaussian second moment:
\[
 \sigma_k^2\ge\tfrac14-
       [R\sqrt{2/\pi}/2+1/2]e^{-32}.
\]
The clock support is exactly contained in [1,E0+8].
The full constraint RMS is therefore approximately 1/2 in energy units;
it is NOT the tiny tail RMS below.

Write u=Omega/Es and Zs=H/Es. Its exact moment generating function is
\[
 M(s)= {e^{s/(1-s/\nu_0)}+
          e^{s(1+\sqrt3/2)/(1-s/\nu_0)}
       \over2(1-s/\nu_0)}
       [1+n(1-e^{su})]^{-8}.
\]
The zero-mode Gaussian mixture and the entire infinite thermal number
distribution are retained. Domain conditions are s<nu0 and
1+n(1-exp(su))>0; the checker verifies both at s=1000.

Let B=exp(-2s)M(s). Chernoff and a scalar maximum give
\[
 \Pr(H>2E_s)\le B,\quad
 \langle(H-2E_s)_+\rangle\le {E_sB\over es},\quad
 \langle(H-2E_s)_+^2\rangle
       \le {4E_s^2B\over e^2s^2}.
\]
The interval calculation uses a stable log-sum expression, with no
cancellation of huge exponential terms and no source-energy truncation.
It yields a tail RMS below 2.37e-27 and a conditional bounded-record
distance below 9.88e-29 on |t|<=1/24.

There is a nonzero-probability window: since |kt|<=1/3,
g(t)>=cos(1/3)g(0)>0 on the whole window. Moreover
\[
 g(0)^2\ge {1\over\sqrt{2\pi}}
      [1-e^{-R^2}/(R\sqrt\pi)]^2,
\]
so its total clock-readout probability is at least
\(2T\cos^2(1/3)g(0)^2>0.029\).
This is a clock/source record probability, not a calibrated gravity signal.

## 4. The clock source is not free

The mean clock energy is exactly
\[
 \langle P\rangle=E_0-\langle H\rangle+\langle r(H)\rangle .
\]
For the chosen parameters it is approximately 3.24774e5 model energy
units, about 13.42% of the original complete static Einstein mean energy
3*pi^2*A. This comparison quantifies its cost; it does not place this
abstract clock in a real spatial stress distribution. Such a clock cannot
be appended while claiming the original background remains a total-source
solution.

Smooth capping preserves the finite-mode input's regularity and moments,
but using f(H) as an actual universal QFT Hamiltonian would change
multi-time transition frequencies, including those probed by field
insertions outside the populated shell. Only the explicitly compared
conditional states and bounded/coarsened records are certified here.
A local realization, full clock stress/cross-noise, common preparation
past and gravitational constraint still require new work.
