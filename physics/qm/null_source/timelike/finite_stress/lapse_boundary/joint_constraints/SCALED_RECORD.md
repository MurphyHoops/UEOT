# JC12 — A reader whose complete retained cost follows the code strength

## Contract and result

Use the actual AP eight-control preparation of QUANTIFIED_PREPARATION, the same cap functions and the elapsed read time 3 in PREPARED_RECORD. This is a new reader family, not a reinterpretation of the fixed-resolution reader. All readout outcomes remain in the output. Let 0<eta<=10^-13 and choose

\[
 \sigma_\eta={1\over10\eta},\qquad v_\eta={1\over4\sigma_\eta^2}=25\eta^2.
\]

The source-preparation, encoding and nonselective readout increments in retained energy are now of order eta^2. The certified binary contrast is strictly positive but only of order eta^2. Neither claim says that background stress noise vanishes or that a gravitational apparatus has been constructed.

## 1. Use the actual control, not the uniform ball estimate

The contraction in QUANTIFIED_PREPARATION has inverse bound 10^6 and Lipschitz factor .004096. Its target has norm at most eta^2/2. Therefore

\[
 \|u(\eta)\|\le {10^6\eta^2\over2(1-.004096)},\quad
 x=1.6\,10^6\|u\|<8.04\,10^{11}\eta^2.
\]

For the present eta range, \(Q=2xe^x(1+3x+x^2)\le2.1x\). The same actual full-field weighted Hilbert--Schmidt estimates, rather than a new finite-mode extrapolation, imply

\[
 E_{\rm pre}\le Q^2<3\,10^{24}\eta^4\le .03\eta^2,\qquad
 {\rm Var}(H)_{\rm pre}\le2(1+Q^2)Q^2<7\,10^{24}\eta^4\le .07\eta^2.
\]

These conservative upper bounds include both species after the common source pulse. The state is centered. The two code alternatives add opposite smooth displacements, and hence add the same mean energy.

## 2. A normal all-outcome limit

The old raw pointer coordinate z has a width that diverges as eta tends to zero. Use the physical comparison coordinate y=eta z and retain its Jacobian. The Kraus density on the same receiver observable Q is

\[
 \widetilde M_y=(2\pi\, .01)^{-1/4}
       \exp[-(y-\eta Q)^2/(4\, .01)],\qquad
 \int\widetilde M_y^\dagger\widetilde M_y\,dy=1.
\]

For each eta>0 this is precisely the Gaussian instrument with sigma_eta, expressed in a common output space. It has the actual common-cutoff Stinespring limit already proved for a smooth receiver. Its eta=0 extension is an independent normal N(0,.01) record tensor the unchanged quantum input. No probability mass is lost at infinity in this output coordinate. Binary coarse graining is y>=0 versus y<0; no successful subset is postselected.

With receiver variance \(\nu<9/16\) and the same state-independent signal lower bound \(\mu>3.42735067487022\,10^{-5}\), the binary probability difference is

\[
 d_\eta=\operatorname{erf}\!\left(
 {\eta^2\mu\over\sqrt{2(.01+\eta^2\nu)}}\right)
 >2.734\,10^{-4}\eta^2.
\]

The lower bound follows from erf(x)>=2x exp(-x^2)/sqrt(pi), evaluated with uniform denominator and exponential bounds. At eta=10^-13 it is greater than 2.734e-30. The exact continuum no-signal interval 0<tau<1/2 is unchanged, because the complete instrument depends only on the causally propagated smooth receiver. This is not a statement of experimental accessibility.

## 3. Complete retained mean and variance

Keep the background AP energy e(r) and variance, preparation, code and reader contributions in the same source. Write

\[
 P_*={11\over20}\sqrt{1+(22/5)^2}<2.482 .
\]

The exact Gaussian energy identities used in PREPARED_RECORD give

\[
 \Delta\langle H_{\rm retained}\rangle
 \le E_{\rm pre}+\eta^2/2+v_\eta/2<13.03\eta^2,
\]
\[
 {\rm Var}(H_{\rm retained})\le
 V_{\rm pre}+(25\eta^2+\eta^2)P_*+
 25\eta^4+{625\eta^4\over2}<65\eta^2.
\]

The variance is relative to the stationary AP vacuum, whose total Hamiltonian is sharp, not a declaration that every local tensor fluctuation is small. The nonselective readout noise contribution for the declared smooth quadratic stress tests is

\[
 25\eta^2\,\operatorname{Re}\langle B_F B_G\rangle
       +1250\eta^4 C_F C_G .
\]

All source--probe cross terms in this formula are retained. The source-species instantaneous marginal can stay unchanged while the total retained stress changes. The eight mean projections imposed before encoding have not thereby been proved to remain zero after encoding and reading.

## 4. Decision

This comparison repairs the fixed reader's mismatch of perturbative orders at the level of the completed, externally prescribed matter-side instrument. It pays for that repair with a quadratic, very small contrast. It supplies no autonomous pointer Hamiltonian, no classical record collection mechanism, no uniform interacting ultraviolet limit, and no joint quantum Einstein solution. Those are separate subsequent gates.
