# Exact finite-shell influence, beyond a noise truncation

On a pair of common finite homogeneous histories with the same canonical
endpoint identification, let the one-mode relative unitary V satisfy
V^dagger a V=alpha a+beta a^dagger, |alpha|^2-|beta|^2=1.
All eight k=2 oscillators have the same V. The continuous metaplectic branch
has
\[
 V_{00}=(\alpha^*)^{-1/2},\quad
 V_{20}={\beta V_{00}\over\sqrt2\alpha^*},\quad
 V_{02}=-{\beta^* V_{00}\over\sqrt2\alpha^*}.
\]
These follow by applying the transformed annihilator to V|0> and its
adjoint relation to <0|V. The Bargmann Gaussian kernel, or its diagonal
Gaussian trace, gives
\[
 {\rm Tr}[(1-q)q^N V]
 ={1-q\over\sqrt{\alpha^*+q^2\alpha-2q}}.
\]
At a pure rotation this reduces to
(1-q)e^{-i theta/2}/(1-q e^{-i theta}), fixing the branch.
The eighth power below removes the square-root ambiguity.

Connecting A1 to A2 uses one V02, one V20 and six V00. The d^2 coherent
pairs and normalization 1/d give
<A2|V^(tensor 2d)|A1>=-d|beta|^2/[2(alpha^*)^(d+2)].
Thus, with d=4,
\[
 F_\pm^{s}
 =\left[{(1-q)^2\over\alpha^*+q^2\alpha-2q}\right]^d
       \mp {cd|\beta|^2\over(\alpha^*)^{d+2}},
 \qquad
 \boxed{\Delta F^s=-{2cd|\beta|^2\over(\alpha^*)^{d+2}}}.
\]
A pure phase (beta=0) cannot distinguish these states; a nonzero squeeze can.
This is a full finite-shell expression, including all orders in the history
difference, not a replacement of the non-Gaussian state by its noise kernel.

For y=|beta|^2,
\[
 |\Delta F^s|={8cy\over(1+y)^3}\le{32c\over27};
\]
the algebraic maximum is y=1/2. This does not prove that a self-consistent
Einstein history attains that value.

For a small compact variation a=A exp(delta u), first-order scattering gives
beta_1=-2i omega int delta u(eta)e^{2i omega eta}deta, up to a common phase.
Consequently
\[
 \Delta\log F=-8cd\omega^2
    \left|\int\delta u\,e^{2i\omega\eta}d\eta\right|^2+O(\delta u^3).
\]
It matches -1/2 times the PRESSURE_NOISE.md kernel smeared with the metric
coupling 3 V0 A^4 delta u, including its normalization and sign.

Other modes multiply this contrast by their common influence. A formal
finite-shell contrast alone need not survive an infinite product or the
zero-mode phase. HISTORY_WITNESS.md supplies one explicit smooth pair for
which neither effect erases it. Renormalized state-independent phases are
shared; no untreated infinite vacuum phase product is asserted.
