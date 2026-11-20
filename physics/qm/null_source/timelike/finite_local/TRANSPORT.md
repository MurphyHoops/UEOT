# Transport the state, rather than choose a new vacuum at each record

This construction is on a specified smooth preparation metric. It proves that one actual CCR state can be carried to each record-dependent future geometry. It does not solve the total Einstein equation while a controller changes that metric.

Let the auxiliary profile and finite-initial solution be those in PROFILE.md and EVOLUTION.md. Put \(a_-=a_0b_{\rm cl}(-2/5)\), \(L=\log(a_-/A)\), \(c=\min(1,|L|)\), \(\sigma=\operatorname{sign}L\), \(\epsilon=1/100\). For \(L=0\), use the constant metric. The smooth step
\(s(x)=\chi(4x/5-4/5)\) has support of its derivative in \([0,1]\), satisfies \(s(1-x)=1-s(x)\), and has integral \(1/2\) on that interval.

Prescribe \(h=a'/a\) as an up-ramp \(\sigma\epsilon c\,s(\epsilon\eta)\), a constant plateau \(\sigma\epsilon c\), and the reversed down-ramp. Each ramp has conformal duration \(1/\epsilon\); the plateau has duration \(D=(|L|-1)_+/\epsilon\). Then
\(\int h\,d\eta=\sigma[c+c(|L|-1)_+]=L\). Integrating \(a=A\exp\int h\) gives a positive \(C^\infty\) metric, exactly static at both ends. A different past auxiliary lapse is not silently substituted.

On every branch \(a\ge a_*=\min(A,(4/7)\sqrt{x_c})>0\). The proper duration is bounded by \(\max(A,a_-)(2+|L|)/\epsilon\). All continuous-record branches have finite duration, but a bounded uniform duration needs the binary construction below. During ramps and plateau the exact zero-mode transport is
\[
P_i\longmapsto P_i,\qquad Q_i\longmapsto Q_i+P_i\int a^{-2}d\eta,
\qquad \int a^{-2}d\eta\le {5\over2\epsilon a_*^2}.
\]
A later static wait adds its actual known shear. No zero-mode covariance is reset.

## Uniform all-mode estimate

For \(V=h'+h^2\), direct differentiation of the two ramps gives
\[
|V^{(j)}|\le(5,22,212,2220,29000)_j\,\epsilon^{j+2},
\quad j=0,\ldots,4.
\]
The constant plateau can be arbitrarily long; it produces only a phase. Put \(W=\sqrt{\omega^2-V}\), \(d=V''/(8\omega^3)\), and \(\Omega=W+d\). With \(m=31/32,M=33/32\), both \(W\) and \(\Omega\) lie between \(m\omega\) and \(M\omega\), since \(\omega\ge\sqrt3\). They equal \(\omega\) at both static ends. The WKB residual is
\[
R={V''\over4}(W^{-2}-W/\omega^3)+{5V'^2\over16W^4}-d^2+
 {W''d\over2W\Omega}-{d''\over2\Omega}
 +{3(2W'd'+d'^2)\over4\Omega^2}
 -{3W'^2d(2W+d)\over4W^2\Omega^2}.
\]
Here \(W'=-V'/(2W)\) and \(W''=-V''/(2W)-V'^2/(4W^3)\). The eight terms, after division by \(\epsilon^6/\omega^4\), have respective bounds \(445,172,1,1,1871,1,1,1\); their explicitly evaluated sum is below 2493. In particular \(|R|<3000\epsilon^6/\omega^4\), and it vanishes on the plateau.

For the exact-minus-WKB solution, use \(N^2=|\delta'|^2+W^2|\delta|^2\). Its Gronwall exponent satisfies
\(\int |W'|/W\le22\epsilon^2/(m^2\omega^2)<10^{-3}\). The forcing has support of total length \(2/\epsilon\). It follows that
\[
N_{\rm out}<6012\epsilon^5\omega^{-9/2},\qquad
|\beta_{\rm prep}(\omega)|<7000\epsilon^5/\omega^5<10^{-7}.
\]
This is an analytic bound for all shells and all plateau lengths. It is not a fit of finitely many mode integrations.

The future exact mode is \(\alpha v_{\rm aux}+\beta_{\rm prep}\overline{v_{\rm aux}}\). At the static auxiliary starting end, the energy cross term cancels, so the initial energy is multiplied by \(1+2|\beta_{\rm prep}|^2\), not a first-order absolute-value bound. The subsequent energy estimate has coefficient
\[
(63/32)^6(13/12)^2(1+2|\beta_{\rm prep}|^2)<69.
\]
The ultraviolet added pair term is bounded by \(10^{-4}/p^4\). The strict margins in FLUCTUATIONS.md retain the pair caps \(25000/p^2\), \(600000/p^2\), and the high-sector RMS coefficients 1600 and 8000. The exact quadratic difference is bounded by \(2|\beta|(\sqrt{1+|\beta|^2}+|\beta|)\) times the reference energy. Using \(\sum_{k\ge2}k^2/\omega_k^4\le16/9\), the change in either renormalized mean component is below \(10^{-5}\lambda^4\), including both fields and their finite thermal populations.

The mode transformation is normal: \(\sum k^2|\beta_{\rm prep}|^2<\infty\). Its Hadamard property follows from smooth exact evolution. The finite-order WKB formula is only the bounding device.

## What this permits

A long ideal filter leaves the old high product state unchanged. A short local filter does not. ACTUAL_HISTORY.md transports the latter actual conditional state, including its excitations and correlations, through exactly this same CCR map. It uses positive-operator domination and moment estimates; it does not reintroduce a product assumption.

The auxiliary preparation and the metric ramp are still off shell. Neither the stress tensor of a controller nor an Einstein solution during this ramp has been supplied here.
