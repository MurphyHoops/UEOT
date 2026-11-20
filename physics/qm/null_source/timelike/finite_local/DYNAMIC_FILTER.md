# A long filter on the same incoming nonstatic history

This certificate is separate from the static short-pulse stress-moment certificate. It does not use a small trace distance as a substitute for an energy-weighted estimate.

On the already certified exact nonlinear mean history \(a=Ae^u\), keep its exact positive-frequency incoming Jost state. The entire long pulse is placed before a certified endpoint, so \(\|u\|_{E_4}\le\rho=10^{-25}\) throughout its causal past. The lowest positive rate exceeds 1.99. Thus, for \(V=u''+u'^2\),
\[
d=\sup_K|u|\le\rho,\qquad
J=\int_{-\infty}^{\eta_{\rm end}}|V|d\eta
 \le\rho+{\rho^2\over2s_{\min}}<2\rho.
\]
The positive-frequency norm controls this integral; it is not an unsupported conversion of a finite-interval sup bound.

Use the long filter from LONG_FILTER.md with \(f_g=a^{-4}t'b\). Its zero \(Q\) coefficient remains exactly zero, while
\(\beta_g=\beta_0\int t e^{-2u}\), \(\beta_0=-1/(\sqrt{2\pi^2}A^2)\).
Since \(t\ge0,\int t=1\), \(|\beta_g/\beta_0-1|\le e^{2d}-1\).

The retarded Volterra bound for an exact incoming mode is
\[
|v_\omega-v_\omega^{(0)}|
 \le {e^{J/\omega}-1\over\sqrt{2\omega}}.
\]
Subtract the exactly vanishing static filtered coefficient, rather than a newly chosen state. With \(D=\|t'\|_1<0.57\),
\[
|c_\omega[g]|
 \le {|b_\omega|D\over A\sqrt{2\omega}}
       (e^{d+J/\omega}-1),\qquad
V_h\le{(1+2n)D^2\over2A^2\sqrt3V_0}
       (e^{d+J/\sqrt3}-1)^2.
\]
All modes and both identical finite thermal populations are retained.

## Calibration is not assumed infinitely precise

Compare at one common out Cauchy time, after undoing the same free evolution. Keep the static source gain and static Magnus \(\Pi^2\) compensation. Put \(\delta_\beta=e^{2d}-1\), \(v_m=\beta_0^2w\), and
\[
D_0=1+{\delta_\beta^2v+V_h/\beta_0^2\over4w}.
\]
A purification of the actual CQ preparation gives the complete two-field fixed-input trace-distance bound
\[
D_{\rm gain+high}\le
 \sqrt{1-D_0^{-2}\exp[-\delta_\beta^2(C\mu-2v)/(4wD_0)]}.
\]
The known time-ordering phase is not silently recalibrated to the actual metric. Its mismatch obeys, for \(L=2\pi+0.1\),
\[
|\Delta R_h|\le{D^2\over2A^2\sqrt3V_0}
 (e^{2d+J/\sqrt3}-1),\quad
|\Delta R_0|\le{D^2Y_0^2L\over2A^2}(e^{2d}-1).
\]
These follow from the retarded Green-function Volterra estimate and
\(\int_{\eta>\eta'}|t'(\eta)t'(\eta')|d\eta d\eta'\le D^2/2\).
The phase contribution to the double-probe trace distance is at most
\((|\Delta R_h|+|\Delta R_0|)/(4v_m)\); add it by the triangle inequality.

The script reports bounds for \(w=A^2\) and for \(w=C/2500\). These are fixed-input out-channel estimates. During the pulse the matter source changes, as LONG_FILTER.md proves even in the exactly static case. Neither the controller stress nor the full Einstein equation during the pulse is closed. The pulse smearing still refers to the specified known metric; an autonomous unknown-metric calibration procedure is not supplied.
