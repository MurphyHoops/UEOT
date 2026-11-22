# JC13 — The actual source-only quadratic CTP kernel and its local subtraction

## Fixed source family and finite datum

This entry uses the new AP ground on unit ESU, not the older AQ input. Only the plus field is perturbed by \(s(t,x)=h(t)\cdot Z(x)\), where h is a real, smooth, compactly supported four-vector. Use the identical field cutoff P_K on both branches and keep edges k=1,...,K-1. Put
\[
 \mu=1/5,\quad \omega_k=\sqrt{k^2+\mu},\quad
 \Omega_k=\omega_k+\omega_{k+1},\quad
 W_k={k(k+1)\over32\omega_k\omega_{k+1}},\quad
 {\cal H}_K=\sum_{k=1}^K{1\over k}.
\]
The source-square counterterm on this column is
\(C_K[h]={\cal H}_K|h|^2/64\).

The extension of the old datum is explicit. Off this column use the quadratic source invariant \(\operatorname{Tr}[(M^2)^2]\) as in SOURCE_ACCOUNTING. Set the additional finite coefficient of \((\operatorname{Tr}M^2)^2\), and other newly allowed trace-source finite terms, to zero. The old traceless two-field datum alone could not fix these new coefficients. A different finite Hamiltonian term gamma |h|^2 would change the phase by -gamma integral |h|^2 and the response below by -2 gamma h. This convention is held fixed in every subsequent source computation.

## 1. Derive at finite cutoff before taking limits

Let \(\widehat h(\Omega)=\int e^{i\Omega t}h(t)\,dt\) and
\(c_h(u)=\int h(t)\cdot h(t-u)\,dt\). The finite-mode vacuum Dyson expansion, including its scalar counterterm, gives the quadratic part of log vacuum amplitude
\[
 \log c_K[h]\big|_2
 =-\tfrac12\sum_{k<K}W_k|\widehat h(\Omega_k)|^2
 +i\left[\sum_{k<K}W_k S_h(\Omega_k)
                  -{{\cal H}_K\over64}\|h\|_2^2\right],
\]
\[
 S_h(\Omega)=\int_0^\infty c_h(u)\sin(\Omega u)\,du
 ={c_h(0)\over\Omega}
   -{1\over\Omega^2}\int_0^\infty c_h''(u)\sin(\Omega u)\,du .
\]
The real part is minus one half of the pair-creation probability coefficient. The imaginary term contains a logarithm which cannot be discarded by choosing an arbitrary phase for the Gaussian implementer.

For two real histories set Delta=h_+-h_- and Sigma=(h_++h_-)/2. The quadratic CTP logarithm is
\[
 \log Z_K[h_+,h_-]\big|_2
 =-\tfrac12{\cal N}_K[\Delta]+i\int\Delta(t)\cdot
                  ({\cal T}_K\Sigma)(t)\,dt,
\]
\[
 {\cal N}_K[\Delta]=\sum_{k<K}W_k|\widehat\Delta(\Omega_k)|^2,
\]
\[
 ({\cal T}_K h)(t)
 =2\sum_{k<K}W_k I_h(\Omega_k,t)-{{\cal H}_K\over32}h(t),\quad
 I_h(\Omega,t)=\int_0^\infty\sin(\Omega u)h(t-u)\,du .
\]
This sign follows from U=exp(-i integral H), with the stated positive-frequency Fourier convention. Equivalently, its phase is Phi[h_+]-Phi[h_-]+Im sum W conjugate(hhat_-) dot hhat_+. The latter cross term is part of the same initial density, not an independent noise source.

## 2. Uniform and causal renormalized limit

For every k>=1,
\[
 0\le {1\over64k}-{W_k\over\Omega_k}\le {1\over80k^2}.
\]
For completeness, omega_k is between k and k+mu/(2k). With t=1/k, a lower bound for W/Omega is
\[
 {1\over64k}\{(1+t^2/5)(1+t/2+t^2/10)\}^{-1}.
\]
Subtract it from 1/(64k). The remaining ratio is bounded by
\(t(1/2+.42t)/(1+t/2)\le .8t\), proving the displayed bound. No fitted high-mode asymptotic is needed.

Twice integrating I_h by parts gives
\[
 I_h={h(t)\over\Omega}
       -{1\over\Omega^2}\int_0^\infty\sin(\Omega u)h''(t-u)\,du .
\]
Consequently the limit
\[
 {\cal T}h=2\sum_{k\ge1}
       \left[W_k I_h(\Omega_k,\cdot)-{h\over64k}\right]
\]
exists uniformly in time and is causal, including the local term. For K>=2,
\[
 \|{\cal T}-{\cal T}_K\|_\infty
 \le{\|h\|_\infty/40+\|h''\|_1/64\over K-1}
                         +{\|h\|_\infty\over32K},
\]
\[
 0\le{\cal N}[\Delta]-{\cal N}_K[\Delta]
 \le{\|\Delta''\|_1^2\over1536(K-1)^3}.
\]
The final 1/(32K) term is necessary: the Hamiltonian cutoff counterterm runs through K whereas pair edges run through K-1. It is not silently discarded.

The noise is positive because it is a sum of squared spectral test amplitudes. The CTP functional has Z[h,h]=1 and Z[h_+,h_-]^*=Z[h_-,h_+] at this order. No separate density and pressure noises have been introduced.

## 3. Derivative, not an unexplained formal determinant

Finite-cutoff derivation and the tail estimates prove convergence of these Hessians. SOURCE_CTP additionally constructs the full phased unitaries and a locally analytic vacuum CTP functional in the actual eight-control neighborhood. Therefore the Hessian here is the derivative of that constructed source-family functional, rather than a determinant whose existence is assumed.

The corresponding first-order renormalized mean force is -T h. A scalar counterterm removes its mean divergence; it cannot remove the norm divergence of an unsmeared source-force vector. Indeed W_k tends to 1/32, so the sharp force vacuum variance diverges. Time-smoothed force tests are the declared domain.

## What this does not close

The prescribed source can exchange energy with matter. Its controller and interaction stress remain required in the total Ward identity. This source-only result does not construct a generally covariant metric Hessian, prove sharp stress variances, preserve the original AQ vacuum Hessian, or solve the Einstein constraints.
