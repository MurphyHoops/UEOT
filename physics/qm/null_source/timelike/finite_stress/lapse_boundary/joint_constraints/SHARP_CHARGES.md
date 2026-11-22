# JC5 — A finite sharp dipole and a divergent sharp quadrupole

This calculation uses the same AP coupled ground and \(r=1/5\).
It does not replace the generic spacetime-smearing requirement.

## 1. Harmonic matrix elements and normalization

The round-sphere projector is
\[
 \Pi_k(x,y)=k\chi_k(d(x,y))/V_0,\qquad
 \chi_k\chi_l=\sum_{m=|k-l|+1,\ {\rm step}\,2}^{k+l-1}\chi_m .
\]
For a real \(L^2\)-normalized scalar harmonic \(f_m\), this gives
\[
 \sum_{ab}\left|\int f_mY_{ka}Y_{lb}\,dV\right|^2
 =\frac{kl}{V_0m}
\]
when the triangle and parity conditions hold, and zero otherwise.
In particular for the unnormalized coordinate \(Z=x_4\),
\[
 \operatorname{Tr}(P_k ZP_{k+1} Z)=k(k+1)/8 .                      \tag{1}
\]

For one normal field of squared mass \(\mu\), define
\(A_f=\int f\,T_{00}\). At a finite common cutoff it is
\[
 A_f=\tfrac12p^TFp+\tfrac12q^TLq+\hbox{scalar},\quad
 L_{ij}=\left[\frac{k^2+l^2}{2}+\mu-\frac{\lambda_f}{6}\right]F_{ij}.
\]
Here \(\omega_k=\sqrt{k^2+\mu}\) and the vacuum pair kernel is
\[
 B_{ij}=
 \frac{(k^2+l^2)/2+\mu-\lambda_f/6-\omega_k\omega_l}
      {2\sqrt{\omega_k\omega_l}}F_{ij},\qquad
 \operatorname{Var}A_f=\tfrac12\sum_{ij}|B_{ij}|^2 .                \tag{2}
\]
The \(-\lambda_f/6\) term is the conformal improvement; omitting it
changes the domain conclusion.

## 2. A finite nonzero dipole on the ground

For \(f=Z\) only adjacent shells occur. Put
\[
 W_{\sigma k}=\frac{k(k+1)}
                    {32\omega_{\sigma k}\omega_{\sigma,k+1}},
\quad
 d_{\sigma k}=k(k+1)+\sigma r-
                 \omega_{\sigma k}\omega_{\sigma,k+1}
 =-\frac{\sigma r}
 {k(k+1)+\sigma r+\omega_{\sigma k}\omega_{\sigma,k+1}} .
\]
The actual centered constituent vectors have the \(L^2\) limit
\[
 \boxed{\operatorname{Var}_{\Omega_r}A_Z
       =\sum_{\sigma=\pm,k\geq1}d_{\sigma k}^2W_{\sigma k}>0.}       \tag{3}
\]
With \(\kappa=1-r\), \(W\leq1/(32\kappa)\) and
\(|d|\leq r/[2\kappa k(k+1)]\), so
\[
 \operatorname{Var}A_Z\leq
 \frac{r^2[2\zeta(2)-3]}{64\kappa^3}.
\]
At cutoff \(K\), the included adjacent pairs have \(k\leq K-1\).
The missing tail starts at \(k=K\) and obeys the sharper bound
\[
 0\leq\operatorname{Var}A_Z-\operatorname{Var}A_{Z,K}
 \leq\frac{r^2}{192\kappa^3K^3}.                                  \tag{4}
\]
Indeed
\(1/[k^2(k+1)^2]\leq[k^{-3}-(k+1)^{-3}]/3\);
telescoping avoids an incorrect lower-limit integral estimate.

The vector \(A_Z\Omega_r\) has final-energy graph regularity exactly
\[
 A_Z\Omega_r\in D((1+H_r-e)^p)\quad\Longleftrightarrow\quad p<3/2
 \qquad(p\geq0).                                                  \tag{5}
\]
The shell weights in (3) are asymptotic to a positive constant times
\(k^{-4}\), while the pair energy is asymptotic to \(2k\).
This does not give all energy moments of that vector.

A fixed classical geometry cannot cancel (3) as an operator fluctuation:
the projected constraint variance would be
\((16\pi G_N)^2\operatorname{Var}A_Z>0\). This is a statement about
that fixed-geometry model, not a no-go theorem for quantum geometry,
mixed constraint operators or an interacting total state.

## 3. The quadrupole counterexample

Take
\[
 f=(4Z^2-1)/\sqrt{V_0},\qquad \|f\|_2=1,\qquad\lambda_f=8 .
\]
The diagonal Gaunt block has
\(\sum|F_{kk}|^2=k^2/(3V_0)\), \(k\geq2\).
Equation (2) gives \(B_{kk}=-2F_{kk}/(3\omega_k)\), hence for each field
\[
 \operatorname{Var}_{\rm diagonal,\mu}A_{f,K}
 =\sum_{k=2}^K\frac{2k^2}{27V_0(k^2+\mu)} .
\]
The two independent \(\mu=\pm r\) fields therefore satisfy
\[
 \boxed{\operatorname{Var}A_{f,K}\geq
             \frac{4(K-1)}{27V_0}\longrightarrow\infty.}          \tag{6}
\]
For a single massless conformal field, the off-diagonal \(k,k+2\)
blocks add \(1/(27V_0)\) per adjacent allowed pair, giving the exact
regression
\(\operatorname{Var}A_{f,K}=(3K-4)/(27V_0)\), \(K\geq2\).

Thus the finite sharp dipole is a special cancellation, and does not
license inserting a general sharp-time stress covariance into a
constraint matrix.

## 4. A preparation resource inequality

Let \(D=H_r-e\), and let \(v\perp\Omega_r\) be the tangent of a smooth,
normalized pure preparation. Define
\[
 S_A=\langle A_Z\Omega_r,D^{-1}A_Z\Omega_r\rangle
 =\sum_{\sigma,k}\frac{d_{\sigma k}^2W_{\sigma k}}
                         {\omega_{\sigma k}+\omega_{\sigma,k+1}}>0 .
\]
For \(a=2\operatorname{Re}\langle A_Z\Omega_r,v\rangle\),
Cauchy–Schwarz in the \(D\)-weighted norm gives
\[
 \boxed{E_2=\langle v,Dv\rangle\geq a^2/(4S_A).}                   \tag{7}
\]
The four coordinate directions are orthogonal by \(SO(4)\), yielding
\(E_2\geq\|\mathbf a\|^2/(4S_A)\). The inverse is used only on the
strictly positive excited subspace. A one-species preparation may use
the smaller one-species \(S_A\) and obtains a stronger bound.
The tail after \(K\) is at most the variance tail in (4) divided by
\(2\sqrt\kappa\,K\). This is a second-order resource bound, not an
exact nonlinear finite-amplitude inequality or a solution of gravity.
