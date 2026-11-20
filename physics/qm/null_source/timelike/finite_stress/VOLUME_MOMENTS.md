# All polynomial volume moments on the critical history

This proof is needed because finite <1/v> does not imply finite <v>, and
finite <v> does not imply a finite total positive-energy variance.

Work first in one P fiber after the fixed parity transformation:
\[
 H=\alpha T-dN^{1/3}+\epsilon N^{-1},\quad \epsilon\ge0.
\]
All estimates below are uniform in the finite-section cutoff and contain
no adverse epsilon term. Finite sections are proof approximations; the
physical operator remains the infinite essentially self-adjoint Jacobi
operator.

## 1. First moment and the special negative-mean bound

Write f_n=sqrt(n)u_n, with f_0=0. The positive form of T is
sum_(n>=0)|f_(n+1)-f_n|^2. The probability current gives
\[
 |{d\over dt}\langle N\rangle|
 \le2\alpha\sqrt{\langle N\rangle}\sqrt{\langle T\rangle}.
\]
For a normalized vector of conserved mean E<=0,
alpha<T><=d<N^(1/3)><=d<N>^(1/3). Consequently
\[
 \langle N\rangle_t^{1/3}
 \le\langle N\rangle_0^{1/3}+{2\over3}\sqrt{\alpha d}|t|.
\tag{17}
\]
The seed in CRITICAL_STATE.md has negative mean already, so this estimate
also applies before its spectral filter. Positivity and Jensen extend
(17) to mixed states. This argument only discards the mean energy at
q=1. Weighted energy expressions at higher q cannot be discarded.

## 2. Discrete IMS and current identities

For an integer q>=1 set A_q=N^((q-1)/2). On finite sequences,
\[
 \langle A_qu,T A_qu\rangle
 -\operatorname{Re}\langle N^{q-1}u,Tu\rangle
 =\sum_{n\ge1}\sqrt{n(n+1)}
       [A_q(n+1)-A_q(n)]^2\operatorname{Re}(\bar u_nu_{n+1}).
\tag{18}
\]
Its absolute value is at most C_q<N^(q-2)> for q>=2. One may take
C_1=0, C_2=1/4; for q>=3 a conservative choice is
C_q=sqrt(2)((q-1)/2)^2 2^max(q-3,0).
The latter follows from the mean value theorem and 2|uv|<=|u|2+|v|2.
For q=2 the edge coefficient is
sqrt(n(n+1))/(sqrt(n+1)+sqrt(n))^2<=1/4.

The current coefficient is bounded by
\[
 { (n+1)^q-n^q\over[n(n+1)]^{(q-1)/2}}
 \le b_q:=q\,2^{(q-1)/2}.
\]
With f_n=n^(q/2)u_n, replace Im(bar f_n f_(n+1)) by
Im(bar f_n(f_(n+1)-f_n)) and apply Cauchy-Schwarz. This gives
\[
 |{d\over dt}\langle N^q\rangle|
 \le2\alpha b_q\sqrt{\langle N^q\rangle}
             \sqrt{\langle A_qu,T A_qu\rangle}.
\tag{19}
\]

## 3. Graph-norm induction, retaining the noncommuting energy term

Let u_j(t)=H^j exp(-itH)u, L_j=||H^j u||, and
F_qj(t)=||N^(q/2)u_j(t)||. All L_j are constant.
Equations (18)-(19), the positive epsilon term, and Cauchy-Schwarz give
\[
 |F'_{qj}|\le b_q\sqrt\alpha
 \left[(F_{q-1,j}F_{q-1,j+1})^{1/2}
 +\sqrt{d+\alpha C_q}\,
      L_j^{2/(3q)}F_{qj}^{1-2/(3q)}\right].
\tag{20}
\]
Here N>=1 absorbs the lower IMS moment into N^(q-2/3), and Holder gives
<N^(q-2/3)> <= L_j^(4/(3q)) F_qj^(2-4/(3q)).
For q=1 the same formula holds with C_1=0. At F=0 the inequality is
understood through regularization sqrt(F2+eta) and upper Dini derivatives;
there is no division by a potentially zero ||H^j u||.

Crucially Re<N^(q-1)u_j,H u_j> is bounded by
F_(q-1,j) F_(q-1,j+1); it is not assigned a sign merely because u_j
has negative spectral support.

The q=0 bounds are K_0j=L_j. Assume
F_(q-1,j)<=K_(q-1,j)(1+|t|)^(3(q-1)/2), and put beta=3q/2,
\[
 A=b_q\sqrt\alpha\sqrt{K_{q-1,j}K_{q-1,j+1}},\quad
 B=b_q\sqrt{\alpha(d+\alpha C_q)}\,L_j^{1/\beta}.
\]
Taking
\[
 K_{qj}\ge\max\{F_{qj}(0),2A/\beta,(2B/\beta)^\beta\}
\tag{21}
\]
makes K_(qj)(1+|t|)^beta a supersolution of (20), since
3(q-1)/2<=beta-1. Thus
\[
 \boxed{F_{qj}(t)\le K_{qj}(1+|t|)^{3q/2}.}
\tag{22}
\]
For any fixed target q,j only finitely many initial weighted H powers
are needed (indices with q+j bounded). They are finite for finite
sequences.

For such a seed, finite-section H_L^j u equals H^j u for all sufficiently
large L. The constants in (21) are therefore independent of L.
Essential self-adjointness on the common finite-support core gives
strong resolvent and unitary convergence. Fatou for the positive weights
transfers (22) to the infinite operator. No hard wall is introduced.

## 4. A smooth compact energy filter preserves the required moments

Let f be the fixed compact smooth function of CRITICAL_STATE.md. The
Fourier representation of f(H/M) is a Bochner integral of exp(isH/M)
with Schwartz weight. Estimate (22) is polynomial, so this integral
converges in every N^(q/2) graph norm.

For mixed H powers use g_j(e)=e^j f(e):
H^j f(H/M)=M^j g_j(H/M).
Its Fourier transform is also Schwartz. Therefore the filtered vector
has every mixed norm ||N^(q/2) H^j phi_P|| finite, and the same holds
on any finite time interval.

The packet center B(P) and its finite-support H powers grow at most
polynomially in P. The normalization is uniformly bounded below.
All constants needed for each fixed q,j are thus polynomially bounded
in P; the complete original Gaussian mixture integrates them.
In particular <v2> and <H2> are finite for the actual normal joint state.

Using only an exponential Gronwall estimate would not suffice: a
Schwartz Fourier transform need not have an exponential moment.
The polynomial estimate is an essential part of this closure.

## 5. Interpretation

This proves finite polynomial geometry moments, not narrow relative
fluctuations, a semiclassical metric or the old AE field equations.
It supplies the domains required for POSITIVE_SOURCE.md and for a
normal positive-clock encoding without infinite unconditioned energy.
