# Validated finite modes for the archived preparation

This directory supplies interval enclosures for the **actual archived nonzero-mode state**, using the same auxiliary scale factor as [instrument.py](../../instrument/instrument.py) and the source qualifications in [SOURCE.md](../../continuation/SOURCE.md). The implementation propagates the canonical pair with a Taylor remainder and an energy ball. Solver tolerances and agreement between two numerical cutoffs are not used as error certificates.

The completed receipts are:

| Receipt | Modes and targets | Accepted cells | Largest weighted mode error |
| --- | --- | ---: | ---: |
| [result.json](result.json) | \(k=2,\ldots,64\); \(\eta=0,3/64,11/64,3/16\) | 656 | approximately \(2.392\,10^{-20}\) |
| [extra_eta0_256.json](extra_eta0_256.json) | \(k=65,\ldots,256\); \(\eta=0\) only | 185 | approximately \(8.111\,10^{-12}\) |

The second run chooses its tolerance to resolve the stress question. Summing all of its mode error bounds with the full \(k^2/(4\pi^2a^4)\) weights gives an energy-density and pressure error bound of approximately \(4.921\,10^{-5}\), below its declared \(0.01\) exit budget. Its relatively loose per-mode budget does not replace the much tighter four-target receipt.

These are finite-mode certificates. The infinite tail and the local renormalization terms are provided separately in [stress](../stress/). The supplied background is fixed: neither receipt proves a self-consistent semiclassical spacetime.

## 1. The same state and normalization

Write \(a_0=\sqrt3\), \(\eta_s=-1/8\), \(\eta_e=-1/16\), and \(x=16(\eta-\eta_s)\). The interpolated quantity is \(a\), not \(a^2\):

\[
 a(\eta)=
 \begin{cases}
 a_0,&\eta\leq\eta_s,\\
 a_0+[\sqrt{3\cos(2\eta)}-a_0]S(x),&\eta_s<\eta<\eta_e,\\
 \sqrt{3\cos(2\eta)},&\eta\geq\eta_e,
 \end{cases}
 \qquad
 S(x)=\frac{e^{-1/x}}{e^{-1/x}+e^{-1/(1-x)}}.
\]

For \(k\geq2\), set \(\omega_k=\sqrt{k^2-1}\), \(v_k=au_k\), and \(p_k=a^2u_k'\). The exact equations and static initial data are

\[
 u_k'=\frac{p_k}{a^2},\qquad
 p_k'=-\omega_k^2a^2u_k,\qquad
 u_k(\eta_s)=\frac1{a_0\sqrt{2\omega_k}},\qquad
 p_k(\eta_s)=-ia_0\sqrt{\frac{\omega_k}{2}}.
\]

Thus \(u_kp_k^*-u_k^*p_k=i\), and the equivalent rescaled equation is

\[
 v_k''+(k^2+q)v_k=0,\qquad q=-1-\frac{a''}{a}.
\]

The physical segment has \(q=\sec^2(2\eta)\); the static preparation segment has \(q=-1\). No conformal coupling or alternate preparation is introduced.

The homogeneous \(k=1\) degree of freedom is excluded from this oscillator algorithm. Its declared regular Gaussian has \({\rm Var}(q_0)=1/6\), \({\rm Var}(p_0)=3/2\), and \(Y_0=(2\pi^2)^{-1/2}\). Its exact contribution is \(\rho_0=p_0^{\rm stress}=3/(8\pi^2a^6)\). The stress integration must include that contribution and must also apply the \(k=1\) term of the declared subtraction prescription.

The auxiliary preparation is a state construction. It does not assert that the finite classical ball had that static past geometry.

## 2. Background derivative enclosures

[background.py](background.py) represents a jet by coefficients \(f^{(j)}/j!\). Addition, multiplication, reciprocal, square root, exponential, and sine/cosine use differentiated identities with directed interval arithmetic. Evaluating those recurrences over a whole cell encloses every derivative at every point of the cell.

The two endpoint caps have conformal width \(1/1024\), or \(x\)-width \(1/64\). Directly evaluating \(1/x\) at a flat endpoint would be invalid. Instead, on \(0<x\leq\epsilon\),

\[
 z=e^{-1/x+1/(1-x)},\qquad S=\frac z{1+z},
\]

and the normalized derivatives of the logarithm satisfy

\[
 |(\log z)^{(j)}|/j!
 \leq x^{-j-1}+(1-x)^{-j-1}.
\]

Each monomial in the exponential Bell recurrence for derivative order \(n\) has total negative power of \(x\) at most \(2n\). For every \(m\leq2n\), the function \(x^{-m}e^{-1/x}\) increases on this cap when \(2n\epsilon\leq1\). The remaining factors also increase there. Evaluating the positive Bell majorant at \(\epsilon\) therefore bounds the entire closed cap, including its flat endpoint by continuity. The reciprocal recurrence uses \(1+z\geq1\). The right cap follows from \(S(x)=1-S(1-x)\).

This is an analytic cap bound, not a sampled maximum. The code rejects an order/cap pair that does not satisfy the monotonicity hypothesis. The high derivatives can be large despite the short transition, and the UV calculation must use their actual enclosures.

Interfaces:

- **derivative_box(lo, hi, order)** returns intervals for \(a^{(j)}/j!\), on one phase cell.
- **q_box(lo, hi, order)** returns intervals for the actual derivatives \(q^{(j)}\), with factorials restored. Order 5 is supported for the UV integration by parts.
- **coefficients(lo, hi, order, step)** returns jets of \(a,a^2,a^{-2}\), scaled by \({\tt step}^j\).
- **BREAKS** gives both preparation endpoints and both cap boundaries. A caller must split cells at these boundaries.

On the physical segment, q_box uses the direct identity \(q=\sec^2(2\eta)\), which avoids needless dependency inflation through the quotient \(a''/a\).

## 3. The energy ball and why rapid oscillation does not cause exponential wrapping

For a difference between two exact solutions, define

\[
 E^2=\omega_k a^2|\delta u|^2+
       \frac{|\delta p|^2}{\omega_k a^2}.
\]

The oscillator cross terms cancel exactly. With \(h=a'/a\),

\[
 \frac{d}{d\eta}E^2
 =2h\left(\omega_k a^2|\delta u|^2-
                 \frac{|\delta p|^2}{\omega_k a^2}\right),
 \qquad
 E(\eta_1)\leq e^{\int_{\eta_0}^{\eta_1}|h|\,d\eta}E(\eta_0).
\]

The growth factor depends on the variation of the background, rather than on \(k\). Rectangular complex intervals are used only for the short Taylor polynomial evaluation. After each step their rounding uncertainty is absorbed into this scalar energy radius, and the center becomes an exact serialized binary rational.

For a cell of length \(d\), the directed enclosure gives

\[
 V=d\sup_{\rm cell}|a'/a|,\quad G=e^V,\quad
 a_{\min}\leq a\leq a_{\max}.
\]

An exact solution starting with energy norm one obeys, throughout the cell,

\[
 |u|\leq\frac{G}{a_{\min}\sqrt{\omega_{\min}}},
 \qquad |p|\leq G a_{\max}\sqrt{\omega_{\max}},
 \quad \omega_{\min}=\sqrt3,\quad
 \omega_{\max}=\sqrt{K^2-1}.
\]

These deliberately conservative bounds apply to every propagated \(k\leq K\), including the high-mode-only supplement.

## 4. A Taylor remainder, not an adaptive-solver tolerance

Let \(b=a^{-2}\), \(c=a^2\), and let \(U_n,P_n\) bound the scaled normalized derivatives \(d^nu^{(n)}/n!\) and \(d^np^{(n)}/n!\) throughout a cell. With the preceding solution bounds as \(U_0,P_0\), the differentiated canonical equations imply

\[
 U_{n+1}\leq\frac d{n+1}\sum_{j=0}^n |b_j|P_{n-j},
 \qquad
 P_{n+1}\leq\frac{d(K^2-1)}{n+1}
                         \sum_{j=0}^n |c_j|U_{n-j}.
\]

Here \(b_j,c_j\) already include \(d^j/j!\). The code carries this majorant recurrence through order 13. The integral Taylor remainder for a degree-12 polynomial is therefore bounded in the endpoint energy norm by

\[
 r=\left[
 \omega_{\max}a_{\max}^2 U_{13}^2+
 \frac{P_{13}^2}{\omega_{\min}a_{\min}^2}
 \right]^{1/2}.
\]

The integral version applies directly to the complex solution; no scalar real mean-value point is assumed.

For a center of initial norm \(N_c\), old error radius \(E\), and interval-to-center rounding radius \(r_{\rm round}\), the accepted update is

\[
 E_{\rm next}\leq G E+rN_c+r_{\rm round}.
\]

Every term on the right is evaluated with directed intervals. The mesh is bisected until its unit local remainder passes the assigned budget. The requested budget guides mesh construction; the reported accumulated radius is the actual certificate.

The proof uses the standard enclosure contract of the supported mpmath interval operations. It is a reproducible interval computation, not a theorem checked by a proof-assistant kernel. The trusted arithmetic implementation and its precision are part of the computational assumptions. Mpmath documents the distinction between its ordinary and interval contexts and notes that interval support remains experimental; this implementation restricts its proof arithmetic to the elementary operations used explicitly here.

## 5. Direct stress intervals preserve the useful correlation

Define \(b_k=v_k'-hv_k=p_k/a\). The raw per-mode coefficients needed by the minimally coupled stress tensor are

\[
 e_k=|b_k|^2+(k^2-1)|v_k|^2,\qquad
 s_k=|b_k|^2-\frac{k^2-1}{3}|v_k|^2.
\]

For \(X=(\sqrt{\omega_k}a u,p/(\sqrt{\omega_k}a))\),

\[
 e_k=\omega_k\|X\|^2,\qquad
 s_k=\omega_k\left(|X_2|^2-\frac{|X_1|^2}{3}\right).
\]

Both quadratic forms have operator norm at most \(\omega_k\). If the exact solution is in an energy ball of radius \(E\) around center \(X_c\), then

\[
 |e_k-e_{k,c}|,\ |s_k-s_{k,c}|
 \leq\omega_k(2\|X_c\|E+E^2).
\]

The receipts output these directed e and s intervals directly. Downstream stress code need not reconstruct them by independently widening \(v\) and \(v'\). The required degeneracy and overall factor are \(k^2/(4\pi^2a^4)\).

The files also expose conservative \(v,v'\) enclosures for other consumers:

\[
 |\delta v|\leq E/\sqrt{\omega_k},\qquad
 |\delta v'|\leq
  \left(\sqrt{\omega_k}+|h|/\sqrt{\omega_k}\right)E.
\]

Each target stores exact rational center components, an outward rational interval for \(a\), and outward rational bounds. The field max_energy_radius is only a convenient floating-point summary; the per-mode rational radii are authoritative. Decimal serialization explicitly checks both endpoints after floor/ceiling rounding.

## 6. Independent checks and the physical-segment identity

[crosscheck.py](crosscheck.py) uses a different analytic representation for the physical segment. Setting \(x=\sin2\eta\) and \(v=\sqrt{\cos2\eta}\,w(x)\) reduces the equation to the Legendre equation with \(\nu=(k-1)/2\). The Ferrers pair gives a canonical fundamental matrix

\[
 {\cal F}_k(\eta)=
 \begin{pmatrix}
 {\mathsf P}_\nu(x)/\sqrt3&
 {\mathsf Q}_\nu(x)/\sqrt3\\
 2\sqrt3\cos^2(2\eta)\,{\mathsf P}_\nu'(x)&
 2\sqrt3\cos^2(2\eta)\,{\mathsf Q}_\nu'(x)
 \end{pmatrix},\qquad \det{\cal F}_k=2.
\]

The high-precision special-function calculation compares this continuation against the certified centers for six modes and three later times. It also independently differentiates the explicit preparation formula at seven points. These are diagnostics recorded in [crosscheck.json](crosscheck.json); floating-point Ferrers evaluations do not supply or shrink the interval radii.

A separate reviewer supplies an interval static-background test in [inference/review_bc.py](../inference/review_bc.py): exact harmonic rotations for \(k=2,17,64\) must lie in the Taylor energy balls, and deliberately setting the remainder to zero must fail. The cap-order rejection is also tested there.

## 7. Reproduction and scope

Use the project scientific Python with assertions enabled:

~~~bash
python -B finite_modes.py --check
python -B extra_eta0.py --check
python -B crosscheck.py --check
~~~

To regenerate the principal receipts:

~~~bash
python -B finite_modes.py --output result.json
python -B extra_eta0.py --output extra_eta0_256.json
python -B crosscheck.py --write
~~~

The finite-mode programs hash their source dependencies before and after propagation and reject a source change during the run. Replay checks all receipt fields except elapsed wall time. No repository state, Core result, GI run, or public-current pointer is modified by these commands.

The mesh certificates cover the evolution interval from the static endpoint through the stated targets. Stored solution enclosures are supplied at the targets, not as a dense-output oracle. The entire quantum stress tensor additionally requires the UV argument, the regular zero mode, and the same-scheme analytic additions. Its effect on the actual finite ball additionally requires an appropriate common physical domain and a self-consistent semiclassical initial-value analysis. Finite-mode propagation alone cannot discharge those obligations.

### Primary references

- [NIST DLMF §14.2](https://dlmf.nist.gov/14.2), especially equations 14.2.1 and 14.2.4, for the Legendre equation and the Ferrers Wronskian; [§14.5](https://dlmf.nist.gov/14.5), equations 14.5.1 and 14.5.3, for the stable values at zero.
- [Mpmath contexts documentation](https://mpmath.org/doc/current/contexts.html), for the interval arithmetic enclosure contract and its implementation qualifications.
- [Anderson and Eaker, gr-qc/9906055](https://arxiv.org/pdf/gr-qc/9906055), especially equations 5–12, for the mode/stress conventions and the separate numerical plus analytic renormalization terms.
