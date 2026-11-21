# The geometry's next derivative obstructs recovery

## G1. Exact finite-mode generator and a legitimate second derivative

Use the same finite-\(K\) raw joint generator, clock, phase convention, and comparison forms as WEIGHTED_EVOLUTION:
\[
H(u)=\alpha(u)A_\eta+\frac{H_s(u)+d_0(u)}{\kappa}
                  +d_1(u)\kappa+d_3(u)\kappa^3,\qquad
\alpha=\frac1{2g}.
\]
The ordering parameter is denoted \(\eta\); conformal-time derivatives carry the subscript \(\eta_{\rm time}\) below when confusion is possible. The fixed pure geometry phase is transported with the domain. The ordinary derivative form written here is in the phase-removed representation.

On the vector-valued core
\(\mathcal E=C_c^\infty(0,\infty)_\kappa\otimes\mathcal S_{\rm source}\),
including an arbitrary purification factor, put
\[
B=\kappa^{-1/2}P_\kappa\kappa^{-1/2}
 =-i(\kappa^{-1}\partial_\kappa-\tfrac12\kappa^{-2}),
\quad
A_\eta=-\kappa^{-1}\partial_\kappa^2+\kappa^{-2}\partial_\kappa
                   +(\eta-\tfrac34)\kappa^{-3}.
\]
Direct differentiation gives
\[
i[H,\kappa]=2\alpha B,\qquad
i[A_\eta,B]=\partial_\kappa(\kappa^{-3}\partial_\kappa)
                     +(3\eta+\tfrac74)\kappa^{-5},\qquad
i[V(\kappa),B]=-\kappa^{-1}V'(\kappa).
\]
Let
\[
I_j=\langle\kappa^{-j}\rangle,\qquad
J_3=\int_0^\infty\kappa^{-3}\|\partial_\kappa\Psi\|^2\,d\kappa.
\]
The exact initial force is
\[
\boxed{\begin{split}
\langle\kappa\rangle''_u={}&
2\alpha'\langle B\rangle+
2\alpha^2[-J_3+(3\eta+\tfrac74)I_5]\\
&+2\alpha\{\langle\kappa^{-3}H_s\rangle+d_0I_3-d_1I_1-3d_3\langle\kappa\rangle\}.
\end{split}}                                                        \tag{G1}
\]
The kinetic term already contains every preparation phase. An extra \(b^2I_1\) must not be added to or subtracted from \(J_3\). Explicit derivatives of \(H_s,d_j\) commute with \(\kappa\); \(\alpha'\) is the only explicit-coefficient derivative in this force.

This is a true initial right second derivative for the actual core preparations, not merely a formal commutator or a Peano coefficient. The predecessor establishes \(\langle\kappa\rangle'_u=2\alpha\langle B\rangle\) throughout the common form-evolution interval. Moreover \(B\) is a bounded symmetric form on \(Q_3\). In the Hardy ground-state derivative \(D_\eta\), its sesquilinear form is
\[
b(\psi,\phi)=-\frac i2\int\kappa^{-1}
 [\langle\psi,D_\eta\phi\rangle-\langle D_\eta\psi,\phi\rangle],
\]
so its modulus is at most
\((\sqrt{I_\psi q_\phi}+\sqrt{q_\psi I_\phi})/2
 \le C\|\psi\|_{Q_3}\|\phi\|_{Q_3}\).
The ground-state real terms cancel. The \(Q_3\)-valued Duhamel estimate in POSITIVE_WINDOW gives
\(\Psi(t)=\phi-itH(0)\phi+O_{Q_3}(t^2)\).
Differentiating the continuous \(B\) form therefore proves (G1).
The second-order expectation has a controlled \(O(t^3)\) remainder since \(\kappa\) is also a bounded \(Q_3\) form.

Finite-rank mixed or entangled core preparations obey the same argument term by term. For an arbitrary normal state, (G1) requires an independently established second Ehrenfest identity and legal limits. Finite \(Q_3\) alone, or merely finite force terms at one instant, does not prove that identity.

## G2. A source-independent gate for a fixed range of orderings

The weighted Hardy identity is
\[
\boxed{J_3-4I_5
 =\int_0^\infty\kappa\,\|\partial_\kappa(\Psi/\kappa^2)\|^2\,d\kappa
 \ge0.}                                                            \tag{G2}
\]
It is valid for vector-valued core functions and their closure in this weighted form. The boundary cross term vanishes on the core. No source independence is assumed.

At the actual initial slice \(K=131072\),
\[
\alpha=-b_0,\quad 3<b_0<4,\quad
|d_0|<e^{50},\quad 0<d_1<e^{30},\quad .14<d_3<1,\quad
0<h<e^{-19980}.
\]
Suppose \(\langle\kappa\rangle=h\) and
\(\langle\kappa\rangle'_u=h'_{\eta_{\rm time}}/h\), as required for recovery.
Since \(g'_u=1/4\), \(|g|>1/8\), and \(|h'_{\eta_{\rm time}}|<1\),
\[
|2\alpha'\langle B\rangle|
 =\left|\frac{g'}g\frac{h'_{\eta_{\rm time}}}h\right|<2/h.
\]
The actual matter Hamiltonian is positive: \(H_s=T+V\ge0\).
Its contribution in (G1) is therefore nonpositive, even with arbitrary source–geometry correlations. Equations (G1)–(G2) imply
\[
\langle\kappa\rangle''_u
 \le-6b_0^2(\tfrac34-\eta)I_5
        +8e^{50}I_3+8e^{30}I_1+24h+2/h .
\]
Hölder gives \(I_3\le I_5^{3/5}\), \(I_1\le I_5^{1/5}\), and Jensen gives \(I_5\ge h^{-5}\). Consequently
\[
\langle\kappa\rangle''_u
 \le[-6b_0^2(\tfrac34-\eta)+P(h)]I_5,\quad
P(h)=8e^{50}h^2+8e^{30}h^4+24h^6+2h^4<1.                            \tag{G3}
\]
For the original ordering \(\eta=0\), this gives
\(\langle\kappa\rangle''_u<-30h^{-5}\).
A convenient uniform contract is
\[
\boxed{\eta\in[-1/4,1/2]\quad\Longrightarrow\quad
\langle\kappa\rangle''_u<-10h^{-5}.}                                 \tag{G4}
\]
For other \(\eta<3/4\), the precise distance condition in (G3) must be retained. There is no uniform extension to orderings arbitrarily close to \(3/4\), or beyond it.

The target quiet history satisfies
\[
h_{\rm old}''(u)=
 \frac{h''_{\eta_{\rm time}}h-(h'_{\eta_{\rm time}})^2}{h^3},
\qquad |h_{\rm old}''|<2h^{-3},
\]
because the accepted second and third conformal-time geometry jets have absolute value below one. Therefore
\[
\boxed{d_\kappa:=h_{\rm old}''-\langle\kappa\rangle''_u>8h^{-5}>0.}    \tag{G5}
\]
This gate does not use the geometric momentum budget or the two-packet ansatz. It applies to the original packets, the new near-recovery family, and every further regular preparation satisfying the stated domain, sign, ordering, and initial mean/velocity conditions.

## G3. Every fixed ordering: a stronger gate on the near-recovery family

The family in NEAR_RECOVERY has a separate result that does not restrict the once-selected ordering to \(\eta\le1/2\). Put
\(C_\eta=3\eta+7/4\ge1\).
For each fixed \(\eta\), sufficiently small \(\delta\) satisfies
\(\delta C_\eta\le1/32\).
The central packet then obeys
\[
K_c:=\delta^{-1}\!\int(1+\sqrt\delta X)^{-3}|b'|^2
      -C_\eta\!\int(1+\sqrt\delta X)^{-5}b^2
 \ge\frac{128}{729\delta}-2C_\eta\ge\frac1{12\delta}.
\]
For the remote packet, \(-K_l\le2C_\eta\). The preparation phase increases \(J_3\), so it is favorable to the upper force bound. With \(m=(1-\delta)h\), \(w<2\delta h/R\),
\[
-J_3+C_\eta I_5
 \le-\frac{(1-w)K_c}{m^5}+\frac{2C_\eta w}{R^5}
 \le-\frac1{24\delta h^5}+\frac{4C_\eta\delta h}{R^6}
 \le-\frac1{48\delta h^5}.
\]
Every packet point satisfies \(\kappa\ge441h/512\), so
\(I_3<2h^{-3}\), \(I_1<2h^{-1}\).
The remaining positive force terms are at most
\(16e^{50}h^{-3}+16e^{30}h^{-1}+24h+2/h
 <1/(8\delta h^5)\).
Since \(2b_0^2>18\), (G1) yields
\[
\boxed{\langle\kappa\rangle''_u<-\frac1{4\delta h^5}.}                \tag{G6}
\]
Thus for **every fixed ordering**, the particular normal family that makes the source's first-jet error tend to zero develops a geometry force whose magnitude grows at least as \(\delta^{-1}\). No ordering is adjusted as \(\theta\) changes. This family-specific theorem is distinct from the source-independent class theorem (G4).

## G4. The mismatch survives on a positive interval

For the actual core preparations covered by POSITIVE_WINDOW, the two histories have the same initial mean and velocity. A general normal state with only a separately justified initial force identity is not automatically covered by the third-order remainder claim. Let their total third-order remainder constant be \(C_\kappa<\infty\) on a common interval \(0\le t\le T_0\). For
\[
0<t\le\min\{T_0,d_\kappa/(4C_\kappa)\}
\]
their difference satisfies
\[
h_{\rm old}(t)-\langle\kappa\rangle_{\rm joint}(t)
 \ge d_\kappa t^2/4>2h^{-5}t^2.
\]
This uses the actual form evolution and does not require that every force term remain separately finite throughout the interval. The interval depends on the preparation. All scales are in the declared \(u\) clock and model units.

## G5. Meaning and limits

The result closes a concrete recovery test: matching a source marginal, geometry mean, geometry velocity, and initial momentum expectation does not recover the accepted mean history. Allowing arbitrarily accurate source first-jet agreement does not repair this particular family.

It is not a theorem against quantum gravity, other clocks, other orderings outside the stated class, different boundary completions, or nonadditive apparatus interactions. It does not replace the infinite-mode joint-state problem. The negative-\(g\) finite-mode generator and its domain are declared physics inputs. The companion script checks the exact differential operators, the Hardy integrand identity modulo its explicit boundary derivative, and the actual interval margins, without executing an old scientific module or ODE.
