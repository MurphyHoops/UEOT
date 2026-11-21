# Same initial reductions and geometry readings, different actual pressure feedback

This is a construction in the original complete \(K=131072\), negative-\(g\) generator. It retains the original thin raw source state and its actual incoming transport. It does not replace the Hamiltonian by a controlled-gate toy.

## C1. Keep the previous two-packet preparation and add a hidden current phase

Use NEGATIVE_RECOVERY's actual \(h=h_i>0\), ordering \(\eta\ge-1/4\), low packet
\(y=\kappa/h\in(3/8,5/8)\), far packet centered at \(R>1\), and
\(w=h/(2R-h)\). Their normalized real profiles are the same. The low conditional density is even about \(y=1/2\).

Define
\[
 X_0=y-\tfrac12,\quad v_s=\langle X_0^2\rangle_s,\quad
 F(y)=X_0^2-v_s .
\]
Then \(\langle F\rangle_s=\langle yF\rangle_s=0\).
Choose a smooth real primitive \(\zeta\) whose derivative equals
\(\kappa F(\kappa/h)\) near the low support and vanishes near every possible far support \(\kappa\ge0.9\). A compact smooth transition in the gap supplies such a primitive. Let
\[
 b=g h'_\eta/h,\qquad
 \theta_\pm=b\kappa^2/2\pm\zeta,\qquad
 \psi_{G,\pm}=e^{i\theta_\pm}
       \left(\sqrt{1-w}\psi_s+\sqrt w\psi_R\right).
\tag{C1}
\]
Apply the same fixed pure geometry phase to return to the original raw frame. Tensor each with the identical rank-two source density. Both are positive normal joint densities of rank at most two, with common-core components.

They have exactly the same full \(\kappa\) probability law, source \(\sigma\),
\(\tau=I_1\sigma\), every finite \(\kappa\) moment, and \(I_2\).
The extra contribution to the initial \(\kappa\) velocity is
\(\pm(1-w)g^{-1}\langle F\rangle_s=0\).
The difference of phase kinetic energies is proportional to
\(4b(1-w)h\langle yF\rangle_s=0\).

Each phase adds the same nonnegative kinetic resource
\[
 q_{\rm extra}=(1-w)h\langle yF^2\rangle_s
 \le5h/32768<h/6000.
\tag{C2}
\]
This does not automatically leave the old \(\Pi_g\) target unchanged.
Repeat the original scalar IVT once for both states together. At \(R=1\),
\(\alpha<0\) makes the added term more negative; at
\(R_{\rm up}=10\sqrt{Q_\eta}h^{-2}\), \(Q_\eta=60000+21|\eta-3/4|\),
its magnitude after multiplication by \(h^3\) is smaller than
\(4h^4/6000\), below the already certified strict bracket margin.
The original \(b^2h\) phase contribution and every \(d_j\), \(H_s\), \(U_0\) term remain included. Thus one common root \(R_*\in(1,R_{\rm up})\) restores the old \(\Pi_g\) mean for both. The \(\kappa\) mean and initial velocity stay exactly matched for every \(R\). There is no later parameter reselection. The previous very large tail costs remain.

## C2. The unrecorded current changes the next source jet

At the initial common core define
\(J_\pm=\langle i[H_G,\kappa^{-1}]\rangle_\pm\).
All multiplication potentials, including the ordering term, commute with \(\kappa^{-1}\). The principal current gives
\[
 J_{\rm phase}=-2\alpha\int\kappa^{-3}\theta'|\psi_G|^2d\kappa,
 \qquad
 \boxed{\Delta J=-4\alpha(1-w)h^{-2}d_s},\quad
 d_s=\langle y^{-2}F(y)\rangle_s .
\tag{C3}
\]
This is a legitimate core coefficient. No global derivative of the unbounded inverse moment was assumed.

To prove a nonzero lower bound, set \(Z=X_0^2\). Evenness replaces \(y^{-2}\) by
\(G(Z)=(1/4+Z)/(1/4-Z)^2\).
For \(0\le Z<1/64\),
\(G'(Z)=(3/4+Z)/(1/4-Z)^3\ge48\).
The independent-copy covariance formula yields
\(d_s=\operatorname{Cov}(Z,G(Z))\ge48\operatorname{Var}Z>0\).

For an explicit bound, \(X=8X_0\) has the actual normalized bump-square density proportional to \(e^{-2X^2/(1-X^2)}\), whose normalization integral is at most two. The events
\(|X|\le1/4\) and \(1/2\le|X|\le3/4\) have probabilities at least
\(e^{-2/15}/4\) and \(e^{-18/7}/4\), and their \(X^2\) values differ by at least \(3/16\). Hence
\[
 \operatorname{Var}(X^2)\ge9e^{-284/105}/4096,\qquad
 d_s\ge27e^{-284/105}/2^{20}.
\tag{C4}
\]

The exact initial product-state expansion of the same complete joint evolution is
\[
 \sigma'_0=-iI_1[H_s,\sigma],\quad
 \sigma''_0=-i[I_1H_s'+J_0H_s,\sigma]
                    -I_2[H_s,[H_s,\sigma]].
\tag{C5}
\]
The two preparations thus have the same \(\sigma_0,\sigma_1\), but
\[
 \Delta\sigma''_0=-i\Delta J[H_s,\sigma].
\]
Use the already constructed actual bounded radial-flow witness \(B_s\), not a newly selected source:
\[
 c_s=\operatorname{Tr}\sigma i[H_s,B_s]
       \ge\sqrt3e^{-2/3}/800>0 .
\]
Since \(|\alpha|>3\) and \(1-w>1/2\),
\[
 |\Delta\langle B_s\rangle''_0|
 \ge\frac{162\sqrt3}{800\,2^{20}}e^{-118/35}h^{-2}
 >10^{-9}h^{-2}.
\tag{C6}
\]

## C3. This is also an actual mean pressure distinction

The explicit \(u\)-dependence of \(p_s(u)\) contributes identical terms for the two states through first order, because \(\sigma_0,\sigma_1\) agree. Therefore the complete second-order difference is
\[
 \boxed{\Delta\langle p_s\rangle''_0
  =-\frac{4\Delta J}{3V_0A^4}
                  \langle D_\Omega\rangle_{\rm old}\ne0.}
\tag{C7}
\]
PRESSURE_WITNESS evaluates the actual incoming expectation and controls its remainder. RAW_WARD then places the corresponding density difference one derivative later; it is consistent with exact source conservation.

POSITIVE_WINDOW gives actual positive intervals and explicit vector-norm remainder formulas for both the trace-distance distinction and the raw pressure distinction. These are not only formal jet inequalities.

## C4. Consequence for the closure task

The source state, inverse-expansion weighted source state, full expansion probability law, initial expansion velocity, and the matched \(\Pi_g\) mean do not determine a unique next source or pressure response. The missing information is a genuine geometry current phase. The original normal joint density and its already constructed evolution remain a closed description. This result does not reject that evolution, choose a unique quantum boundary rule, or complete physical unification.
