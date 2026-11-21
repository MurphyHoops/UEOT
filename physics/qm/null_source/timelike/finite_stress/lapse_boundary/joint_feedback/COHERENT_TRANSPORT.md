# Coherent endpoint transport, physical preparation, and the joint limit

This page synthesizes the action-derived endpoint identities with the new normality/resource and original-generator tests. It is not counted as an additional automatic science certificate. The finite identities reuse ACTION_BOUNDARY, ACTION_LIFT and the existing canonical map; new consequences are distinguished from an implemented preparation or a continuum dynamics theorem.

## T1. Transport all parts of the same CTP trace

At finite cutoff let \(V_{i,\pm}\), \(V_{f,\pm}\) be the original canonical endpoint transformations on the two branches. Use the orientation that \(V\) maps the reference representation to the bulk one. For the same branch propagators, initial cross kernel and final pairing, define
\[
U_\pm^V=V_{f,\pm}U_\pm V_{i,\pm}^\dagger,\quad
\rho_i^V=V_{i,+}\rho_i V_{i,-}^\dagger,\quad
J_f^V=V_{f,-}J_fV_{f,+}^\dagger.
\]
Then the exact trace identity is
\[
\operatorname{Tr}[J_f^V U_+^V\rho_i^V(U_-^V)^\dagger]
=\operatorname{Tr}[J_fU_+\rho_iU_-^\dagger].                       \tag{T1}
\]
It needs bounded unitaries/pairings and a trace-class cross kernel, not individual \(Q\) moments. If \(J_f=I\), the transformed pairing is \(V_{f,-}V_{f,+}^\dagger\); equality of scale factors alone does not make it the identity when the branch expansion/frame data differ.

For a time-dependent frame,
\[
H^V=VHV^\dagger+i(\partial_tV)V^\dagger
\]
is necessary to obtain T1. In the basic shear \(V=e^{i\kappa Q}\), \(Q=q^2/2\),
\[
VpV^\dagger=p-\kappa q,\quad V{\cal D}V^\dagger={\cal D}-2\kappa Q.
\]
Starting from the original \(H_{\rm raw}=NH_0+h{\cal D}\), \(h=N\kappa\), the transformed Hamiltonian is
\(NH_0-(\kappa'+N\kappa^2)Q\). Omitting the time connection would change the propagation. The full gravitational/AE/scalar terms, ordering and domains must still be transported; this basic identity does not replace them.

A useful finite check is zero physical evolution, \(U_\pm=I\), with the same frame at each branch's initial and final endpoint. The full transformed trace is identically one for every branch-frame parameter. Dropping \(J_f^V\) would instead leave the nontrivial characteristic function of \(Q\). Its derivatives would look like noise although the experiment has not changed.

## T2. Initial contacts and the flat connection

For the basic high shear, with the fixed reference \(\kappa_*\) held once and
\(\beta_\pm=\kappa_\pm-\kappa_*\),
\[
\rho^V=e^{i\beta_+Q}\rho_{\rm ref}e^{-i\beta_-Q}.
\]
If the external reference source family is held fixed, its finite-cutoff contacts are
\[
\partial_{\kappa_+}\rho^V=iQ\rho^V,\quad
\partial_{\kappa_-}\rho^V=-i\rho^VQ,
\]
\[
\partial_{\kappa_+}^2\rho^V=-Q^2\rho^V,\quad
\partial_{\kappa_-}^2\rho^V=-\rho^VQ^2,\quad
\partial_{\kappa_+}\partial_{\kappa_-}\rho^V=Q\rho^VQ.              \tag{T2}
\]
For external parameters \(a,b\), the full chain rule also includes
\[
\begin{split}
\partial_{ab}\rho^V={}&i\beta_{+,ab}Q\rho^V-i\beta_{-,ab}\rho^VQ
-\beta_{+,a}\beta_{+,b}Q^2\rho^V
-\beta_{-,a}\beta_{-,b}\rho^VQ^2\\
&+(\beta_{+,a}\beta_{-,b}+\beta_{+,b}\beta_{-,a})Q\rho^VQ .
\end{split}
\]
At \(N=1\), for scale/lapse directions \((w,\nu),(z,\mu)\) at fixed canonical \(q\),
\[
\delta\kappa=w'-h\nu,\qquad
\delta_{xy}\kappa=2h\nu\mu-w'\mu-z'\nu.                           \tag{T3}
\]
For physical \(\phi\)-fixed scale variations, the additional \(q=a\phi\) scaling and its measure/dilation must be differentiated too.

The actual finite-\(K\) Schwartz source and compact smooth geometry core justify these products and derivatives. More generally a positive density with \(\operatorname{Tr}\rho Q^4<\infty\) suffices for the required trace-class second derivatives. An off-diagonal CTP cross kernel is not itself positive; one must instead specify its left/right product domains, or use the actual Schwartz factorization. Arbitrary normal states do not automatically have these moments.

There is a weaker separating-test version for every normal state. For finite-rank \(B=|f\rangle\langle g|\), \(f,g\in D(Q^2)\), the products \(QB,BQ,Q^2B,BQ^2,QBQ\) are bounded. Thus
\(\operatorname{Tr}\rho V_-^\dagger BV_+\) has the corresponding first and second weak derivatives. This does not assert that \(Q\rho Q\) is trace class for arbitrary \(\rho\).

For a differentiable general controlled \(V\), including noncommuting scaling/low-mode factors, define
\[
{\cal A}_a=-i(\partial_aV)V^\dagger,\qquad
\nabla_a\rho^V=\partial_a\rho^V-i{\cal A}_{+,a}\rho^V
                                    +i\rho^V{\cal A}_{-,a}.
\]
On the common derivative domain,
\[
\partial_a{\cal A}_b-\partial_b{\cal A}_a-i[{\cal A}_a,{\cal A}_b]=0,
\quad
\nabla_a\rho^V=V_+(\partial_a\rho_{\rm ref})V_-^\dagger.             \tag{T4}
\]
The second covariant derivative likewise transports
\(\partial_a\partial_b\rho_{\rm ref}\).
For example \(V=e^{i\kappa Q}e^{-iu{\cal D}}\), with
\([{\cal D},Q]=-2iQ\), has
\({\cal A}_\kappa=Q\), \({\cal A}_u=-{\cal D}+2\kappa Q\).
These connections do not commute, although their curvature vanishes.

A reference source family unchanged by an **external** variation has zero covariant state derivative. This is not the statement that a quantum geometry density kernel has zero derivatives. For a specified joint kernel
\(\rho_{\rm ref}(\kappa_+,\kappa_-)=g(\kappa_+)g(\kappa_-)^*\rho_S\),
T4 retains \(g'\), its phase and all actual geometry preparation data. Treating the external endpoint labels as quantum coordinates while discarding these derivatives would delete the physical current rather than solve its constraint.

## T3. A transported mixed term is not a free new constraint charge

On the common core, \(VP_\kappa V^\dagger=P_\kappa-Q\) and
\(VpV^\dagger=p-\kappa q\). The original commuting factors remain commuting:
\[
[P_\kappa-Q,p-\kappa q]=iq-iq=0.
\]
This is a common-core differential identity, not a self-adjoint realization of half-line \(P_\kappa\). The physical flux weights and connection terms already identified in PHYSICAL_SLICE also remain part of that transport.

More generally, for a **given self-adjoint residual** \(R\), set
\(R^V=VRV^\dagger\) on \(VD(R)\). For every bounded Borel function,
\[
\operatorname{Tr}(V\rho V^\dagger)f(R^V)=\operatorname{Tr}\rho f(R). \tag{T5}
\]
Its entire residual spectral law, including the constraint-kernel probability, is unchanged. For a merely formal constraint without a selected self-adjoint realization only its core/form identity is asserted.

The old fixed-source/independent-carrier exclusion is covariant in exactly the same way: both carrier and source algebras, their support projection and the state have to be transported. Canonical mixed momentum terms do not evade that theorem. Leaving a state or observable untransported changes the physical preparation/question.

## T4. What a true preparation contribution would have to provide

If variations change the physical past, even the same incoming state generally has a nonzero finite-slice density variation. A common preparation must have
\[
\rho_i[g_+,g_-]=U_{{\rm pre},+}[g_+]\rho_0U_{{\rm pre},-}[g_-]^\dagger
\]
from the same \(\rho_0\) and actual past dynamics. After removing the frame connection, its derivatives contain genuine Duhamel insertions:
\[
\delta U_{\rm pre}=-i\int U(i,s)\,\delta H(s)\,U(s,t_0)\,ds .
\]
Second variations contain both time-ordered double insertions and
\(-i\int U\,\delta^2H\,U\). All source, controller and interaction stress must enter that same Hamiltonian/action. On an explicit finite-cutoff common domain, this gives legitimate physical initial response blocks with positive Gram consistency.

Such an external-metric cross kernel alone does not specify a normal geometry–source state. At finite \(K\), a separately specified normal joint reference density can be transported by the controlled \(V_K\). A chosen normal geometry packet and a measurable controlled source preparation can also define a normal joint state. Their original constraints, mean history and geometric current then require verification. This choice is not supplied by T2.

The actual source-driven initial constraint column from ACTION_LIFT, including
\(h_i\,\delta P_u+H_{i,K}=0\), remains a physical requirement. Neither a flat connection nor the presence of \(Q\rho Q\) in a branch kernel enforces it.

## T5. A coherent observable limit exists kinematically

Let \({\cal A}_K=B({\cal H}_G\otimes{\cal F}_{\le K})\) and
\(j_{LK}(A)=A\otimes I\). The endpoint maps define
\[
\alpha_{LK}=\operatorname{Ad}V_L\circ j_{LK}\circ
             \operatorname{Ad}V_K^\dagger,\qquad
\alpha_{ML}\alpha_{LK}=\alpha_{MK}.                               \tag{T6}
\]
For one fixed normal raw state \(\rho\), its restrictions \(\rho_K\) and
\(\tilde\rho_K=V_K\rho_KV_K^\dagger\) obey
\[
\operatorname{Tr}\tilde\rho_L\,\alpha_{LK}(A)
 =\operatorname{Tr}\tilde\rho_KA .
\]
The resulting inductive algebra and state are isomorphic to the raw ones by the local maps \(\operatorname{Ad}V_K^\dagger\). No full-field Fock unitary \(V_\infty\) is inferred.

For the legitimate half-line geometry Weyl pair
\[
M_s=\kappa^{is},\qquad D_t\psi(\kappa)=e^{t/2}\psi(e^t\kappa),
\]
the transported \(M_s\) and \(V_KD_tV_K^\dagger\) are compatible and have the continuous characteristics of the original normal state. Their GNS representation is regular for these groups.

For the endpoint form in ENDPOINT_NORMALITY, the latter observable explicitly contains
\[
e^{i\theta_K(1-e^t)\kappa}
 V_{{\rm low},K}(\kappa)V_{{\rm low},K}(e^t\kappa)^\dagger
 e^{i(1-e^t)\kappa Q_{3:K}}D_t .                                  \tag{T7}
\]
For a general scalar phase \(S_K(\kappa)\), replace the first factor by \(e^{i[S_K(\kappa)-S_K(e^t\kappa)]}\); this includes the original cubic geometric phase. It is not the bare fixed-partition dilation \(D_t\). Thus this regular transported algebra does not contradict ENDPOINT_NORMALITY's nonregular limit for the fixed bare observables, or MIXED_RESOURCE's cost for a fixed normal geometry marginal. They are different limiting observable questions.

## T6. Why this does not yet close the joint physics

For time-dependent frames let
\(\bar U_K(u,v)=V_K(u)^\dagger U_K(u,v)V_K(v)\).
A dynamics compatible with T6 would require, for all bounded local \(A\),
\[
\bar U_L^\dagger j_{LK}(A)\bar U_L
 =j_{LK}(\bar U_K^\dagger A\bar U_K).
\]
Its common-core derivative requires
\([\bar H_L,jA]=j[\bar H_K,A]\). JOINT_CUTOFF J4 directly disproves this exact condition for the original coefficients. J10–J11 additionally reject the unchanged actual-source product-core generator limit. CORRELATED_GAUSSIAN subsequently constructs a different, changed-source normal bulk state limit; its original covariant constraint form still diverges. Thus that positive state construction closes a kinematic question without supplying compatible physical dynamics.

A renormalized propagator limit can still be a different mathematical question, but it needs uniform estimates, a declared topology, transported adjoints and a common preparation/domain. It does not follow from T6, the finite-\(K\) unitary theorem, or the fixed-background CTP limit. The latter retains an external classical geometry and is not already a solution of the quantum joint evolution.

The next closed-loop task is therefore concrete: construct or reject a common renormalized joint propagator and normal/algebraic preparation in the chosen representation, with its original constraints and total source. Canonical covariance, state preparation, continuum dynamics and an autonomous readout must be verified together before a claim of physical unification.
