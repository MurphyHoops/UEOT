# Two smooth radial flags are enough for this fixed preparation

The task is to condition the already specified two-ring source, not to make an arbitrarily accurate measurement of every possible source state. The actual CQ preparation has latent \(R=1\) or \(1+\sqrt3/2\), with equal weights; \(|p|^2=CR\), and each pure zero-mode block has momentum variance \(v=X_0/4\) per coordinate. The fixed angular distribution need not be changed. Write \(L=1+\sqrt3/4\).

Use the short, local derivative coupling of LOCAL_READOUT.md with input-referred pointer variance
\[
w_{\rm ptr}=C/2500
\]
per coordinate. The exact conditional record law before the reader is Gaussian:
\(Z|p\sim N(p,(v+w_{\rm ptr}+w_h)I_2)\), with the all-mode \(w_h\) bounded there. A continuous record does not have to be physically read.

Let \(r=|Z|/\sqrt C\), \(r_*=(3+\sqrt3)/4\), \(\delta_r=10^{-3}\), and use the same smooth step \(s\) as in TRANSPORT.md:
\[
\theta(r)={\pi\over2}s\left({r-r_*+\delta_r\over2\delta_r}\right),
\quad M_+(r)=\sin\theta(r),\quad M_-(r)=\cos\theta(r).
\]
Only these two flags are retained. This is a smooth complete reader instrument, with \(M_+^2+M_-^2=1\). It is not a sharp radial projection, which would make pointer kinetic energy divergent. It is not the single Kraus map \(\sqrt{E_\pm(S_0)}\) substituted for the actual field-pointer instrument.

The actual target maps are
\[
{\cal I}_b(\rho)=\operatorname{Tr}_{\rm ptr}
 [M_bU(\rho\otimes\sigma_{\rm ptr})U^\dagger M_b]
 =\int e_b(z)K_z\rho K_z^\dagger\,d^2z.
\]
Both the nonselective map and its exact source spectral law are unchanged by this reader. No fine angle/radius record is produced and erased. No event is removed. Internal \(O(2)\) covariance of the coupling and radial invariance of the flag are preserved.

## Error and posterior means

Put \(\delta=(v+w_{\rm ptr}+w_h)/C\) and \(\Delta r=(\sqrt3-1)/4\). The triangle inequality and the two-dimensional Gaussian radial tail give, for either ring, both misclassification probability and transition-annulus probability at most
\[
\varepsilon_{\rm tail}=
 \exp[-(\Delta r-\delta_r)^2/(2\delta)]<1.1\,10^{-18}.
\]
The annulus bound is separate; it is not inferred by claiming that every annulus event is misclassified.

For the source estimator equal to the ring value,
\[
D_{\rm int}=E(S_0-R)^2=4(v/C)L+8(v/C)^2.
\]
Minkowski then gives
\[
E\operatorname{Var}(S_0|b)
 \le\big(\sqrt{D_{\rm int}}+(\sqrt3/2)\sqrt{\varepsilon_{\rm tail}}\big)^2
 <1.56\,10^{-11}.
\]
The actual Bayesian posterior means, rather than the estimator values, set the future geometry. With \(v_{\rm within}=4(v/C)L+4(v/C)^2\),
\[
|\mu_b-[R_b+2v/C]|
 \le{\sqrt{v_{\rm within}\varepsilon_{\rm tail}}
              +(\sqrt3/2)\varepsilon_{\rm tail}
       \over 1/2-\varepsilon_{\rm tail}}<9\,10^{-15}.
\]
Each flag probability differs from \(1/2\) by at most the tail bound. Thus \(3/5<q_b=\mu_b/\mu<7/5\). This is a fixed-prior result. SEMANTICS.md explains why it cannot be promoted to a universal, input-independent source selector.

## Finite reader energy and actual target disturbance

For physical pointer coordinates \(X=g\beta Z\),
\[
\sum_b M_b^\dagger(\Pi_1^2+\Pi_2^2)M_b
 -(\Pi_1^2+\Pi_2^2)=|\nabla_X\theta|^2.
\]
The step bound gives \(|\theta'_r|\le800\pi\). Only the transition annulus contributes. Relative to the original pointer momentum variance sum \(1/(2g^2\beta^2w_{\rm ptr})\), the increase is at most
\(2(w_{\rm ptr}/C)(800\pi)^2\varepsilon_{\rm tail}<6\,10^{-15}\).
This is the energy cost of the specified smooth reader on its specified pointer; it does not include a gravitational model of the controller.

The entire flag-plus-field state differs from the ideal latent-ring label with the undisturbed input by at most
\[
\sqrt{(v+w_h)/(2w_{\rm ptr}+v+w_h)}
 +\varepsilon_{\rm tail}<8\,10^{-4}.
\]
This bound follows from Gaussian purification overlap and contractivity, retaining the two flags. It is an actual fixed-input estimate, not a diamond-norm statement. A trace-distance bound alone does not control unbounded stress; ACTUAL_HISTORY.md supplies the needed second moments separately. The two-field out mean energy injected by this weak short protocol is below \(1.88\,10^{-11}\) in the model units.

## One clock for both branches

Since \(3/5<q_b<7/5\), \(a_0/\sqrt{x_c}<6/5\), \(\sqrt{x_c}/A<5/4\), and \(b_-<13/12\), the branch radius ratio obeys
\(4/7<a_-/A<13/8\). Therefore \(|\log(a_-/A)|<1\) on both flags. The preparation of TRANSPORT.md needs only two ramps, with total conformal duration 200, and proper duration at most \(325A\).

Wait at each branch's final static radius until the same elapsed proper time \(325A\), retaining the actual phase and zero-mode shear. Then perform the auxiliary transition, of common proper duration \((4/5)/\lambda\), and start the same positive future window. Both outcomes thus share one proper-time schedule. Neither a tail cutoff nor a different parameter root at each time is used.

This prepares a lawful state and a specified metric history. The total matter-plus-apparatus Einstein equation during readout, waiting and metric preparation remains an independent physical gate.


For causal availability of the classical flag, take a stipulated localized collection event after the readout, and allow a further fixed conformal time \(\pi\) on the old static geometry before any global branch-dependent preparation begins. This is enough to broadcast from that point across the closed \(S^3\); it adds proper time \(\pi A\) and zero shear \(\pi/A^2\). The old stationary high covariance only rotates phases, and the actual displacement energy/moment bounds are unchanged. The later two-ramp and static-wait synchronization remains \(325A\). This closes the geometry of flag dissemination conditional on a localized collection event; the physical collection device and its gravitational source still belong to the apparatus gate.
