# A dynamical controller is not a free internal relabelling

Use the explicit new action
\[
 S=-\frac12\int\sqrt{-g}\,[F^2(\nabla\chi)^2+
 (\nabla\phi)^2+(\nabla\psi)^2+2\kappa(\chi)\nabla\phi\cdot\nabla\psi],
\]
with F>0 and |kappa|<1. In coordinates (chi,phi_+,phi_-) the target-space metric is diag(F^2,1+kappa,1-kappa), positive and smooth. Its mixed sectional curvature is
\[
 K_{+-}=\frac{\kappa'(\chi)^2}{4F^2(1-\kappa^2)}.
\]
The script computes the Christoffel symbols and Riemann component independently. Wherever kappa' is nonzero this metric is curved, so an invertible pointwise field-coordinate transformation cannot turn the full dynamical model into three free flat-target fields.

The Euler expressions are E_phi=div(dphi+kappa dpsi), E_psi=div(dpsi+kappa dphi), E_chi=F^2 Box chi-kappa' dphi.dpsi. For the full metric stress,
\[
 \nabla^\mu T_{\mu\nu}=E_A\partial_\nu X^A.
\]
The controller supplies the opposite of the fields/interaction divergence -kappa' dphi.dpsi dchi. This is a complete classical Ward identity; the interacting quantum field theory still needs its own effective-theory and renormalization data.

By comparison, a globally pure internal connection A_mu=R^{-1}partial_mu R can be removed by Psi=R Phi, with D Phi=R^{-1}dPsi. If the initial and final R agree, consistent endpoint identifications give free scattering identity; if they differ by a constant orthogonal matrix, the result is an internal rotation. A fixed species reader may distinguish that rotation, while the total stress is unchanged. The reader must be transformed consistently when interpreting a change of variables.

For a real orthogonal block matrix O, preservation of the target momentum vector requires its target rows to be (I,0). Orthogonality then makes the probe/target block zero. Even the weaker operator identity |P_T'|^2=|P_T|^2 forces B^T B=0 for the target/probe block B, hence B=0, and again C=0. Thus this pure-rotation mechanism cannot provide the specified nonzero target-to-probe QND gain.

This conclusion is limited to the stated globally pure-gauge and orthogonal model. It does not exclude physical gauge fields, other reader contracts or the curved controller model.
