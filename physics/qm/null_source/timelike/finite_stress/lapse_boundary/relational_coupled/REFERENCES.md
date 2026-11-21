# 本轮实际使用的外部数学来源

- A. Balmaseda, D. Lonigro, J. M. Pérez-Pardo,
  *On the Schrödinger Equation for Time-Dependent Hamiltonians with a Constant Form Domain*,
  arXiv:2112.11063v2 (2022), https://arxiv.org/pdf/2112.11063 .
  root实际读取Assumption3.8、Proposition3.9、Theorem3.10及其适用范围。
  本轮使用闭型表示定理和C²共同型域的传播定理；具体系数、共同域和界由新证明验证。
  这些是标准外部数学，不计为UEOT新定理。
- J. Kisyński, *Sur les opérateurs de Green des problèmes de Cauchy abstraits*,
  Studia Mathematica 23 (1964), 285–328,
  https://doi.org/10.4064/sm-23-3-285-328 .
  原传播定理来源；本轮通过上述研究论文的精确重述核适用条件，
  没有声称root已取得并逐页审读原出版社PDF。
- J. Louko, E. Martínez-Pascual,
  *Constraint rescaling in refined algebraic quantisation: momentum constraint*,
  J. Math. Phys.52,123504 (2011), https://arxiv.org/abs/1107.1092 .
  用于提醒classical constraint rescaling不自动保证量子实现等价；
  本轮positive clock-patch构造自行给出，不把该论文的特定模型结论当作本模型定理。

半轴Hardy、Poincaré、闭型表示和Stone群定理是标准数学输入。
本目录明确区分这些输入与对当前固定作用量/源态/参数的新应用。

## 后继闭环实际核对的一级来源

- L. Bruneau, J. Dereziński, V. Georgescu, *Homogeneous Schrödinger operators
  on half-line*, https://users.fuw.edu.pl/~derezins/homogeneous.pdf .
  root实际打开原作者PDF，核半轴Hardy、inverse-square与Friedrichs范围。
  ORDERING_DOMAIN的具体参数映射和资源界由本目录自行推导。
- P. Korman, *A remark on Pinney's equation*,
  https://homepages.uc.edu/~kormanp/pinney.pdf .
  root实际读取两页原文；使用标准Wronskian构造，具体lens恒等式另验。
- P. R. Anderson, W. Eaker, *Analytic approximation and an improved method
  for computing the stress-energy of quantized scalar fields in
  Robertson-Walker spacetimes*, https://arxiv.org/pdf/gr-qc/9906055 .
  root实际读取原文eqs.(5)--(9)附近：源与adiabatic counterterms必须合并。
  它没有给本量子几何/CTP算子的全场存在性。
- S. Hollands, R. M. Wald, https://arxiv.org/abs/gr-qc/0103074 ,
  https://arxiv.org/abs/gr-qc/0111108 .
  root实际核对两篇摘要所述local/covariant Wick与time-ordered产品范围；
  只作固定背景重整化责任说明，未声称逐页审读或套用到量子几何。

- Z. Ammari, S. Breteaux, *Propagation of chaos for many-boson systems in
  one dimension with a point pair-interaction*, https://arxiv.org/pdf/0906.3047 .
  root实际读 Appendix C Definition C.1、Corollary C.4 及所列全部比较型假设，
  特别是 D(F^(3/2)) 上的commutator条件；A/C独立核对。
  本轮只使用其抽象传播定理，不搬用该文many-boson物理模型或结论。

## Clock-boundary and scalar-clock sources actually checked

- Bruneau--Derezinski--Georgescu, the above homogeneous-operator paper:
  root additionally read Theorem 5.2 (Hankel unitary diagonalization) and
  the local-projection decay used in the proof of Theorem 6.1.
  G_ZERO_BOUNDARY proves the complete coupled wave operators itself;
  that result is not quoted from the free inverse-square paper.
- D. Lenz, T. Weinmann, M. Wirth, *Self-adjoint extensions of bipartite
  Hamiltonians*, https://arxiv.org/pdf/1912.03670 .
  Root read Section 1, especially Theorem 1.2 on deficiency spaces and
  the self-adjoint extension parametrization. Only that general standard
  theorem is used; the UEOT operator is not asserted to be their
  separable bipartite Hamiltonian.
- P. A. Hoehn, A. R. H. Smith, M. P. E. Lock,
  *Equivalence of Approaches to Relational Quantum Dynamics in
  Relativistic Settings*, Frontiers in Physics (2021),
  https://www.frontiersin.org/journals/physics/articles/10.3389/fphy.2021.587083/full .
  Root read the section 6 discussion distinguishing the conserved
  Klein--Gordon current and raw wavefunction probabilities, and the
  section 7 frequency-sector caveat. It is a framework comparison,
  not a proof of the current extension, source embedding or device.

The bounded-congruence Abel calculation in MATTER_CLOCK uses an explicit
resolvent/Laplace/Duhamel argument written there. It does not infer
group-average equivalence merely from a classical constraint rescaling.

- Ammari--Breteaux, Appendix B Theorem B.2 in the already cited
  https://arxiv.org/pdf/0906.3047 : root additionally read the exact
  form version of Nelson's commutator theorem, including its
  D(S^(3/2)) hypothesis. RAW_SOURCE_BOUNDARY verifies those hypotheses
  for the actual finite-K source quadratics.
- C. J. Fewster, R. Verch, *Quantum fields and local measurements*,
  https://arxiv.org/pdf/1810.06512 : root read Proposition 3.1(b)
  and Eq.(3.23), including the nonselective/selected distinction.
  ANGULAR_CLOCK_INPUT applies this only to the complete local QFT
  on the prescribed geometry, not to a sharp finite-K model.
