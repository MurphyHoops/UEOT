# v31.8 规划：A 路只读审查

**科学目标与范围：PASS。** 本合同尚未执行，不计 v31.7。没有发现把结论输入构造器、把向量版冒充任意纯化，或把一般联合态偷换成可分离态的设计。

源 SHA-256：`dfed37f3245fd2e4e48ac6b7e51d3df953b8294a96505b1f54884ce50e36147d`。

## 核心核对

- **priority**：A separation/tomography, B full purity then precise uniqueness, C composable history budgets target actual remaining gaps; solved Doob example is not used to replace them.
- **effect_distance**：Existing effectDistance_eq_zero_iff means equality of all effect probabilities, not equality of matrices; the proposed new separation theorem supplies the missing step.
- **legal_effects**：All index probes must be legal effects. General product-effect tomography ranges over all joint densities and does not assume separability.
- **gram_columns**：Gram factors are PSD-derived; positive column weights sum to one. Residual positivity must be derived from the sum of the other columns; square-root normalization and zero cases are explicit proof obligations.
- **pure_scope**：Vector-to-extreme is inherited, reverse extreme-to-vector is a new theorem. Arbitrary-purification uniqueness cannot be claimed before connecting this reverse direction.
- **unitary_scope**：Same actual finite auxiliary carrier first; different dimensions separately typed. No existence of the needed unitary or desired result is supplied as a field.
- **history_scope**：Actual finite history carrier, explicit dephasing if extended to coherent history inputs, real block normalization and zero-block treatment, all-event TV and primitive defects remain distinct stages.
- **claims**：Plan is unproved, not part of v31.7 totals, and makes no full-Core, universal complex-selection, physical-generation or infinite-system claim.

## 执行前精确化建议

- **N1**：Keep the old effectDistance_eq_zero_iff meaning; separately name the new equality-to-density theorem.
- **N2**：State auxiliary action as psi2(i,a)=sum_b U(a,b)*psi1(i,b), U†U=UU†=I, with actual I tensor U action. For vectorize A(i,a)=A_i_a, factor equality B=A*V corresponds to auxiliary unitary U=transpose V; do not silently identify these orientations.
- **N3**：Specify real-linear spanning of Hermitian spaces, since the probability pairing is real-linear.
- **N4**：For action budgets define the worst case over finite histories/used actions, or explicitly assume finite actions; avoid an undeclared maximum over an arbitrary action type.

没有执行新的 Lean、修改规划或发布任何远端动作。


## Final plan revision read-back

All three requested precision items are now applied: keep the existing zero-distance/equal-probability theorem semantics and add a new separation name; use real-linear Hermitian spanning; fix the auxiliary action and the factor transpose orientation explicitly. Final revised plan SHA256: `280fdb652561fee8a278654df21445ee862071999281cb3a1ddeae201dacc67c`. Final status: **PASS_FINAL_PLAN_SCIENTIFIC_SCOPE**. This is a planning/source-scope review, not execution or formalization of v31.8.
