# v31.7 发布文档准备脚本独立语义复审

状态：`PASS_READ_ONLY_SCRIPT_REVIEW_ACTUAL_OUTPUT_REVIEW_PENDING`。

两个 helper 已完整只读审阅，B 未导入、未执行、未修改它们，也没有修改或重编数学源码。当前没有阻塞项；实际候选生成后的文件核对仍待完成。

## 审阅身份

- `/tmp/qm317_prepare_release.py`：`717ac7e3b8fa71d86098338e77f34817ca9d1989d28617e5d6a9e1c6ae75e474`。
- `/tmp/qm317_book_release.py`：`cb7163e87af99c9c9063441d555fa37c6ef7791b1f83a11e501a1df19f52d495`。

首次问题来自修订前的全文读取与即时协作反馈；当时未在 root 开始修复前捕获原脚本字节。因此后来的 after_feedback 快照明确视为已含主要修复的检查点，不冒充初始缺陷版本。最终复审绑定上列精确脚本。

## 六项反馈及实际修正

### R1 — RESOLVED

Current code identity is replaced, but top-level canonical_identity remains edition3.2 with the old MD SHA/57 chapters/117 results. Top-level remote_metadata_completion still points to v3.2 remote acceptance without an explicit historical role.

Current canonical_identity is rebuilt from actual3.3 Markdown bytes/counts. Prior3.2 code/canonical/remote objects are explicitly preserved under prior_v3_2 fields. Current remote_metadata_completion is PENDING and remote_verified=false. SOURCE_MANIFEST points to current local proof and current legacy source-reuse identity without claiming a new757 execution.

### R2 — RESOLVED

The inherited body retains Total459/22, the current573=459+114 paragraph, and current84 dedicated witness count; seven new rows are inserted after the old total instead of updating it. These conflict with the new646/855/151 header.

All seven new rows precede the Total row; current total becomes646/29; current855=646+209 and v31.7 increment187+95=282 are explicit; current witness exclusion becomes151. The v31.6 and earlier increments are explicitly historical. All five replacement anchors occur exactly once in the inherited README.

### R3 — RESOLVED

Every inherited entry receives current_proof_receipt and a mathematical-source-rechecked verification scope, including QMK12 NOT_ESTABLISHED, QMK13 NOT_CLAIMED, QMK17 SOURCE_REVIEW and Python/refinement-open claims. Their original status is preserved, but the added proof scope is too broad.

Only machine_status VERIFIED_LEAN_BUILD_AND_AXIOM_AUDIT receives the actual rechecked proof scope. Open/runtime/source-review entries explicitly retain their original status and have current_proof_receipt removed. QMK21 uses the actual instance receipt, QMK40/44 the actual witness receipt.

### R4 — RESOLVED

Runtime and instance/evidence receipt fields remain on v31.6; QMK28 still lists constructing the joint carrier as open; QMK40/44 still use current84/459, and QMK44 says no current convergence/uniqueness theorem.

Prior_v31_6_evidence preserves old receipt/scope/limits/open-item values before current runtime/instance paths move to v31.7. QMK28 open_items now concern stepwise/action budgets and stabilized distance, QMK39 the additional real presentation, QMK40/44 current151/646 with original witness scope, and QMK43/44 explicitly point to specified-model new dynamics.

### R5 — RESOLVED

Source conditional-state exact contraction can be read as a pairwise arbitrary-initial-state contraction. Actual theorem is exact distance to the fixed source state, with initial-state-dependent denominator z_n(tau). Doob pairwise contraction is separately proved.

QMK54 and the formal README now say exact distance scaling to the source fixed state. The limit explicitly preserves the initial-state-dependent denominator and excludes arbitrary two-source-state contraction. Doob pairwise exact contraction remains separately and correctly stated. The report formula was already correct; review prompted a prose-scope correction, not a theorem change.

### R6 — RESOLVED

ledger schema retains ueot_qm.claim_ledger.v31.6; new claims omit module source lists; real partial trace is ambiguous in a finite complex setting; report contains 复杂量子模型.

Schema is v31.7. Every newQMK45–54 claim obtains sources from actual declaration inventory and all witnesses must be in the actual audit targets. actual partial trace and 复量子模型 replace ambiguous terms.

## 当前与历史的证据边界

- **CURRENT_integration**：Entire current object rebuilt; pr_status/main_status PENDING; successful predecessor integration nested only under previous_version.
- **ledger**：Current verification LOCAL_VERIFIED_REMOTE_PENDING, local_status PASS, remote_status PENDING; prior version verification preserved separately.
- **book_source_manifest**：Current3.3 code/canonical identity local only; current remote_verified=false. Old remote receipt explicitly historical.
- **book_release_gate**：Creates local proof/structure/PDF/visual gates, remote_gate PENDING and remote_verified=false. No source/main commit or workflow PASS invented.

## 科学语义核查

- Full-state convex-purity and actual finite Gram purification do not claim the reverse pure-to-vector characterization or essential uniqueness.
- Actual complete operational presentations and seven elementary laws are distinguished from all reconstruction axioms or a Core-only derivation.
- Every finite auxiliary PSD input and actual adaptive leaf matrix are covered; whole-protocol defect is explicitly distinguished from stepwise/action budgets and diamond error.
- Feedback negative control keeps the quantum memory identity while separating real later records.
- Doob exact pairwise contraction is distinguished from source conditional exact distance to rho-star with a state-dependent denominator.
- The same rational model provenance, legal identity-Doob countermodel, finite-success limits and infinite-path boundary remain explicit.
- v31.8 remains unformalized planning; reality of three generations, masses, vacuum, continuum and empirical truth is not promoted.

特别保留本次发现与修正：任意两初态的精确收缩属于 Doob 通道；源条件态证明的是到固定ρ*的距离按 a_n/z_n(τ) 缩放。原主报告的显式公式已正确，修订的是标题和英文段落中可能引起过强理解的措辞，未修改数学结论。

## 实际状态与下一步

已只读核对统一 lean-verification、acceptance-progress 和 finite-witnesses 三份实际回执均为 PASS；源集包含80项，SHA `b453ce5028eb1ef7d324326245ae5c6cc1a0bf3f40cabf691f25bb1aae7a5911`，主包646定理/855审计。

PDF视觉回执完成前不运行出版 helper；实际生成后，还须对 CURRENT、54条台账、各 README 与总著来源清单逐个回读并绑hash。本复审不会把脚本准备、历史成功或本地PASS改写成新版本远端PASS。
