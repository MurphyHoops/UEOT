# UEOT-QM

当前方案：**v31.0，2026-10-19**。  
研究主线：已有 v23.0–v30.11 QM 成果与 Frozen Core v3 的精确桥接。  
本次发布的范围：方案、理论/Lean 审计、新条件定理的纸面精化及精确可复算证据。

## 从这里开始

- [完整升级方案](UEOT_QM_UPGRADE_PLAN_v31.0.md)：理论定位、各阶段继承、两条主线、六个量子桥、实验出口和验收。
- [工作路线](ROADMAP.md)：当前优先级、依赖与后续执行次序。
- [Core 对象—协议桥](audits/CORE_OBJECT_PROTOCOL_BRIDGE_20261019.md)：核心定义、旧推论边界、可观测闭包与有限资源合同。
- [Lean 证据与接口审计](audits/CORE_LEAN_TO_QM_AUDIT_20261019.md)：固定提交中的准确 theorem 名、真实输入和 proof 边界。
- [三代选择定理精化](audits/G3_SELECTOR_REFINEMENT_20261019.md)：去掉 atomicity、完整谱修正、两代对照谱和独立检查。
- [来源清单](status/SOURCE_MANIFEST_20261019.json)、[QM 主张台账](status/CLAIM_LEDGER_v31.json)、[当前状态](status/CURRENT.json)、[交叉审查回执](audits/REVIEW_20261019.md)。

## 本次已经推进的内容

三代条件选择中，指定表示谱的异常方程加上弱作用窗口预算，已足以推出 `(Nc,Nf,k)=(3,3,1)`；primitive/atomicity 不再作为额外前提。任意 β 的 generalized-331 谱明确补入 exotic-lepton singlet completion，并保留一个放宽轻子表示模板后的两代局域异常反例。完整证明见专题审计。

量子操作主线将 v23 已有 FFIPS/instrument/SRN 成果接到 Core v3 的响应商、递归充分态和误差运输。优先实现有限 instrument → 合法记录 → 受限协议闭包 → 可递归对象 → 误差证书；新的 QM Lean 表面尚待构建。

Core 的 106/106 是冻结数学合同的覆盖记录。当前 QM 目录不把该计数、历史数值回归或本轮纸面定理等同于“全部量子物理已在 Lean 中证明”。有关历史来源、本轮检查和未来任务的状态分别列于台账。

## 可复跑的本轮证据

从仓库根目录运行（Python 3，仅标准库；不要使用关闭断言的 `python -O`）：

```bash
python physics/qm/benchmarks/qm_bridge_benchmarks.py
python physics/qm/benchmarks/qm_frontier_exact_audit.py
```

实际回执：

- [操作桥基准](benchmarks/results/qm_bridge_benchmarks.json)：4 组通过，包括协议闭包、后选择放大、有限 CCR 障碍和 selector。
- [异常/谱精确审计](benchmarks/results/qm_frontier_exact_audit.json)：13 项通过，包括符号恒等式、两代谱与逐前提对照。
- [执行来源](benchmarks/results/EXECUTION_MANIFEST_20261019.json)：脚本哈希、结果哈希、执行环境和证据范围。

这是新程序的精确有限/符号核对。历史 v30.11 的 27/27 只读取了其原回执，本轮未重新运行那个归档程序。

## 目录与边界

`physics/qm/` 是本项目已有的远端 QM 目录。量子包拟建于 `formalization/ueot-qm/`；QFT/RG 的未来专门实现继续遵循仓库既有分层，本目录保留统一入口。

历史 QM 原件的字节迁移仍待完成；来源清单已记录可读正文的核对范围及两个 v28.1 文件的版本冲突。本次方案不将文本视图伪装成经过哈希核验的历史原件。

