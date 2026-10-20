# C 对 v31.7 统一验收与声明库存脚本的最终只读审查

**PASS：当前脚本合同与已知最终主源码一致。** 此结论是源码审查；未执行统一验收或任何新增 Lean 调用，不能当作全包实际 PASS。root 已明确将在所有作者见证冻结后以同一个共享 flock 锁执行。

## 审查身份

| 脚本 | SHA256 |
|---|---|
| `/tmp/qm317_accept.py` | `f22992a1e7983ee8064e506f3fe44a2d479664d4b77eaa41ed919dea540d10c9` |
| `/tmp/qm317_inventory.py` | `b99427a6438fc90efc86baf0b67fa5649f1f9ff0a8a0e3b47c407b24b486089c` |
| `/tmp/qm317_source_parser.py` | `503eff61729dff90b18bd98278903e2831ecfb35659681a53a6bd9374d52e6de` |
| `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/scripts/verify_finite_witnesses.py` | `5587ffd016e17cd98ddd451add48e689affb53f8a8a7953793ddb28b03ab4922` |
| `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/scripts/check_axioms.py` | `5ee27622fdf8200f34945abf8354ad5ba3598b0adfba4b206d9e9368cf9aec4a` |

## 实际已修复的问题

1. B 新见证的 Qubit/Label 是两个真实 abbrev。旧 parser 忽略它们会因 #print 全名不匹配而在验收前拒绝。现 parser 接受并审计 abbrev，单独记录 abbreviation 数；统一期望审计数为全部声明长度。纯 Python 对7个实际见证重新解析得到 **110 theorem +39 def +2 abbrev =151**，顺序与全部 #print 一致。
2. 公共审计从“只比较数量”补为实际 axiom map 键集合严格等于冻结 inventory 的目标集合。独立回读当前 AxiomAudit 的 **855 个唯一请求**，全名恰好与 inventory 一致。
3. run 的 TimeoutExpired/OSError 现在写本命令日志、标记 exit_code=None 与 timed_out/launch_error，并绑定日志 SHA、追加 execution-journal；随后显式失败，外层写 acceptance-progress FAIL。不会把资源/启动失败当数学验收。
4. 继承573目标仍来自旧本地文件，但现在强制按 Gitblob 对照实际读取的7b1远端树；已独立算得 `47b5e5e6d736ecf0f26c6373fb794893214b82c8`，与该远端路径完全一致，不以历史本地HEAD为科学基线。

## 计数与覆盖

实际冻结主库存为 **29模块、646显式定理、855审计目标**，增量为187定理、282审计目标。源码声明数不是物理规律数。新模块的全部显式声明、命名非局部实例、结构类型与构造器、显式注册的两投影实例都列入。B作者清单将结构类型替换为构造器，而root同时审两者，root较多1项是明示覆盖增强。

本审查逐项核对所有当前主模块字节/SHA/大小仍与冻结inventory相同；没有运行 inventory --write-audit。嵌套注释/字符串遮罩、namespace/section 栈、重复请求拒绝、所有显式定理覆盖和完整导出集合检查均合理。该扫描范围是当前显式源码命令，未声称列出编译器全部自动生成投影/recursor/internal constant。

## 失败出口与源冻结

完整源集合在验收前后逐路径字节身份一致；具体见证逐次验证源码、通用源码、olean 与上下文身份，日志中的实际公理列表独立核验。Core 的56项闭包同时绑定真实远端7b1 Gitblob与v31.6 SHA及实际导入olean，覆盖范围未扩张为全部Core理论。

构建/公理/见证/证书/runtime任一失败均阻止最后PASS。100 runtime方法、4个demo、6/42证书和4个真假负控由各自实际验证器负责，并与通用定理/见证计数分开。`full_scientific_theory_verified` 明确为false，结果范围仍是声明的有限数学实现，不是无界物理真理。

实际启动合同：`flock /tmp/qm317-lean.lock python3 /tmp/qm317_accept.py`，并使用已授权官方Lean所需执行权限；accept.py 内部依赖这个外层锁。全部作者最终源码冻结后再启动，是运行前提。此次没有执行统一门、修改共享源码或操作远端。
