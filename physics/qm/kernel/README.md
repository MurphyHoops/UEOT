# UEOT-QM / Kernel 1.10

当前新增主入口为[有限条件参考实现](../conditioning/README.md)，完整科学链见[v31.10报告](../UEOT_QM_KERNEL_v31.10.md)。49个公开模块、959条显式定理、1285项具名声明公理审计；新增8模块、105条显式定理、162项具名审计。运行验收19项测试、95项精确符号检查通过。

本目录继续保留既有Gaussian-rational精确内核、表示证书、Lean导出、谱与331检查器。其API合同、维数/整数限制及全部范例完整保留于[原v31.9说明](evidence/v31.10/prior/kernel-README-v31.9.md)；其中版本计数和验收状态属于原历史时点。

## 运行

从仓库根目录执行：

```bash
python physics/qm/conditioning/verify_runtime.py --output-dir /tmp/qm-finite-conditioning
python physics/qm/kernel/verify_kernel.py --output /tmp/qm-runtime.json
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/demo_v313.py
python physics/qm/kernel/demo_v315.py
```

新参考实现需要NumPy、SciPy及SymPy；旧内核保持Python标准库实现。当前实际运行与历史程序分别登记，[CURRENT](../status/CURRENT.json)不将旧回执冒充新执行。Python程序全输入正确性、任意数值谱认证与硬件实现仍有各自责任。
