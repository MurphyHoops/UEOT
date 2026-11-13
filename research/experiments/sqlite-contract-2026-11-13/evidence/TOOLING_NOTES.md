# 外层工具与读取记录

- 2026-11-13 21:35（Asia/Shanghai）：主审第一次将v1 compact字段模板用于v2 compact读取时，Python摘取脚本以 KeyError: ack_class 退出1。它是后处理字段假设错误，未启动SQLite、未改原始数据，不是v2试验执行失败。随后先检查v2实际字段，再按其真实嵌套结构读取；原v2 controller退出0回执及源hash保持原样。
