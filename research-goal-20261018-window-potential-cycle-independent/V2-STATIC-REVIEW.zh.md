# 生产 v2 的独立只读差分审查

原已封静态审查文件与 `independent-files.json` 不改。

只读 `git diff --no-index` 显示，`cycle_once.py`（SHA256 `4184a9dca7db7b1a40226e3287258c02100c26e53f69b6d436e24e5eaf67cfd9`）至新 `cycle_v2_once.py`（SHA256 `da234b34963e8b3c5dfca5cead78e28be2ee9873c6db702ebbe4a4147539d187`）只删除 check_gate 中三行：读取 `prior_I_independent_receipt`、加入 refs、检查其 `passed`。

原 B/H 数学输入、Mi、canonical index/四朝向 vertex 映射、iterative DFS、环和完整 DAG 输出、资源限制、一次 child/no-retry 均无改。图必要关仅依赖已独审 B/H，其数学逻辑不依赖 I 点值，因此移除此顺序依赖合理。root 仍须另给生产 gate，生产最终包和独审另各有一次运行授权；本审查没有 AST、导入或执行生产源码，没有构图或验证任何生产结果。
