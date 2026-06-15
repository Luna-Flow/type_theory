# type_theory

本模块提供可复用的命名变量与 De Bruijn 绑定语义、捕获规避代换、结构化单步规约，以及带 fuel 的无类型 NbE。

任意自定义领域 AST 都可以实现 `BindingSyntax`，以使用一次性的 simultaneous substitution 和自定义规约规则。Lambda 层可以选择命名语法、De Bruijn 小步规约或带 quote 的有界 NbE。
