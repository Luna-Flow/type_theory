# 设计

单步规约是操作语义的权威接口，多步正规化和 trace 只能循环调用该接口。

NbE 使用惰性 thunk、closure、neutral level 与 quote 独立实现，并通过测试与 De Bruijn 小步规约保持结果一致。

实现 `BindingSyntax` 的任意自定义 AST 都可以使用通用代换与规约遍历。规约规则、领域求值、canonicalization 和 fixed-point 策略由下游 AST 自己定义，不属于本模块的固定语义。

公开 API 边界上的预期失败使用结构化数据表示。例如，`RuleName::new` 在名称为空时返回 `RuleNameError::Empty`。会中止执行的 `unsafe_*` 构造器仅用于调用方已经保证相应内部 invariant 的场景。
