# 設計

一段階簡約が操作的意味論の基準です。多段階正規化と trace はこの API を繰り返し呼び出します。

NbE は lazy thunk、closure、neutral level、quote で独立に実装し、De Bruijn small-step とテストで整合性を確認します。

公開 API 境界で想定される失敗は、構造化データとして表現します。例えば `RuleName::new` は空の名前に対して `RuleNameError::Empty` を返します。実行を中断する `unsafe_*` コンストラクタは、対応する内部 invariant が呼び出し側で保証される場合にのみ使用します。
