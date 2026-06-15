# type_theory

このモジュールは named/De Bruijn 束縛、捕獲回避代入、構造化一段階簡約、および fuel 付き untyped NbE を提供します。

任意のドメイン固有 AST は `BindingSyntax` を実装することで、一回だけの simultaneous substitution とカスタム簡約規則を利用できます。
