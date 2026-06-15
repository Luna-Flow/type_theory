# type_theory

This module provides reusable named and De Bruijn binding semantics,
capture-avoiding substitution, structured single-step reduction, and bounded
untyped NbE.

Custom domain ASTs should implement `BindingSyntax` to use one-pass generic
substitution and arbitrary custom rewrite rules. Lambda users may choose named
syntax, De Bruijn small-step reduction, or bounded NbE with quote.
