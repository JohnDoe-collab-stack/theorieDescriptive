namespace Descriptive.Faithful

/-!
Layer A (syntax): a minimal, targeted syntax of unary-open formulas and
descriptive terms, sufficient for the faithful nucleus:
- Russell term `{u | u ∉ u}`
- Derived empty `{x ∈ c | x ≠ x}`

We intentionally avoid a full FOL embedding.
-/

inductive PrimConst where
  | mk : Nat → PrimConst

inductive Formula1 where
  | memSelf : Formula1           -- x ∈ x
  | neqSelf : Formula1           -- x ≠ x
  | memPrim : PrimConst → Formula1  -- x ∈ prim(p)
  | not : Formula1 → Formula1    -- ¬ φ
  | and : Formula1 → Formula1 → Formula1  -- φ ∧ ψ

inductive Term where
  | prim : PrimConst → Term
  | global : Formula1 → Term
  | relative : Term → Formula1 → Term

def russell : Term :=
  Term.global (Formula1.not Formula1.memSelf)

def derivedEmpty (c : Term) : Term :=
  Term.relative c Formula1.neqSelf

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Syntax file: no theorems/lemmas to audit.
-/
-- (no theorems/lemmas in this file)
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
