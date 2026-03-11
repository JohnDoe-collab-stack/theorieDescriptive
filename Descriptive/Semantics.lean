import Descriptive.Syntax

namespace Descriptive.Faithful

/-!
Layer B (partial semantics): objects, partial denotation of terms, and membership
on objects. This is constructive: denotation is `Option Obj`.

We also define:
- `Ex t` meaning "t denotes"
- `MemTerm s t` meaning "the object denoted by s is a member of the object denoted by t"
- an evaluation of `Formula1` on objects.
-/

def Holds (MemObj : α → α → Prop) (denotePrim : PrimConst → Option α) (φ : Formula1) (x : α) :
    Prop :=
  match φ with
  | Formula1.memSelf => MemObj x x
  | Formula1.neqSelf => x ≠ x
  | Formula1.memPrim p =>
      match denotePrim p with
      | some a => MemObj x a
      | none => False
  | Formula1.not ψ => ¬ Holds MemObj denotePrim ψ x
  | Formula1.and ψ χ => Holds MemObj denotePrim ψ x ∧ Holds MemObj denotePrim χ x

theorem holds_memPrim_iff (MemObj : α → α → Prop) (denotePrim : PrimConst → Option α)
    (p : PrimConst) (x : α) :
    Holds MemObj denotePrim (Formula1.memPrim p) x ↔ ∃ a : α, denotePrim p = some a ∧ MemObj x a := by
  dsimp [Holds]
  cases hp : denotePrim p with
  | none =>
      constructor
      · intro h; cases h
      · intro h
        rcases h with ⟨a, ha, _⟩
        cases ha
  | some a =>
      constructor
      · intro h
        exact ⟨a, rfl, h⟩
      · intro h
        rcases h with ⟨a', ha', hxa⟩
        cases ha'
        exact hxa

structure DescriptiveSemantics where
  Obj : Type
  MemObj : Obj → Obj → Prop
  denote : Term → Option Obj

  /-- If a global description denotes `a`, then membership in `a` is given by the formula. -/
  global_spec :
    ∀ (φ : Formula1) (a : Obj),
      denote (Term.global φ) = some a →
        ∀ y : Obj, MemObj y a ↔ Holds MemObj (fun p => denote (Term.prim p)) φ y

  /-- Relative descriptions denote whenever the base term denotes. -/
  rel_ex :
    ∀ (t : Term) (φ : Formula1) (b : Obj),
      denote t = some b →
        ∃ a : Obj, denote (Term.relative t φ) = some a

  /-- If `relative t φ` denotes `a` and `t` denotes `b`, then membership in `a` is intersection. -/
  rel_spec :
    ∀ (t : Term) (φ : Formula1) (b a : Obj),
      denote t = some b →
      denote (Term.relative t φ) = some a →
        ∀ y : Obj,
          MemObj y a ↔ (MemObj y b ∧ Holds MemObj (fun p => denote (Term.prim p)) φ y)

def Ex (S : DescriptiveSemantics) (t : Term) : Prop :=
  ∃ a : S.Obj, S.denote t = some a

def MemTerm (S : DescriptiveSemantics) (s t : Term) : Prop :=
  ∃ (a b : S.Obj), S.denote s = some a ∧ S.denote t = some b ∧ S.MemObj a b

def MemObjTerm (S : DescriptiveSemantics) (y : S.Obj) (t : Term) : Prop :=
  ∃ a : S.Obj, S.denote t = some a ∧ S.MemObj y a

theorem memObjTerm_implies_ex (S : DescriptiveSemantics) {y : S.Obj} {t : Term} :
    MemObjTerm S y t → Ex S t := by
  intro h
  rcases h with ⟨a, ht, _⟩
  exact ⟨a, ht⟩

theorem memTerm_implies_ex_left (S : DescriptiveSemantics) {s t : Term} :
    MemTerm S s t → Ex S s := by
  intro h
  rcases h with ⟨a, b, hs, ht, _⟩
  exact ⟨a, hs⟩

theorem memTerm_implies_ex_right (S : DescriptiveSemantics) {s t : Term} :
    MemTerm S s t → Ex S t := by
  intro h
  rcases h with ⟨a, b, hs, ht, _⟩
  exact ⟨b, ht⟩

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.memTerm_implies_ex_left
#print axioms Descriptive.Faithful.memTerm_implies_ex_right
#print axioms Descriptive.Faithful.memObjTerm_implies_ex
#print axioms Descriptive.Faithful.holds_memPrim_iff
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
