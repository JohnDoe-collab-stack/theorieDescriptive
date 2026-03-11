namespace Descriptive

/-!
Minimal constructive interface (Option B): an abstract semantics of terms with
existence `Ex`, membership `Mem`, and two description operators.
-/

structure DescriptiveCore where
  Term : Type
  Ex : Term → Prop
  Mem : Term → Term → Prop

  globalDescr : (Term → Prop) → Term
  relDescr : Term → (Term → Prop) → Term

  global_spec :
    ∀ φ : Term → Prop,
      Ex (globalDescr φ) →
        ∀ y : Term, Mem y (globalDescr φ) ↔ φ y

  rel_spec :
    ∀ (t : Term) (φ : Term → Prop),
      Ex t →
        Ex (relDescr t φ) ∧
          ∀ y : Term, Mem y (relDescr t φ) ↔ (Mem y t ∧ φ y)

def russell (C : DescriptiveCore) : C.Term :=
  C.globalDescr (fun u => ¬ C.Mem u u)

def derivedEmpty (C : DescriptiveCore) (c : C.Term) : C.Term :=
  C.relDescr c (fun x => x ≠ x)

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Core file: no theorems/lemmas to audit.
-/
-- (no theorems/lemmas in this file)
/- AXIOM_AUDIT_END -/

end Descriptive

