import Descriptive.Core

namespace Descriptive

/-!
External trajectory structure: this is a structure on **terms** (syntax-level),
not on denoted objects.
-/

structure Trajectory (T : Type) where
  h : T → Nat

def TrajPrecedes {T : Type} (τ : Trajectory T) (s t : T) : Prop :=
  τ.h s < τ.h t

theorem primitive_precedes_derivedEmpty
    (C : DescriptiveCore) (τ : Trajectory C.Term) (c : C.Term)
    (h_c : τ.h c = 0)
    (h_rel :
      ∀ (t : C.Term) (φ : C.Term → Prop),
        τ.h (C.relDescr t φ) = Nat.succ (τ.h t)) :
    TrajPrecedes τ c (derivedEmpty C c) := by
  dsimp [TrajPrecedes, derivedEmpty]
  have h_rhs :
      τ.h (C.relDescr c (fun x => x ≠ x)) = Nat.succ (τ.h c) :=
    h_rel c (fun x => x ≠ x)
  rw [h_rhs]
  rw [h_c]
  exact Nat.zero_lt_succ 0

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.primitive_precedes_derivedEmpty
/- AXIOM_AUDIT_END -/

end Descriptive

