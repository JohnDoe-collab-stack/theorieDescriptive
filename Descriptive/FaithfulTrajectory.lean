import Descriptive.FaithfulRussell

namespace Descriptive.Faithful

/-!
External trajectory structure: this order is a structure on **terms** (syntax),
not on denoted objects.
-/

structure Trajectory where
  h : Term → Nat

def TrajPrecedes (τ : Trajectory) (s t : Term) : Prop :=
  τ.h s < τ.h t

theorem primitive_precedes_derivedEmpty
    (τ : Trajectory) (c : Term)
    (h_c : τ.h c = 0)
    (h_rel :
      ∀ (t : Term) (φ : Formula1),
        τ.h (Term.relative t φ) = Nat.succ (τ.h t)) :
    TrajPrecedes τ c (derivedEmpty c) := by
  dsimp [TrajPrecedes, derivedEmpty]
  have h_rhs : τ.h (Term.relative c Formula1.neqSelf) = Nat.succ (τ.h c) :=
    h_rel c Formula1.neqSelf
  rw [h_rhs, h_c]
  exact Nat.zero_lt_succ 0

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.primitive_precedes_derivedEmpty
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful

