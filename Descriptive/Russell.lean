import Descriptive.Core

namespace Descriptive

theorem russell_not_ex (C : DescriptiveCore) :
    ¬ C.Ex (russell C) := by
  intro hEx
  have hmem :
      C.Mem (russell C) (russell C) ↔ ¬ C.Mem (russell C) (russell C) :=
    C.global_spec (φ := fun u => ¬ C.Mem u u) hEx (y := russell C)
  have hnot : ¬ C.Mem (russell C) (russell C) := by
    intro hr
    exact (hmem.mp hr) hr
  have hr : C.Mem (russell C) (russell C) :=
    hmem.mpr hnot
  exact (hmem.mp hr) hr

theorem derivedEmpty_ex (C : DescriptiveCore) {c : C.Term}
    (hc : C.Ex c) :
    C.Ex (derivedEmpty C c) := by
  have h := C.rel_spec c (fun x => x ≠ x) hc
  exact h.1

theorem derivedEmpty_empty (C : DescriptiveCore) {c : C.Term}
    (hc : C.Ex c) :
    ∀ y : C.Term, ¬ C.Mem y (derivedEmpty C c) := by
  intro y hy
  have hspec := (C.rel_spec c (fun x => x ≠ x) hc).2 y
  have hy' := hspec.mp hy
  exact hy'.2 rfl

theorem derivedEmpty_profile (C : DescriptiveCore) {c : C.Term}
    (hc : C.Ex c) :
    C.Ex (derivedEmpty C c) ∧ ∀ y : C.Term, ¬ C.Mem y (derivedEmpty C c) := by
  constructor
  · exact derivedEmpty_ex C hc
  · exact derivedEmpty_empty C hc

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.russell_not_ex
#print axioms Descriptive.derivedEmpty_ex
#print axioms Descriptive.derivedEmpty_empty
#print axioms Descriptive.derivedEmpty_profile
/- AXIOM_AUDIT_END -/

end Descriptive

