import Descriptive.Russell

namespace Descriptive

def Extensional (C : DescriptiveCore) : Prop :=
  ∀ a b : C.Term, (∀ y : C.Term, C.Mem y a ↔ C.Mem y b) → a = b

theorem derivedEmpty_eq_of_extensional
    (C : DescriptiveCore)
    (hExt : Extensional C)
    {c c' : C.Term}
    (hc : C.Ex c)
    (hc' : C.Ex c') :
    derivedEmpty C c = derivedEmpty C c' := by
  refine hExt (derivedEmpty C c) (derivedEmpty C c') ?_
  intro y
  refine Iff.intro ?_ ?_
  · intro hy
    have hspec := (C.rel_spec c (fun x => x ≠ x) hc).2 y
    have hy' := hspec.mp hy
    exact False.elim (hy'.2 rfl)
  · intro hy
    have hspec := (C.rel_spec c' (fun x => x ≠ x) hc').2 y
    have hy' := hspec.mp hy
    exact False.elim (hy'.2 rfl)

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.derivedEmpty_eq_of_extensional
/- AXIOM_AUDIT_END -/

end Descriptive

