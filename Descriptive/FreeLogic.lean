import Descriptive.Semantics

namespace Descriptive.Faithful

/-!
Free-logic layer (minimal): derived notions ensuring that term-level membership
only makes sense when the participating terms denote.

We do not embed full FOL; we only provide the minimal constructive interface
used by the faithful nucleus.
-/

def DenoteEq (S : DescriptiveSemantics) (s t : Term) : Prop :=
  ∃ a : S.Obj, S.denote s = some a ∧ S.denote t = some a

theorem denoteEq_implies_ex_left (S : DescriptiveSemantics) {s t : Term} :
    DenoteEq S s t → Ex S s := by
  intro h
  rcases h with ⟨a, hs, _⟩
  exact ⟨a, hs⟩

theorem denoteEq_implies_ex_right (S : DescriptiveSemantics) {s t : Term} :
    DenoteEq S s t → Ex S t := by
  intro h
  rcases h with ⟨a, _, ht⟩
  exact ⟨a, ht⟩

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.denoteEq_implies_ex_left
#print axioms Descriptive.Faithful.denoteEq_implies_ex_right
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
