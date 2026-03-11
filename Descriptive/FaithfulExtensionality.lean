import Descriptive.FaithfulRussell

namespace Descriptive.Faithful

def ExtensionalObj (S : DescriptiveSemantics) : Prop :=
  ∀ a b : S.Obj, (∀ y : S.Obj, S.MemObj y a ↔ S.MemObj y b) → a = b

theorem derivedEmpty_same_denotation_of_extensional
    (S : DescriptiveSemantics)
    (hExt : ExtensionalObj S)
    {c c' : Term}
    (hc : Ex S c)
    (hc' : Ex S c') :
    S.denote (derivedEmpty c) = S.denote (derivedEmpty c') := by
  rcases derivedEmpty_denotes_emptyObj (S := S) (c := c) hc with ⟨a, ha, hEmpty⟩
  rcases derivedEmpty_denotes_emptyObj (S := S) (c := c') hc' with ⟨a', ha', hEmpty'⟩
  have hiff : ∀ y : S.Obj, S.MemObj y a ↔ S.MemObj y a' := by
    intro y
    constructor
    · intro hy
      exact False.elim (hEmpty y hy)
    · intro hy
      exact False.elim (hEmpty' y hy)
  have haa' : a = a' := hExt a a' hiff
  calc
    S.denote (derivedEmpty c) = some a := ha
    _ = some a' := by cases haa'; rfl
    _ = S.denote (derivedEmpty c') := by symm; exact ha'

theorem derivedEmpty_terms_distinct_same_denotation_of_extensional
    (S : DescriptiveSemantics)
    (hExt : ExtensionalObj S)
    {c c' : Term}
    (hc : Ex S c)
    (hc' : Ex S c')
    (hcc' : c ≠ c') :
    derivedEmpty c ≠ derivedEmpty c' ∧
      S.denote (derivedEmpty c) = S.denote (derivedEmpty c') := by
  refine And.intro ?_ ?_
  · intro hEq
    -- Explicitly: if two relative-description terms are equal, their bases are equal.
    -- This is purely syntactic (term-level), independent of denotation.
    have : c = c' := by
      -- Reduce both sides to `Term.relative _ _`.
      dsimp [derivedEmpty] at hEq
      injection hEq
    exact hcc' this
  · exact derivedEmpty_same_denotation_of_extensional (S := S) hExt hc hc'

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.derivedEmpty_same_denotation_of_extensional
#print axioms Descriptive.Faithful.derivedEmpty_terms_distinct_same_denotation_of_extensional
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
