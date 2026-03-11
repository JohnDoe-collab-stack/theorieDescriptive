import Descriptive.FaithfulRussell
import Descriptive.FaithfulExtensionality
import Descriptive.FiniteExtensionality

namespace Descriptive.Faithful

/-!
Generic theorem package for finite internalized instances.

Given a `FiniteDescriptiveCore`, we can work at the level of the induced
`DescriptiveSemantics`:

`S := FiniteDescriptiveCore.toDescriptiveSemantics C`.

This module collects the central results (Russell obstruction, derived empty,
finite extensionality, and the standard extensionality consequences), with
minimal, explicit hypotheses.
-/

namespace FiniteDescriptiveCore

abbrev S (C : FiniteDescriptiveCore) : DescriptiveSemantics :=
  FiniteDescriptiveCore.toDescriptiveSemantics C

theorem russell_not_ex (C : FiniteDescriptiveCore) :
    ¬ Ex (S C) russell := by
  exact Descriptive.Faithful.russell_not_ex (S := S C)

theorem derivedEmpty_denote_eq_of_emptyRep (C : FiniteDescriptiveCore) {e : C.Obj}
    (hEmpty : FiniteGlobalCore.representableExt C.core [] = some e)
    {c : Term} (hc : Ex (S C) c) :
    (S C).denote (derivedEmpty c) = some e := by
  exact FiniteDescriptiveCore.denote_derivedEmpty_eq_of_emptyRep (C := C) (e := e) hEmpty hc

theorem derivedEmpty_ex (C : FiniteDescriptiveCore) {c : Term}
    (hc : Ex (S C) c) :
    Ex (S C) (derivedEmpty c) := by
  exact Descriptive.Faithful.derivedEmpty_ex (S := S C) (c := c) hc

theorem derivedEmpty_emptyTerm (C : FiniteDescriptiveCore) {c : Term}
    (hc : Ex (S C) c) :
    ∀ y : Term, ¬ MemTerm (S C) y (derivedEmpty c) := by
  intro y
  exact Descriptive.Faithful.derivedEmpty_emptyTerm (S := S C) (c := c) (y := y) hc

theorem derivedEmpty_profile (C : FiniteDescriptiveCore) {c : Term}
    (hc : Ex (S C) c) :
    Ex (S C) (derivedEmpty c) ∧ ∀ y : Term, ¬ MemTerm (S C) y (derivedEmpty c) := by
  refine ⟨derivedEmpty_ex (C := C) hc, derivedEmpty_emptyTerm (C := C) hc⟩

theorem extensionalObj (C : FiniteDescriptiveCore)
    (hCan : FiniteGlobalCore.MembersOfCanonical C.core)
    (hInj : FiniteGlobalCore.MembersOfInjective C.core) :
    ExtensionalObj (S C) := by
  -- this is exactly the generic finite extensionality theorem
  simpa [S] using
    (FiniteDescriptiveCore.extensionalObj_toDescriptiveSemantics (C := C) hCan hInj)

theorem derivedEmpty_same_denotation (C : FiniteDescriptiveCore)
    (hCan : FiniteGlobalCore.MembersOfCanonical C.core)
    (hInj : FiniteGlobalCore.MembersOfInjective C.core)
    {c c' : Term} (hc : Ex (S C) c) (hc' : Ex (S C) c') :
    (S C).denote (derivedEmpty c) = (S C).denote (derivedEmpty c') := by
  have hExt : ExtensionalObj (S C) :=
    extensionalObj (C := C) hCan hInj
  exact
    Descriptive.Faithful.derivedEmpty_same_denotation_of_extensional (S := S C) hExt hc hc'

theorem derivedEmpty_terms_distinct_same_denotation (C : FiniteDescriptiveCore)
    (hCan : FiniteGlobalCore.MembersOfCanonical C.core)
    (hInj : FiniteGlobalCore.MembersOfInjective C.core)
    {c c' : Term} (hc : Ex (S C) c) (hc' : Ex (S C) c') (hcc' : c ≠ c') :
    derivedEmpty c ≠ derivedEmpty c' ∧ (S C).denote (derivedEmpty c) = (S C).denote (derivedEmpty c') := by
  have hExt : ExtensionalObj (S C) :=
    extensionalObj (C := C) hCan hInj
  exact
    Descriptive.Faithful.derivedEmpty_terms_distinct_same_denotation_of_extensional
      (S := S C) hExt hc hc' hcc'

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.russell_not_ex
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_denote_eq_of_emptyRep
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_profile
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_same_denotation
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_terms_distinct_same_denotation
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
