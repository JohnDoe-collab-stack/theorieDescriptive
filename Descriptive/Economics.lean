import Descriptive.DenotationDynamics

namespace Descriptive.Faithful

/-!
Economics reading (minimal, formal).

Interpretation inside a semantics `S`:

- `Term` is a *description* of a menu / budget / contract.
- `S.Obj` is an *outcome* (bundle, allocation, state, ...).
- `MemObjTerm S y t` means: outcome `y` is *feasible/affordable* under description `t`.
- Two descriptions are observationally identical if they induce the same feasibility profile.

This module isolates:

1) Identification from feasibility data (requires object extensionality).
2) Demand/choice invariance under observational equivalence (an economic axiom on the choice rule).
-/

abbrev Feasible (S : DescriptiveSemantics) (y : S.Obj) (t : Term) : Prop :=
  MemObjTerm S y t

abbrev SameFeasible (S : DescriptiveSemantics) (s t : Term) : Prop :=
  ObsObjEq S s t

structure ChoiceRule (S : DescriptiveSemantics) where
  Choose : S.Obj → Term → Prop
  choose_feasible : ∀ {y : S.Obj} {t : Term}, Choose y t → Feasible S y t
  /-- Extensionality of observed behavior: only feasibility matters. -/
  extensional :
    ∀ {s t : Term},
      SameFeasible S s t →
        ∀ y : S.Obj, Choose y s ↔ Choose y t

def SameDemand (S : DescriptiveSemantics) (R : ChoiceRule S) (s t : Term) : Prop :=
  ∀ y : S.Obj, R.Choose y s ↔ R.Choose y t

theorem denoteEq_implies_sameFeasible (S : DescriptiveSemantics) {s t : Term} :
    DenoteEq S s t → SameFeasible S s t :=
  denoteEq_implies_obsObjEq (S := S)

theorem identification_of_feasibleProfile
    (S : DescriptiveSemantics)
    (hExt : ExtensionalObj S)
    {s t : Term}
    (hs : Ex S s)
    (ht : Ex S t)
    (hObs : SameFeasible S s t) :
    DenoteEq S s t :=
  denoteEq_of_obsObjEq_of_extensional (S := S) hExt hs ht hObs

theorem denoteEq_implies_sameDemand
    (S : DescriptiveSemantics)
    (R : ChoiceRule S)
    {s t : Term}
    (h : DenoteEq S s t) :
    SameDemand S R s t := by
  -- Denotation equality implies the same feasibility profile, and the choice rule is extensional.
  exact R.extensional (denoteEq_implies_sameFeasible (S := S) h)

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.identification_of_feasibleProfile
#print axioms Descriptive.Faithful.denoteEq_implies_sameDemand
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful

