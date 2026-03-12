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

def Menu (S : DescriptiveSemantics) (t : Term) : S.Obj → Prop :=
  fun y => Feasible S y t

/-!
Choice, revealed behavior, rationalizability.

We keep choice rules abstract, but we also provide a concrete and standard
family of choice rules: utility maximization on the feasible set.

This is useful because it turns the "only feasibility matters" principle into a
theorem (not an axiom): any utility-maximizing demand is extensional w.r.t.
feasibility.
-/

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

def UtilityMaximizer (S : DescriptiveSemantics) (u : S.Obj → Nat) (y : S.Obj) (t : Term) : Prop :=
  Feasible S y t ∧ ∀ y' : S.Obj, Feasible S y' t → u y' ≤ u y

def utilityChoiceRule (S : DescriptiveSemantics) (u : S.Obj → Nat) : ChoiceRule S where
  Choose := fun y t => UtilityMaximizer S u y t
  choose_feasible := by
    intro y t h
    exact h.1
  extensional := by
    intro s t hObs y
    constructor
    · intro hy
      refine And.intro ?_ ?_
      · exact (hObs y).1 hy.1
      · intro y' hy'
        have hy'' : Feasible S y' s := (hObs y').2 hy'
        exact hy.2 y' hy''
    · intro hy
      refine And.intro ?_ ?_
      · exact (hObs y).2 hy.1
      · intro y' hy'
        have hy'' : Feasible S y' t := (hObs y').1 hy'
        exact hy.2 y' hy''

def Rationalizable (S : DescriptiveSemantics) (R : ChoiceRule S) : Prop :=
  ∃ u : S.Obj → Nat, ∀ (y : S.Obj) (t : Term), R.Choose y t ↔ UtilityMaximizer S u y t

theorem utilityChoiceRule_sameDemand_of_sameFeasible (S : DescriptiveSemantics) (u : S.Obj → Nat)
    {s t : Term} (hObs : SameFeasible S s t) :
    SameDemand S (utilityChoiceRule S u) s t := by
  intro y
  exact (utilityChoiceRule S u).extensional hObs y

def IdentifiableByFeasibility (S : DescriptiveSemantics) : Prop :=
  ∀ {s t : Term}, Ex S s → Ex S t → SameFeasible S s t → DenoteEq S s t

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

theorem extensionalObj_implies_identifiableByFeasibility (S : DescriptiveSemantics)
    (hExt : ExtensionalObj S) :
    IdentifiableByFeasibility S := by
  intro s t hs ht hObs
  exact identification_of_feasibleProfile (S := S) hExt hs ht hObs

theorem denoteEq_implies_sameDemand
    (S : DescriptiveSemantics)
    (R : ChoiceRule S)
    {s t : Term}
    (h : DenoteEq S s t) :
    SameDemand S R s t := by
  -- Denotation equality implies the same feasibility profile, and the choice rule is extensional.
  exact R.extensional (denoteEq_implies_sameFeasible (S := S) h)

/-!
An explicit "incomplete markets" witness.

`DenotationDynamics` provides `toySemantics` where the membership relation is
uninformative (always false). In that semantics, two distinct denoting terms
can be feasibility-equivalent but denote different objects: feasibility data
alone does not identify denotation.
-/

def IncompleteMarkets (S : DescriptiveSemantics) : Prop :=
  ∃ s t : Term, Ex S s ∧ Ex S t ∧ SameFeasible S s t ∧ ¬ DenoteEq S s t

theorem toy_not_extensionalObj : ¬ ExtensionalObj toySemantics := by
  intro hExt
  -- unfold the concrete object type so numerals are accepted
  dsimp [ExtensionalObj, toySemantics] at hExt
  have : (0 : Nat) = 1 := hExt 0 1 (by
    intro y
    -- `MemObj` is constantly `False`
    simp
    )
  exact Nat.zero_ne_one this

theorem toy_incompleteMarkets : IncompleteMarkets toySemantics := by
  refine ⟨t0, t1, toy_ex_t0, toy_ex_t1, ?_, ?_⟩
  · -- feasibility-equivalent
    exact toy_obsObjEq_t0_t1
  · -- but not equal in denotation
    exact toy_not_denoteEq_t0_t1

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.extensionalObj_implies_identifiableByFeasibility
#print axioms Descriptive.Faithful.utilityChoiceRule_sameDemand_of_sameFeasible
#print axioms Descriptive.Faithful.toy_incompleteMarkets
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
