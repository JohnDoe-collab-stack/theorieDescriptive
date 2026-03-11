import Descriptive.FreeLogic

namespace Descriptive.Faithful

theorem russell_not_ex (S : DescriptiveSemantics) :
    ¬ Ex S russell := by
  intro hEx
  rcases hEx with ⟨a, ha⟩
  have hmem0 :=
    S.global_spec (φ := Formula1.not Formula1.memSelf) (a := a) ha (y := a)
  have hmem : S.MemObj a a ↔ ¬ S.MemObj a a := by
    constructor
    · intro h
      have hH :
          Holds S.MemObj (fun p => S.denote (Term.prim p)) (Formula1.not Formula1.memSelf) a :=
        hmem0.mp h
      dsimp [Holds] at hH
      exact hH
    · intro hnot
      have hH :
          Holds S.MemObj (fun p => S.denote (Term.prim p)) (Formula1.not Formula1.memSelf) a := by
        dsimp [Holds]
        exact hnot
      exact hmem0.mpr hH
  have hnot : ¬ S.MemObj a a := by
    intro h
    exact (hmem.mp h) h
  have h : S.MemObj a a :=
    (hmem.mpr hnot)
  exact (hmem.mp h) h

theorem derivedEmpty_ex (S : DescriptiveSemantics) {c : Term}
    (hc : Ex S c) :
    Ex S (derivedEmpty c) := by
  rcases hc with ⟨b, hb⟩
  rcases S.rel_ex c Formula1.neqSelf b hb with ⟨a, ha⟩
  exact ⟨a, ha⟩

theorem derivedEmpty_denotes_emptyObj (S : DescriptiveSemantics) {c : Term}
    (hc : Ex S c) :
    ∃ a : S.Obj,
      S.denote (derivedEmpty c) = some a ∧
      ∀ y : S.Obj, ¬ S.MemObj y a := by
  rcases hc with ⟨b, hb⟩
  rcases S.rel_ex c Formula1.neqSelf b hb with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro y
  intro hy
  have hspec := S.rel_spec c Formula1.neqSelf b a hb ha y
  have :
      S.MemObj y b ∧
        Holds S.MemObj (fun p => S.denote (Term.prim p)) Formula1.neqSelf y :=
    (hspec.mp hy)
  exact this.2 rfl

theorem derivedEmpty_emptyObjTerm (S : DescriptiveSemantics) {c : Term}
    (hc : Ex S c) :
    ∀ y : S.Obj, ¬ MemObjTerm S y (derivedEmpty c) := by
  intro y
  intro h
  rcases derivedEmpty_denotes_emptyObj (S := S) (c := c) hc with ⟨a, ha, hEmpty⟩
  rcases h with ⟨a', ha', hy⟩
  have haEq : a' = a := by
    have : some a' = some a := by
      calc
        some a' = S.denote (derivedEmpty c) := by symm; exact ha'
        _ = some a := ha
    cases this
    rfl
  subst haEq
  exact hEmpty y hy

theorem derivedEmpty_emptyTerm (S : DescriptiveSemantics) {c y : Term}
    (hc : Ex S c) :
    ¬ MemTerm S y (derivedEmpty c) := by
  intro h
  rcases h with ⟨ya, ea, hy, he, hmem⟩
  have hNo : ¬ MemObjTerm S ya (derivedEmpty c) := by
    have := derivedEmpty_emptyObjTerm (S := S) (c := c) hc ya
    exact this
  exact hNo ⟨ea, he, hmem⟩

theorem derivedEmpty_profile (S : DescriptiveSemantics) {c : Term}
    (hc : Ex S c) :
    Ex S (derivedEmpty c) ∧ ∀ y : Term, ¬ MemTerm S y (derivedEmpty c) := by
  constructor
  · exact derivedEmpty_ex (S := S) (c := c) hc
  · intro y
    exact derivedEmpty_emptyTerm (S := S) (c := c) (y := y) hc

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.russell_not_ex
#print axioms Descriptive.Faithful.derivedEmpty_ex
#print axioms Descriptive.Faithful.derivedEmpty_denotes_emptyObj
#print axioms Descriptive.Faithful.derivedEmpty_emptyObjTerm
#print axioms Descriptive.Faithful.derivedEmpty_emptyTerm
#print axioms Descriptive.Faithful.derivedEmpty_profile
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
