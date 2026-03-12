import Descriptive.FaithfulExtensionality

namespace Descriptive.Faithful

/-!
Denotation vs. extensional observation.

This module makes explicit the dynamic between:
- term equality (syntax),
- denotation equality (`DenoteEq`),
- extensional equality of objects (via `ExtensionalObj`),
- and what can be *observed* through membership (`MemObjTerm`, `MemTerm`).

Everything is constructive.
-/

def ObsObjEq (S : DescriptiveSemantics) (s t : Term) : Prop :=
  ∀ y : S.Obj, MemObjTerm S y s ↔ MemObjTerm S y t

def ObsTermEq (S : DescriptiveSemantics) (s t : Term) : Prop :=
  ∀ u : Term, MemTerm S u s ↔ MemTerm S u t

theorem memObjTerm_iff_of_denote_eq_some (S : DescriptiveSemantics) {t : Term} {a : S.Obj}
    (ht : S.denote t = some a) (y : S.Obj) :
    MemObjTerm S y t ↔ S.MemObj y a := by
  constructor
  · intro h
    rcases h with ⟨a', ht', hy⟩
    have : a' = a := by
      have : some a' = some a := by
        calc
          some a' = S.denote t := by symm; exact ht'
          _ = some a := ht
      cases this
      rfl
    subst this
    exact hy
  · intro hy
    exact ⟨a, ht, hy⟩

theorem denoteEq_implies_obsObjEq (S : DescriptiveSemantics) {s t : Term} :
    DenoteEq S s t → ObsObjEq S s t := by
  intro h
  rcases h with ⟨a, hs, ht⟩
  intro y
  have hs' := memObjTerm_iff_of_denote_eq_some (S := S) hs y
  have ht' := memObjTerm_iff_of_denote_eq_some (S := S) ht y
  -- both are equivalent to `MemObj y a`
  constructor <;> intro hmem
  · exact (ht'.2) ((hs'.1) hmem)
  · exact (hs'.2) ((ht'.1) hmem)

theorem denoteEq_implies_obsTermEq (S : DescriptiveSemantics) {s t : Term} :
    DenoteEq S s t → ObsTermEq S s t := by
  intro h
  rcases h with ⟨denoteObj, hs, ht⟩
  intro u
  constructor
  · intro hu
    rcases hu with ⟨ua, ta, huDen, hsDen, humem⟩
    -- `ta` must be `denoteObj` since `s` denotes `denoteObj`
    have hta : ta = denoteObj := by
      have : some ta = some denoteObj := by
        calc
          some ta = S.denote s := by symm; exact hsDen
          _ = some denoteObj := hs
      cases this
      rfl
    have humem' : S.MemObj ua denoteObj := by
      simpa [hta] using humem
    exact ⟨ua, denoteObj, huDen, ht, humem'⟩
  · intro hu
    rcases hu with ⟨ua, ta, huDen, htDen, humem⟩
    have hta : ta = denoteObj := by
      have : some ta = some denoteObj := by
        calc
          some ta = S.denote t := by symm; exact htDen
          _ = some denoteObj := ht
      cases this
      rfl
    have humem' : S.MemObj ua denoteObj := by
      simpa [hta] using humem
    exact ⟨ua, denoteObj, huDen, hs, humem'⟩

theorem denoteEq_of_obsObjEq_of_extensional (S : DescriptiveSemantics) (hExt : ExtensionalObj S)
    {s t : Term} (hs : Ex S s) (ht : Ex S t) (hObs : ObsObjEq S s t) :
    DenoteEq S s t := by
  rcases hs with ⟨a, hsa⟩
  rcases ht with ⟨b, htb⟩
  have hiff : ∀ y : S.Obj, S.MemObj y a ↔ S.MemObj y b := by
    intro y
    have hsa' := memObjTerm_iff_of_denote_eq_some (S := S) hsa y
    have htb' := memObjTerm_iff_of_denote_eq_some (S := S) htb y
    -- transport through the observation equivalence
    constructor
    · intro hy
      have : MemObjTerm S y s := hsa'.2 hy
      have : MemObjTerm S y t := (hObs y).1 this
      exact htb'.1 this
    · intro hy
      have : MemObjTerm S y t := htb'.2 hy
      have : MemObjTerm S y s := (hObs y).2 this
      exact hsa'.1 this
  have hab : a = b := hExt a b hiff
  cases hab
  exact ⟨a, hsa, htb⟩

/-!
Counterexample: without extensionality, observational equality need not imply
denotation equality.

We build a semantics where two distinct objects have the same membership
relation (always `False`), and only primitive terms denote. Then all denoting
primitive terms are observationally indistinguishable via membership, but they
need not denote the same object.
-/

def primVal : PrimConst → Nat
  | PrimConst.mk n => n

def toyDenote : Term → Option Nat
  | Term.prim p => some (primVal p)
  | Term.global _ => none
  | Term.relative t _ => toyDenote t

def toySemantics : DescriptiveSemantics where
  Obj := Nat
  MemObj := fun _ _ => False
  denote := toyDenote
  global_spec := by
    intro φ a h
    cases h
  rel_ex := by
    intro t φ b ht
    refine ⟨b, ?_⟩
    -- `toyDenote (relative t φ)` is definitionally `toyDenote t`
    simpa [toyDenote] using ht
  rel_spec := by
    intro t φ b a ht ha y
    -- Membership is always false, hence the desired equivalence is trivial.
    constructor
    · intro hy
      cases hy
    · intro hy
      cases hy with
      | intro hyMem _ =>
        cases hyMem

def t0 : Term := Term.prim (PrimConst.mk 0)
def t1 : Term := Term.prim (PrimConst.mk 1)

theorem toy_ex_t0 : Ex toySemantics t0 :=
by
  dsimp [Ex, toySemantics, t0, toyDenote, primVal]
  exact ⟨0, rfl⟩

theorem toy_ex_t1 : Ex toySemantics t1 :=
by
  dsimp [Ex, toySemantics, t1, toyDenote, primVal]
  exact ⟨1, rfl⟩

theorem toy_obsObjEq_t0_t1 : ObsObjEq toySemantics t0 t1 := by
  intro y
  constructor <;> intro h <;> rcases h with ⟨a, _, hy⟩ <;> cases hy

theorem toy_not_denoteEq_t0_t1 : ¬ DenoteEq toySemantics t0 t1 := by
  -- Unfold so the witness lives in `Nat` (not just `toySemantics.Obj`).
  dsimp [DenoteEq, toySemantics]
  intro h
  rcases h with ⟨a, hs, ht⟩
  have hs' : (some 0 : Option Nat) = some a := by
    have hs0 : toyDenote t0 = some a := hs
    dsimp [t0, toyDenote, primVal] at hs0
    exact hs0
  have ht' : (some 1 : Option Nat) = some a := by
    have ht0 : toyDenote t1 = some a := ht
    dsimp [t1, toyDenote, primVal] at ht0
    exact ht0
  have ha0 : a = 0 := by
    cases hs'
    rfl
  have ha1 : a = 1 := by
    cases ht'
    rfl
  have : (0 : Nat) = 1 := by
    calc
      0 = a := by symm; exact ha0
      _ = 1 := ha1
  cases this

theorem toy_obs_not_denoteEq : ObsObjEq toySemantics t0 t1 ∧ ¬ DenoteEq toySemantics t0 t1 :=
  ⟨toy_obsObjEq_t0_t1, toy_not_denoteEq_t0_t1⟩

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.Faithful.denoteEq_implies_obsObjEq
#print axioms Descriptive.Faithful.denoteEq_implies_obsTermEq
#print axioms Descriptive.Faithful.denoteEq_of_obsObjEq_of_extensional
#print axioms Descriptive.Faithful.toy_obs_not_denoteEq
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful
