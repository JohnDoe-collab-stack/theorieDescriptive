import Descriptive.FiniteRelative

namespace Descriptive.Faithful

/-!
Bridge from the finite internalized layers (`FiniteGlobalCore` + `FiniteRelative`)
to a full `DescriptiveSemantics`.

The missing ingredient beyond `FiniteGlobalCore` is a *uniform closure* condition
for relative extensions: for every base object `b` and formula `φ`, the filtered
extension `relativeExt b φ` is represented by some object of the finite universe.

This file remains constructive (no `Classical`, no `propext`, no quotients).
-/

structure FiniteDescriptiveCore extends FiniteGlobalCore where
  /-- Uniform representability of all relative extensions. -/
  relative_repr :
    ∀ (b : Obj) (φ : Formula1),
      ∃ a : Obj, membersOf a = FiniteGlobalCore.relativeExt toFiniteGlobalCore b φ

namespace FiniteDescriptiveCore

abbrev core (C : FiniteDescriptiveCore) : FiniteGlobalCore :=
  C.toFiniteGlobalCore

def denote (C : FiniteDescriptiveCore) : Term → Option C.Obj
  | Term.prim p => C.denotePrim p
  | Term.global φ => FiniteGlobalCore.denoteGlobal C.core φ
  | Term.relative t φ =>
      match denote C t with
      | some b => FiniteGlobalCore.denoteRelative C.core b φ
      | none => none

theorem holds_denotePrim_iff (C : FiniteDescriptiveCore) (φ : Formula1) (y : C.Obj) :
    Holds C.MemObj C.denotePrim φ y ↔ Holds C.MemObj (fun p => denote C (Term.prim p)) φ y := by
  induction φ generalizing y with
  | memSelf =>
      rfl
  | neqSelf =>
      rfl
  | memPrim p =>
      rfl
  | not ψ ih =>
      dsimp [Holds]
      constructor
      · intro h hψ
        exact h ((ih _).2 hψ)
      · intro h hψ
        exact h ((ih _).1 hψ)
  | and ψ χ ihψ ihχ =>
      dsimp [Holds]
      constructor
      · intro h
        exact ⟨(ihψ _).1 h.1, (ihχ _).1 h.2⟩
      · intro h
        exact ⟨(ihψ _).2 h.1, (ihχ _).2 h.2⟩

def toDescriptiveSemantics (C : FiniteDescriptiveCore) : DescriptiveSemantics where
  Obj := C.Obj
  MemObj := C.MemObj
  denote := denote C
  global_spec := by
    intro φ a hden y
    -- Reduce the premise to `denoteGlobal`.
    have h0 : FiniteGlobalCore.denoteGlobal C.core φ = some a := by
      dsimp [FiniteDescriptiveCore.denote] at hden
      exact hden
    have hSpec :=
      FiniteGlobalCore.denoteGlobal_spec (C := C.core) (φ := φ) (a := a) h0 (y := y)
    exact hSpec.trans (holds_denotePrim_iff (C := C) (φ := φ) (y := y))
  rel_ex := by
    intro t φ b hb
    have hRep : ∃ a : C.Obj, C.membersOf a = FiniteGlobalCore.relativeExt C.core b φ :=
      C.relative_repr b φ
    rcases
        FiniteGlobalCore.denoteRelative_complete_ex (C := C.core) (b := b) (φ := φ) hRep with
      ⟨a, ha⟩
    refine ⟨a, ?_⟩
    -- `denote (relative t φ)` reduces to `denoteRelative b φ`.
    dsimp [FiniteDescriptiveCore.denote]
    rw [hb]
    exact ha
  rel_spec := by
    intro t φ b a hb ha y
    -- Reduce to a statement about `denoteRelative b φ`.
    have ha' : FiniteGlobalCore.denoteRelative C.core b φ = some a := by
      dsimp [FiniteDescriptiveCore.denote] at ha
      rw [hb] at ha
      exact ha
    have hSpec :=
      FiniteGlobalCore.denoteRelative_spec (C := C.core) (b := b) (φ := φ) (a := a) ha' (y := y)
    -- Convert `Holds ... denotePrim` to the `DescriptiveSemantics` convention.
    constructor
    · intro hMem
      have h : C.MemObj y b ∧ Holds C.MemObj C.denotePrim φ y := (hSpec).1 hMem
      refine ⟨h.1, ?_⟩
      exact (holds_denotePrim_iff (C := C) (φ := φ) (y := y)).1 h.2
    · intro hMem
      have h : C.MemObj y b ∧ Holds C.MemObj C.denotePrim φ y := by
        refine ⟨hMem.1, ?_⟩
        exact (holds_denotePrim_iff (C := C) (φ := φ) (y := y)).2 hMem.2
      exact (hSpec).2 h

theorem denote_global_eq (C : FiniteDescriptiveCore) (φ : Formula1) :
    (toDescriptiveSemantics C).denote (Term.global φ) = FiniteGlobalCore.denoteGlobal C.core φ := by
  rfl

theorem denote_relative_eq (C : FiniteDescriptiveCore) (t : Term) (φ : Formula1) :
    (toDescriptiveSemantics C).denote (Term.relative t φ) =
      match (toDescriptiveSemantics C).denote t with
      | some b => FiniteGlobalCore.denoteRelative C.core b φ
      | none => none := by
  rfl

theorem denote_relative_eq_of_denote (C : FiniteDescriptiveCore) {t : Term} {b : C.Obj}
    (hb : (toDescriptiveSemantics C).denote t = some b) (φ : Formula1) :
    (toDescriptiveSemantics C).denote (Term.relative t φ) = FiniteGlobalCore.denoteRelative C.core b φ := by
  have hb' : denote C t = some b := by
    dsimp [toDescriptiveSemantics, denote] at hb
    exact hb
  dsimp [toDescriptiveSemantics, denote]
  rw [hb']

theorem ex_global_iff_membersOf (C : FiniteDescriptiveCore) (φ : Formula1) :
    Ex (toDescriptiveSemantics C) (Term.global φ) ↔
      ∃ a : C.Obj, C.membersOf a = FiniteGlobalCore.extOfFormula C.core φ := by
  dsimp [Ex, toDescriptiveSemantics, denote]
  -- now apply the finite-global characterization
  exact (FiniteGlobalCore.ex_denoteGlobal_iff_membersOf (C := C.core) (φ := φ))

theorem ex_relative_of_denote_iff_membersOf (C : FiniteDescriptiveCore) {t : Term} {b : C.Obj}
    (hb : (toDescriptiveSemantics C).denote t = some b) (φ : Formula1) :
    Ex (toDescriptiveSemantics C) (Term.relative t φ) ↔
      ∃ a : C.Obj, C.membersOf a = FiniteGlobalCore.relativeExt C.core b φ := by
  have hb' : denote C t = some b := by
    dsimp [toDescriptiveSemantics, denote] at hb
    exact hb
  dsimp [Ex, toDescriptiveSemantics, denote]
  rw [hb']
  -- apply the finite-relative characterization
  exact (FiniteGlobalCore.ex_denoteRelative_iff_membersOf (C := C.core) (b := b) (φ := φ))

theorem denote_derivedEmpty_eq_of_emptyRep (C : FiniteDescriptiveCore) {e : C.Obj}
    (hEmpty : FiniteGlobalCore.representableExt C.core [] = some e)
    {c : Term} (hc : Ex (toDescriptiveSemantics C) c) :
    (toDescriptiveSemantics C).denote (derivedEmpty c) = some e := by
  rcases hc with ⟨b, hb⟩
  -- unfold `derivedEmpty` and reduce to the relative case
  dsimp [derivedEmpty, toDescriptiveSemantics, denote] at hb ⊢
  rw [hb]
  -- `relativeExt b neqSelf` is the empty list
  have hExt : FiniteGlobalCore.relativeExt C.core b Formula1.neqSelf = [] :=
    FiniteGlobalCore.relativeExt_neqSelf_eq_nil (C := C.core) (b := b)
  dsimp [FiniteGlobalCore.denoteRelative]
  rw [hExt]
  exact hEmpty

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.toDescriptiveSemantics
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.ex_global_iff_membersOf
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.ex_relative_of_denote_iff_membersOf
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.denote_derivedEmpty_eq_of_emptyRep
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
