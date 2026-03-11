import Descriptive.FiniteGlobal

namespace Descriptive.Faithful

/-!
Finite internalized *relative* descriptions.

This file extends `FiniteGlobalCore` with the relative analogue of:
- finite extensions,
- representability search,
- internalized relative denotation.

It does not depend on any concrete instance (e.g. `Concrete4`).
-/

namespace FiniteGlobalCore

def relativeExt (C : FiniteGlobalCore) (b : C.Obj) (φ : Formula1) : List C.Obj :=
  (C.membersOf b).filter (fun y => holdsBool C φ y)

theorem mem_relativeExt_iff (C : FiniteGlobalCore) (b : C.Obj) (φ : Formula1) (y : C.Obj) :
    y ∈ relativeExt C b φ ↔ (C.MemObj y b ∧ Holds C.MemObj C.denotePrim φ y) := by
  unfold relativeExt
  have h0 : y ∈ C.membersOf b ∧ holdsBool C φ y = true ↔
      (y ∈ C.membersOf b ∧ Holds C.MemObj C.denotePrim φ y) := by
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      exact (holdsBool_eq_true_iff (C := C) (φ := φ) (y := y)).1 h.2
    · intro h
      refine ⟨h.1, ?_⟩
      exact (holdsBool_eq_true_iff (C := C) (φ := φ) (y := y)).2 h.2
  have hmem :
      y ∈ (C.membersOf b).filter (fun z => holdsBool C φ z) ↔
        (y ∈ C.membersOf b ∧ holdsBool C φ y = true) :=
    (mem_filter_holdsBool_iff (C := C) (φ := φ) (y := y) (objs := C.membersOf b))
  constructor
  · intro h
    have h' : y ∈ C.membersOf b ∧ holdsBool C φ y = true := hmem.1 h
    have h'' : y ∈ C.membersOf b ∧ Holds C.MemObj C.denotePrim φ y := (h0).1 h'
    refine ⟨?_, h''.2⟩
    exact (C.mem_membersOf_iff y b).1 h''.1
  · intro h
    have hyMem : y ∈ C.membersOf b := (C.mem_membersOf_iff y b).2 h.1
    have h' : y ∈ C.membersOf b ∧ Holds C.MemObj C.denotePrim φ y := ⟨hyMem, h.2⟩
    have h'' : y ∈ C.membersOf b ∧ holdsBool C φ y = true := (h0).2 h'
    exact hmem.2 h''

def denoteRelative (C : FiniteGlobalCore) (b : C.Obj) (φ : Formula1) : Option C.Obj :=
  representableExt C (relativeExt C b φ)

theorem denoteRelative_spec (C : FiniteGlobalCore) {b : C.Obj} {φ : Formula1} {a : C.Obj} :
    denoteRelative C b φ = some a →
      ∀ y : C.Obj, C.MemObj y a ↔ (C.MemObj y b ∧ Holds C.MemObj C.denotePrim φ y) := by
  intro hden y
  have hL : C.membersOf a = relativeExt C b φ :=
    representableExt_sound (C := C) (L := relativeExt C b φ) (a := a) (by
      dsimp [denoteRelative] at hden
      exact hden)
  constructor
  · intro hMem
    have : y ∈ C.membersOf a := (C.mem_membersOf_iff y a).2 hMem
    have h' : y ∈ relativeExt C b φ := by
      have h' := this
      rw [hL] at h'
      exact h'
    exact (mem_relativeExt_iff (C := C) (b := b) (φ := φ) (y := y)).1 h'
  · intro h
    have : y ∈ relativeExt C b φ :=
      (mem_relativeExt_iff (C := C) (b := b) (φ := φ) (y := y)).2 h
    have h' : y ∈ C.membersOf a := by
      have h' := this
      rw [← hL] at h'
      exact h'
    exact (C.mem_membersOf_iff y a).1 h'

theorem denoteRelative_complete_ex (C : FiniteGlobalCore) (b : C.Obj) (φ : Formula1) :
    (∃ a : C.Obj, C.membersOf a = relativeExt C b φ) → ∃ a' : C.Obj, denoteRelative C b φ = some a' := by
  intro h
  rcases representableExt_complete (C := C) (L := relativeExt C b φ) h with ⟨a', ha', _⟩
  refine ⟨a', ?_⟩
  dsimp [denoteRelative]
  exact ha'

theorem ex_denoteRelative_iff_membersOf (C : FiniteGlobalCore) (b : C.Obj) (φ : Formula1) :
    (∃ a : C.Obj, denoteRelative C b φ = some a) ↔ ∃ a : C.Obj, C.membersOf a = relativeExt C b φ := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact
      representableExt_sound (C := C) (L := relativeExt C b φ) (a := a) (by
        dsimp [denoteRelative] at ha
        exact ha)
  · intro h
    rcases representableExt_complete (C := C) (L := relativeExt C b φ) h with ⟨a', ha', _⟩
    refine ⟨a', ?_⟩
    dsimp [denoteRelative]
    exact ha'

theorem relativeExt_neqSelf_no_mem (C : FiniteGlobalCore) (b : C.Obj) (y : C.Obj) :
    ¬ y ∈ relativeExt C b Formula1.neqSelf := by
  intro h
  have : C.MemObj y b ∧ Holds C.MemObj C.denotePrim Formula1.neqSelf y :=
    (mem_relativeExt_iff (C := C) (b := b) (φ := Formula1.neqSelf) (y := y)).1 h
  -- `Holds ... neqSelf y` is `y ≠ y`, contradiction by `rfl`.
  exact this.2 rfl

theorem list_eq_nil_of_forall_not_mem {α : Type} (L : List α) :
    (∀ y : α, ¬ y ∈ L) → L = [] := by
  induction L with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      have : False := h x (List.Mem.head xs)
      cases this

theorem relativeExt_neqSelf_eq_nil (C : FiniteGlobalCore) (b : C.Obj) :
    relativeExt C b Formula1.neqSelf = [] := by
  apply list_eq_nil_of_forall_not_mem
  intro y
  exact relativeExt_neqSelf_no_mem (C := C) (b := b) (y := y)

theorem denoteRelative_neqSelf_denotes_emptyObj (C : FiniteGlobalCore) (b : C.Obj)
    (hEmpty : ∃ e : C.Obj, C.membersOf e = []) :
    ∃ a : C.Obj, denoteRelative C b Formula1.neqSelf = some a ∧ ∀ y : C.Obj, ¬ C.MemObj y a := by
  rcases hEmpty with ⟨e, he⟩
  have hRel : ∃ a : C.Obj, C.membersOf a = relativeExt C b Formula1.neqSelf := by
    refine ⟨e, ?_⟩
    -- `relativeExt ... neqSelf` is empty as a list.
    simpa [relativeExt_neqSelf_eq_nil (C := C) (b := b)] using he
  rcases denoteRelative_complete_ex (C := C) (b := b) (φ := Formula1.neqSelf) hRel with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro y hMem
  have h0 :
      C.MemObj y a ↔ (C.MemObj y b ∧ Holds C.MemObj C.denotePrim Formula1.neqSelf y) :=
    denoteRelative_spec (C := C) (b := b) (φ := Formula1.neqSelf) (a := a) ha y
  have : C.MemObj y b ∧ Holds C.MemObj C.denotePrim Formula1.neqSelf y := (h0).1 hMem
  exact this.2 rfl

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteGlobalCore.denoteRelative_spec
#print axioms Descriptive.Faithful.FiniteGlobalCore.denoteRelative_complete_ex
#print axioms Descriptive.Faithful.FiniteGlobalCore.ex_denoteRelative_iff_membersOf
#print axioms Descriptive.Faithful.FiniteGlobalCore.denoteRelative_neqSelf_denotes_emptyObj
/- AXIOM_AUDIT_END -/

end FiniteGlobalCore

end Descriptive.Faithful

