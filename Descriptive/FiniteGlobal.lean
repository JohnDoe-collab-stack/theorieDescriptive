import Descriptive.Semantics

namespace Descriptive.Faithful

/-!
Abstract finite-global core: a minimal interface capturing the internalized
finite interpretation of global descriptions.

This module does not depend on any concrete instance (e.g. `Concrete4`).
-/

structure FiniteGlobalCore where
  Obj : Type
  instDecEq : DecidableEq Obj
  MemObj : Obj → Obj → Prop

  /-- A finite list enumerating all objects. -/
  allObjs : List Obj
  /-- Completeness of the enumeration (membership uses `List.Mem`). -/
  allObjs_complete : ∀ x : Obj, x ∈ allObjs

  /-- List of members for each object. -/
  membersOf : Obj → List Obj
  /-- Correctness of `membersOf` w.r.t. `MemObj`. -/
  mem_membersOf_iff : ∀ (y a : Obj), y ∈ membersOf a ↔ MemObj y a

  /-- Denotation of primitive constants (partial, via `Option`). -/
  denotePrim : PrimConst → Option Obj

  /-- Decidability of `Holds` for all formulas and objects. -/
  holdsDec : ∀ (φ : Formula1) (x : Obj), Decidable (Holds MemObj denotePrim φ x)

namespace FiniteGlobalCore

instance (C : FiniteGlobalCore) : DecidableEq C.Obj :=
  C.instDecEq

def holdsBool (C : FiniteGlobalCore) (φ : Formula1) (y : C.Obj) : Bool :=
  match C.holdsDec φ y with
  | isTrue _ => true
  | isFalse _ => false

theorem holdsBool_eq_true_iff (C : FiniteGlobalCore) (φ : Formula1) (y : C.Obj) :
    holdsBool C φ y = true ↔ Holds C.MemObj C.denotePrim φ y := by
  unfold holdsBool
  cases h : C.holdsDec φ y with
  | isTrue hp =>
      constructor
      · intro _; exact hp
      · intro _; rfl
  | isFalse hn =>
      constructor
      · intro h0; cases h0
      · intro hp; exact False.elim (hn hp)

theorem mem_filter_holdsBool_iff (C : FiniteGlobalCore) (φ : Formula1) (y : C.Obj) (objs : List C.Obj) :
    y ∈ objs.filter (fun z => holdsBool C φ z) ↔ (y ∈ objs ∧ holdsBool C φ y = true) := by
  induction objs with
  | nil =>
      constructor
      · intro h; cases h
      · intro h; cases h.1
  | cons x xs ih =>
      cases hx : holdsBool C φ x with
      | false =>
          have hfilter :
              (x :: xs).filter (fun z => holdsBool C φ z) =
                xs.filter (fun z => holdsBool C φ z) := by
            dsimp [List.filter]
            rw [hx]
          constructor
          · intro h
            have h' : y ∈ xs.filter (fun z => holdsBool C φ z) := by
              have h' := h
              rw [hfilter] at h'
              exact h'
            have h'' : y ∈ xs ∧ holdsBool C φ y = true := (ih).1 h'
            exact ⟨List.Mem.tail x h''.1, h''.2⟩
          · intro h
            cases h.1 with
            | head =>
                have : (false : Bool) = true := hx.symm.trans h.2
                cases this
            | tail _ hy =>
                have h' : y ∈ xs.filter (fun z => holdsBool C φ z) := (ih).2 ⟨hy, h.2⟩
                rw [hfilter]
                exact h'
      | true =>
          have hfilter :
              (x :: xs).filter (fun z => holdsBool C φ z) =
                x :: xs.filter (fun z => holdsBool C φ z) := by
            dsimp [List.filter]
            rw [hx]
          constructor
          · intro h
            have h' : y ∈ x :: xs.filter (fun z => holdsBool C φ z) := by
              have h' := h
              rw [hfilter] at h'
              exact h'
            cases h' with
            | head =>
                exact ⟨List.Mem.head xs, hx⟩
            | tail _ hy =>
                have h'' : y ∈ xs ∧ holdsBool C φ y = true := (ih).1 hy
                exact ⟨List.Mem.tail x h''.1, h''.2⟩
          · intro h
            have : y ∈ x :: xs.filter (fun z => holdsBool C φ z) := by
              cases h.1 with
              | head =>
                  exact List.Mem.head (xs.filter (fun z => holdsBool C φ z))
              | tail _ hy =>
                  exact List.Mem.tail x ((ih).2 ⟨hy, h.2⟩)
            rw [hfilter]
            exact this

def extOfFormula (C : FiniteGlobalCore) (φ : Formula1) : List C.Obj :=
  C.allObjs.filter (fun y => holdsBool C φ y)

theorem mem_extOfFormula_iff (C : FiniteGlobalCore) (φ : Formula1) (y : C.Obj) :
    y ∈ extOfFormula C φ ↔ Holds C.MemObj C.denotePrim φ y := by
  have hy : y ∈ C.allObjs := C.allObjs_complete y
  unfold extOfFormula
  constructor
  · intro hmem
    have h' : y ∈ C.allObjs ∧ holdsBool C φ y = true :=
      (mem_filter_holdsBool_iff (C := C) (φ := φ) (y := y) C.allObjs).1 hmem
    exact (holdsBool_eq_true_iff (C := C) (φ := φ) (y := y)).1 h'.2
  · intro hH
    have hb : holdsBool C φ y = true := (holdsBool_eq_true_iff (C := C) (φ := φ) (y := y)).2 hH
    exact (mem_filter_holdsBool_iff (C := C) (φ := φ) (y := y) C.allObjs).2 ⟨hy, hb⟩

def representableExtFrom (C : FiniteGlobalCore) (objs : List C.Obj) (L : List C.Obj) : Option C.Obj :=
  match objs with
  | [] => none
  | a :: as => if C.membersOf a = L then some a else representableExtFrom C as L

def representableExt (C : FiniteGlobalCore) (L : List C.Obj) : Option C.Obj :=
  representableExtFrom C C.allObjs L

theorem representableExtFrom_sound (C : FiniteGlobalCore) {objs : List C.Obj} {L : List C.Obj} {a : C.Obj} :
    representableExtFrom C objs L = some a → C.membersOf a = L := by
  induction objs with
  | nil =>
      intro h
      cases h
  | cons b bs ih =>
      intro h
      dsimp [representableExtFrom] at h
      by_cases hb : C.membersOf b = L
      ·
        rw [if_pos hb] at h
        cases h
        exact hb
      ·
        rw [if_neg hb] at h
        exact ih h

theorem representableExtFrom_complete (C : FiniteGlobalCore) {objs : List C.Obj} {L : List C.Obj} :
    (∃ a : C.Obj, a ∈ objs ∧ C.membersOf a = L) → ∃ a' : C.Obj, representableExtFrom C objs L = some a' := by
  intro h
  induction objs with
  | nil =>
      rcases h with ⟨a, ha, _⟩
      cases ha
  | cons b bs ih =>
      rcases h with ⟨a, haMem, haEq⟩
      cases haMem with
      | head =>
          refine ⟨b, ?_⟩
          dsimp [representableExtFrom]
          rw [if_pos haEq]
      | tail _ haMemBs =>
          have : ∃ a : C.Obj, a ∈ bs ∧ C.membersOf a = L := ⟨a, haMemBs, haEq⟩
          rcases ih this with ⟨a', ha'⟩
          by_cases hb : C.membersOf b = L
          ·
            refine ⟨b, ?_⟩
            dsimp [representableExtFrom]
            rw [if_pos hb]
          ·
            refine ⟨a', ?_⟩
            dsimp [representableExtFrom]
            rw [if_neg hb]
            exact ha'

theorem representableExt_sound (C : FiniteGlobalCore) {L : List C.Obj} {a : C.Obj} :
    representableExt C L = some a → C.membersOf a = L := by
  intro h
  exact representableExtFrom_sound (C := C) (objs := C.allObjs) (L := L) (a := a) h

theorem representableExt_complete (C : FiniteGlobalCore) {L : List C.Obj} :
    (∃ a : C.Obj, C.membersOf a = L) →
      ∃ a' : C.Obj, representableExt C L = some a' ∧ C.membersOf a' = L := by
  intro h
  rcases h with ⟨a, ha⟩
  have haMem : a ∈ C.allObjs := C.allObjs_complete a
  have : ∃ a' : C.Obj, representableExtFrom C C.allObjs L = some a' :=
    representableExtFrom_complete (C := C) (objs := C.allObjs) (L := L) ⟨a, haMem, ha⟩
  rcases this with ⟨a', ha'⟩
  refine ⟨a', ?_, ?_⟩
  · exact ha'
  · exact representableExtFrom_sound (C := C) (objs := C.allObjs) (L := L) ha'

def denoteGlobal (C : FiniteGlobalCore) (φ : Formula1) : Option C.Obj :=
  representableExt C (extOfFormula C φ)

theorem denoteGlobal_spec (C : FiniteGlobalCore) {φ : Formula1} {a : C.Obj} :
    denoteGlobal C φ = some a →
      ∀ y : C.Obj, C.MemObj y a ↔ Holds C.MemObj C.denotePrim φ y := by
  intro hden y
  have hL : C.membersOf a = extOfFormula C φ :=
    representableExt_sound (C := C) (L := extOfFormula C φ) (a := a) hden
  constructor
  · intro hMem
    have : y ∈ C.membersOf a := (C.mem_membersOf_iff y a).2 hMem
    have h' : y ∈ extOfFormula C φ := by
      have h' := this
      rw [hL] at h'
      exact h'
    exact (mem_extOfFormula_iff (C := C) (φ := φ) (y := y)).1 h'
  · intro hH
    have : y ∈ extOfFormula C φ := (mem_extOfFormula_iff (C := C) (φ := φ) (y := y)).2 hH
    have h' : y ∈ C.membersOf a := by
      have h' := this
      rw [← hL] at h'
      exact h'
    exact (C.mem_membersOf_iff y a).1 h'

theorem denoteGlobal_complete_ex (C : FiniteGlobalCore) (φ : Formula1) :
    (∃ a : C.Obj, C.membersOf a = extOfFormula C φ) → ∃ a' : C.Obj, denoteGlobal C φ = some a' := by
  intro h
  rcases representableExt_complete (C := C) (L := extOfFormula C φ) h with ⟨a', ha', _⟩
  refine ⟨a', ?_⟩
  dsimp [denoteGlobal]
  exact ha'

theorem ex_denoteGlobal_iff_representableExt (C : FiniteGlobalCore) (φ : Formula1) :
    (∃ a : C.Obj, denoteGlobal C φ = some a) ↔
      ∃ a : C.Obj, representableExt C (extOfFormula C φ) = some a := by
  rfl

theorem ex_denoteGlobal_iff_membersOf (C : FiniteGlobalCore) (φ : Formula1) :
    (∃ a : C.Obj, denoteGlobal C φ = some a) ↔ ∃ a : C.Obj, C.membersOf a = extOfFormula C φ := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    exact ⟨a, representableExt_sound (C := C) (L := extOfFormula C φ) (a := a) (by dsimp [denoteGlobal] at ha; exact ha)⟩
  · intro h
    rcases representableExt_complete (C := C) (L := extOfFormula C φ) h with ⟨a', ha', _⟩
    refine ⟨a', ?_⟩
    dsimp [denoteGlobal]
    exact ha'

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteGlobalCore.denoteGlobal_spec
#print axioms Descriptive.Faithful.FiniteGlobalCore.denoteGlobal_complete_ex
#print axioms Descriptive.Faithful.FiniteGlobalCore.ex_denoteGlobal_iff_membersOf
/- AXIOM_AUDIT_END -/

end FiniteGlobalCore

end Descriptive.Faithful
