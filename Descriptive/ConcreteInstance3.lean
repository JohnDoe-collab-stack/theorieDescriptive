import Descriptive.FaithfulExtensionality
import Descriptive.FaithfulTrajectory

namespace Descriptive.Faithful.Concrete3

open Descriptive.Faithful

/-!
Third concrete instance (finite, set-like).

We interpret four objects as a tiny well-founded hierarchy:
- `empty`                  ≈ ∅
- `singletonEmpty`         ≈ {∅}
- `singletonSingletonEmpty`≈ {{∅}}
- `pairEmptySingleton`     ≈ {∅, {∅}}

Membership `MemObj` is the obvious set-membership between these objects.

Relative descriptions are total over denoting bases, by explicitly computing
the subset of members of the base object satisfying the formula.
-/

inductive Obj where
  | empty
  | singletonEmpty
  | singletonSingletonEmpty
  | pairEmptySingleton
  deriving DecidableEq

def MemObj : Obj → Obj → Prop
  | _, Obj.empty => False
  | y, Obj.singletonEmpty => y = Obj.empty
  | y, Obj.singletonSingletonEmpty => y = Obj.singletonEmpty
  | y, Obj.pairEmptySingleton => y = Obj.empty ∨ y = Obj.singletonEmpty

theorem no_mem_self : ∀ x : Obj, ¬ MemObj x x := by
  intro x
  cases x <;> intro h
  · cases h
  · -- singletonEmpty ∈ singletonEmpty would force singletonEmpty = empty
    have : Obj.singletonEmpty = Obj.empty := h
    cases this
  · -- singletonSingletonEmpty ∈ singletonSingletonEmpty would force singletonSingletonEmpty = singletonEmpty
    have : Obj.singletonSingletonEmpty = Obj.singletonEmpty := h
    cases this
  · -- pairEmptySingleton ∈ pairEmptySingleton would force pairEmptySingleton = empty or singletonEmpty
    cases h with
    | inl h0 =>
        have : Obj.pairEmptySingleton = Obj.empty := h0
        cases this
    | inr h1 =>
        have : Obj.pairEmptySingleton = Obj.singletonEmpty := h1
        cases this

def denotePrim : PrimConst → Obj
  | PrimConst.mk n =>
      match n with
      | 0 => Obj.singletonEmpty
      | 1 => Obj.pairEmptySingleton
      | _ + 2 => Obj.singletonEmpty

def denotePrimOpt : PrimConst → Option Obj :=
  fun p => some (denotePrim p)

def memObjDec (x a : Obj) : Decidable (MemObj x a) :=
  match a, x with
  | Obj.empty, _ => isFalse (by intro h; cases h)
  | Obj.singletonEmpty, Obj.empty => isTrue rfl
  | Obj.singletonEmpty, Obj.singletonEmpty =>
      isFalse (by intro h; cases h)
  | Obj.singletonEmpty, Obj.singletonSingletonEmpty =>
      isFalse (by intro h; cases h)
  | Obj.singletonEmpty, Obj.pairEmptySingleton =>
      isFalse (by intro h; cases h)
  | Obj.singletonSingletonEmpty, Obj.singletonEmpty => isTrue rfl
  | Obj.singletonSingletonEmpty, Obj.empty =>
      isFalse (by intro h; cases h)
  | Obj.singletonSingletonEmpty, Obj.singletonSingletonEmpty =>
      isFalse (by intro h; cases h)
  | Obj.singletonSingletonEmpty, Obj.pairEmptySingleton =>
      isFalse (by intro h; cases h)
  | Obj.pairEmptySingleton, Obj.empty => isTrue (Or.inl rfl)
  | Obj.pairEmptySingleton, Obj.singletonEmpty => isTrue (Or.inr rfl)
  | Obj.pairEmptySingleton, Obj.singletonSingletonEmpty =>
      isFalse (by
        intro h
        cases h with
        | inl h0 => cases h0
        | inr h1 => cases h1)
  | Obj.pairEmptySingleton, Obj.pairEmptySingleton =>
      isFalse (by
        intro h
        cases h with
        | inl h0 => cases h0
        | inr h1 => cases h1)

def holdsDec : (φ : Formula1) → (x : Obj) → Decidable (Holds MemObj denotePrimOpt φ x)
  | Formula1.memSelf, x => by
      exact isFalse (by
        dsimp [Holds]
        exact no_mem_self x)
  | Formula1.neqSelf, x =>
      isFalse (by intro h; exact h rfl)
  | Formula1.memPrim p, x => by
      dsimp [Holds, denotePrimOpt]
      exact memObjDec x (denotePrim p)
  | Formula1.not ψ, x =>
      match holdsDec ψ x with
      | isTrue hψ => isFalse (by intro h; exact h hψ)
      | isFalse hnψ => isTrue hnψ
  | Formula1.and ψ χ, x =>
      match holdsDec ψ x, holdsDec χ x with
      | isTrue hψ, isTrue hχ => isTrue ⟨hψ, hχ⟩
      | isFalse hnψ, _ => isFalse (by intro h; exact hnψ h.1)
      | _, isFalse hnχ => isFalse (by intro h; exact hnχ h.2)

def denoteRelative (b : Obj) (φ : Formula1) : Obj :=
  match b with
  | Obj.empty => Obj.empty
  | Obj.singletonEmpty =>
      match holdsDec φ Obj.empty with
      | isTrue _ => Obj.singletonEmpty
      | isFalse _ => Obj.empty
  | Obj.singletonSingletonEmpty =>
      match holdsDec φ Obj.singletonEmpty with
      | isTrue _ => Obj.singletonSingletonEmpty
      | isFalse _ => Obj.empty
  | Obj.pairEmptySingleton =>
      match holdsDec φ Obj.empty, holdsDec φ Obj.singletonEmpty with
      | isTrue _, isTrue _ => Obj.pairEmptySingleton
      | isTrue _, isFalse _ => Obj.singletonEmpty
      | isFalse _, isTrue _ => Obj.singletonSingletonEmpty
      | isFalse _, isFalse _ => Obj.empty

theorem mem_denoteRelative_iff (b y : Obj) (φ : Formula1) :
    MemObj y (denoteRelative b φ) ↔ (MemObj y b ∧ Holds MemObj denotePrimOpt φ y) := by
  cases b with
  | empty =>
      constructor
      · intro h; cases h
      · intro h; cases h.1
  | singletonEmpty =>
      cases hd0 : holdsDec φ Obj.empty with
      | isTrue hφ =>
          have hdef : denoteRelative Obj.singletonEmpty φ = Obj.singletonEmpty := by
            dsimp [denoteRelative]
            rw [hd0]
          rw [hdef]
          cases y with
          | empty =>
              constructor
              · intro h; exact ⟨h, hφ⟩
              · intro h; exact h.1
          | singletonEmpty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | singletonSingletonEmpty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | pairEmptySingleton =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
      | isFalse hnφ =>
          have hdef : denoteRelative Obj.singletonEmpty φ = Obj.empty := by
            dsimp [denoteRelative]
            rw [hd0]
          rw [hdef]
          cases y with
          | empty =>
              constructor
              · intro h; cases h
              · intro h
                exact False.elim (hnφ h.2)
          | singletonEmpty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | singletonSingletonEmpty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | pairEmptySingleton =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
  | singletonSingletonEmpty =>
      cases hd1 : holdsDec φ Obj.singletonEmpty with
      | isTrue hφ =>
          have hdef : denoteRelative Obj.singletonSingletonEmpty φ = Obj.singletonSingletonEmpty := by
            dsimp [denoteRelative]
            rw [hd1]
          rw [hdef]
          cases y with
          | singletonEmpty =>
              constructor
              · intro h; exact ⟨h, hφ⟩
              · intro h; exact h.1
          | empty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | singletonSingletonEmpty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | pairEmptySingleton =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
      | isFalse hnφ =>
          have hdef : denoteRelative Obj.singletonSingletonEmpty φ = Obj.empty := by
            dsimp [denoteRelative]
            rw [hd1]
          rw [hdef]
          cases y with
          | singletonEmpty =>
              constructor
              · intro h; cases h
              · intro h
                exact False.elim (hnφ h.2)
          | empty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | singletonSingletonEmpty =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
          | pairEmptySingleton =>
              constructor
              · intro h; cases h
              · intro h; cases h.1
  | pairEmptySingleton =>
      cases hd0 : holdsDec φ Obj.empty with
      | isTrue h0 =>
          cases hd1 : holdsDec φ Obj.singletonEmpty with
          | isTrue h1 =>
              have hdef : denoteRelative Obj.pairEmptySingleton φ = Obj.pairEmptySingleton := by
                dsimp [denoteRelative]
                rw [hd0, hd1]
              rw [hdef]
              cases y with
              | empty =>
                  constructor
                  · intro _; exact ⟨Or.inl rfl, h0⟩
                  · intro h; exact h.1
              | singletonEmpty =>
                  constructor
                  · intro _; exact ⟨Or.inr rfl, h1⟩
                  · intro h; exact h.1
              | singletonSingletonEmpty =>
                  constructor
                  · intro h
                    cases h with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
                  · intro h
                    cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
              | pairEmptySingleton =>
                  constructor
                  · intro h
                    cases h with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
                  · intro h
                    cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
          | isFalse hn1 =>
              have hdef : denoteRelative Obj.pairEmptySingleton φ = Obj.singletonEmpty := by
                dsimp [denoteRelative]
                rw [hd0, hd1]
              rw [hdef]
              cases y with
              | empty =>
                  constructor
                  · intro _; exact ⟨Or.inl rfl, h0⟩
                  · intro _; rfl
              | singletonEmpty =>
                  constructor
                  · intro h; cases h
                  · intro h
                    exact False.elim (hn1 h.2)
              | singletonSingletonEmpty =>
                  constructor
                  · intro h; cases h
                  · intro h; cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
              | pairEmptySingleton =>
                  constructor
                  · intro h; cases h
                  · intro h; cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
      | isFalse hn0 =>
          cases hd1 : holdsDec φ Obj.singletonEmpty with
          | isTrue h1 =>
              have hdef : denoteRelative Obj.pairEmptySingleton φ = Obj.singletonSingletonEmpty := by
                dsimp [denoteRelative]
                rw [hd0, hd1]
              rw [hdef]
              cases y with
              | empty =>
                  constructor
                  · intro h; cases h
                  · intro h
                    exact False.elim (hn0 h.2)
              | singletonEmpty =>
                  constructor
                  · intro _; exact ⟨Or.inr rfl, h1⟩
                  · intro h
                    cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => exact h1'
              | singletonSingletonEmpty =>
                  constructor
                  · intro h; cases h
                  · intro h; cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
              | pairEmptySingleton =>
                  constructor
                  · intro h; cases h
                  · intro h; cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
          | isFalse hn1 =>
              have hdef : denoteRelative Obj.pairEmptySingleton φ = Obj.empty := by
                dsimp [denoteRelative]
                rw [hd0, hd1]
              rw [hdef]
              cases y with
              | empty =>
                  constructor
                  · intro h; cases h
                  · intro h
                    exact False.elim (hn0 h.2)
              | singletonEmpty =>
                  constructor
                  · intro h; cases h
                  · intro h
                    exact False.elim (hn1 h.2)
              | singletonSingletonEmpty =>
                  constructor
                  · intro h; cases h
                  · intro h; cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'
              | pairEmptySingleton =>
                  constructor
                  · intro h; cases h
                  · intro h; cases h.1 with
                    | inl h0' => cases h0'
                    | inr h1' => cases h1'

def denote : Term → Option Obj
  | Term.prim p => some (denotePrim p)
  | Term.global φ =>
      match φ with
      | Formula1.memSelf => some Obj.empty
      | Formula1.neqSelf => some Obj.empty
      | Formula1.memPrim _ => none
      | Formula1.not _ => none
      | Formula1.and _ _ => none
  | Term.relative t φ =>
      match denote t with
      | some b => some (denoteRelative b φ)
      | none => none

def concreteSemantics3 : DescriptiveSemantics where
  Obj := Obj
  MemObj := MemObj
  denote := denote
  global_spec := by
    intro φ a hden y
    cases φ with
    | memSelf =>
        dsimp [denote] at hden
        cases hden
        constructor
        · intro hmem; cases hmem
        · intro hHy
          dsimp [Holds, denote, denotePrimOpt] at hHy
          exact False.elim (no_mem_self y hHy)
    | neqSelf =>
        dsimp [denote] at hden
        cases hden
        constructor
        · intro hmem; cases hmem
        · intro hHy
          dsimp [Holds] at hHy
          exact False.elim (hHy rfl)
    | memPrim p =>
        dsimp [denote] at hden
        cases hden
    | not ψ =>
        dsimp [denote] at hden
        cases hden
    | and ψ χ =>
        dsimp [denote] at hden
        cases hden
  rel_ex := by
    intro t φ b hb
    refine ⟨denoteRelative b φ, ?_⟩
    dsimp [denote]
    rw [hb]
  rel_spec := by
    intro t φ b a hb ha y
    dsimp [denote] at ha
    rw [hb] at ha
    dsimp at ha
    cases ha
    have hfun : (fun p => denote (Term.prim p)) = denotePrimOpt := by rfl
    rw [hfun]
    exact mem_denoteRelative_iff b y φ

def c0 : Term :=
  Term.prim (PrimConst.mk 0)

def c1 : Term :=
  Term.prim (PrimConst.mk 1)

theorem c0_ex : Ex concreteSemantics3 c0 := by
  refine ⟨Obj.singletonEmpty, ?_⟩
  rfl

theorem c1_ex : Ex concreteSemantics3 c1 := by
  refine ⟨Obj.pairEmptySingleton, ?_⟩
  rfl

theorem c0_ne_c1 : c0 ≠ c1 := by
  intro h
  dsimp [c0, c1] at h
  have : (PrimConst.mk 0) = (PrimConst.mk 1) := by
    injection h
  have : (0 : Nat) = 1 := by
    injection this
  exact Nat.zero_ne_one this

theorem some_global_ex :
    Ex concreteSemantics3 (Term.global Formula1.memSelf) := by
  refine ⟨Obj.empty, ?_⟩
  rfl

theorem russell_not_ex_concrete3 :
    ¬ Ex concreteSemantics3 russell := by
  exact Descriptive.Faithful.russell_not_ex (S := concreteSemantics3)

theorem derivedEmpty_c0_ex :
    Ex concreteSemantics3 (derivedEmpty c0) := by
  exact derivedEmpty_ex (S := concreteSemantics3) (c := c0) c0_ex

theorem derivedEmpty_c1_ex :
    Ex concreteSemantics3 (derivedEmpty c1) := by
  exact derivedEmpty_ex (S := concreteSemantics3) (c := c1) c1_ex

theorem denoteRelative_neqSelf (b : Obj) :
    denoteRelative b Formula1.neqSelf = Obj.empty := by
  cases b <;> rfl

theorem denote_derivedEmpty (c : Term) (hc : Ex concreteSemantics3 c) :
    concreteSemantics3.denote (derivedEmpty c) = some Obj.empty := by
  rcases hc with ⟨b, hb⟩
  dsimp [concreteSemantics3] at hb ⊢
  dsimp [derivedEmpty, denote]
  rw [hb]
  dsimp
  rw [denoteRelative_neqSelf b]

theorem derivedEmpty_c0_emptyObj :
    ∃ a : concreteSemantics3.Obj,
      concreteSemantics3.denote (derivedEmpty c0) = some a ∧
      ∀ y : concreteSemantics3.Obj, ¬ concreteSemantics3.MemObj y a := by
  refine ⟨Obj.empty, ?_, ?_⟩
  · exact denote_derivedEmpty c0 c0_ex
  · intro y hy
    cases hy

theorem derivedEmpty_c1_emptyObj :
    ∃ a : concreteSemantics3.Obj,
      concreteSemantics3.denote (derivedEmpty c1) = some a ∧
      ∀ y : concreteSemantics3.Obj, ¬ concreteSemantics3.MemObj y a := by
  refine ⟨Obj.empty, ?_, ?_⟩
  · exact denote_derivedEmpty c1 c1_ex
  · intro y hy
    cases hy

theorem derivedEmpty_c0_emptyTerm :
    ∀ y : Term, ¬ MemTerm concreteSemantics3 y (derivedEmpty c0) := by
  intro y
  exact derivedEmpty_emptyTerm (S := concreteSemantics3) (c := c0) (y := y) c0_ex

theorem memPrim0_distinguishes_objects :
    Holds MemObj (fun p => concreteSemantics3.denote (Term.prim p))
        (Formula1.memPrim (PrimConst.mk 0)) Obj.empty ∧
      ¬ Holds MemObj (fun p => concreteSemantics3.denote (Term.prim p))
        (Formula1.memPrim (PrimConst.mk 0)) Obj.singletonEmpty := by
  refine And.intro ?_ ?_
  ·
    dsimp [Holds, concreteSemantics3, denote, denotePrimOpt, denotePrim, MemObj]
  · intro h
    dsimp [Holds, concreteSemantics3, denote, denotePrimOpt, denotePrim, MemObj] at h
    cases h

def concreteTrajectory3 : Trajectory :=
  { h := fun t =>
      let rec h' : Term → Nat
        | Term.prim _ => 0
        | Term.global _ => 0
        | Term.relative t0 _ => Nat.succ (h' t0)
      h' t
  }

theorem c0_precedes_derivedEmpty_c0 :
    TrajPrecedes concreteTrajectory3 c0 (derivedEmpty c0) := by
  refine primitive_precedes_derivedEmpty (τ := concreteTrajectory3) (c := c0) ?_ ?_
  · rfl
  · intro t φ
    rfl

theorem concrete3_extensional :
    ExtensionalObj concreteSemantics3 := by
  intro a b hab
  dsimp [concreteSemantics3] at hab
  cases a <;> cases b
  · rfl
  ·
    have h := hab Obj.empty
    have hb : MemObj Obj.empty Obj.singletonEmpty := rfl
    have : MemObj Obj.empty Obj.empty := h.mpr hb
    cases this
  ·
    have h := hab Obj.singletonEmpty
    have hb : MemObj Obj.singletonEmpty Obj.singletonSingletonEmpty := rfl
    have : MemObj Obj.singletonEmpty Obj.empty := h.mpr hb
    cases this
  ·
    have h := hab Obj.empty
    have hb : MemObj Obj.empty Obj.pairEmptySingleton := Or.inl rfl
    have : MemObj Obj.empty Obj.empty := h.mpr hb
    cases this
  ·
    have h := hab Obj.empty
    have ha : MemObj Obj.empty Obj.singletonEmpty := rfl
    have : MemObj Obj.empty Obj.empty := h.mp ha
    cases this
  · rfl
  ·
    have h := hab Obj.empty
    have ha : MemObj Obj.empty Obj.singletonEmpty := rfl
    have : MemObj Obj.empty Obj.singletonSingletonEmpty := h.mp ha
    cases this
  ·
    have h := hab Obj.singletonEmpty
    have hb : MemObj Obj.singletonEmpty Obj.pairEmptySingleton := Or.inr rfl
    have : MemObj Obj.singletonEmpty Obj.singletonEmpty := h.mpr hb
    exact False.elim (no_mem_self Obj.singletonEmpty this)
  ·
    have h := hab Obj.singletonEmpty
    have ha : MemObj Obj.singletonEmpty Obj.singletonSingletonEmpty := rfl
    have : MemObj Obj.singletonEmpty Obj.empty := h.mp ha
    cases this
  ·
    have h := hab Obj.singletonEmpty
    have ha : MemObj Obj.singletonEmpty Obj.singletonSingletonEmpty := rfl
    have : MemObj Obj.singletonEmpty Obj.singletonEmpty := h.mp ha
    exact False.elim (no_mem_self Obj.singletonEmpty this)
  · rfl
  ·
    have h := hab Obj.empty
    have hb : MemObj Obj.empty Obj.pairEmptySingleton := Or.inl rfl
    have : MemObj Obj.empty Obj.singletonSingletonEmpty := h.mpr hb
    cases this
  ·
    have h := hab Obj.empty
    have ha : MemObj Obj.empty Obj.pairEmptySingleton := Or.inl rfl
    have : MemObj Obj.empty Obj.empty := h.mp ha
    cases this
  ·
    have h := hab Obj.singletonEmpty
    have ha : MemObj Obj.singletonEmpty Obj.pairEmptySingleton := Or.inr rfl
    have : MemObj Obj.singletonEmpty Obj.singletonEmpty := h.mp ha
    exact False.elim (no_mem_self Obj.singletonEmpty this)
  ·
    have h := hab Obj.empty
    have ha : MemObj Obj.empty Obj.pairEmptySingleton := Or.inl rfl
    have : MemObj Obj.empty Obj.singletonSingletonEmpty := h.mp ha
    cases this
  · rfl

theorem derivedEmpty_c0_c1_same_denotation :
    concreteSemantics3.denote (derivedEmpty c0) =
      concreteSemantics3.denote (derivedEmpty c1) := by
  have h0 : concreteSemantics3.denote (derivedEmpty c0) = some Obj.empty :=
    denote_derivedEmpty c0 c0_ex
  have h1 : concreteSemantics3.denote (derivedEmpty c1) = some Obj.empty :=
    denote_derivedEmpty c1 c1_ex
  exact h0.trans h1.symm

theorem derivedEmpty_c0_c1_distinct_terms_same_denotation :
    derivedEmpty c0 ≠ derivedEmpty c1 ∧
    concreteSemantics3.denote (derivedEmpty c0) =
      concreteSemantics3.denote (derivedEmpty c1) := by
  refine And.intro ?_ ?_
  · intro hEq
    have : c0 = c1 := by
      dsimp [derivedEmpty] at hEq
      injection hEq
    exact c0_ne_c1 this
  · exact derivedEmpty_c0_c1_same_denotation

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main exported results in this file.
-/
#print axioms Descriptive.Faithful.Concrete3.some_global_ex
#print axioms Descriptive.Faithful.Concrete3.russell_not_ex_concrete3
#print axioms Descriptive.Faithful.Concrete3.derivedEmpty_c0_ex
#print axioms Descriptive.Faithful.Concrete3.derivedEmpty_c0_emptyObj
#print axioms Descriptive.Faithful.Concrete3.c0_precedes_derivedEmpty_c0
#print axioms Descriptive.Faithful.Concrete3.concrete3_extensional
#print axioms Descriptive.Faithful.Concrete3.derivedEmpty_c0_c1_same_denotation
#print axioms Descriptive.Faithful.Concrete3.derivedEmpty_c0_c1_distinct_terms_same_denotation
#print axioms Descriptive.Faithful.Concrete3.memPrim0_distinguishes_objects
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful.Concrete3
