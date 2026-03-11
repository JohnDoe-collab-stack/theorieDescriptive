import Descriptive.FaithfulExtensionality
import Descriptive.FaithfulTrajectory

namespace Descriptive.Faithful.Concrete2

open Descriptive.Faithful

/-!
Second concrete instance (non-degenerate).

Goals satisfied:
- `Obj` has three distinct objects.
- `MemObj` is nontrivial.
- at least one global denotes: `Term.global Formula1.memSelf`.
- `russell` does not denote for the Russell obstruction (not because "no globals denote").
- `derivedEmpty c0` and `derivedEmpty c1` denote the same empty object.
- `ExtensionalObj` is provable and nontrivial (membership distinguishes the objects).
- distinct terms, same denotation (two derived-empties).

No `Classical`, no `propext`, no `Quot`, no `Quot.sound`, no `sorry`.
-/

inductive Obj where
  | empty
  | self
  | base
  deriving DecidableEq

def MemObj : Obj → Obj → Prop
  | _, Obj.empty => False
  | y, Obj.self => y = Obj.self
  | y, Obj.base => y = Obj.empty

def denotePrim : PrimConst → Obj
  | PrimConst.mk n =>
      match n with
      | 0 => Obj.base
      | 1 => Obj.self
      | _ + 2 => Obj.base

def denotePrimOpt : PrimConst → Option Obj :=
  fun p => some (denotePrim p)

def holdsDec : (φ : Formula1) → (x : Obj) → Decidable (Holds MemObj denotePrimOpt φ x)
  | Formula1.memSelf, x =>
      match x with
      | Obj.empty => isFalse (by intro h; cases h)
      | Obj.self => isTrue rfl
      | Obj.base => isFalse (by intro h; cases h)
  | Formula1.neqSelf, x =>
      isFalse (by intro h; exact h rfl)
  | Formula1.memPrim p, x =>
      match p with
      | PrimConst.mk n =>
          match n, x with
          | 0, Obj.empty =>
              isTrue (by
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj])
          | 0, Obj.self =>
              isFalse (by
                intro h
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj] at h
                cases h)
          | 0, Obj.base =>
              isFalse (by
                intro h
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj] at h
                cases h)
          | 1, Obj.empty =>
              isFalse (by
                intro h
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj] at h
                cases h)
          | 1, Obj.self =>
              isTrue (by
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj])
          | 1, Obj.base =>
              isFalse (by
                intro h
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj] at h
                cases h)
          | _ + 2, Obj.empty =>
              isTrue (by
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj])
          | _ + 2, Obj.self =>
              isFalse (by
                intro h
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj] at h
                cases h)
          | _ + 2, Obj.base =>
              isFalse (by
                intro h
                dsimp [Holds, denotePrimOpt, denotePrim, MemObj] at h
                cases h)
  | Formula1.not ψ, x =>
      match holdsDec ψ x with
      | isTrue hψ => isFalse (by intro h; exact h hψ)
      | isFalse hψ => isTrue hψ
  | Formula1.and ψ χ, x =>
      match holdsDec ψ x, holdsDec χ x with
      | isTrue hψ, isTrue hχ => isTrue ⟨hψ, hχ⟩
      | isFalse hψ, _ => isFalse (by intro h; exact hψ h.1)
      | _, isFalse hχ => isFalse (by intro h; exact hχ h.2)

def relObj (b : Obj) (φ : Formula1) : Obj :=
  match b with
  | Obj.empty => Obj.empty
  | Obj.self =>
      match holdsDec φ Obj.self with
      | isTrue _ => Obj.self
      | isFalse _ => Obj.empty
  | Obj.base =>
      match holdsDec φ Obj.empty with
      | isTrue _ => Obj.base
      | isFalse _ => Obj.empty

def denote : Term → Option Obj
  | Term.prim p => some (denotePrim p)
  | Term.global φ =>
      match φ with
      | Formula1.memSelf => some Obj.self
      | Formula1.neqSelf => some Obj.empty
      | Formula1.memPrim _ => none
      | Formula1.not _ => none
      | Formula1.and _ _ => none
  | Term.relative t φ =>
      match denote t with
      | some b => some (relObj b φ)
      | none => none

theorem mem_relObj_iff (b y : Obj) (φ : Formula1) :
    MemObj y (relObj b φ) ↔ (MemObj y b ∧ Holds MemObj denotePrimOpt φ y) := by
  cases b with
  | empty =>
      -- `relObj empty φ = empty`, and `MemObj _ empty` is always false.
      constructor
      · intro h; cases h
      · intro h; cases h.1
  | self =>
      cases h : holdsDec φ Obj.self with
      | isTrue hφ =>
          dsimp [relObj]
          rw [h]
          cases y <;> constructor
          · intro hmem
            -- y = empty
            cases hmem
          · intro h'
            cases h'.1
          · intro _
            exact ⟨rfl, hφ⟩
          · intro _
            rfl
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1
      | isFalse hnφ =>
          dsimp [relObj]
          rw [h]
          cases y <;> constructor
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1
          · intro hmem
            cases hmem
          · intro h'
            exact False.elim (hnφ h'.2)
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1
  | base =>
      cases h : holdsDec φ Obj.empty with
      | isTrue hφ =>
          dsimp [relObj]
          rw [h]
          cases y <;> constructor
          · intro _
            exact ⟨rfl, hφ⟩
          · intro _
            rfl
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1
      | isFalse hnφ =>
          dsimp [relObj]
          rw [h]
          cases y <;> constructor
          · intro hmem
            cases hmem
          · intro h'
            exact False.elim (hnφ h'.2)
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1
          · intro hmem
            cases hmem
          · intro h'
            cases h'.1

def concreteSemantics2 : DescriptiveSemantics where
  Obj := Obj
  MemObj := MemObj
  denote := denote
  global_spec := by
    intro φ a hden y
    cases φ with
    | memSelf =>
        cases hden
        -- membership in `self` is `y = self`, and `Holds memSelf y` is `MemObj y y`
        cases y <;> constructor <;> intro h <;> cases h <;> rfl
    | neqSelf =>
        cases hden
        constructor
        · intro h; cases h
        · intro h; exact False.elim (h rfl)
    | memPrim p =>
        cases hden
    | not ψ =>
        cases hden
    | and ψ χ =>
        cases hden
  rel_ex := by
    intro t φ b hb
    refine ⟨relObj b φ, ?_⟩
    dsimp [denote]
    rw [hb]
  rel_spec := by
    intro t φ b a hb ha y
    have ha0 : denote (Term.relative t φ) = some (relObj b φ) := by
      dsimp [denote]
      rw [hb]
    have : some (relObj b φ) = some a := by
      calc
        some (relObj b φ) = denote (Term.relative t φ) := by symm; exact ha0
        _ = some a := ha
    cases this
    exact mem_relObj_iff b y φ

def c0 : Term :=
  Term.prim (PrimConst.mk 0)

def c1 : Term :=
  Term.prim (PrimConst.mk 1)

theorem c0_ex : Ex concreteSemantics2 c0 := by
  refine ⟨Obj.base, ?_⟩
  rfl

theorem c1_ex : Ex concreteSemantics2 c1 := by
  refine ⟨Obj.self, ?_⟩
  rfl

theorem c0_ne_c1 : c0 ≠ c1 := by
  intro h
  dsimp [c0, c1] at h
  have : (PrimConst.mk 0) = (PrimConst.mk 1) := by
    injection h
  have : (0 : Nat) = 1 := by
    injection this
  exact Nat.zero_ne_one this

theorem global_memSelf_ex :
    Ex concreteSemantics2 (Term.global Formula1.memSelf) := by
  refine ⟨Obj.self, ?_⟩
  rfl

theorem russell_not_ex_concrete2 :
    ¬ Ex concreteSemantics2 russell := by
  -- Informative reason: if it denoted, `global_spec` would force `p ↔ ¬ p`.
  exact Descriptive.Faithful.russell_not_ex (S := concreteSemantics2)

theorem derivedEmpty_c0_ex :
    Ex concreteSemantics2 (derivedEmpty c0) := by
  exact derivedEmpty_ex (S := concreteSemantics2) (c := c0) c0_ex

theorem derivedEmpty_c1_ex :
    Ex concreteSemantics2 (derivedEmpty c1) := by
  exact derivedEmpty_ex (S := concreteSemantics2) (c := c1) c1_ex

theorem denote_derivedEmpty (c : Term) (hc : Ex concreteSemantics2 c) :
    concreteSemantics2.denote (derivedEmpty c) = some Obj.empty := by
  rcases hc with ⟨b, hb⟩
  -- `derivedEmpty c = relative c neqSelf`, and `holdsDec neqSelf _` is always `isFalse`.
  dsimp [concreteSemantics2] at hb ⊢
  dsimp [derivedEmpty, denote]
  rw [hb]
  cases b <;> rfl

theorem derivedEmpty_c0_emptyObj :
    ∃ a : concreteSemantics2.Obj,
      concreteSemantics2.denote (derivedEmpty c0) = some a ∧
      ∀ y : concreteSemantics2.Obj, ¬ concreteSemantics2.MemObj y a := by
  refine ⟨Obj.empty, ?_, ?_⟩
  · exact denote_derivedEmpty c0 c0_ex
  · intro y hy
    cases hy

theorem derivedEmpty_c1_emptyObj :
    ∃ a : concreteSemantics2.Obj,
      concreteSemantics2.denote (derivedEmpty c1) = some a ∧
      ∀ y : concreteSemantics2.Obj, ¬ concreteSemantics2.MemObj y a := by
  refine ⟨Obj.empty, ?_, ?_⟩
  · exact denote_derivedEmpty c1 c1_ex
  · intro y hy
    cases hy

theorem derivedEmpty_c0_emptyTerm :
    ∀ y : Term, ¬ MemTerm concreteSemantics2 y (derivedEmpty c0) := by
  intro y h
  rcases h with ⟨a, b, ha, hb, hab⟩
  have hb0 : b = Obj.empty := by
    -- compute denotation of `derivedEmpty c0`
    have : concreteSemantics2.denote (derivedEmpty c0) = some Obj.empty :=
      denote_derivedEmpty c0 c0_ex
    -- compare with `hb`
    have : some b = some Obj.empty := by
      calc
        some b = concreteSemantics2.denote (derivedEmpty c0) := by symm; exact hb
        _ = some Obj.empty := this
    cases this
    rfl
  subst hb0
  -- now `hab : MemObj a empty`, impossible
  cases a <;> cases hab

def concreteTrajectory2 : Trajectory :=
  { h :=
      fun t =>
        let rec h' : Term → Nat
          | Term.prim _ => 0
          | Term.global _ => 0
          | Term.relative t0 _ => Nat.succ (h' t0)
        h' t
  }

theorem c0_precedes_derivedEmpty_c0 :
    TrajPrecedes concreteTrajectory2 c0 (derivedEmpty c0) := by
  refine primitive_precedes_derivedEmpty (τ := concreteTrajectory2) (c := c0) ?_ ?_
  · rfl
  · intro t φ
    rfl

theorem concrete2_extensional :
    ExtensionalObj concreteSemantics2 := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · -- empty = self impossible: witness y = self
    have h := hab Obj.self
    have : MemObj Obj.self Obj.self := rfl
    have : MemObj Obj.self Obj.empty := (h.2 this)
    cases this
  · -- empty = base impossible: witness y = empty
    have h := hab Obj.empty
    have : MemObj Obj.empty Obj.base := rfl
    have : MemObj Obj.empty Obj.empty := (h.2 this)
    cases this
  · -- self = empty impossible: witness y = self
    have h := hab Obj.self
    have : MemObj Obj.self Obj.self := rfl
    have : MemObj Obj.self Obj.empty := (h.1 this)
    cases this
  · rfl
  · -- self = base impossible: witness y = self
    have h := hab Obj.self
    have : MemObj Obj.self Obj.self := rfl
    have : MemObj Obj.self Obj.base := (h.1 this)
    cases this
  · -- base = empty impossible: witness y = empty
    have h := hab Obj.empty
    have : MemObj Obj.empty Obj.base := rfl
    have : MemObj Obj.empty Obj.empty := (h.1 this)
    cases this
  · -- base = self impossible: witness y = empty
    have h := hab Obj.empty
    have : MemObj Obj.empty Obj.base := rfl
    have : MemObj Obj.empty Obj.self := (h.1 this)
    cases this
  · rfl

theorem derivedEmpty_c0_c1_same_denotation :
    concreteSemantics2.denote (derivedEmpty c0) =
      concreteSemantics2.denote (derivedEmpty c1) := by
  -- both reduce to `some empty`
  have h0 : concreteSemantics2.denote (derivedEmpty c0) = some Obj.empty :=
    denote_derivedEmpty c0 c0_ex
  have h1 : concreteSemantics2.denote (derivedEmpty c1) = some Obj.empty :=
    denote_derivedEmpty c1 c1_ex
  exact h0.trans h1.symm

theorem derivedEmpty_c0_c1_distinct_terms_same_denotation :
    derivedEmpty c0 ≠ derivedEmpty c1 ∧
    concreteSemantics2.denote (derivedEmpty c0) =
      concreteSemantics2.denote (derivedEmpty c1) := by
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
#print axioms Descriptive.Faithful.Concrete2.global_memSelf_ex
#print axioms Descriptive.Faithful.Concrete2.russell_not_ex_concrete2
#print axioms Descriptive.Faithful.Concrete2.derivedEmpty_c0_ex
#print axioms Descriptive.Faithful.Concrete2.derivedEmpty_c0_emptyObj
#print axioms Descriptive.Faithful.Concrete2.c0_precedes_derivedEmpty_c0
#print axioms Descriptive.Faithful.Concrete2.concrete2_extensional
#print axioms Descriptive.Faithful.Concrete2.derivedEmpty_c0_c1_same_denotation
#print axioms Descriptive.Faithful.Concrete2.derivedEmpty_c0_c1_distinct_terms_same_denotation
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful.Concrete2
