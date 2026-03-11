import Descriptive.FaithfulExtensionality
import Descriptive.FaithfulTrajectory
import Descriptive.FiniteGlobal
import Descriptive.FiniteRelative
import Descriptive.FiniteSemanticsBuilder
import Descriptive.FiniteExtensionality
import Descriptive.FiniteTheorems

namespace Descriptive.Faithful.Concrete4

open Descriptive.Faithful

/-!
Concrete instance 4: finite "set-like" micro-universe with *internalized* global descriptions.

Global denotation is computed by:
1) enumerating all objects;
2) computing the finite extension of a formula on this universe;
3) searching for an existing object whose member-list matches this extension.
-/

/- 1. Objects -/

inductive Obj where
  | empty
  | singletonEmpty
  | singletonSingletonEmpty
  | pairEmptySingleton
  deriving DecidableEq

/- 2. Membership -/

def MemObj : Obj → Obj → Prop
  | _, Obj.empty => False
  | y, Obj.singletonEmpty => y = Obj.empty
  | y, Obj.singletonSingletonEmpty => y = Obj.singletonEmpty
  | y, Obj.pairEmptySingleton => y = Obj.empty ∨ y = Obj.singletonEmpty

/- 3. Enumeration of all objects -/

def allObjs : List Obj :=
  [Obj.empty, Obj.singletonEmpty, Obj.singletonSingletonEmpty, Obj.pairEmptySingleton]

theorem mem_allObjs (x : Obj) : x ∈ allObjs := by
  cases x <;> unfold allObjs
  · exact List.Mem.head _
  · exact List.Mem.tail Obj.empty (List.Mem.head _)
  · exact List.Mem.tail Obj.empty (List.Mem.tail Obj.singletonEmpty (List.Mem.head _))
  ·
    exact
      List.Mem.tail Obj.empty
        (List.Mem.tail Obj.singletonEmpty (List.Mem.tail Obj.singletonSingletonEmpty (List.Mem.head _)))

/- 4. Members list -/

def membersOf : Obj → List Obj
  | Obj.empty => []
  | Obj.singletonEmpty => [Obj.empty]
  | Obj.singletonSingletonEmpty => [Obj.singletonEmpty]
  | Obj.pairEmptySingleton => [Obj.empty, Obj.singletonEmpty]

theorem mem_membersOf_iff (y a : Obj) : y ∈ membersOf a ↔ MemObj y a := by
  cases a with
  | empty =>
      constructor
      · intro h; cases h
      · intro h; cases h
  | singletonEmpty =>
      cases y with
      | empty =>
          constructor
          · intro _; rfl
          · intro _; exact List.Mem.head _
      | singletonEmpty =>
          constructor
          · intro h
            cases h with
            | tail _ h' => cases h'
          · intro h; cases h
      | singletonSingletonEmpty =>
          constructor
          · intro h
            cases h with
            | tail _ h' => cases h'
          · intro h; cases h
      | pairEmptySingleton =>
          constructor
          · intro h
            cases h with
            | tail _ h' => cases h'
          · intro h; cases h
  | singletonSingletonEmpty =>
      cases y with
      | singletonEmpty =>
          constructor
          · intro _; rfl
          · intro _; exact List.Mem.head _
      | empty =>
          constructor
          · intro h
            cases h with
            | tail _ h' => cases h'
          · intro h; cases h
      | singletonSingletonEmpty =>
          constructor
          · intro h
            cases h with
            | tail _ h' => cases h'
          · intro h; cases h
      | pairEmptySingleton =>
          constructor
          · intro h
            cases h with
            | tail _ h' => cases h'
          · intro h; cases h
  | pairEmptySingleton =>
      cases y with
      | empty =>
          constructor
          · intro _; exact Or.inl rfl
          · intro h
            cases h with
            | inl h0 =>
                cases h0
                exact List.Mem.head _
            | inr h1 =>
                cases h1
      | singletonEmpty =>
          constructor
          · intro _; exact Or.inr rfl
          · intro h
            cases h with
            | inl h0 =>
                cases h0
            | inr h1 =>
                cases h1
                exact List.Mem.tail Obj.empty (List.Mem.head _)
      | singletonSingletonEmpty =>
          constructor
          · intro h
            cases h with
            | tail _ h' =>
                cases h' with
                | tail _ h'' => cases h''
          · intro h
            cases h with
            | inl h0 => cases h0
            | inr h1 => cases h1
      | pairEmptySingleton =>
          constructor
          · intro h
            cases h with
            | tail _ h' =>
                cases h' with
                | tail _ h'' => cases h''
          · intro h
            cases h with
            | inl h0 => cases h0
            | inr h1 => cases h1

/- 5. Primitive denotation -/

def denotePrim : PrimConst → Obj
  | PrimConst.mk n =>
      match n with
      | 0 => Obj.singletonEmpty
      | 1 => Obj.pairEmptySingleton
      | _ + 2 => Obj.singletonEmpty

def denotePrimOpt : PrimConst → Option Obj :=
  fun p => some (denotePrim p)

/- 6. Decidability for Holds -/

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
  | Formula1.memSelf, x =>
      memObjDec x x
  | Formula1.neqSelf, _ =>
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

/- 7. Finite internalized global core (factored through `FiniteGlobalCore`) -/

def finiteGlobalCore : FiniteGlobalCore where
  Obj := Obj
  instDecEq := inferInstance
  MemObj := MemObj
  allObjs := allObjs
  allObjs_complete := mem_allObjs
  membersOf := membersOf
  mem_membersOf_iff := mem_membersOf_iff
  denotePrim := denotePrimOpt
  holdsDec := holdsDec

abbrev extOfFormula (φ : Formula1) : List Obj :=
  FiniteGlobalCore.extOfFormula finiteGlobalCore φ

abbrev representableExt (L : List Obj) : Option Obj :=
  FiniteGlobalCore.representableExt finiteGlobalCore L

abbrev denoteGlobal (φ : Formula1) : Option Obj :=
  FiniteGlobalCore.denoteGlobal finiteGlobalCore φ

theorem denoteGlobal_spec {φ : Formula1} {a : Obj} :
    denoteGlobal φ = some a →
      ∀ y : Obj, MemObj y a ↔ Holds MemObj denotePrimOpt φ y := by
  exact FiniteGlobalCore.denoteGlobal_spec (C := finiteGlobalCore) (φ := φ) (a := a)

/- 10. Relative denotation (finite, internalized) -/

abbrev relativeExt (b : Obj) (φ : Formula1) : List Obj :=
  FiniteGlobalCore.relativeExt finiteGlobalCore b φ

abbrev denoteRelativeOpt (b : Obj) (φ : Formula1) : Option Obj :=
  FiniteGlobalCore.denoteRelative finiteGlobalCore b φ

theorem relativeExt_representable (b : Obj) (φ : Formula1) :
    ∃ a : Obj, membersOf a = relativeExt b φ := by
  cases b with
  | empty =>
      refine ⟨Obj.empty, ?_⟩
      rfl
  | singletonEmpty =>
      cases hd0 : holdsDec φ Obj.empty with
      | isTrue _ =>
          refine ⟨Obj.singletonEmpty, ?_⟩
          unfold relativeExt FiniteGlobalCore.relativeExt
          dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
          dsimp [List.filter]
          rw [hd0]
      | isFalse _ =>
          refine ⟨Obj.empty, ?_⟩
          unfold relativeExt FiniteGlobalCore.relativeExt
          dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
          dsimp [List.filter]
          rw [hd0]
  | singletonSingletonEmpty =>
      cases hd1 : holdsDec φ Obj.singletonEmpty with
      | isTrue _ =>
          refine ⟨Obj.singletonSingletonEmpty, ?_⟩
          unfold relativeExt FiniteGlobalCore.relativeExt
          dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
          dsimp [List.filter]
          rw [hd1]
      | isFalse _ =>
          refine ⟨Obj.empty, ?_⟩
          unfold relativeExt FiniteGlobalCore.relativeExt
          dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
          dsimp [List.filter]
          rw [hd1]
  | pairEmptySingleton =>
      cases hd0 : holdsDec φ Obj.empty with
      | isTrue _ =>
          cases hd1 : holdsDec φ Obj.singletonEmpty with
          | isTrue _ =>
              refine ⟨Obj.pairEmptySingleton, ?_⟩
              unfold relativeExt FiniteGlobalCore.relativeExt
              dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
              dsimp [List.filter]
              rw [hd0, hd1]
          | isFalse _ =>
              refine ⟨Obj.singletonEmpty, ?_⟩
              unfold relativeExt FiniteGlobalCore.relativeExt
              dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
              dsimp [List.filter]
              rw [hd0, hd1]
      | isFalse _ =>
          cases hd1 : holdsDec φ Obj.singletonEmpty with
          | isTrue _ =>
              refine ⟨Obj.singletonSingletonEmpty, ?_⟩
              unfold relativeExt FiniteGlobalCore.relativeExt
              dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
              dsimp [List.filter]
              rw [hd0, hd1]
          | isFalse _ =>
              refine ⟨Obj.empty, ?_⟩
              unfold relativeExt FiniteGlobalCore.relativeExt
              dsimp [finiteGlobalCore, membersOf, FiniteGlobalCore.holdsBool]
              dsimp [List.filter]
              rw [hd0, hd1]

/- 11. Generic bridge to `DescriptiveSemantics` -/

def finiteDescriptiveCore4 : FiniteDescriptiveCore where
  toFiniteGlobalCore := finiteGlobalCore
  relative_repr := by
    intro b φ
    -- `relativeExt` is defined from `finiteGlobalCore`.
    simpa [relativeExt] using (relativeExt_representable (b := b) (φ := φ))

abbrev concreteSemantics4 : DescriptiveSemantics :=
  FiniteDescriptiveCore.toDescriptiveSemantics finiteDescriptiveCore4

abbrev denote : Term → Option Obj :=
  (concreteSemantics4.denote)

/- 12.a Characterizations of global denotation in `Concrete4` -/

theorem ex_global_iff_denoteGlobal (φ : Formula1) :
    Ex concreteSemantics4 (Term.global φ) ↔ ∃ a : Obj, denoteGlobal φ = some a := by
  dsimp [Ex, concreteSemantics4, FiniteDescriptiveCore.toDescriptiveSemantics, FiniteDescriptiveCore.denote, FiniteDescriptiveCore.core,
    finiteDescriptiveCore4, denoteGlobal]
  rfl

theorem ex_global_iff_representableExt (φ : Formula1) :
    Ex concreteSemantics4 (Term.global φ) ↔
      ∃ a : Obj, representableExt (extOfFormula φ) = some a := by
  constructor
  · intro h
    have h' : ∃ a : Obj, denoteGlobal φ = some a := (ex_global_iff_denoteGlobal (φ := φ)).1 h
    rcases h' with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    dsimp [denoteGlobal] at ha
    exact ha
  · intro h
    rcases h with ⟨a, ha⟩
    refine (ex_global_iff_denoteGlobal (φ := φ)).2 ?_
    refine ⟨a, ?_⟩
    dsimp [denoteGlobal]
    exact ha

theorem ex_global_iff_membersOf (φ : Formula1) :
    Ex concreteSemantics4 (Term.global φ) ↔ ∃ a : Obj, membersOf a = extOfFormula φ := by
  simpa [concreteSemantics4, extOfFormula, FiniteDescriptiveCore.core] using
    (FiniteDescriptiveCore.ex_global_iff_membersOf (C := finiteDescriptiveCore4) (φ := φ))

/- 12. Concrete theorems -/

def c0 : Term :=
  Term.prim (PrimConst.mk 0)

def c1 : Term :=
  Term.prim (PrimConst.mk 1)

theorem c0_ex : Ex concreteSemantics4 c0 := by
  refine ⟨Obj.singletonEmpty, ?_⟩
  rfl

theorem c1_ex : Ex concreteSemantics4 c1 := by
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

def φ0 : Formula1 :=
  Formula1.memPrim (PrimConst.mk 0)

theorem some_global_ex_concrete4 :
    Ex concreteSemantics4 (Term.global φ0) := by
  refine ⟨Obj.singletonEmpty, ?_⟩
  -- compute the extension: `memPrim 0` holds exactly on `Obj.empty`
  -- hence it is represented by `singletonEmpty`.
  rfl

theorem russell_not_ex_concrete4 :
    ¬ Ex concreteSemantics4 russell := by
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.russell_not_ex (C := finiteDescriptiveCore4))

theorem derivedEmpty_c0_ex :
    Ex concreteSemantics4 (derivedEmpty c0) := by
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_ex (C := finiteDescriptiveCore4) (c := c0) c0_ex)

theorem derivedEmpty_c1_ex :
    Ex concreteSemantics4 (derivedEmpty c1) := by
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_ex (C := finiteDescriptiveCore4) (c := c1) c1_ex)

theorem emptyRep :
    FiniteGlobalCore.representableExt finiteGlobalCore [] = some Obj.empty := by
  dsimp [FiniteGlobalCore.representableExt, FiniteGlobalCore.representableExtFrom, finiteGlobalCore, allObjs, membersOf]

theorem denote_derivedEmpty (c : Term) (hc : Ex concreteSemantics4 c) :
    concreteSemantics4.denote (derivedEmpty c) = some Obj.empty := by
  -- Specialize the generic finite theorem package.
  have hc' : Ex (Descriptive.Faithful.FiniteDescriptiveCore.S finiteDescriptiveCore4) c := by
    simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using hc
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_denote_eq_of_emptyRep
      (C := finiteDescriptiveCore4) (e := Obj.empty) emptyRep (c := c) hc')

theorem denote_derivedEmpty_empty (c : Term) (hc : Ex concreteSemantics4 c) :
    concreteSemantics4.denote (derivedEmpty c) = some Obj.empty :=
  denote_derivedEmpty c hc

theorem derivedEmpty_c0_emptyObj :
    ∃ a : concreteSemantics4.Obj,
      concreteSemantics4.denote (derivedEmpty c0) = some a ∧
      ∀ y : concreteSemantics4.Obj, ¬ concreteSemantics4.MemObj y a := by
  refine ⟨Obj.empty, ?_, ?_⟩
  · exact denote_derivedEmpty c0 c0_ex
  · intro y hy
    cases hy

theorem derivedEmpty_c1_emptyObj :
    ∃ a : concreteSemantics4.Obj,
      concreteSemantics4.denote (derivedEmpty c1) = some a ∧
      ∀ y : concreteSemantics4.Obj, ¬ concreteSemantics4.MemObj y a := by
  refine ⟨Obj.empty, ?_, ?_⟩
  · exact denote_derivedEmpty c1 c1_ex
  · intro y hy
    cases hy

theorem memPrim0_distinguishes_objects :
    Holds MemObj (fun p => concreteSemantics4.denote (Term.prim p))
        (Formula1.memPrim (PrimConst.mk 0)) Obj.empty ∧
      ¬ Holds MemObj (fun p => concreteSemantics4.denote (Term.prim p))
        (Formula1.memPrim (PrimConst.mk 0)) Obj.singletonEmpty := by
  refine And.intro ?_ ?_
  ·
    have hPrim0 : concreteSemantics4.denote (Term.prim (PrimConst.mk 0)) = some Obj.singletonEmpty := by
      rfl
    dsimp [Holds]
    rw [hPrim0]
    change MemObj Obj.empty Obj.singletonEmpty
    rfl
  · intro h
    have hPrim0 : concreteSemantics4.denote (Term.prim (PrimConst.mk 0)) = some Obj.singletonEmpty := by
      rfl
    dsimp [Holds] at h
    rw [hPrim0] at h
    dsimp [MemObj] at h
    cases h

def concreteTrajectory4 : Trajectory :=
  { h := fun t =>
      let rec h' : Term → Nat
        | Term.prim _ => 0
        | Term.global _ => 0
        | Term.relative t0 _ => Nat.succ (h' t0)
      h' t
  }

theorem c0_precedes_derivedEmpty_c0 :
    TrajPrecedes concreteTrajectory4 c0 (derivedEmpty c0) := by
  refine primitive_precedes_derivedEmpty (τ := concreteTrajectory4) (c := c0) ?_ ?_
  · rfl
  · intro t φ
    rfl

theorem membersOf_injective : Function.Injective membersOf := by
  intro a b h
  cases a <;> cases b
  · rfl
  ·
    have h' : ([] : List Obj) = [Obj.empty] := h
    cases h'
  ·
    have h' : ([] : List Obj) = [Obj.singletonEmpty] := h
    cases h'
  ·
    have h' : ([] : List Obj) = [Obj.empty, Obj.singletonEmpty] := h
    cases h'
  ·
    have h' : [Obj.empty] = [] := h
    cases h'
  · rfl
  ·
    have h' : [Obj.empty] = [Obj.singletonEmpty] := h
    cases h'
  ·
    have h' : [Obj.empty] = [Obj.empty, Obj.singletonEmpty] := h
    cases h'
  ·
    have h' : [Obj.singletonEmpty] = [] := h
    cases h'
  ·
    have h' : [Obj.singletonEmpty] = [Obj.empty] := h
    cases h'
  · rfl
  ·
    have h' : [Obj.singletonEmpty] = [Obj.empty, Obj.singletonEmpty] := h
    cases h'
  ·
    have h' : [Obj.empty, Obj.singletonEmpty] = [] := h
    cases h'
  ·
    have h' : [Obj.empty, Obj.singletonEmpty] = [Obj.empty] := h
    cases h'
  ·
    have h' : [Obj.empty, Obj.singletonEmpty] = [Obj.singletonEmpty] := h
    cases h'
  · rfl

theorem membersOf_canonical : FiniteGlobalCore.MembersOfCanonical finiteDescriptiveCore4.core := by
  intro a
  cases a <;> rfl

theorem membersOf_injective_core : FiniteGlobalCore.MembersOfInjective finiteDescriptiveCore4.core := by
  dsimp [FiniteGlobalCore.MembersOfInjective, FiniteDescriptiveCore.core, finiteDescriptiveCore4, finiteGlobalCore]
  exact membersOf_injective

theorem concrete4_extensional :
    ExtensionalObj concreteSemantics4 := by
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj
      (C := finiteDescriptiveCore4) membersOf_canonical membersOf_injective_core)

theorem derivedEmpty_c0_c1_same_denotation :
    concreteSemantics4.denote (derivedEmpty c0) =
      concreteSemantics4.denote (derivedEmpty c1) := by
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_same_denotation
      (C := finiteDescriptiveCore4) membersOf_canonical membersOf_injective_core c0_ex c1_ex)

theorem derivedEmpty_c0_c1_distinct_terms_same_denotation :
    derivedEmpty c0 ≠ derivedEmpty c1 ∧
    concreteSemantics4.denote (derivedEmpty c0) =
      concreteSemantics4.denote (derivedEmpty c1) := by
  simpa [concreteSemantics4, Descriptive.Faithful.FiniteDescriptiveCore.S] using
    (Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_terms_distinct_same_denotation
      (C := finiteDescriptiveCore4) membersOf_canonical membersOf_injective_core c0_ex c1_ex c0_ne_c1)

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for selected results in this file.
-/
#print axioms Descriptive.Faithful.Concrete4.denoteGlobal_spec
#print axioms Descriptive.Faithful.Concrete4.ex_global_iff_membersOf
#print axioms Descriptive.Faithful.Concrete4.ex_global_iff_representableExt
#print axioms Descriptive.Faithful.Concrete4.some_global_ex_concrete4
#print axioms Descriptive.Faithful.Concrete4.russell_not_ex_concrete4
#print axioms Descriptive.Faithful.Concrete4.derivedEmpty_c0_ex
#print axioms Descriptive.Faithful.Concrete4.denote_derivedEmpty_empty
#print axioms Descriptive.Faithful.Concrete4.derivedEmpty_c0_emptyObj
#print axioms Descriptive.Faithful.Concrete4.memPrim0_distinguishes_objects
#print axioms Descriptive.Faithful.Concrete4.concrete4_extensional
#print axioms Descriptive.Faithful.Concrete4.derivedEmpty_c0_c1_same_denotation
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful.Concrete4
