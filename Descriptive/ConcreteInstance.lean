import Descriptive.FaithfulExtensionality
import Descriptive.FaithfulTrajectory

namespace Descriptive.Faithful.Concrete

open Descriptive.Faithful

/-!
A first tiny concrete instance of `Descriptive.Faithful.DescriptiveSemantics`.

Design choice (minimal):
- `Obj := Unit`
- `MemObj := False` (everything is empty)
- `denote` is explicit and computable:
  - primitives denote
  - globals never denote
  - relatives denote iff the base denotes
- extensionality on objects is trivial (only one object)
- two distinct primitive donors yield distinct terms whose derived-empties denote the same object
-/

def concreteMemObj : Unit → Unit → Prop :=
  fun _ _ => False

def concreteDenote : Term → Option Unit
  | Term.prim _ => some ()
  | Term.global _ => none
  | Term.relative t _ =>
      match concreteDenote t with
      | some _ => some ()
      | none => none

def concreteSemantics : DescriptiveSemantics where
  Obj := Unit
  MemObj := concreteMemObj
  denote := concreteDenote
  global_spec := by
    intro φ a h
    -- `concreteDenote (global φ) = none`, so the premise is impossible.
    cases h
  rel_ex := by
    intro t φ b hb
    refine ⟨(), ?_⟩
    -- If the base denotes, the relative denotes.
    cases b
    -- Now `hb : concreteDenote t = some ()`.
    -- Unfold the definition of `concreteDenote` at a relative term and rewrite by `hb`.
    calc
      concreteDenote (Term.relative t φ)
          = (match concreteDenote t with
              | some _ => some ()
              | none => none) := rfl
      _ = (match (some ()) with
            | some _ => some ()
            | none => none) := by rw [hb]
      _ = some () := rfl
  rel_spec := by
    intro t φ b a hb ha y
    -- `MemObj` is always false, so both sides are false.
    constructor
    · intro h
      cases h
    · intro h
      cases h.1

def c0 : Term :=
  Term.prim (PrimConst.mk 0)

def c1 : Term :=
  Term.prim (PrimConst.mk 1)

theorem c0_ex : Ex concreteSemantics c0 := by
  refine ⟨(), ?_⟩
  rfl

theorem c1_ex : Ex concreteSemantics c1 := by
  refine ⟨(), ?_⟩
  rfl

theorem c0_ne_c1 : c0 ≠ c1 := by
  intro h
  -- Reduce to `0 = 1` by constructor injectivity (no computation principles beyond `injection`).
  dsimp [c0, c1] at h
  have h' : (PrimConst.mk 0) = (PrimConst.mk 1) := by
    injection h
  have : (0 : Nat) = 1 := by
    injection h'
  exact Nat.zero_ne_one this

theorem russell_not_ex_concrete :
    ¬ Ex concreteSemantics russell := by
  intro h
  rcases h with ⟨a, ha⟩
  -- `russell` is a global term, and globals never denote in this instance.
  cases ha

theorem derivedEmpty_c0_ex :
    Ex concreteSemantics (derivedEmpty c0) := by
  exact derivedEmpty_ex (S := concreteSemantics) (c := c0) c0_ex

theorem derivedEmpty_c0_emptyObj :
    ∃ a : concreteSemantics.Obj,
      concreteSemantics.denote (derivedEmpty c0) = some a ∧
      ∀ y : concreteSemantics.Obj, ¬ concreteSemantics.MemObj y a := by
  refine ⟨(), ?_, ?_⟩
  · rfl
  · intro y hy
    cases hy

theorem derivedEmpty_c0_emptyTerm :
    ∀ y : Term, ¬ MemTerm concreteSemantics y (derivedEmpty c0) := by
  intro y h
  rcases h with ⟨ya, ea, hy, he, hmem⟩
  cases hmem

def concreteTrajectory : Trajectory :=
  { h :=
      fun t =>
        let rec h' : Term → Nat
          | Term.prim _ => 0
          | Term.global _ => 0
          | Term.relative t0 _ => Nat.succ (h' t0)
        h' t
  }

theorem c0_precedes_derivedEmpty_c0 :
    TrajPrecedes concreteTrajectory c0 (derivedEmpty c0) := by
  refine primitive_precedes_derivedEmpty (τ := concreteTrajectory) (c := c0) ?_ ?_
  · rfl
  · intro t φ
    -- By definition of the concrete height.
    rfl

theorem concrete_extensional :
    ExtensionalObj concreteSemantics := by
  intro a b hab
  cases a
  cases b
  rfl

theorem derivedEmpty_c0_c1_same_denotation :
    concreteSemantics.denote (derivedEmpty c0) =
      concreteSemantics.denote (derivedEmpty c1) := by
  exact derivedEmpty_same_denotation_of_extensional
    (S := concreteSemantics) concrete_extensional c0_ex c1_ex

theorem derivedEmpty_c0_c1_distinct_terms_same_denotation :
    derivedEmpty c0 ≠ derivedEmpty c1 ∧
    concreteSemantics.denote (derivedEmpty c0) =
      concreteSemantics.denote (derivedEmpty c1) := by
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
#print axioms Descriptive.Faithful.Concrete.russell_not_ex_concrete
#print axioms Descriptive.Faithful.Concrete.c0_ex
#print axioms Descriptive.Faithful.Concrete.derivedEmpty_c0_ex
#print axioms Descriptive.Faithful.Concrete.derivedEmpty_c0_emptyObj
#print axioms Descriptive.Faithful.Concrete.c0_precedes_derivedEmpty_c0
#print axioms Descriptive.Faithful.Concrete.concrete_extensional
#print axioms Descriptive.Faithful.Concrete.c0_ne_c1
#print axioms Descriptive.Faithful.Concrete.derivedEmpty_c0_c1_same_denotation
#print axioms Descriptive.Faithful.Concrete.derivedEmpty_c0_c1_distinct_terms_same_denotation
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful.Concrete
