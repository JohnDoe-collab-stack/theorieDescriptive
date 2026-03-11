import Descriptive.FaithfulExtensionality
import Descriptive.FiniteSemanticsBuilder

namespace Descriptive.Faithful

/-!
Finite extensionality abstraction.

In finite internalized instances, objects are represented by explicit member lists `membersOf`.
This module provides a small, reusable criterion to derive object extensionality
(`ExtensionalObj`) from:

1. a *canonicality* assumption: `membersOf` is computed by filtering `allObjs` using `MemObj`;
2. an *injectivity* assumption: `membersOf` is injective.

Both assumptions are local and constructive.
-/

namespace FiniteGlobalCore

/-- Injectivity of the list representation `membersOf`. -/
def MembersOfInjective (C : FiniteGlobalCore) : Prop :=
  Function.Injective C.membersOf

def memDec {α : Type} [DecidableEq α] (x : α) : (L : List α) → Decidable (x ∈ L)
  | [] =>
      isFalse (by intro h; cases h)
  | y :: ys =>
      if hxy : x = y then
        isTrue (by cases hxy; exact List.Mem.head _)
      else
        match memDec x ys with
        | isTrue hmem =>
            isTrue (List.Mem.tail y hmem)
        | isFalse hn =>
            isFalse (by
              intro h
              cases h with
              | head =>
                  exact hxy rfl
              | tail _ h' =>
                  exact hn h')

/-- A canonical decidable instance for `MemObj y a`, derived from `membersOf`. -/
def memObjDec (C : FiniteGlobalCore) (y a : C.Obj) : Decidable (C.MemObj y a) :=
  match memDec y (C.membersOf a) with
  | isTrue hy =>
      isTrue ((C.mem_membersOf_iff y a).1 hy)
  | isFalse hny =>
      isFalse (fun hmem => hny ((C.mem_membersOf_iff y a).2 hmem))

def memObjBool (C : FiniteGlobalCore) (y a : C.Obj) : Bool :=
  @decide (C.MemObj y a) (memObjDec C y a)

/-- Canonicality of `membersOf`: it is the `allObjs`-filter by `MemObj`. -/
def MembersOfCanonical (C : FiniteGlobalCore) : Prop :=
  ∀ a : C.Obj, C.membersOf a = C.allObjs.filter (fun y => memObjBool C y a)

theorem filter_congr {α : Type} (L : List α) (p q : α → Bool) :
    (∀ x : α, x ∈ L → p x = q x) → L.filter p = L.filter q := by
  intro h
  induction L with
  | nil =>
      rfl
  | cons x xs ih =>
      have h0 : p x = q x :=
        h x (List.Mem.head _)
      cases hp : p x <;> cases hq : q x
      · -- false, false
        dsimp [List.filter]
        rw [hp, hq]
        exact ih (fun y hy => h y (List.Mem.tail x hy))
      · -- false, true (impossible)
        have : (false : Bool) = true := by
          calc
            (false : Bool) = p x := by symm; exact hp
            _ = q x := h0
            _ = true := hq
        cases this
      · -- true, false (impossible)
        have : (true : Bool) = false := by
          calc
            (true : Bool) = p x := by symm; exact hp
            _ = q x := h0
            _ = false := hq
        cases this
      · -- true, true
        dsimp [List.filter]
        rw [hp, hq]
        have hxs : xs.filter p = xs.filter q :=
          ih (fun y hy => h y (List.Mem.tail x hy))
        exact congrArg (fun t => x :: t) hxs

theorem decide_eq_of_iff_explicit {p q : Prop} (dp : Decidable p) (dq : Decidable q) (h : p ↔ q) :
    @decide p dp = @decide q dq := by
  cases dp with
  | isTrue hp =>
      have hq : q := h.1 hp
      cases dq with
      | isTrue _ =>
          rfl
      | isFalse hnq =>
          exact False.elim (hnq hq)
  | isFalse hnp =>
      have hnq : ¬ q := by
        intro hq
        exact hnp (h.2 hq)
      cases dq with
      | isTrue hq =>
          exact False.elim (hnq hq)
      | isFalse _ =>
          rfl

theorem membersOf_eq_of_memObj_iff (C : FiniteGlobalCore)
    (hCan : MembersOfCanonical C) {a b : C.Obj}
    (hMem : ∀ y : C.Obj, C.MemObj y a ↔ C.MemObj y b) :
    C.membersOf a = C.membersOf b := by
  -- reduce to filter-equality on `allObjs`
  have ha : C.membersOf a = C.allObjs.filter (fun y => memObjBool C y a) := hCan a
  have hb : C.membersOf b = C.allObjs.filter (fun y => memObjBool C y b) := hCan b
  -- show the filters coincide by pointwise equality of the predicates
  have hFilt :
      C.allObjs.filter (fun y => memObjBool C y a) =
        C.allObjs.filter (fun y => memObjBool C y b) := by
    apply filter_congr (L := C.allObjs)
    intro y hy
    exact
      decide_eq_of_iff_explicit (p := C.MemObj y a) (q := C.MemObj y b)
        (dp := memObjDec C y a) (dq := memObjDec C y b) (h := hMem y)
  exact ha.trans (hFilt.trans hb.symm)

end FiniteGlobalCore

namespace FiniteDescriptiveCore

theorem extensionalObj_toDescriptiveSemantics (C : FiniteDescriptiveCore)
    (hCan : FiniteGlobalCore.MembersOfCanonical C.core)
    (hInj : FiniteGlobalCore.MembersOfInjective C.core) :
    ExtensionalObj (FiniteDescriptiveCore.toDescriptiveSemantics C) := by
  intro a b hab
  apply hInj
  exact
    FiniteGlobalCore.membersOf_eq_of_memObj_iff (C := C.core) hCan (a := a) (b := b) hab

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteGlobalCore.MembersOfInjective
#print axioms Descriptive.Faithful.FiniteGlobalCore.MembersOfCanonical
#print axioms Descriptive.Faithful.FiniteGlobalCore.membersOf_eq_of_memObj_iff
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj_toDescriptiveSemantics
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
