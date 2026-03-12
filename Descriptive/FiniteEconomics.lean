import Descriptive.FiniteSemanticsBuilder
import Descriptive.Economics

namespace Descriptive.Faithful

/-!
Finite economics: existence and computability of utility-maximizing demand.

In a `FiniteDescriptiveCore C`, every object has a finite, enumerated member
list `C.membersOf a`. When a term `t` denotes an object `a`, the feasible set of
outcomes for `t` is exactly the membership set of `a`. Therefore:

- utility maximizers exist as soon as the feasible set is nonempty;
- the *demand set* is computable as a list filter of `membersOf a`.

Everything is constructive.
-/

namespace FiniteDemand

def maxNatList {α : Type} (u : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => Nat.max (u x) (maxNatList u xs)

theorem le_maxNatList_of_mem {α : Type} (u : α → Nat) :
    ∀ {xs : List α} {x : α}, x ∈ xs → u x ≤ maxNatList u xs := by
  intro xs x hx
  induction xs with
  | nil =>
      cases hx
  | cons a as ih =>
      cases hx with
      | head =>
          dsimp [maxNatList]
          change u x ≤ max (u x) (maxNatList u as)
          rw [Nat.max_def]
          by_cases hle : u x ≤ maxNatList u as
          · rw [if_pos hle]
            exact hle
          · rw [if_neg hle]
            exact Nat.le_refl _
      | tail _ hx' =>
          have h := ih hx'
          dsimp [maxNatList]
          change u x ≤ max (u a) (maxNatList u as)
          rw [Nat.max_def]
          by_cases hle : u a ≤ maxNatList u as
          · rw [if_pos hle]
            exact h
          · rw [if_neg hle]
            have hrestlt : maxNatList u as < u a := Nat.lt_of_not_ge hle
            exact Nat.le_trans h (Nat.le_of_lt hrestlt)

theorem maxNatList_le_of_forall_le {α : Type} (u : α → Nat) :
    ∀ {xs : List α} {M : Nat}, (∀ x : α, x ∈ xs → u x ≤ M) → maxNatList u xs ≤ M := by
  intro xs M h
  induction xs with
  | nil =>
      dsimp [maxNatList]
      exact Nat.zero_le _
  | cons a as ih =>
      dsimp [maxNatList]
      have ha : u a ≤ M := h a (List.Mem.head as)
      have hrest : maxNatList u as ≤ M := ih (fun x hx => h x (List.Mem.tail a hx))
      change max (u a) (maxNatList u as) ≤ M
      rw [Nat.max_def]
      by_cases hle : u a ≤ maxNatList u as
      · rw [if_pos hle]
        exact hrest
      · rw [if_neg hle]
        exact ha

def demandMembers {α : Type} (u : α → Nat) (xs : List α) : List α :=
  let m := maxNatList u xs
  xs.filter (fun y => decide (u y = m))

theorem decide_eq_true_iff (p : Prop) (dp : Decidable p) : @decide p dp = true ↔ p := by
  cases dp with
  | isTrue hp =>
      constructor
      · intro _
        exact hp
      · intro _
        rfl
  | isFalse hp =>
      constructor
      · intro h
        cases h
      · intro hp'
        cases (hp hp')

theorem mem_filter_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (y : α), y ∈ xs.filter p ↔ (y ∈ xs ∧ p y = true) := by
  intro xs
  induction xs with
  | nil =>
      intro y
      constructor
      · intro hy
        cases hy
      · intro hy
        cases hy.1
  | cons x xs ih =>
      intro y
      cases hpx : p x with
      | false =>
          constructor
          · intro hy
            have hy0 := hy
            have hxFilter : List.filter p (x :: xs) = xs.filter p := by
              dsimp [List.filter]
              rw [hpx]
            rw [hxFilter] at hy0
            have hy' : y ∈ xs.filter p := hy0
            have h := (ih y).1 hy'
            refine ⟨List.Mem.tail x h.1, h.2⟩
          · rintro ⟨hyMem, hyPred⟩
            have hy' : y ∈ xs.filter p := by
              cases hyMem with
              | head =>
                  have hyPred0 := hyPred
                  rw [hpx] at hyPred0
                  cases hyPred0
              | tail _ hyTail =>
                  exact (ih y).2 ⟨hyTail, hyPred⟩
            have hxFilter : List.filter p (x :: xs) = xs.filter p := by
              dsimp [List.filter]
              rw [hpx]
            -- goal: `y ∈ List.filter p (x :: xs)`
            rw [hxFilter]
            exact hy'
      | true =>
          constructor
          · intro hy
            have hy0 := hy
            have hxFilter : List.filter p (x :: xs) = x :: xs.filter p := by
              dsimp [List.filter]
              rw [hpx]
            rw [hxFilter] at hy0
            have hy' : y ∈ x :: xs.filter p := hy0
            cases hy' with
            | head =>
                refine ⟨List.Mem.head xs, ?_⟩
                exact hpx
            | tail _ hyTail =>
                have h := (ih y).1 hyTail
                refine ⟨List.Mem.tail x h.1, h.2⟩
          · rintro ⟨hyMem, hyPred⟩
            have hy' : y ∈ x :: xs.filter p := by
              cases hyMem with
              | head =>
                  exact List.Mem.head (xs.filter p)
              | tail _ hyTail =>
                  exact List.Mem.tail x ((ih y).2 ⟨hyTail, hyPred⟩)
            have hxFilter : List.filter p (x :: xs) = x :: xs.filter p := by
              dsimp [List.filter]
              rw [hpx]
            rw [hxFilter]
            exact hy'

theorem mem_demandMembers_iff {α : Type} (u : α → Nat) (xs : List α) (y : α) :
    y ∈ demandMembers u xs ↔ (y ∈ xs ∧ u y = maxNatList u xs) := by
  dsimp [demandMembers]
  constructor
  · intro hy
    have h :=
      (mem_filter_iff (p := fun z => decide (u z = maxNatList u xs)) (xs := xs) (y := y)).1 hy
    refine ⟨h.1, ?_⟩
    exact (decide_eq_true_iff (p := (u y = maxNatList u xs)) (dp := inferInstance)).1 h.2
  · rintro ⟨hyxs, huy⟩
    refine
      (mem_filter_iff (p := fun z => decide (u z = maxNatList u xs)) (xs := xs) (y := y)).2 ?_
    refine ⟨hyxs, ?_⟩
    exact (decide_eq_true_iff (p := (u y = maxNatList u xs)) (dp := inferInstance)).2 huy

def argMax {α : Type} (u : α → Nat) : List α → Option α
  | [] => none
  | x :: xs =>
      match argMax u xs with
      | none => some x
      | some y => if u x ≤ u y then some y else some x

theorem argMax_some_of_cons {α : Type} (u : α → Nat) (x : α) (xs : List α) :
    ∃ y : α, argMax u (x :: xs) = some y := by
  cases h : argMax u xs with
  | none =>
      refine ⟨x, ?_⟩
      dsimp [argMax]
      rw [h]
  | some y =>
      by_cases hxy : u x ≤ u y
      · refine ⟨y, ?_⟩
        dsimp [argMax]
        rw [h]
        change (if u x ≤ u y then some y else some x) = some y
        rw [if_pos hxy]
      · refine ⟨x, ?_⟩
        dsimp [argMax]
        rw [h]
        change (if u x ≤ u y then some y else some x) = some x
        rw [if_neg hxy]

theorem argMax_spec {α : Type} (u : α → Nat) :
    ∀ {xs : List α} {y : α},
      argMax u xs = some y →
        y ∈ xs ∧ ∀ z : α, z ∈ xs → u z ≤ u y := by
  intro xs
  induction xs with
  | nil =>
      intro y h
      cases h
  | cons x xs ih =>
      intro y h
      cases hrec : argMax u xs with
      | none =>
          -- this forces `xs = []`, otherwise `argMax u xs` cannot be `none`
          cases xs with
          | nil =>
              dsimp [argMax] at h
              have hx : x = y := by
                cases h
                rfl
              cases hx
              refine ⟨List.Mem.head [], ?_⟩
              intro z hz
              cases hz with
              | head =>
                  exact Nat.le_refl _
              | tail _ hz' =>
                  cases hz'
          | cons x2 xs2 =>
              rcases argMax_some_of_cons (u := u) (x := x2) (xs := xs2) with ⟨y2, hy2⟩
              have : (none : Option α) = some y2 :=
                (hrec.symm.trans hy2)
              cases this
      | some y0 =>
          by_cases hxy : u x ≤ u y0
          · -- result is `y0`
            dsimp [argMax] at h
            rw [hrec] at h
            change (if u x ≤ u y0 then some y0 else some x) = some y at h
            rw [if_pos hxy] at h
            have hy0 : y0 = y := by
              cases h
              rfl
            have hspec0 := ih (y := y0) hrec
            cases hy0
            refine ⟨List.Mem.tail x hspec0.1, ?_⟩
            intro z hz
            cases hz with
            | head =>
                exact hxy
            | tail _ hz' =>
                exact hspec0.2 z hz'
          · -- result is `x`
            dsimp [argMax] at h
            rw [hrec] at h
            change (if u x ≤ u y0 then some y0 else some x) = some y at h
            rw [if_neg hxy] at h
            have hx : x = y := by
              cases h
              rfl
            cases hx
            refine ⟨List.Mem.head xs, ?_⟩
            intro z hz
            cases hz with
            | head =>
                exact Nat.le_refl _
            | tail _ hz' =>
                have hspec := ih (y := y0) hrec
                have hzle : u z ≤ u y0 := hspec.2 z hz'
                have hxgt : u y0 < u x := Nat.lt_of_not_ge hxy
                exact Nat.le_trans hzle (Nat.le_of_lt hxgt)

theorem argMax_eq_maxNatList {α : Type} (u : α → Nat) :
    ∀ {xs : List α} {y : α}, argMax u xs = some y → u y = maxNatList u xs := by
  intro xs y h
  have hspec := argMax_spec (u := u) h
  have hy_le : u y ≤ maxNatList u xs :=
    le_maxNatList_of_mem (u := u) hspec.1
  have hmax_le : maxNatList u xs ≤ u y := by
    refine maxNatList_le_of_forall_le (u := u) (xs := xs) (M := u y) ?_
    intro z hz
    exact hspec.2 z hz
  exact Nat.le_antisymm hy_le hmax_le

theorem argMax_mem_demandMembers {α : Type} (u : α → Nat) :
    ∀ {xs : List α} {y : α}, argMax u xs = some y → y ∈ demandMembers u xs := by
  intro xs y h
  have hspec := argMax_spec (u := u) h
  have huEq : u y = maxNatList u xs := argMax_eq_maxNatList (u := u) h
  exact (mem_demandMembers_iff (u := u) (xs := xs) (y := y)).2 ⟨hspec.1, huEq⟩

end FiniteDemand

open FiniteDemand

namespace FiniteDescriptiveCore

def demandList (C : FiniteDescriptiveCore) (u : C.Obj → Nat) (t : Term) : List C.Obj :=
  match (toDescriptiveSemantics C).denote t with
  | none => []
  | some a => demandMembers u (C.membersOf a)

theorem demandList_eq_of_denote (C : FiniteDescriptiveCore) (u : C.Obj → Nat) {t : Term} {a : C.Obj}
    (ht : (toDescriptiveSemantics C).denote t = some a) :
    demandList C u t = demandMembers u (C.membersOf a) := by
  dsimp [demandList]
  rw [ht]

theorem demandList_sound (C : FiniteDescriptiveCore) (u : C.Obj → Nat) {t : Term} {y : C.Obj} :
    y ∈ demandList C u t → UtilityMaximizer (toDescriptiveSemantics C) u y t := by
  intro hy
  cases ht : (toDescriptiveSemantics C).denote t with
  | none =>
      -- then `demandList` is empty
      have hdemand : demandList C u t = ([] : List C.Obj) := by
        dsimp [demandList]
        rw [ht]
      have hy0 := hy
      rw [hdemand] at hy0
      cases hy0
  | some a =>
      -- unfold `demandList` and use the `membersOf` characterization
      have hdemand : demandList C u t = demandMembers u (C.membersOf a) :=
        demandList_eq_of_denote (C := C) (u := u) (t := t) (a := a) ht
      have hy0 := hy
      rw [hdemand] at hy0
      have hy' : y ∈ demandMembers u (C.membersOf a) := hy0
      have hmem :
          y ∈ C.membersOf a ∧ u y = maxNatList u (C.membersOf a) :=
        (mem_demandMembers_iff (u := u) (xs := C.membersOf a) (y := y)).1 hy'
      refine And.intro ?_ ?_
      · -- feasibility
        have hMemObj : C.MemObj y a := (C.mem_membersOf_iff y a).1 hmem.1
        -- `Feasible` is `MemObjTerm`
        have hMemObjTerm : MemObjTerm (toDescriptiveSemantics C) y t := by
          refine ⟨a, ht, ?_⟩
          exact hMemObj
        exact hMemObjTerm
      · -- maximality among feasible outcomes
        intro y' hyFeas
        -- reduce `Feasible y' t` to `MemObj y' a`, hence membership in `membersOf a`
        have hMemObjTerm : MemObjTerm (toDescriptiveSemantics C) y' t := hyFeas
        have hMemObj : C.MemObj y' a := by
          -- use the fixed denotation `ht`
          have hiff :=
            memObjTerm_iff_of_denote_eq_some (S := toDescriptiveSemantics C) (t := t) (a := a) ht y'
          exact (hiff.1 hMemObjTerm)
        have hmemOf : y' ∈ C.membersOf a := (C.mem_membersOf_iff y' a).2 hMemObj
        -- compare utilities via the list maximum
        have hy'le : u y' ≤ maxNatList u (C.membersOf a) :=
          le_maxNatList_of_mem (u := u) hmemOf
        -- rewrite max value using `u y = max`
        have hy'le0 := hy'le
        rw [hmem.2.symm] at hy'le0
        exact hy'le0

theorem demandList_complete (C : FiniteDescriptiveCore) (u : C.Obj → Nat) {t : Term} {y : C.Obj}
    (hy : UtilityMaximizer (toDescriptiveSemantics C) u y t) :
    y ∈ demandList C u t := by
  -- unfold the maximizer to get feasibility
  have hyFeas : MemObjTerm (toDescriptiveSemantics C) y t := hy.1
  rcases hyFeas with ⟨a, ht, hMemObj⟩
  have hmemOf : y ∈ C.membersOf a := (C.mem_membersOf_iff y a).2 hMemObj
  -- show `u y` equals the maximum on `membersOf a`
  have hmax_le : maxNatList u (C.membersOf a) ≤ u y := by
    refine maxNatList_le_of_forall_le (u := u) (xs := C.membersOf a) (M := u y) ?_
    intro y' hy'
    have hMemObj' : C.MemObj y' a := (C.mem_membersOf_iff y' a).1 hy'
    have hyFeas' : MemObjTerm (toDescriptiveSemantics C) y' t := ⟨a, ht, hMemObj'⟩
    exact hy.2 y' hyFeas'
  have hy_le : u y ≤ maxNatList u (C.membersOf a) :=
    le_maxNatList_of_mem (u := u) hmemOf
  have huEq : u y = maxNatList u (C.membersOf a) := Nat.le_antisymm hy_le hmax_le
  -- conclude membership in the demand list
  have : y ∈ demandMembers u (C.membersOf a) :=
    (mem_demandMembers_iff (u := u) (xs := C.membersOf a) (y := y)).2 ⟨hmemOf, huEq⟩
  -- rewrite `demandList` using the denotation witness
  simpa [demandList, ht] using this

theorem exists_utilityMaximizer_of_exists_feasible (C : FiniteDescriptiveCore) (u : C.Obj → Nat)
    {t : Term} (hEx : Ex (toDescriptiveSemantics C) t)
    (hFeas : ∃ y : C.Obj, MemObjTerm (toDescriptiveSemantics C) y t) :
    ∃ y : C.Obj, UtilityMaximizer (toDescriptiveSemantics C) u y t := by
  rcases hEx with ⟨a, ht⟩
  rcases hFeas with ⟨y0, hy0⟩
  -- feasibility gives a witness that `membersOf a` is nonempty
  have hMemObj0 : C.MemObj y0 a :=
    (memObjTerm_iff_of_denote_eq_some (S := toDescriptiveSemantics C) ht y0).1 hy0
  have hmem0 : y0 ∈ C.membersOf a := (C.mem_membersOf_iff y0 a).2 hMemObj0
  cases hxs : C.membersOf a with
  | nil =>
      have hmem0' := hmem0
      rw [hxs] at hmem0'
      cases hmem0'
  | cons x xs =>
      rcases argMax_some_of_cons (u := u) (x := x) (xs := xs) with ⟨y, harg⟩
      have hyMem : y ∈ demandMembers u (x :: xs) :=
        argMax_mem_demandMembers (u := u) harg
      have hyMem' : y ∈ demandMembers u (C.membersOf a) := by
        have hyMem0 := hyMem
        rw [hxs.symm] at hyMem0
        exact hyMem0
      have hyList : y ∈ demandList C u t := by
        have hdemand : demandList C u t = demandMembers u (C.membersOf a) :=
          demandList_eq_of_denote (C := C) (u := u) (t := t) (a := a) ht
        rw [hdemand]
        exact hyMem'
      exact ⟨y, demandList_sound (C := C) (u := u) (t := t) (y := y) hyList⟩

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.demandList_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.demandList_complete
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.exists_utilityMaximizer_of_exists_feasible
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
