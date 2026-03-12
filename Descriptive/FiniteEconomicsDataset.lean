import Descriptive.FiniteEconomics

namespace Descriptive.Faithful

/-!
## Finite datasets, revealed inequalities, and rationalization

This module turns the constructive finite demand theory from `FiniteEconomics`
into a *dataset* language.

The key economic point is the tie-break: `demandChoice` chooses the **first**
utility-maximizer in the menu list. Therefore, an observed choice `y` from a
menu `t` is equivalent (constructively, in the finite semantics) to a finite
system of inequalities on the latent utility function `u : Obj → Nat`:

- every feasible `z` must satisfy `u z ≤ u y` (weak maximization);
- every feasible `z` that appears **before** `y` in the menu list must satisfy
  `u z + 1 ≤ u y` (strictness forcing the tie-break to pick `y`).

Everything is constructive (no axioms, no `Classical`).
-/

namespace FiniteDescriptiveCore

/-!
### Menus (as concrete lists)
-/

def menuList (C : FiniteDescriptiveCore) (t : Term) : List C.Obj :=
  match (toDescriptiveSemantics C).denote t with
  | none => []
  | some a => C.membersOf a

theorem mem_menuList_iff_feasible (C : FiniteDescriptiveCore) (t : Term) (y : C.Obj) :
    y ∈ menuList C t ↔ Feasible (toDescriptiveSemantics C) y t := by
  cases ht : (toDescriptiveSemantics C).denote t with
  | none =>
      constructor
      · intro hy
        dsimp [menuList] at hy
        rw [ht] at hy
        cases hy
      · intro hy
        rcases hy with ⟨a, ha, _⟩
        have : (none : Option C.Obj) = some a := ht.symm.trans ha
        cases this
  | some a =>
      constructor
      · intro hy
        have hyMem : y ∈ C.membersOf a := by
          dsimp [menuList] at hy
          rw [ht] at hy
          exact hy
        have hMemObj : C.MemObj y a := (C.mem_membersOf_iff y a).1 hyMem
        exact ⟨a, ht, hMemObj⟩
      · intro hy
        have hiff :=
          memObjTerm_iff_of_denote_eq_some (S := toDescriptiveSemantics C) (t := t) (a := a) ht y
        have hMemObj : C.MemObj y a := (hiff.1 hy)
        have hyMem : y ∈ C.membersOf a := (C.mem_membersOf_iff y a).2 hMemObj
        dsimp [menuList]
        rw [ht]
        exact hyMem

structure Observation (C : FiniteDescriptiveCore) where
  t : Term
  y : C.Obj
  feasible : Feasible (toDescriptiveSemantics C) y t

/-!
### Prefix-before (menu order)
-/

def prefixBefore {α : Type} [DecidableEq α] : List α → α → List α
  | [], _ => []
  | x :: xs, y => if x = y then [] else x :: prefixBefore xs y

theorem mem_prefixBefore_implies_mem {α : Type} [DecidableEq α] :
    ∀ {xs : List α} {x y : α}, x ∈ prefixBefore xs y → x ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro x y hx
      dsimp [prefixBefore] at hx
      cases hx
  | cons a as ih =>
      intro x y hx
      dsimp [prefixBefore] at hx
      by_cases hay : a = y
      · rw [if_pos hay] at hx
        cases hx
      · rw [if_neg hay] at hx
        cases hx with
        | head => exact List.Mem.head as
        | tail _ hx' => exact List.Mem.tail a (ih hx')

/-!
### Constructive list lemmas (avoid `propext` / `Quot.sound`)

Some standard library lemmas like `List.mem_append` and `List.mem_map_of_mem`
are proved in this environment using `propext` (and sometimes `Quot.sound`).
To keep the development strictly constructive, we re-prove the small fragments
we need here.
-/

theorem mem_append_left' {α : Type} :
    ∀ {a : α} {s t : List α}, a ∈ s → a ∈ s ++ t := by
  intro a s t
  induction s with
  | nil =>
      intro ha
      cases ha
  | cons x xs ih =>
      intro ha
      cases ha with
      | head =>
          exact List.Mem.head (xs ++ t)
      | tail _ ha' =>
          exact List.Mem.tail x (ih ha')

theorem mem_append_right' {α : Type} :
    ∀ {a : α} {s t : List α}, a ∈ t → a ∈ s ++ t := by
  intro a s t
  induction s with
  | nil =>
      intro ha
      exact ha
  | cons x xs ih =>
      intro ha
      exact List.Mem.tail x (ih ha)

theorem mem_append_elim' {α : Type} :
    ∀ {a : α} {s t : List α}, a ∈ s ++ t → a ∈ s ∨ a ∈ t := by
  intro a s t ha
  induction s with
  | nil =>
      -- `[] ++ t = t`
      exact Or.inr ha
  | cons x xs ih =>
      -- `a ∈ x :: (xs ++ t)`
      cases ha with
      | head =>
          exact Or.inl (List.Mem.head xs)
      | tail _ ha' =>
          have h := ih ha'
          cases h with
          | inl h0 => exact Or.inl (List.Mem.tail x h0)
          | inr h0 => exact Or.inr h0

theorem mem_map_of_mem' {α β : Type} (f : α → β) :
    ∀ {xs : List α} {a : α}, a ∈ xs → f a ∈ xs.map f := by
  intro xs a ha
  induction xs with
  | nil =>
      cases ha
  | cons x xs ih =>
      cases ha with
      | head =>
          exact List.Mem.head (xs.map f)
      | tail _ ha' =>
          exact List.Mem.tail (f x) (ih ha')

theorem mem_map_elim' {α β : Type} (f : α → β) :
    ∀ {xs : List α} {b : β}, b ∈ xs.map f → ∃ a : α, a ∈ xs ∧ f a = b := by
  intro xs b hb
  induction xs with
  | nil =>
      cases hb
  | cons x xs ih =>
      cases hb with
      | head =>
          exact ⟨x, List.Mem.head xs, rfl⟩
      | tail _ hb' =>
          rcases ih hb' with ⟨a, ha, hfa⟩
          exact ⟨a, List.Mem.tail x ha, hfa⟩

/-!
### Revealed inequalities (constraints)
-/

structure Constraint (α : Type) where
  src : α
  dst : α
  w : Nat

abbrev SatisfiesConstraint {α : Type} (u : α → Nat) (c : Constraint α) : Prop :=
  u c.src + c.w ≤ u c.dst

def SatisfiesConstraints {α : Type} (u : α → Nat) (cs : List (Constraint α)) : Prop :=
  ∀ c : Constraint α, c ∈ cs → SatisfiesConstraint u c

def constraintsOf (C : FiniteDescriptiveCore) (t : Term) (y : C.Obj) : List (Constraint C.Obj) :=
  let menu := menuList C t
  let weak := menu.map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj))
  let strict := (prefixBefore menu y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj))
  strict ++ weak

theorem satisfiesConstraints_of_mem_append {α : Type} {u : α → Nat} {cs ds : List (Constraint α)} :
    SatisfiesConstraints u (cs ++ ds) → SatisfiesConstraints u cs ∧ SatisfiesConstraints u ds := by
  intro h
  refine And.intro ?_ ?_
  · intro c hc
    exact h c (mem_append_left' (a := c) (s := cs) (t := ds) hc)
  · intro c hc
    exact h c (mem_append_right' (a := c) (s := cs) (t := ds) hc)

theorem satisfiesConstraints_append_of_left_right {α : Type} {u : α → Nat} {cs ds : List (Constraint α)} :
    SatisfiesConstraints u cs → SatisfiesConstraints u ds → SatisfiesConstraints u (cs ++ ds) := by
  intro hcs hds c hc
  have hc' : c ∈ cs ∨ c ∈ ds := mem_append_elim' (a := c) (s := cs) (t := ds) hc
  cases hc' with
  | inl h0 => exact hcs c h0
  | inr h0 => exact hds c h0

theorem satisfiesConstraints_of_map {α β : Type} (f : α → Constraint β) (u : β → Nat) :
    ∀ {xs : List α},
      (∀ a : α, a ∈ xs → SatisfiesConstraint u (f a)) →
        SatisfiesConstraints u (xs.map f) := by
  intro xs h c hc
  induction xs with
  | nil =>
      cases hc
  | cons a as ih =>
      cases hc with
      | head =>
          exact h a (List.Mem.head as)
      | tail _ hc' =>
          have h' : ∀ a' : α, a' ∈ as → SatisfiesConstraint u (f a') := by
            intro a' ha'
            exact h a' (List.Mem.tail a ha')
          exact ih h' hc'

/-!
### List-order tie-break lemmas
-/

theorem chooseHead_filter_eq_some_of_first {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ {xs : List α} {y : α},
      y ∈ xs →
        p y = true →
          (∀ z : α, z ∈ prefixBefore xs y → p z = false) →
            chooseHead (xs.filter p) = some y := by
  intro xs
  induction xs with
  | nil =>
      intro y hy _ _
      cases hy
  | cons x xs ih =>
      intro y hy hp hpre
      by_cases hxy : x = y
      · cases hxy
        dsimp [List.filter]
        rw [hp]
        dsimp [chooseHead]
      · have hyTail : y ∈ xs := by
          cases hy with
          | head => cases (hxy rfl)
          | tail _ hy' => exact hy'
        have hxPre : x ∈ prefixBefore (x :: xs) y := by
          dsimp [prefixBefore]
          rw [if_neg hxy]
          exact List.Mem.head (prefixBefore xs y)
        have hxFail : p x = false := hpre x hxPre
        dsimp [chooseHead]
        dsimp [List.filter]
        rw [hxFail]
        have hpreTail : ∀ z : α, z ∈ prefixBefore xs y → p z = false := by
          intro z hz
          have hz0 : z ∈ prefixBefore (x :: xs) y := by
            dsimp [prefixBefore]
            rw [if_neg hxy]
            exact List.Mem.tail x hz
          exact hpre z hz0
        exact ih (y := y) hyTail hp hpreTail

theorem chooseHead_filter_eq_some_implies_prefix_false {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ {xs : List α} {y z : α},
      chooseHead (xs.filter p) = some y →
        z ∈ prefixBefore xs y →
          p z = false := by
  intro xs
  induction xs with
  | nil =>
      intro y z h hz
      dsimp [List.filter, chooseHead] at h
      cases h
  | cons x xs ih =>
      intro y z h hz
      dsimp [prefixBefore] at hz
      by_cases hxy : x = y
      · cases hxy
        rw [if_pos rfl] at hz
        cases hz
      · rw [if_neg hxy] at hz
        cases hz with
        | head =>
            -- show `p x = false`, otherwise the filtered head is `x`.
            cases hpx : p x with
            | false =>
                exact rfl
            | true =>
                have hfilter : (x :: xs).filter p = x :: xs.filter p := by
                  dsimp [List.filter]
                  rw [hpx]
                have hhead : chooseHead ((x :: xs).filter p) = some x := by
                  dsimp [chooseHead]
                  rw [hfilter]
                have : (some y : Option α) = some x := Eq.trans h.symm hhead
                cases this with
                | _ => cases (hxy rfl)
        | tail _ hzTail =>
            -- again `p x = false`, so we reduce to the tail.
            have hpxFalse : p x = false := by
              cases hpx : p x with
              | false => exact rfl
              | true =>
                  have hfilter : (x :: xs).filter p = x :: xs.filter p := by
                    dsimp [List.filter]
                    rw [hpx]
                  have hhead : chooseHead ((x :: xs).filter p) = some x := by
                    dsimp [chooseHead]
                    rw [hfilter]
                  have : (some y : Option α) = some x := Eq.trans h.symm hhead
                  cases this with
                  | _ => cases (hxy rfl)
            have hfilter : (x :: xs).filter p = xs.filter p := by
              dsimp [List.filter]
              rw [hpxFalse]
            have hTail : chooseHead (xs.filter p) = some y := by
              -- rewrite `h` along `hfilter`
              have h0 := h
              rw [hfilter] at h0
              exact h0
            exact ih (y := y) (z := z) hTail hzTail

/-!
### From `demandChoice` to inequalities
-/

theorem demandChoice_eq_some_implies_menu_le
    (C : FiniteDescriptiveCore) (u : C.Obj → Nat) {t : Term} {y : C.Obj}
    (hChoice : demandChoice C u t = some y) :
    ∀ z : C.Obj, z ∈ menuList C t → u z ≤ u y := by
  intro z hzMenu
  have hyMax : UtilityMaximizer (toDescriptiveSemantics C) u y t :=
    demandChoice_sound (C := C) (u := u) (t := t) (y := y) hChoice
  have hzFeas : Feasible (toDescriptiveSemantics C) z t :=
    (mem_menuList_iff_feasible (C := C) (t := t) (y := z)).1 hzMenu
  exact hyMax.2 z hzFeas

theorem demandChoice_eq_some_implies_satisfiesConstraints
    (C : FiniteDescriptiveCore) (u : C.Obj → Nat) {t : Term} {y : C.Obj}
    (hChoice : demandChoice C u t = some y) :
    SatisfiesConstraints u (constraintsOf C t y) := by
  -- derive the "menu" and that `y` is a maximizer
  have hyMax : UtilityMaximizer (toDescriptiveSemantics C) u y t :=
    demandChoice_sound (C := C) (u := u) (t := t) (y := y) hChoice
  have hyMenu : y ∈ menuList C t :=
    (mem_menuList_iff_feasible (C := C) (t := t) (y := y)).2 hyMax.1
  let menu := menuList C t
  have hyEqMax : u y = FiniteDemand.maxNatList u menu := by
    have hmaxLe : FiniteDemand.maxNatList u menu ≤ u y := by
      refine FiniteDemand.maxNatList_le_of_forall_le (u := u) (xs := menu) (M := u y) ?_
      intro z hz
      exact demandChoice_eq_some_implies_menu_le (C := C) (u := u) (t := t) (y := y) hChoice z hz
    have hyLe : u y ≤ FiniteDemand.maxNatList u menu :=
      FiniteDemand.le_maxNatList_of_mem (u := u) (xs := menu) (x := y) hyMenu
    exact Nat.le_antisymm hyLe hmaxLe
  -- max predicate on the menu
  let p : C.Obj → Bool := fun z => decide (u z = FiniteDemand.maxNatList u menu)
  -- `demandChoice = some y` implies `chooseHead (menu.filter p) = some y`
  have hHead : chooseHead (menu.filter p) = some y := by
    cases ht : (toDescriptiveSemantics C).denote t with
    | none =>
        have hdemand : demandList C u t = ([] : List C.Obj) := by
          dsimp [demandList]
          rw [ht]
        have h0 := hChoice
        dsimp [demandChoice] at h0
        rw [hdemand] at h0
        dsimp [chooseHead] at h0
        cases h0
    | some a =>
        -- reduce to the concrete menu `membersOf a`
        have hMenu : menu = C.membersOf a := by
          dsimp [menu, menuList]
          rw [ht]
        have hdemand : demandList C u t = FiniteDemand.demandMembers u (C.membersOf a) :=
          demandList_eq_of_denote (C := C) (u := u) (t := t) (a := a) ht
        -- rewrite the menu in `hChoice` and unfold `demandMembers`
        have hChoiceMenu : chooseHead (FiniteDemand.demandMembers u menu) = some y := by
          have h0 := hChoice
          dsimp [demandChoice] at h0
          rw [hdemand] at h0
          -- rewrite `membersOf a` to `menu`
          rw [← hMenu] at h0
          exact h0
        dsimp [FiniteDemand.demandMembers] at hChoiceMenu
        -- `p` is definitionally the max predicate used in `demandMembers`
        dsimp [p]
        exact hChoiceMenu
  -- package strict/weak constraints
  dsimp [constraintsOf]
  refine satisfiesConstraints_append_of_left_right ?_ ?_
  · -- strict: prefix elements must fail the max predicate, hence be strictly below the max.
    refine satisfiesConstraints_of_map (f := fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) (u := u) ?_
    intro z hzPre
    have hzMenu : z ∈ menu := mem_prefixBefore_implies_mem (xs := menu) (x := z) (y := y) hzPre
    have hzLe : u z ≤ u y :=
      demandChoice_eq_some_implies_menu_le (C := C) (u := u) (t := t) (y := y) hChoice z (by
        -- `hzMenu` is in `menu := menuList C t`
        dsimp [menu] at hzMenu
        exact hzMenu
      )
    have hpzFalse : p z = false :=
      chooseHead_filter_eq_some_implies_prefix_false (p := p) (xs := menu) (y := y) (z := z) hHead hzPre
    have hzNeMax : u z ≠ FiniteDemand.maxNatList u menu := by
      intro hzEq
      have : p z = true := by
        dsimp [p]
        exact
          (FiniteDemand.decide_eq_true_iff
              (p := (u z = FiniteDemand.maxNatList u menu)) (dp := inferInstance)).2 hzEq
      have : False := by
        -- `true = false`
        have : true = false := this.symm.trans hpzFalse
        cases this
      cases this
    have hzNe : u z ≠ u y := by
      intro hzEq
      have : u z = FiniteDemand.maxNatList u menu := by
        -- `u z = u y = max`
        exact hzEq.trans hyEqMax
      exact hzNeMax this
    have hzLt : u z < u y := Nat.lt_of_le_of_ne hzLe hzNe
    dsimp [SatisfiesConstraint]
    exact Nat.succ_le_of_lt hzLt
  · -- weak: every menu element satisfies `u z ≤ u y`
    refine satisfiesConstraints_of_map (f := fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) (u := u) ?_
    intro z hzMenu
    have hzLe : u z ≤ u y :=
      demandChoice_eq_some_implies_menu_le (C := C) (u := u) (t := t) (y := y) hChoice z hzMenu
    dsimp [SatisfiesConstraint]
    exact hzLe

/-!
### From inequalities back to `demandChoice`
-/

theorem satisfiesConstraints_implies_demandChoice_eq_some
    (C : FiniteDescriptiveCore) (u : C.Obj → Nat) {t : Term} {y : C.Obj}
    (hyFeas : Feasible (toDescriptiveSemantics C) y t)
    (hSat : SatisfiesConstraints u (constraintsOf C t y)) :
    demandChoice C u t = some y := by
  rcases hyFeas with ⟨a, ht, hMemObj⟩
  have hyMem : y ∈ C.membersOf a := (C.mem_membersOf_iff y a).2 hMemObj
  -- rewrite the menu
  have hMenu : menuList C t = C.membersOf a := by
    dsimp [menuList]
    rw [ht]
  let menu := C.membersOf a
  have hyMenu : y ∈ menu := by
    dsimp [menu]
    exact hyMem
  -- split strict/weak constraints
  have hSplit :=
    satisfiesConstraints_of_mem_append
      (u := u)
      (cs := (prefixBefore (menuList C t) y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)))
      (ds := (menuList C t).map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)))
      (by
        dsimp [constraintsOf] at hSat
        exact hSat
      )
  have hStrict0 :
      SatisfiesConstraints u ((prefixBefore (menuList C t) y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj))) :=
    hSplit.1
  have hWeak0 :
      SatisfiesConstraints u ((menuList C t).map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj))) :=
    hSplit.2
  -- transport to `menu`
  have hStrict :
      SatisfiesConstraints u ((prefixBefore menu y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj))) := by
    intro c hc
    -- rewrite membership along `hMenu`
    have hc' : c ∈ (prefixBefore (menuList C t) y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) := by
      -- rewrite the underlying list
      have : prefixBefore (menuList C t) y = prefixBefore menu y := by
        dsimp [menu]
        rw [hMenu]
      have hmap :
          (prefixBefore (menuList C t) y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) =
            (prefixBefore menu y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) := by
        rw [this]
      have hc0 := hc
      -- turn membership in RHS into membership in LHS
      rw [← hmap] at hc0
      exact hc0
    exact hStrict0 c hc'
  have hWeak :
      SatisfiesConstraints u (menu.map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj))) := by
    intro c hc
    have hc' : c ∈ (menuList C t).map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) := by
      dsimp [menu] at hc
      have : menuList C t = menu := by
        dsimp [menu]
        rw [hMenu]
      have hmap :
          (menuList C t).map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) =
            menu.map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) := by
        rw [this]
      have hc0 := hc
      rw [← hmap] at hc0
      exact hc0
    exact hWeak0 c hc'
  -- show `u y` is the menu maximum
  have hMenuLe : ∀ z : C.Obj, z ∈ menu → u z ≤ u y := by
    intro z hz
    have hzC : (⟨z, y, 0⟩ : Constraint C.Obj) ∈ menu.map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) := by
      exact mem_map_of_mem' (f := fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) hz
    have hzSat := hWeak (⟨z, y, 0⟩ : Constraint C.Obj) hzC
    dsimp [SatisfiesConstraint] at hzSat
    exact hzSat
  have hMaxLe : FiniteDemand.maxNatList u menu ≤ u y := by
    refine FiniteDemand.maxNatList_le_of_forall_le (u := u) (xs := menu) (M := u y) ?_
    intro z hz
    exact hMenuLe z hz
  have hyLeMax : u y ≤ FiniteDemand.maxNatList u menu :=
    FiniteDemand.le_maxNatList_of_mem (u := u) (xs := menu) (x := y) hyMenu
  have hyEqMax : u y = FiniteDemand.maxNatList u menu := Nat.le_antisymm hyLeMax hMaxLe
  -- max predicate on the menu
  let p : C.Obj → Bool := fun z => decide (u z = FiniteDemand.maxNatList u menu)
  have hpY : p y = true := by
    dsimp [p]
    exact
      (FiniteDemand.decide_eq_true_iff
          (p := (u y = FiniteDemand.maxNatList u menu)) (dp := inferInstance)).2 hyEqMax
  have hpPrefix : ∀ z : C.Obj, z ∈ prefixBefore menu y → p z = false := by
    intro z hzPre
    have hzC : (⟨z, y, 1⟩ : Constraint C.Obj) ∈ (prefixBefore menu y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) := by
      exact mem_map_of_mem' (f := fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) hzPre
    have hzSat := hStrict (⟨z, y, 1⟩ : Constraint C.Obj) hzC
    dsimp [SatisfiesConstraint] at hzSat
    have hzLt : u z < u y :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self (u z)) hzSat
    have hzNe : u z ≠ u y := Nat.ne_of_lt hzLt
    have hzNeMax : u z ≠ FiniteDemand.maxNatList u menu := by
      intro hEq
      have : u z = u y := hEq.trans hyEqMax.symm
      exact hzNe this
    dsimp [p]
    cases hpz : decide (u z = FiniteDemand.maxNatList u menu) with
    | true =>
        have hzEq : u z = FiniteDemand.maxNatList u menu :=
          (FiniteDemand.decide_eq_true_iff
              (p := (u z = FiniteDemand.maxNatList u menu)) (dp := inferInstance)).1 hpz
        have : False := hzNeMax hzEq
        cases this
    | false =>
        rfl
  have hHead : chooseHead (menu.filter p) = some y :=
    chooseHead_filter_eq_some_of_first (p := p) (xs := menu) (y := y) hyMenu hpY hpPrefix
  have hHead' := hHead
  dsimp [p] at hHead'
  -- rewrite `demandChoice` to this head statement
  have hdemand : demandList C u t = FiniteDemand.demandMembers u menu := by
    have hdemand0 :
        demandList C u t = FiniteDemand.demandMembers u (C.membersOf a) :=
      demandList_eq_of_denote (C := C) (u := u) (t := t) (a := a) ht
    dsimp [menu]
    exact hdemand0
  dsimp [demandChoice]
  rw [hdemand]
  -- `demandMembers` is a filter by `p`
  dsimp [FiniteDemand.demandMembers]
  exact hHead'

/-!
### Dataset rationalization
-/

def RationalizesDataset (C : FiniteDescriptiveCore) (u : C.Obj → Nat) (data : List (Observation C)) : Prop :=
  ∀ obs : Observation C, obs ∈ data → demandChoice C u obs.t = some obs.y

def bindList {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | x :: xs, f => f x ++ bindList xs f

theorem mem_bindList_iff {α β : Type} :
    ∀ (xs : List α) (f : α → List β) (b : β),
      b ∈ bindList xs f ↔ ∃ a : α, a ∈ xs ∧ b ∈ f a := by
  intro xs
  induction xs with
  | nil =>
      intro f b
      constructor
      · intro hb
        dsimp [bindList] at hb
        cases hb
      · intro hb
        rcases hb with ⟨a, ha, _⟩
        cases ha
  | cons x xs ih =>
      intro f b
      constructor
      · intro hb
        dsimp [bindList] at hb
        have hb' : b ∈ f x ∨ b ∈ bindList xs f := mem_append_elim' (a := b) (s := f x) (t := bindList xs f) hb
        cases hb' with
        | inl h0 =>
            exact ⟨x, List.Mem.head xs, h0⟩
        | inr h0 =>
            rcases (ih f b).1 h0 with ⟨a, ha, hbfa⟩
            exact ⟨a, List.Mem.tail x ha, hbfa⟩
      · intro hb
        rcases hb with ⟨a, ha, hbfa⟩
        dsimp [bindList]
        cases ha with
        | head =>
            exact mem_append_left' (a := b) (s := f x) (t := bindList xs f) hbfa
        | tail _ ha' =>
            have : b ∈ bindList xs f := (ih f b).2 ⟨a, ha', hbfa⟩
            exact mem_append_right' (a := b) (s := f x) (t := bindList xs f) this

def ConstraintsOfDataset (C : FiniteDescriptiveCore) (data : List (Observation C)) : List (Constraint C.Obj) :=
  bindList data (fun obs => constraintsOf C obs.t obs.y)

theorem rationalizesDataset_implies_satisfiesConstraints
    (C : FiniteDescriptiveCore) (u : C.Obj → Nat) (data : List (Observation C)) :
    RationalizesDataset C u data → SatisfiesConstraints u (ConstraintsOfDataset C data) := by
  intro hR c hc
  dsimp [ConstraintsOfDataset] at hc
  rcases (mem_bindList_iff (xs := data) (f := fun obs => constraintsOf C obs.t obs.y) (b := c)).1 hc with
    ⟨obs, hObsMem, hcIn⟩
  have hChoice : demandChoice C u obs.t = some obs.y := hR obs hObsMem
  have hSatObs : SatisfiesConstraints u (constraintsOf C obs.t obs.y) :=
    demandChoice_eq_some_implies_satisfiesConstraints (C := C) (u := u) (t := obs.t) (y := obs.y) hChoice
  exact hSatObs c hcIn

theorem satisfiesConstraints_implies_rationalizesDataset
    (C : FiniteDescriptiveCore) (u : C.Obj → Nat) (data : List (Observation C)) :
    SatisfiesConstraints u (ConstraintsOfDataset C data) → RationalizesDataset C u data := by
  intro hSat obs hObsMem
  have hSatObs : SatisfiesConstraints u (constraintsOf C obs.t obs.y) := by
    intro c hc
    apply hSat c
    dsimp [ConstraintsOfDataset]
    exact (mem_bindList_iff (xs := data) (f := fun obs => constraintsOf C obs.t obs.y) (b := c)).2 ⟨obs, hObsMem, hc⟩
  exact
    satisfiesConstraints_implies_demandChoice_eq_some
      (C := C) (u := u) (t := obs.t) (y := obs.y) obs.feasible hSatObs

theorem rationalizesDataset_iff_satisfiesConstraints
    (C : FiniteDescriptiveCore) (u : C.Obj → Nat) (data : List (Observation C)) :
    RationalizesDataset C u data ↔ SatisfiesConstraints u (ConstraintsOfDataset C data) := by
  constructor
  · exact rationalizesDataset_implies_satisfiesConstraints (C := C) (u := u) (data := data)
  · exact satisfiesConstraints_implies_rationalizesDataset (C := C) (u := u) (data := data)

/-!
### A computable (sound) rationalizer

Given a finite dataset, we can *attempt* to construct a utility function by
iterative constraint propagation (difference constraints with weights `0/1`).
We then *check* that the produced `u` satisfies the constraints, and only in
that case return it.

This is intentionally minimal: we only prove **soundness** (if it returns a
utility, that utility rationalizes the dataset).
-/

def satisfiesConstraintsBool {α : Type} (u : α → Nat) : List (Constraint α) → Bool
  | [] => true
  | c :: cs => decide (SatisfiesConstraint u c) && satisfiesConstraintsBool u cs

theorem satisfiesConstraints_of_bool_true {α : Type} (u : α → Nat) :
    ∀ (cs : List (Constraint α)), satisfiesConstraintsBool u cs = true → SatisfiesConstraints u cs := by
  intro cs
  induction cs with
  | nil =>
      intro _ c hc
      cases hc
  | cons c cs ih =>
      intro hBool c' hc'
      dsimp [satisfiesConstraintsBool] at hBool
      cases hdec : decide (SatisfiesConstraint u c) with
      | false =>
          rw [hdec] at hBool
          -- `false && _ = true` is impossible
          cases hBool
      | true =>
          rw [hdec] at hBool
          have hTail : satisfiesConstraintsBool u cs = true := by
            -- `true && b = true` forces `b = true`
            cases hcs : satisfiesConstraintsBool u cs with
            | false =>
                rw [hcs] at hBool
                cases hBool
            | true =>
                rfl
          cases hc' with
          | head =>
              exact
                (FiniteDemand.decide_eq_true_iff (p := SatisfiesConstraint u c) (dp := inferInstance)).1 hdec
          | tail _ hcTail =>
              have hSatTail : SatisfiesConstraints u cs := ih hTail
              exact hSatTail c' hcTail

def incomingMax {α : Type} [DecidableEq α] (u : α → Nat) (v : α) : List (Constraint α) → Nat
  | [] => 0
  | c :: cs =>
      if c.dst = v then
        Nat.max (u c.src + c.w) (incomingMax u v cs)
      else
        incomingMax u v cs

def relaxOnce {α : Type} [DecidableEq α] (cs : List (Constraint α)) (u : α → Nat) : α → Nat :=
  fun v => Nat.max (u v) (incomingMax u v cs)

def iterate {α : Type} (n : Nat) (f : α → α) (x : α) : α :=
  Nat.rec x (fun _ acc => f acc) n

def solveUtility (C : FiniteDescriptiveCore) (data : List (Observation C)) : Option (C.Obj → Nat) :=
  let cs := ConstraintsOfDataset C data
  let u0 : C.Obj → Nat := fun _ => 0
  let u := iterate C.allObjs.length (relaxOnce cs) u0
  if satisfiesConstraintsBool u cs then some u else none

theorem solveUtility_sound (C : FiniteDescriptiveCore) (data : List (Observation C))
    {u : C.Obj → Nat} :
    solveUtility C data = some u → RationalizesDataset C u data := by
  intro h
  dsimp [solveUtility] at h
  -- after unfolding, we can case split on the boolean check
  cases hSat :
      satisfiesConstraintsBool
        (iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0))
        (ConstraintsOfDataset C data) with
  | false =>
      rw [hSat] at h
      cases h
  | true =>
      rw [hSat] at h
      cases h
      -- now `u` is the produced candidate utility
      let uCand : C.Obj → Nat :=
        iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0)
      have hProp : SatisfiesConstraints uCand (ConstraintsOfDataset C data) := by
        exact satisfiesConstraints_of_bool_true (u := uCand) (ConstraintsOfDataset C data) (by
          -- `hSat` is exactly the boolean fact we need (after unfolding `uCand`)
          dsimp [uCand]
          exact hSat
        )
      exact (rationalizesDataset_iff_satisfiesConstraints (C := C) (u := uCand) (data := data)).2 hProp

/-!
### Informative failure: an explicit violated constraint

`solveUtility` currently returns `none` on failure. For economics/debugging it is
often better to expose *which* revealed inequality fails for the candidate `u`.
The following API returns either a rationalizing `u`, or a concrete violated
constraint `c`.
-/

theorem decide_eq_false_iff (p : Prop) (dp : Decidable p) : @decide p dp = false ↔ ¬ p := by
  cases dp with
  | isTrue hp =>
      constructor
      · intro h
        cases h
      · intro hnp
        cases (hnp hp)
  | isFalse hnp =>
      constructor
      · intro _
        exact hnp
      · intro _
        rfl

def findFirstViolation {α : Type} (u : α → Nat) : List (Constraint α) → Option (Constraint α)
  | [] => none
  | c :: cs =>
      if decide (SatisfiesConstraint u c) then
        findFirstViolation u cs
      else
        some c

theorem findFirstViolation_sound {α : Type} (u : α → Nat) :
    ∀ (cs : List (Constraint α)) (c : Constraint α),
      findFirstViolation u cs = some c → c ∈ cs ∧ ¬ SatisfiesConstraint u c := by
  intro cs
  induction cs with
  | nil =>
      intro c h
      cases h
  | cons c0 cs ih =>
      intro c h
      dsimp [findFirstViolation] at h
      by_cases hSat : SatisfiesConstraint u c0
      · have hdec : decide (SatisfiesConstraint u c0) = true :=
          (FiniteDemand.decide_eq_true_iff (p := SatisfiesConstraint u c0) (dp := inferInstance)).2 hSat
        rw [hdec] at h
        have h' := ih c h
        exact ⟨List.Mem.tail c0 h'.1, h'.2⟩
      · have hdec : decide (SatisfiesConstraint u c0) = false :=
          (decide_eq_false_iff (p := SatisfiesConstraint u c0) (dp := inferInstance)).2 hSat
        rw [hdec] at h
        cases h
        exact ⟨List.Mem.head cs, hSat⟩

theorem findFirstViolation_none_implies_satisfiesConstraints {α : Type} (u : α → Nat) :
    ∀ (cs : List (Constraint α)),
      findFirstViolation u cs = none → SatisfiesConstraints u cs := by
  intro cs
  induction cs with
  | nil =>
      intro _ c hc
      cases hc
  | cons c0 cs ih =>
      intro hNone c hc
      dsimp [findFirstViolation] at hNone
      by_cases hSat : SatisfiesConstraint u c0
      · have hdec : decide (SatisfiesConstraint u c0) = true :=
          (FiniteDemand.decide_eq_true_iff (p := SatisfiesConstraint u c0) (dp := inferInstance)).2 hSat
        rw [hdec] at hNone
        have hTail : SatisfiesConstraints u cs := ih hNone
        cases hc with
        | head => exact hSat
        | tail _ hcTail => exact hTail c hcTail
      · have hdec : decide (SatisfiesConstraint u c0) = false :=
          (decide_eq_false_iff (p := SatisfiesConstraint u c0) (dp := inferInstance)).2 hSat
        rw [hdec] at hNone
        cases hNone

inductive SolveResult (α : Type) where
  | success : (α → Nat) → SolveResult α
  | fail : (α → Nat) → Constraint α → SolveResult α

def solveUtilityResult (C : FiniteDescriptiveCore) (data : List (Observation C)) : SolveResult C.Obj :=
  let cs := ConstraintsOfDataset C data
  let u0 : C.Obj → Nat := fun _ => 0
  let u := iterate C.allObjs.length (relaxOnce cs) u0
  match findFirstViolation u cs with
  | none => SolveResult.success u
  | some c => SolveResult.fail u c

theorem solveUtilityResult_success_sound (C : FiniteDescriptiveCore) (data : List (Observation C))
    {u : C.Obj → Nat} :
    solveUtilityResult C data = SolveResult.success u → RationalizesDataset C u data := by
  intro h
  dsimp [solveUtilityResult] at h
  -- unfold the match on `findFirstViolation`
  cases hFind :
      findFirstViolation
        (iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0))
        (ConstraintsOfDataset C data) with
  | some c =>
      rw [hFind] at h
      cases h
  | none =>
      rw [hFind] at h
      cases h
      let uCand : C.Obj → Nat :=
        iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0)
      have hSat : SatisfiesConstraints uCand (ConstraintsOfDataset C data) := by
        exact
          findFirstViolation_none_implies_satisfiesConstraints
            (u := uCand) (ConstraintsOfDataset C data) (by
              dsimp [uCand]
              exact hFind
            )
      exact (rationalizesDataset_iff_satisfiesConstraints (C := C) (u := uCand) (data := data)).2 hSat

theorem solveUtilityResult_fail_sound (C : FiniteDescriptiveCore) (data : List (Observation C))
    {u : C.Obj → Nat} {c : Constraint C.Obj} :
    solveUtilityResult C data = SolveResult.fail u c →
      c ∈ ConstraintsOfDataset C data ∧ ¬ SatisfiesConstraint u c := by
  intro h
  dsimp [solveUtilityResult] at h
  let uCand : C.Obj → Nat :=
    iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0)
  cases hFind : findFirstViolation uCand (ConstraintsOfDataset C data) with
  | none =>
      rw [hFind] at h
      cases h
  | some c0 =>
      rw [hFind] at h
      have hSound0 :=
        findFirstViolation_sound (u := uCand) (ConstraintsOfDataset C data) c0 (by
          dsimp [uCand] at hFind
          exact hFind
        )
      cases h
      exact hSound0

/-!
### Economic impossibility certificate: positive cycles (GARP-type)

The constraints `u src + w ≤ u dst` are *revealed-inequality edges* with weight `w`.
Any closed path whose total weight is positive forces `u x < u x`, hence makes the
dataset **not** rationalizable. This is the constructive analogue of a revealed
preference cycle / GARP violation (here with the deterministic tie-break encoded
by `w = 1` edges).
-/

def pathWeight {α : Type} : List (Constraint α) → Nat
  | [] => 0
  | c :: cs => c.w + pathWeight cs

inductive PathIn {α : Type} (cs : List (Constraint α)) : α → α → List (Constraint α) → Prop
  | nil (x : α) : PathIn cs x x []
  | cons {x y : α} {c : Constraint α} {p : List (Constraint α)} :
      c ∈ cs → c.src = x → PathIn cs c.dst y p → PathIn cs x y (c :: p)

def PositiveCycle {α : Type} (cs : List (Constraint α)) : Prop :=
  ∃ x : α, ∃ p : List (Constraint α), PathIn cs x x p ∧ 0 < pathWeight p

/-!
### GARP-style reading (0/1 weights)

In the dataset constraints produced by `constraintsOf`, weights are always `0` (weak) or `1` (strict).
In that situation, a “positive cycle” is exactly a revealed-preference cycle with **at least one**
strict step.
-/

def HasStrictEdge {α : Type} (p : List (Constraint α)) : Prop :=
  ∃ c : Constraint α, c ∈ p ∧ c.w = 1

def AllWeights01 {α : Type} (cs : List (Constraint α)) : Prop :=
  ∀ c : Constraint α, c ∈ cs → c.w = 0 ∨ c.w = 1

theorem constraintsOf_allWeights01 (C : FiniteDescriptiveCore) (t : Term) (y : C.Obj) :
    AllWeights01 (constraintsOf C t y) := by
  intro c hc
  dsimp [constraintsOf] at hc
  have hc' :
      c ∈ (prefixBefore (menuList C t) y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)) ∨
        c ∈ (menuList C t).map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)) :=
    mem_append_elim'
      (a := c)
      (s := (prefixBefore (menuList C t) y).map (fun z => (⟨z, y, 1⟩ : Constraint C.Obj)))
      (t := (menuList C t).map (fun z => (⟨z, y, 0⟩ : Constraint C.Obj)))
      hc
  cases hc' with
  | inl hStrict =>
      rcases mem_map_elim'
          (f := fun z => (⟨z, y, 1⟩ : Constraint C.Obj))
          (xs := prefixBefore (menuList C t) y)
          (b := c) hStrict with ⟨z, hz, rfl⟩
      exact Or.inr rfl
  | inr hWeak =>
      rcases mem_map_elim'
          (f := fun z => (⟨z, y, 0⟩ : Constraint C.Obj))
          (xs := menuList C t)
          (b := c) hWeak with ⟨z, hz, rfl⟩
      exact Or.inl rfl

theorem ConstraintsOfDataset_allWeights01 (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    AllWeights01 (ConstraintsOfDataset C data) := by
  intro c hc
  dsimp [ConstraintsOfDataset] at hc
  rcases (mem_bindList_iff (xs := data) (f := fun obs => constraintsOf C obs.t obs.y) (b := c)).1 hc with
    ⟨obs, hObsMem, hcIn⟩
  exact constraintsOf_allWeights01 (C := C) (t := obs.t) (y := obs.y) c hcIn

theorem PathIn.mem_cs_of_mem_path {α : Type} {cs : List (Constraint α)} :
    ∀ {x y : α} {p : List (Constraint α)},
      PathIn cs x y p → ∀ c : Constraint α, c ∈ p → c ∈ cs := by
  intro x y p hPath
  induction hPath with
  | nil =>
      intro c hc
      cases hc
  | cons hcMem _ hTail ih =>
      intro c hc
      cases hc with
      | head =>
          exact hcMem
      | tail _ hc' =>
          exact ih c hc'

theorem exists_pos_weightEdge_of_pathWeight_pos {α : Type} :
    ∀ {p : List (Constraint α)}, 0 < pathWeight p → ∃ c : Constraint α, c ∈ p ∧ 0 < c.w := by
  intro p hPos
  induction p with
  | nil =>
      dsimp [pathWeight] at hPos
      cases hPos
  | cons c ps ih =>
      cases hw : c.w with
      | zero =>
          have hPos' : 0 < pathWeight ps := by
            -- `0 < 0 + pathWeight ps` reduces to `0 < pathWeight ps`
            dsimp [pathWeight] at hPos
            simpa [hw, Nat.zero_add] using hPos
          rcases ih hPos' with ⟨c', hc'mem, hc'wpos⟩
          exact ⟨c', List.Mem.tail c hc'mem, hc'wpos⟩
      | succ w =>
          have : 0 < c.w := by
            rw [hw]
            exact Nat.succ_pos w
          exact ⟨c, List.Mem.head ps, this⟩

theorem hasStrictEdge_implies_pathWeight_pos {α : Type} :
    ∀ {p : List (Constraint α)}, HasStrictEdge p → 0 < pathWeight p := by
  intro p hStrict
  induction p with
  | nil =>
      rcases hStrict with ⟨c, hc, _⟩
      cases hc
  | cons c0 ps ih =>
      rcases hStrict with ⟨c, hcMem, hw⟩
      cases hcMem with
      | head =>
          -- strict edge is the head
          dsimp [pathWeight]
          rw [hw]
          -- `0 < 1 + pathWeight ps`
          rw [Nat.one_add]
          exact Nat.succ_pos (pathWeight ps)
      | tail _ hcMem' =>
          have hPosTail : 0 < pathWeight ps := ih ⟨c, hcMem', hw⟩
          have hLe : pathWeight ps ≤ c0.w + pathWeight ps := Nat.le_add_left _ _
          exact Nat.lt_of_lt_of_le hPosTail hLe

def GARPViolation {α : Type} (cs : List (Constraint α)) : Prop :=
  ∃ x : α, ∃ p : List (Constraint α), PathIn cs x x p ∧ HasStrictEdge p

theorem positiveCycle_iff_garpViolation_of_allWeights01 {α : Type} {cs : List (Constraint α)} :
    AllWeights01 cs → (PositiveCycle cs ↔ GARPViolation cs) := by
  intro h01
  constructor
  · intro hPos
    rcases hPos with ⟨x, p, hPath, hWeightPos⟩
    rcases exists_pos_weightEdge_of_pathWeight_pos (p := p) hWeightPos with ⟨c, hcMemP, hcWpos⟩
    have hcMemCs : c ∈ cs := PathIn.mem_cs_of_mem_path (cs := cs) (x := x) (y := x) (p := p) hPath c hcMemP
    have hw01 := h01 c hcMemCs
    cases hw01 with
    | inl hw0 =>
        rw [hw0] at hcWpos
        exact False.elim (Nat.not_lt_zero _ hcWpos)
    | inr hw1 =>
        exact ⟨x, p, hPath, ⟨c, hcMemP, hw1⟩⟩
  · intro hG
    rcases hG with ⟨x, p, hPath, hStrict⟩
    exact ⟨x, p, hPath, hasStrictEdge_implies_pathWeight_pos hStrict⟩

theorem pathWeight_append {α : Type} :
    ∀ (p q : List (Constraint α)), pathWeight (p ++ q) = pathWeight p + pathWeight q := by
  intro p q
  induction p with
  | nil =>
      dsimp [pathWeight]
      rw [Nat.zero_add]
  | cons c ps ih =>
      dsimp [pathWeight]
      -- `pathWeight ((c :: ps) ++ q) = c.w + pathWeight (ps ++ q)`
      -- and `pathWeight (c :: ps) + pathWeight q = (c.w + pathWeight ps) + pathWeight q`
      rw [ih]
      exact (Nat.add_assoc _ _ _).symm

theorem pathIn_append {α : Type} {cs : List (Constraint α)} :
    ∀ {x y z : α} {p q : List (Constraint α)},
      PathIn cs x y p → PathIn cs y z q → PathIn cs x z (p ++ q) := by
  intro x y z p q hp hq
  induction hp with
  | nil =>
      -- `[] ++ q = q`
      exact hq
  | cons hcMem hsrc hTail ih =>
      -- `(c :: p) ++ q = c :: (p ++ q)`
      dsimp
      exact PathIn.cons hcMem hsrc (ih hq)

theorem positiveCycle_of_paths {α : Type} {cs : List (Constraint α)}
    {x y : α} {p q : List (Constraint α)} :
    PathIn cs x y p → PathIn cs y x q → 0 < pathWeight p + pathWeight q → PositiveCycle cs := by
  intro hp hq hPos
  refine ⟨x, p ++ q, ?_, ?_⟩
  · exact pathIn_append (cs := cs) (x := x) (y := y) (z := x) (p := p) (q := q) hp hq
  · have hw : pathWeight (p ++ q) = pathWeight p + pathWeight q := pathWeight_append p q
    -- rewrite the goal along `hw`
    rw [hw]
    exact hPos

theorem pathIn_sound {α : Type} (u : α → Nat) {cs : List (Constraint α)} :
    ∀ {x y : α} {p : List (Constraint α)},
      PathIn cs x y p → SatisfiesConstraints u cs → u x + pathWeight p ≤ u y := by
  intro x y p hPath hSat
  induction hPath with
  | nil =>
      rename_i x0
      dsimp [pathWeight]
      exact Nat.le_refl (u x0)
  | cons hcMem hsrc hTail ih =>
      rename_i x0 y0 c0 p0
      -- Unfold the constraint satisfaction and rewrite along `c0.src = x0`.
      have hEdge0 : u c0.src + c0.w ≤ u c0.dst := hSat c0 hcMem
      have hEdge1 : u x0 + c0.w ≤ u c0.dst := by
        have h' := hEdge0
        rw [hsrc] at h'
        exact h'
      have h1 : (u x0 + c0.w) + pathWeight p0 ≤ (u c0.dst) + pathWeight p0 :=
        Nat.add_le_add_right hEdge1 (pathWeight p0)
      have h : (u x0 + c0.w) + pathWeight p0 ≤ u y0 := Nat.le_trans h1 ih
      -- Rewrite the goal into the same normal form.
      dsimp [pathWeight]
      have h2 : u x0 + (c0.w + pathWeight p0) ≤ u y0 := by
        have h' : u x0 + c0.w + pathWeight p0 ≤ u y0 := h
        -- `u x0 + c0.w + pathWeight p0 = u x0 + (c0.w + pathWeight p0)`
        rw [Nat.add_assoc] at h'
        exact h'
      exact h2

theorem pathIn_singleton {α : Type} {cs : List (Constraint α)} (c : Constraint α) :
    c ∈ cs → PathIn cs c.src c.dst [c] := by
  intro hc
  -- `PathIn cs c.src c.dst (c :: [])`
  exact PathIn.cons (x := c.src) (y := c.dst) (c := c) (p := []) hc rfl (PathIn.nil c.dst)

/-!
### Longest-path witnesses (towards completeness)

To prove solver completeness and extract a **positive cycle certificate** on failure,
it is useful to carry *witness paths* alongside the propagated numeric potentials.

The following (purely constructive) machinery maintains the invariant:

`pot.path v` is a concrete `PathIn cs` ending at `v`, and its `pathWeight` equals `pot.val v`.
-/

structure Pot (α : Type) where
  val : α → Nat
  start : α → α
  path : α → List (Constraint α)

def PotInvariant {α : Type} (cs : List (Constraint α)) (pot : Pot α) : Prop :=
  ∀ v : α, PathIn cs (pot.start v) v (pot.path v) ∧ pathWeight (pot.path v) = pot.val v

def basePot {α : Type} : Pot α :=
  { val := fun _ => 0, start := fun v => v, path := fun _ => [] }

theorem basePot_invariant {α : Type} (cs : List (Constraint α)) : PotInvariant cs (basePot (α := α)) := by
  intro v
  refine And.intro ?_ ?_
  · exact PathIn.nil v
  · rfl

structure IncomingChoice (α : Type) where
  val : Nat
  edge : Option (Constraint α)

def incomingChoice {α : Type} [DecidableEq α] (pot : Pot α) (v : α) : List (Constraint α) → IncomingChoice α
  | [] => ⟨0, none⟩
  | c :: cs =>
      let rest := incomingChoice pot v cs
      if c.dst = v then
        let candVal := pot.val c.src + c.w
        if candVal ≥ rest.val then ⟨candVal, some c⟩ else rest
      else
        rest

theorem incomingChoice_edge_spec {α : Type} [DecidableEq α] (pot : Pot α) (v : α) :
    ∀ (cs : List (Constraint α)) (c : Constraint α),
      (incomingChoice pot v cs).edge = some c →
        c ∈ cs ∧ c.dst = v ∧ (incomingChoice pot v cs).val = pot.val c.src + c.w := by
  intro cs
  induction cs with
  | nil =>
      intro c h
      dsimp [incomingChoice] at h
      cases h
  | cons c0 cs ih =>
      intro c h
      dsimp [incomingChoice] at h
      by_cases hdst : c0.dst = v
      · rw [if_pos hdst] at h
        by_cases hge : pot.val c0.src + c0.w ≥ (incomingChoice pot v cs).val
        · rw [if_pos hge] at h
          -- `edge = some c0`
          cases h
          refine And.intro ?_ (And.intro ?_ ?_)
          · exact List.Mem.head cs
          · exact hdst
          · dsimp [incomingChoice]
            rw [if_pos hdst]
            rw [if_pos hge]
            -- goal is now definitional
        · rw [if_neg hge] at h
          have h' := ih c h
          rcases h' with ⟨hmem, hd, hv⟩
          refine And.intro (List.Mem.tail c0 hmem) (And.intro hd ?_)
          dsimp [incomingChoice]
          rw [if_pos hdst]
          rw [if_neg hge]
          exact hv
      · rw [if_neg hdst] at h
        have h' := ih c h
        rcases h' with ⟨hmem, hd, hv⟩
        refine And.intro (List.Mem.tail c0 hmem) (And.intro hd ?_)
        dsimp [incomingChoice]
        rw [if_neg hdst]
        exact hv

theorem incomingChoice_edge_none_implies_val_zero {α : Type} [DecidableEq α]
    (pot : Pot α) (v : α) :
    ∀ (cs : List (Constraint α)),
      (incomingChoice pot v cs).edge = none → (incomingChoice pot v cs).val = 0 := by
  intro cs
  induction cs with
  | nil =>
      intro h
      dsimp [incomingChoice] at h
      cases h
      rfl
  | cons c0 cs ih =>
      intro h
      dsimp [incomingChoice] at h
      by_cases hdst : c0.dst = v
      · rw [if_pos hdst] at h
        by_cases hge : pot.val c0.src + c0.w ≥ (incomingChoice pot v cs).val
        · rw [if_pos hge] at h
          cases h
        · rw [if_neg hge] at h
          have h0 := ih h
          dsimp [incomingChoice]
          rw [if_pos hdst]
          rw [if_neg hge]
          exact h0
      · rw [if_neg hdst] at h
        have h0 := ih h
        dsimp [incomingChoice]
        rw [if_neg hdst]
        exact h0

def relaxOncePot {α : Type} [DecidableEq α] (cs : List (Constraint α)) (pot : Pot α) : Pot α :=
  { val := fun v =>
      let inc := incomingChoice pot v cs
      Nat.max (pot.val v) inc.val
    start := fun v =>
      let inc := incomingChoice pot v cs
      if pot.val v ≥ inc.val then pot.start v
      else
        match inc.edge with
        | none => pot.start v
        | some c => pot.start c.src
    path := fun v =>
      let inc := incomingChoice pot v cs
      if pot.val v ≥ inc.val then pot.path v
      else
        match inc.edge with
        | none => pot.path v
        | some c => pot.path c.src ++ [c] }

theorem relaxOncePot_invariant {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ pot : Pot α, PotInvariant cs pot → PotInvariant cs (relaxOncePot cs pot) := by
  intro pot hInv v
  by_cases hkeep : pot.val v ≥ (incomingChoice pot v cs).val
  · have hv := hInv v
    refine And.intro ?_ ?_
    · simpa [relaxOncePot, hkeep] using hv.1
    · have hmax : Nat.max (pot.val v) (incomingChoice pot v cs).val = pot.val v :=
        Nat.max_eq_left hkeep
      simpa [relaxOncePot, hkeep, hmax] using hv.2
  · have hlt : pot.val v < (incomingChoice pot v cs).val := Nat.lt_of_not_ge hkeep
    cases hEdge : (incomingChoice pot v cs).edge with
    | none =>
        have hval0 : (incomingChoice pot v cs).val = 0 :=
          incomingChoice_edge_none_implies_val_zero (pot := pot) (v := v) (cs := cs) hEdge
        rw [hval0] at hlt
        exact False.elim (Nat.not_lt_zero _ hlt)
    | some c =>
        have hSpec :
            c ∈ cs ∧ c.dst = v ∧ (incomingChoice pot v cs).val = pot.val c.src + c.w :=
          incomingChoice_edge_spec (pot := pot) (v := v) cs c hEdge
        have hMem : c ∈ cs := hSpec.1
        have hDst : c.dst = v := hSpec.2.1
        have hVal : (incomingChoice pot v cs).val = pot.val c.src + c.w := hSpec.2.2
        have hSrcInv := hInv c.src
        have hPathSrc : PathIn cs (pot.start c.src) c.src (pot.path c.src) := hSrcInv.1
        have hPathEdge : PathIn cs c.src c.dst [c] := pathIn_singleton (cs := cs) c hMem
        have hPathNew : PathIn cs (pot.start c.src) v (pot.path c.src ++ [c]) := by
          have h0 : PathIn cs (pot.start c.src) c.dst (pot.path c.src ++ [c]) :=
            pathIn_append (cs := cs) (x := pot.start c.src) (y := c.src) (z := c.dst)
              (p := pot.path c.src) (q := [c]) hPathSrc hPathEdge
          simpa [hDst] using h0
        have hWeightNew : pathWeight (pot.path c.src ++ [c]) = pot.val c.src + c.w := by
          have hWsrc : pathWeight (pot.path c.src) = pot.val c.src := hSrcInv.2
          have hWedge : pathWeight ([c] : List (Constraint α)) = c.w := by rfl
          have hWapp : pathWeight (pot.path c.src ++ [c]) =
              pathWeight (pot.path c.src) + pathWeight ([c] : List (Constraint α)) :=
            pathWeight_append (pot.path c.src) [c]
          rw [hWapp, hWsrc, hWedge]
        refine And.intro ?_ ?_
        · simpa [relaxOncePot, hkeep, hEdge] using hPathNew
        · have hmax :
              Nat.max (pot.val v) (incomingChoice pot v cs).val = (incomingChoice pot v cs).val :=
            Nat.max_eq_right (Nat.le_of_lt hlt)
          -- rewrite the RHS to the improving value and finish by the concrete weight computation
          calc
            pathWeight
                (if pot.val v ≥ (incomingChoice pot v cs).val then pot.path v
                else
                  match (incomingChoice pot v cs).edge with
                  | none => pot.path v
                  | some c => pot.path c.src ++ [c]) =
                pathWeight (pot.path c.src ++ [c]) := by
                  simp [hkeep, hEdge]
            _ = pot.val c.src + c.w := hWeightNew
            _ = (incomingChoice pot v cs).val := hVal.symm
            _ = Nat.max (pot.val v) (incomingChoice pot v cs).val := hmax.symm

theorem positiveCycle_implies_not_satisfiable {α : Type} {cs : List (Constraint α)} :
    PositiveCycle cs → ¬ ∃ u : α → Nat, SatisfiesConstraints u cs := by
  intro hCycle hex
  rcases hCycle with ⟨x, p, hPath, hPos⟩
  rcases hex with ⟨u, hSat⟩
  have hLe : u x + pathWeight p ≤ u x := pathIn_sound (u := u) (cs := cs) (x := x) (y := x) (p := p) hPath hSat
  have hLt : u x < u x + pathWeight p := Nat.lt_add_of_pos_right hPos
  exact (Nat.not_lt_of_ge hLe) hLt

theorem positiveCycle_implies_not_rationalizable (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    PositiveCycle (ConstraintsOfDataset C data) → ¬ ∃ u : C.Obj → Nat, RationalizesDataset C u data := by
  intro hCycle hex
  rcases hex with ⟨u, hR⟩
  have hSat : SatisfiesConstraints u (ConstraintsOfDataset C data) :=
    (rationalizesDataset_iff_satisfiesConstraints (C := C) (u := u) (data := data)).1 hR
  exact positiveCycle_implies_not_satisfiable (cs := ConstraintsOfDataset C data) hCycle ⟨u, hSat⟩

theorem positiveCycle_iff_garpViolation_dataset (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    PositiveCycle (ConstraintsOfDataset C data) ↔ GARPViolation (ConstraintsOfDataset C data) := by
  exact
    positiveCycle_iff_garpViolation_of_allWeights01 (cs := ConstraintsOfDataset C data)
      (ConstraintsOfDataset_allWeights01 (C := C) (data := data))

theorem garpViolation_implies_not_rationalizable (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    GARPViolation (ConstraintsOfDataset C data) → ¬ ∃ u : C.Obj → Nat, RationalizesDataset C u data := by
  intro hG
  have hCycle : PositiveCycle (ConstraintsOfDataset C data) :=
    (positiveCycle_iff_garpViolation_dataset (C := C) (data := data)).2 hG
  exact positiveCycle_implies_not_rationalizable (C := C) (data := data) hCycle

theorem positiveCycle_implies_solveUtility_eq_none (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    PositiveCycle (ConstraintsOfDataset C data) → solveUtility C data = none := by
  intro hCycle
  cases hSol : solveUtility C data with
  | none => rfl
  | some u =>
      have hR : RationalizesDataset C u data := solveUtility_sound (C := C) (data := data) (u := u) (by
        simpa [hSol]
      )
      have : False := (positiveCycle_implies_not_rationalizable (C := C) (data := data) hCycle) ⟨u, hR⟩
      cases this

theorem positiveCycle_implies_solveUtilityResult_is_fail (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    PositiveCycle (ConstraintsOfDataset C data) →
      ∃ u : C.Obj → Nat, ∃ c : Constraint C.Obj, solveUtilityResult C data = SolveResult.fail u c := by
  intro hCycle
  cases hRes : solveUtilityResult C data with
  | success u =>
      have hR : RationalizesDataset C u data :=
        solveUtilityResult_success_sound (C := C) (data := data) (u := u) (by simpa [hRes])
      have : False := (positiveCycle_implies_not_rationalizable (C := C) (data := data) hCycle) ⟨u, hR⟩
      cases this
  | fail u c =>
      -- after `cases`, the goal is definitionally a reflexive equality
      exact ⟨u, c, rfl⟩

/-!
### “Completeness targets” (statements we can now aim for)

At this point we can already prove one direction *without* any extra finiteness:

`SatisfiableConstraints cs → ¬ PositiveCycle cs`.

The remaining “endgame” is the converse direction (under finiteness of the
ambient object type): `¬ PositiveCycle cs → SatisfiableConstraints cs`, yielding
decidability with dual certificates (utility vs. positive cycle).
-/

def SatisfiableConstraints {α : Type} (cs : List (Constraint α)) : Prop :=
  ∃ u : α → Nat, SatisfiesConstraints u cs

theorem satisfiableConstraints_implies_noPositiveCycle {α : Type} {cs : List (Constraint α)} :
    SatisfiableConstraints cs → ¬ PositiveCycle cs := by
  intro hSat hCycle
  exact positiveCycle_implies_not_satisfiable (cs := cs) hCycle hSat

theorem exists_rationalizer_implies_noPositiveCycle (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    (∃ u : C.Obj → Nat, RationalizesDataset C u data) → ¬ PositiveCycle (ConstraintsOfDataset C data) := by
  intro hex hCycle
  have : ¬ ∃ u : C.Obj → Nat, RationalizesDataset C u data :=
    positiveCycle_implies_not_rationalizable (C := C) (data := data) hCycle
  exact this hex

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.rationalizesDataset_iff_satisfiesConstraints
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.satisfiesConstraints_implies_demandChoice_eq_some
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtility_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_success_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_fail_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.positiveCycle_implies_not_rationalizable
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.positiveCycle_iff_garpViolation_dataset
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.garpViolation_implies_not_rationalizable
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.satisfiableConstraints_implies_noPositiveCycle
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
