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

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.rationalizesDataset_iff_satisfiesConstraints
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.satisfiesConstraints_implies_demandChoice_eq_some
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtility_sound
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
