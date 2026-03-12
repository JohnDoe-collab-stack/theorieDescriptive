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

def decidableMem {α : Type} [DecidableEq α] (a : α) :
    ∀ xs : List α, Decidable (a ∈ xs)
  | [] =>
      isFalse (by
        intro ha
        cases ha
      )
  | x :: xs =>
      if hax : a = x then
        isTrue (by
          cases hax
          exact List.Mem.head xs
        )
      else
        match decidableMem a xs with
        | isTrue hmem =>
            isTrue (List.Mem.tail x hmem)
        | isFalse hnot =>
            isFalse (by
              intro hmem
              cases hmem with
              | head =>
                  exact hax rfl
              | tail _ hmem' =>
                  exact hnot hmem'
            )

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
        max (u c.src + c.w) (incomingMax u v cs)
      else
        incomingMax u v cs

theorem incomingMax_congr {α : Type} [DecidableEq α] {u u' : α → Nat} (v : α) :
    ∀ cs : List (Constraint α),
      (∀ x : α, u x = u' x) →
        incomingMax u v cs = incomingMax u' v cs := by
  intro cs hEq
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      dsimp [incomingMax]
      by_cases hdst : c.dst = v
      · rw [if_pos hdst]
        rw [if_pos hdst]
        have hSrc : u c.src = u' c.src := hEq c.src
        have hTail : incomingMax u v cs = incomingMax u' v cs := ih
        rw [hSrc, hTail]
      · rw [if_neg hdst]
        rw [if_neg hdst]
        exact ih

def relaxOnce {α : Type} [DecidableEq α] (cs : List (Constraint α)) (u : α → Nat) : α → Nat :=
  fun v => max (u v) (incomingMax u v cs)

/-!
### Canonical minimal rationalizer (pointwise)

The operator `relaxOnce cs` propagates revealed-inequality lower bounds.
If a function `u` already satisfies all constraints, then `relaxOnce cs u = u`.
Moreover, iterating from the bottom function `0` yields a **pointwise minimal**
candidate among all satisfying utilities.
-/

def FunLe {α : Type} (u v : α → Nat) : Prop :=
  ∀ x : α, u x ≤ v x

theorem nat_le_max_left (a b : Nat) : a ≤ max a b := by
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    exact Nat.le_refl a

theorem nat_le_max_right (a b : Nat) : b ≤ max a b := by
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact Nat.le_refl b
  · rw [if_neg h]
    have hlt : b < a := Nat.lt_of_not_ge h
    exact Nat.le_of_lt hlt

theorem nat_max_le_of_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact hb
  · rw [if_neg h]
    exact ha

theorem nat_max_eq_left_of_le {a b : Nat} (h : b ≤ a) : max a b = a := by
  rw [Nat.max_def]
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    have habEq : a = b := Nat.le_antisymm hab h
    exact habEq.symm
  · rw [if_neg hab]

theorem nat_max_le_max {a b c d : Nat} (hac : a ≤ c) (hbd : b ≤ d) : max a b ≤ max c d := by
  have ha' : a ≤ max c d := Nat.le_trans hac (nat_le_max_left c d)
  have hb' : b ≤ max c d := Nat.le_trans hbd (nat_le_max_right c d)
  exact nat_max_le_of_le ha' hb'

theorem incomingMax_mono {α : Type} [DecidableEq α] {u u' : α → Nat} (h : FunLe u u') (v : α) :
    ∀ cs : List (Constraint α), incomingMax u v cs ≤ incomingMax u' v cs := by
  intro cs
  induction cs with
  | nil =>
      dsimp [incomingMax]
      exact Nat.le_refl 0
  | cons c cs ih =>
      dsimp [incomingMax]
      by_cases hdst : c.dst = v
      · rw [if_pos hdst]
        rw [if_pos hdst]
        have hsrc : u c.src + c.w ≤ u' c.src + c.w :=
          Nat.add_le_add_right (h c.src) c.w
        exact nat_max_le_max hsrc ih
      · rw [if_neg hdst]
        rw [if_neg hdst]
        exact ih

theorem relaxOnce_mono {α : Type} [DecidableEq α] (cs : List (Constraint α)) {u u' : α → Nat}
    (h : FunLe u u') : FunLe (relaxOnce cs u) (relaxOnce cs u') := by
  intro v
  dsimp [relaxOnce]
  exact nat_max_le_max (h v) (incomingMax_mono (v := v) h cs)

theorem incomingMax_le_of_satisfiesConstraints {α : Type} [DecidableEq α] (u : α → Nat) :
    ∀ (cs : List (Constraint α)), SatisfiesConstraints u cs → ∀ v : α, incomingMax u v cs ≤ u v := by
  intro cs hSat
  induction cs with
  | nil =>
      intro v
      dsimp [incomingMax]
      exact Nat.zero_le (u v)
  | cons c cs ih =>
      intro v
      dsimp [incomingMax]
      by_cases hdst : c.dst = v
      · rw [if_pos hdst]
        have hEdge0 : u c.src + c.w ≤ u c.dst :=
          hSat c (List.Mem.head cs)
        have hEdge : u c.src + c.w ≤ u v := by
          cases hdst
          exact hEdge0
        have hSatTail : SatisfiesConstraints u cs := by
          intro c' hc'
          exact hSat c' (List.Mem.tail c hc')
        have hTail : incomingMax u v cs ≤ u v := ih hSatTail v
        exact nat_max_le_of_le hEdge hTail
      · rw [if_neg hdst]
        have hSatTail : SatisfiesConstraints u cs := by
          intro c' hc'
          exact hSat c' (List.Mem.tail c hc')
        exact ih hSatTail v

theorem relaxOnce_eq_of_satisfiesConstraints {α : Type} [DecidableEq α] (cs : List (Constraint α)) (u : α → Nat)
    (hSat : SatisfiesConstraints u cs) : ∀ v : α, relaxOnce cs u v = u v := by
  intro v
  dsimp [relaxOnce]
  have hInc : incomingMax u v cs ≤ u v := incomingMax_le_of_satisfiesConstraints (u := u) cs hSat v
  exact nat_max_eq_left_of_le hInc

theorem relaxOnce_le_of_satisfiesConstraints {α : Type} [DecidableEq α] (cs : List (Constraint α)) (u u' : α → Nat)
    (hSat : SatisfiesConstraints u' cs) (h : FunLe u u') : FunLe (relaxOnce cs u) u' := by
  have hMono : FunLe (relaxOnce cs u) (relaxOnce cs u') := relaxOnce_mono (cs := cs) h
  intro v
  have hEq : relaxOnce cs u' v = u' v := relaxOnce_eq_of_satisfiesConstraints (cs := cs) (u := u') hSat v
  have hLe : relaxOnce cs u' v ≤ u' v := by
    rw [hEq]
    exact Nat.le_refl (u' v)
  exact Nat.le_trans (hMono v) hLe

def iterate {α : Type} (n : Nat) (f : α → α) (x : α) : α :=
  Nat.rec x (fun _ acc => f acc) n

theorem iterate_relaxOnce_le_of_satisfiesConstraints {α : Type} [DecidableEq α] (cs : List (Constraint α)) (u : α → Nat)
    (hSat : SatisfiesConstraints u cs) :
    ∀ n : Nat, FunLe (iterate n (relaxOnce cs) (fun _ => 0)) u := by
  intro n
  induction n with
  | zero =>
      intro v
      dsimp [iterate]
      exact Nat.zero_le (u v)
  | succ n ih =>
      dsimp [iterate]
      exact relaxOnce_le_of_satisfiesConstraints (cs := cs) (u := iterate n (relaxOnce cs) (fun _ => 0)) (u' := u) hSat ih

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

abbrev canonicalUtility (C : FiniteDescriptiveCore) (data : List (Observation C)) : C.Obj → Nat :=
  iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0)

theorem canonicalUtility_le_of_rationalizesDataset (C : FiniteDescriptiveCore) (data : List (Observation C))
    {u : C.Obj → Nat} :
    RationalizesDataset C u data → FunLe (canonicalUtility C data) u := by
  intro hR
  have hSat : SatisfiesConstraints u (ConstraintsOfDataset C data) :=
    (rationalizesDataset_iff_satisfiesConstraints (C := C) (u := u) (data := data)).1 hR
  dsimp [canonicalUtility]
  exact
    iterate_relaxOnce_le_of_satisfiesConstraints
      (cs := ConstraintsOfDataset C data) (u := u) hSat C.allObjs.length

theorem solveUtilityResult_success_minimal (C : FiniteDescriptiveCore) (data : List (Observation C))
    {u : C.Obj → Nat} :
    solveUtilityResult C data = SolveResult.success u →
      ∀ u' : C.Obj → Nat, RationalizesDataset C u' data → FunLe u u' := by
  intro hRes u' hR'
  dsimp [solveUtilityResult] at hRes
  cases hFind :
      findFirstViolation
        (iterate C.allObjs.length (relaxOnce (ConstraintsOfDataset C data)) (fun _ => 0))
        (ConstraintsOfDataset C data) with
  | some c =>
      rw [hFind] at hRes
      cases hRes
  | none =>
      rw [hFind] at hRes
      cases hRes
      exact canonicalUtility_le_of_rationalizesDataset (C := C) (data := data) hR'

structure MinimalRationalizerCert (C : FiniteDescriptiveCore) (data : List (Observation C)) : Type where
  u : C.Obj → Nat
  rationalizes : RationalizesDataset C u data
  minimal : ∀ u' : C.Obj → Nat, RationalizesDataset C u' data → FunLe u u'

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
`PositiveCycle` is a *proposition* (good for theorems), but for an executable
“rationality test” we also want a *certificate object* carrying the explicit
cycle path.
-/

structure PositiveCycleCert {α : Type} (cs : List (Constraint α)) : Type where
  x : α
  p : List (Constraint α)
  path : PathIn cs x x p
  pos : 0 < pathWeight p

def PositiveCycleCert.toPositiveCycle {α : Type} {cs : List (Constraint α)} (cert : PositiveCycleCert cs) :
    PositiveCycle cs :=
  ⟨cert.x, cert.p, cert.path, cert.pos⟩

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

def PotLenInvariant {α : Type} (k : Nat) (pot : Pot α) : Prop :=
  ∀ v : α, (pot.path v).length ≤ k

theorem length_append' {α : Type} :
    ∀ (as bs : List α), (as ++ bs).length = as.length + bs.length := by
  intro as bs
  induction as with
  | nil =>
      dsimp
      rw [Nat.zero_add]
  | cons a as ih =>
      dsimp
      rw [ih]
      -- `Nat.succ (as.length + bs.length) = Nat.succ as.length + bs.length`
      exact (Nat.succ_add _ _).symm

theorem append_assoc' {α : Type} :
    ∀ (as bs cs : List α), as ++ bs ++ cs = as ++ (bs ++ cs) := by
  intro as bs cs
  induction as with
  | nil =>
      rfl
  | cons a as ih =>
      dsimp
      exact congrArg (fun t => a :: t) ih

def basePot {α : Type} : Pot α :=
  { val := fun _ => 0, start := fun v => v, path := fun _ => [] }

theorem basePot_invariant {α : Type} (cs : List (Constraint α)) : PotInvariant cs (basePot (α := α)) := by
  intro v
  refine And.intro ?_ ?_
  · exact PathIn.nil v
  · rfl

theorem basePot_lenInvariant {α : Type} : PotLenInvariant 0 (basePot (α := α)) := by
  intro v
  dsimp [PotLenInvariant, basePot]
  exact Nat.le_refl 0

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
      Nat.max (pot.val v) (incomingChoice pot v cs).val
    start := fun v =>
      if pot.val v ≥ (incomingChoice pot v cs).val then pot.start v
      else
        match (incomingChoice pot v cs).edge with
        | none => pot.start v
        | some c => pot.start c.src
    path := fun v =>
      if pot.val v ≥ (incomingChoice pot v cs).val then pot.path v
      else
        match (incomingChoice pot v cs).edge with
        | none => pot.path v
        | some c => pot.path c.src ++ [c] }

theorem relaxOncePot_invariant {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ pot : Pot α, PotInvariant cs pot → PotInvariant cs (relaxOncePot cs pot) := by
  intro pot hInv v
  by_cases hkeep : pot.val v ≥ (incomingChoice pot v cs).val
  · have hv := hInv v
    refine And.intro ?_ ?_
    · dsimp [relaxOncePot]
      rw [if_pos hkeep]
      rw [if_pos hkeep]
      exact hv.1
    · dsimp [relaxOncePot]
      rw [if_pos hkeep]
      -- rewrite the produced value by unfolding `max`
      change pathWeight (pot.path v) = max (pot.val v) (incomingChoice pot v cs).val
      rw [Nat.max_def]
      by_cases hle : pot.val v ≤ (incomingChoice pot v cs).val
      · rw [if_pos hle]
        have hEq : pot.val v = (incomingChoice pot v cs).val :=
          Nat.le_antisymm hle hkeep
        -- reduce to the original invariant
        rw [hEq] at hv
        exact hv.2
      · rw [if_neg hle]
        exact hv.2
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
          cases hDst
          exact h0
        have hWeightNew : pathWeight (pot.path c.src ++ [c]) = pot.val c.src + c.w := by
          have hWsrc : pathWeight (pot.path c.src) = pot.val c.src := hSrcInv.2
          have hWedge : pathWeight ([c] : List (Constraint α)) = c.w := by rfl
          have hWapp : pathWeight (pot.path c.src ++ [c]) =
              pathWeight (pot.path c.src) + pathWeight ([c] : List (Constraint α)) :=
            pathWeight_append (pot.path c.src) [c]
          rw [hWapp, hWsrc, hWedge]
        refine And.intro ?_ ?_
        · dsimp [relaxOncePot]
          rw [if_neg hkeep]
          rw [if_neg hkeep]
          rw [hEdge]
          dsimp
          exact hPathNew
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
                  -- the `else` + `some c` branch is definitional here
                  rw [if_neg hkeep]
                  rw [hEdge]
            _ = pot.val c.src + c.w := hWeightNew
            _ = (incomingChoice pot v cs).val := hVal.symm
            _ = Nat.max (pot.val v) (incomingChoice pot v cs).val := hmax.symm

theorem relaxOncePot_lenInvariant {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ {k : Nat} {pot : Pot α}, PotLenInvariant k pot → PotLenInvariant (k + 1) (relaxOncePot cs pot) := by
  intro k pot hLen v
  dsimp [PotLenInvariant] at hLen ⊢
  by_cases hkeep : pot.val v ≥ (incomingChoice pot v cs).val
  · have h0 : (pot.path v).length ≤ k := hLen v
    have h0' : (pot.path v).length ≤ k + 1 := Nat.le_trans h0 (Nat.le_succ k)
    dsimp [relaxOncePot]
    rw [if_pos hkeep]
    exact h0'
  · cases hEdge : (incomingChoice pot v cs).edge with
    | none =>
        have h0 : (pot.path v).length ≤ k := hLen v
        have h0' : (pot.path v).length ≤ k + 1 := Nat.le_trans h0 (Nat.le_succ k)
        dsimp [relaxOncePot]
        rw [if_neg hkeep]
        -- match on `edge = none`
        rw [hEdge]
        exact h0'
    | some c =>
        have hSrc : (pot.path c.src).length ≤ k := hLen c.src
        have hApp : (pot.path c.src ++ [c]).length = (pot.path c.src).length + 1 := by
          have h := length_append' (pot.path c.src) ([c] : List (Constraint α))
          have h1 : ([c] : List (Constraint α)).length = 1 := rfl
          rw [h1] at h
          exact h
        have hBound : (pot.path c.src ++ [c]).length ≤ k + 1 := by
          rw [hApp]
          exact Nat.add_le_add_right hSrc 1
        dsimp [relaxOncePot]
        rw [if_neg hkeep]
        rw [hEdge]
        exact hBound

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
      have hR : RationalizesDataset C u data :=
        solveUtility_sound (C := C) (data := data) (u := u) hSol
      have : False := (positiveCycle_implies_not_rationalizable (C := C) (data := data) hCycle) ⟨u, hR⟩
      cases this

theorem positiveCycle_implies_solveUtilityResult_is_fail (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    PositiveCycle (ConstraintsOfDataset C data) →
      ∃ u : C.Obj → Nat, ∃ c : Constraint C.Obj, solveUtilityResult C data = SolveResult.fail u c := by
  intro hCycle
  cases hRes : solveUtilityResult C data with
  | success u =>
      have hR : RationalizesDataset C u data :=
        solveUtilityResult_success_sound (C := C) (data := data) (u := u) hRes
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

/-!
### Completeness (finite): failure ⇒ positive cycle ⇒ (¬cycle ⇒ rationalizer)

The solver `solveUtilityResult` computes the `n`-step relaxation (with
`n = C.allObjs.length`). If the resulting candidate violates a revealed
inequality, then there must exist a **positive cycle** among the constraints.

This is a constructive Bellman–Ford-style certificate: *strict improvement
after `n` rounds implies a cycle, and the cycle cannot have weight 0 because
it would yield an equally good shorter path*, contradicting maximality at step
`n`.
-/

theorem le_max_left' (a b : Nat) : a ≤ Nat.max a b := by
  change a ≤ max a b
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    exact Nat.le_refl a

theorem le_max_right' (a b : Nat) : b ≤ Nat.max a b := by
  change b ≤ max a b
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact Nat.le_refl b
  · rw [if_neg h]
    have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge h)
    exact hba

def takeN {α : Type} : Nat → List α → List α
  | 0, _ => []
  | Nat.succ _, [] => []
  | Nat.succ n, x :: xs => x :: takeN n xs

def dropN {α : Type} : Nat → List α → List α
  | 0, xs => xs
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: xs => dropN n xs

theorem takeN_dropN_eq {α : Type} :
    ∀ (n : Nat) (xs : List α), takeN n xs ++ dropN n xs = xs := by
  intro n xs
  induction n generalizing xs with
  | zero =>
      rfl
  | succ n ih =>
      cases xs with
      | nil =>
          rfl
      | cons x xs =>
          dsimp [takeN, dropN]
          -- `(x :: a) ++ b = x :: (a ++ b)` by definition
          change x :: (takeN n xs ++ dropN n xs) = x :: xs
          exact congrArg (fun t => x :: t) (ih xs)

def verticesOfPath {α : Type} (s : α) : List (Constraint α) → List α
  | [] => [s]
  | c :: cs => s :: verticesOfPath c.dst cs

theorem verticesOfPath_length {α : Type} (s : α) :
    ∀ (p : List (Constraint α)), (verticesOfPath s p).length = p.length + 1 := by
  intro p
  induction p generalizing s with
  | nil =>
      rfl
  | cons c ps ih =>
      dsimp [verticesOfPath]
      -- `length (s :: verticesOfPath c.dst ps) = succ (ps.length + 1)`
      rw [ih (s := c.dst)]

def nthOr {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, Nat.succ n => nthOr d xs n

theorem nthOr_append_length {α : Type} (d : α) :
    ∀ (pre : List α) (x : α) (rest : List α),
      nthOr d (pre ++ x :: rest) pre.length = x := by
  intro pre x rest
  induction pre with
  | nil =>
      rfl
  | cons a as ih =>
      dsimp [List.length]
      dsimp [nthOr]
      exact ih

def vertexAt {α : Type} (s : α) : List (Constraint α) → Nat → α
  | [], _ => s
  | _ :: _, 0 => s
  | c :: cs, Nat.succ n => vertexAt c.dst cs n

theorem nthOr_eq_of_lt {α : Type} :
    ∀ (xs : List α) (n : Nat) (d1 d2 : α),
      n < xs.length → nthOr d1 xs n = nthOr d2 xs n := by
  intro xs n d1 d2 hlt
  induction xs generalizing n with
  | nil =>
      dsimp [List.length] at hlt
      cases hlt
  | cons x xs ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          dsimp [List.length] at hlt
          have hlt' : n < xs.length := Nat.lt_of_succ_lt_succ hlt
          dsimp [nthOr]
          exact ih (n := n) hlt'

theorem vertexAt_eq_nthOr_verticesOfPath_of_le {α : Type} (s : α) :
    ∀ (p : List (Constraint α)) (n : Nat),
      n ≤ p.length → vertexAt s p n = nthOr s (verticesOfPath s p) n := by
  intro p n hn
  induction p generalizing s n with
  | nil =>
      dsimp [List.length] at hn
      cases n with
      | zero => rfl
      | succ n =>
          cases (Nat.not_succ_le_zero n hn)
  | cons c ps ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          -- reduce the bound
          have hn' : n ≤ ps.length := Nat.le_of_succ_le_succ hn
          -- unfold both sides
          dsimp [vertexAt, verticesOfPath, nthOr]
          have h0 : vertexAt c.dst ps n = nthOr c.dst (verticesOfPath c.dst ps) n :=
            ih (s := c.dst) (n := n) hn'
          -- defaults don't matter in-bounds
          have hlt : n < (verticesOfPath c.dst ps).length := by
            have : (verticesOfPath c.dst ps).length = ps.length + 1 := verticesOfPath_length (s := c.dst) ps
            rw [this]
            exact Nat.lt_succ_of_le hn'
          have h1 : nthOr c.dst (verticesOfPath c.dst ps) n = nthOr s (verticesOfPath c.dst ps) n :=
            (nthOr_eq_of_lt (xs := verticesOfPath c.dst ps) (n := n) (d1 := c.dst) (d2 := s) hlt)
          exact Eq.trans h0 h1

theorem incomingChoice_val_eq_incomingMax {α : Type} [DecidableEq α] (pot : Pot α) (v : α) :
    ∀ (cs : List (Constraint α)), (incomingChoice pot v cs).val = incomingMax pot.val v cs := by
  intro cs
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      by_cases hdst : c.dst = v
      · -- unfold without triggering simp-lemmas for `Nat.max` (some rely on `propext`)
        dsimp [incomingChoice]
        rw [if_pos hdst]
        dsimp [incomingMax]
        rw [if_pos hdst]
        -- rewrite the tail choice-value using IH
        rw [ih]
        -- compare `if` with `Nat.max`
        by_cases hge : pot.val c.src + c.w ≥ incomingMax pot.val v cs
        · rw [if_pos hge]
          dsimp
          -- `max cand rest = cand` by unfolding `Nat.max`
          change pot.val c.src + c.w = max (pot.val c.src + c.w) (incomingMax pot.val v cs)
          rw [Nat.max_def]
          -- compare `cand ≤ rest`
          by_cases hle : (pot.val c.src + c.w) ≤ incomingMax pot.val v cs
          · rw [if_pos hle]
            -- `cand = rest` by antisymmetry
            have hEq : pot.val c.src + c.w = incomingMax pot.val v cs :=
              Nat.le_antisymm hle hge
            rw [hEq]
          · rw [if_neg hle]
            -- goal is definitional after unfolding the `if`
        · rw [if_neg hge]
          -- in this branch, `cand ≤ rest`
          have hle : pot.val c.src + c.w ≤ incomingMax pot.val v cs :=
            Nat.le_of_lt (Nat.lt_of_not_ge hge)
          change (incomingChoice pot v cs).val = max (pot.val c.src + c.w) (incomingMax pot.val v cs)
          rw [Nat.max_def]
          rw [if_pos hle]
          exact ih
      · dsimp [incomingChoice]
        rw [if_neg hdst]
        dsimp [incomingMax]
        rw [if_neg hdst]
        exact ih

theorem relaxOncePot_val_eq_relaxOnce {α : Type} [DecidableEq α] (cs : List (Constraint α)) (pot : Pot α) :
    ∀ v : α, (relaxOncePot cs pot).val v = relaxOnce cs pot.val v := by
  intro v
  dsimp [relaxOncePot, relaxOnce]
  have hinc : (incomingChoice pot v cs).val = incomingMax pot.val v cs :=
    incomingChoice_val_eq_incomingMax (pot := pot) (v := v) cs
  rw [hinc]

theorem iterate_relaxOncePot_val_eq_iterate_relaxOnce {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ n : Nat,
      ∀ v : α,
        (iterate n (relaxOncePot cs) (basePot (α := α))).val v =
          iterate n (relaxOnce cs) (fun _ : α => 0) v := by
  intro n
  induction n with
  | zero =>
      intro v
      rfl
  | succ n ih =>
      intro v
      -- unfold one step of `iterate` on both sides (definitionally)
      dsimp [iterate]
      -- rewrite the Pot-valued relaxation to the numeric relaxation
      rw [relaxOncePot_val_eq_relaxOnce (cs := cs)
            (pot := Nat.rec (basePot (α := α)) (fun _ acc => relaxOncePot cs acc) n) v]
      -- use the pointwise IH to compare the two `relaxOnce` inputs
      let potN : Pot α :=
        Nat.rec (basePot (α := α)) (fun _ acc => relaxOncePot cs acc) n
      let uN : α → Nat :=
        Nat.rec (motive := fun _ => α → Nat) (fun _ => 0) (fun _ acc => relaxOnce cs acc) n
      have hPoint : ∀ x : α, potN.val x = uN x := by
        intro x
        have hx := ih x
        dsimp [iterate] at hx
        dsimp [potN, uN]
        exact hx
      dsimp [relaxOnce]
      have hUv : potN.val v = uN v := hPoint v
      have hInc : incomingMax potN.val v cs = incomingMax uN v cs :=
        incomingMax_congr (v := v) (cs := cs) (u := potN.val) (u' := uN) hPoint
      rw [hUv, hInc]

theorem incomingChoice_ge_of_edge {α : Type} [DecidableEq α] (pot : Pot α) (v : α) :
    ∀ (cs : List (Constraint α)) (c : Constraint α),
      c ∈ cs → c.dst = v → pot.val c.src + c.w ≤ (incomingChoice pot v cs).val := by
  intro cs
  induction cs with
  | nil =>
      intro c hc
      cases hc
  | cons c0 cs ih =>
      intro c hcMem hdst
      dsimp [incomingChoice]
      -- `rest := incomingChoice pot v cs`
      by_cases hdst0 : c0.dst = v
      · rw [if_pos hdst0]
        -- consider which edge we are bounding
        cases hcMem with
        | head =>
            -- `c = c0`
            by_cases hge : pot.val c0.src + c0.w ≥ (incomingChoice pot v cs).val
            · rw [if_pos hge]
              exact Nat.le_refl (pot.val c0.src + c0.w)
            · rw [if_neg hge]
              -- if we didn't pick it, then it is ≤ rest
              exact Nat.le_of_lt (Nat.lt_of_not_ge hge)
        | tail _ hcTail =>
            -- bound comes from the tail, so use IH and compare with the chosen max
            have hTail : pot.val c.src + c.w ≤ (incomingChoice pot v cs).val :=
              ih c hcTail hdst
            by_cases hge : pot.val c0.src + c0.w ≥ (incomingChoice pot v cs).val
            · rw [if_pos hge]
              -- rest ≤ cand, so tail bound ≤ cand
              have hrestLe : (incomingChoice pot v cs).val ≤ pot.val c0.src + c0.w := hge
              exact Nat.le_trans hTail hrestLe
            · rw [if_neg hge]
              -- chosen value is the rest
              exact hTail
      · rw [if_neg hdst0]
        -- no change; reduce to tail
        have hcMem' : c ∈ cs := by
          cases hcMem with
          | head =>
              cases hdst0 (by simpa using hdst)
          | tail _ hcTail =>
              exact hcTail
        exact ih c hcMem' hdst

theorem pathIn_decompose_last {α : Type} {cs : List (Constraint α)} :
    ∀ {x y : α} {p : List (Constraint α)},
      PathIn cs x y p →
        p = [] ∨ ∃ (c : Constraint α) (q : List (Constraint α)),
          p = q ++ [c] ∧ PathIn cs x c.src q ∧ c ∈ cs ∧ c.dst = y := by
  intro x y p hPath
  induction hPath with
  | nil x =>
      exact Or.inl rfl
  | cons hcMem hsrc hTail ih =>
      rename_i x0 y0 c0 p0
      cases ih with
      | inl hp0 =>
          -- tail is empty, so we have a singleton edge
          have hTail0 : PathIn cs c0.dst y0 ([] : List (Constraint α)) := by
            simpa [hp0] using hTail
          -- `hTail0` forces `y0 = c0.dst`
          cases hTail0 with
          | nil _ =>
              refine Or.inr ?_
              refine ⟨c0, [], ?_, ?_, ?_, ?_⟩
              · rw [hp0]
                rfl
              · -- `PathIn cs x0 c0.src []`
                have : c0.src = x0 := hsrc
                simpa [this] using (PathIn.nil x0)
              · exact hcMem
              · rfl
      | inr hex =>
          rcases hex with ⟨cLast, q, hpq, hq, hMemLast, hDstLast⟩
          refine Or.inr ?_
          refine ⟨cLast, (c0 :: q), ?_, ?_, ?_, ?_⟩
          · rw [hpq]
            rfl
          · exact PathIn.cons hcMem hsrc hq
          · exact hMemLast
          · exact hDstLast

def iteratePot {α : Type} [DecidableEq α] (n : Nat) (cs : List (Constraint α)) : Pot α :=
  iterate n (relaxOncePot cs) (basePot (α := α))

theorem iteratePot_invariant {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ n : Nat, PotInvariant cs (iteratePot (α := α) n cs) := by
  intro n
  induction n with
  | zero =>
      dsimp [iteratePot]
      exact basePot_invariant (α := α) cs
  | succ n ih =>
      dsimp [iteratePot, iterate]
      -- `relaxOncePot` preserves the invariant
      exact relaxOncePot_invariant (cs := cs) _ ih

theorem iteratePot_lenInvariant {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ n : Nat, PotLenInvariant n (iteratePot (α := α) n cs) := by
  intro n
  induction n with
  | zero =>
      dsimp [iteratePot]
      exact basePot_lenInvariant (α := α)
  | succ n ih =>
      dsimp [iteratePot, iterate]
      -- length invariant steps by `+1`
      exact relaxOncePot_lenInvariant (cs := cs) (k := n) (pot := iteratePot (α := α) n cs) ih

theorem length_le_zero_iff_nil' {α : Type} :
    ∀ (xs : List α), xs.length ≤ 0 → xs = [] := by
  intro xs h
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases (Nat.not_succ_le_zero xs.length h)

theorem iteratePot_upperBound {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ (n : Nat) (v x : α) (p : List (Constraint α)),
      PathIn cs x v p → p.length ≤ n → pathWeight p ≤ (iteratePot (α := α) n cs).val v := by
  intro n
  induction n with
  | zero =>
      intro v x p hPath hlen
      have hp : p = [] := length_le_zero_iff_nil' (xs := p) hlen
      rw [hp]
      dsimp [pathWeight, iteratePot]
      exact Nat.le_refl 0
  | succ n ih =>
      intro v x p hPath hlen
      -- unfold `iteratePot (n+1)`
      dsimp [iteratePot, iterate]
      -- let `potN` be the `n`-step potential
      let potN : Pot α := iteratePot (α := α) n cs
      have hInvN : PotInvariant cs potN := iteratePot_invariant (α := α) (cs := cs) n
      have hLenN : PotLenInvariant n potN := iteratePot_lenInvariant (α := α) (cs := cs) n
      -- work by cases on whether the path is empty
      cases p with
      | nil =>
          dsimp [pathWeight]
          -- `0 ≤ _`
          exact Nat.zero_le _
      | cons c0 ps =>
          -- decompose the path at the last edge
          have hDec := pathIn_decompose_last (cs := cs) (x := x) (y := v) (p := c0 :: ps) hPath
          cases hDec with
          | inl hnil =>
              cases hnil
          | inr hex =>
              rcases hex with ⟨cLast, q, hpq, hq, hMemLast, hDstLast⟩
              -- the prefix `q` has length ≤ n
              have hlenq : q.length ≤ n := by
                -- `length (q ++ [cLast]) = q.length + 1`
                have hqLen :
                    (q ++ [cLast]).length = q.length + 1 := by
                  have h := length_append' q ([cLast] : List (Constraint α))
                  -- `[cLast].length = 1`
                  rw [show ([cLast] : List (Constraint α)).length = 1 from rfl] at h
                  exact h
                -- rewrite the bound along `hpq`
                have hlen' : (q ++ [cLast]).length ≤ n + 1 := by
                  have hlen0 := hlen
                  have hEqLen : (c0 :: ps).length = (q ++ [cLast]).length := congrArg List.length hpq
                  rw [hEqLen] at hlen0
                  exact hlen0
                -- now `q.length + 1 ≤ n + 1` implies `q.length ≤ n`
                have : q.length + 1 ≤ n + 1 := by
                  rw [hqLen] at hlen'
                  exact hlen'
                exact Nat.le_of_succ_le_succ this
              -- apply IH to the prefix path `q` ending at `cLast.src`
              have hWq : pathWeight q ≤ potN.val cLast.src := by
                -- IH expects the `n`-step potential
                exact ih (v := cLast.src) (x := x) (p := q) hq hlenq
              -- extend by the last edge weight
              have hWq' : pathWeight q + cLast.w ≤ potN.val cLast.src + cLast.w :=
                Nat.add_le_add_right hWq cLast.w
              -- and bound by the incoming max at `v`
              have hInc :
                  potN.val cLast.src + cLast.w ≤ (incomingChoice potN v cs).val := by
                exact incomingChoice_ge_of_edge (pot := potN) (v := v) cs cLast hMemLast (by
                  -- `cLast.dst = v`
                  exact hDstLast
                )
              have hWcand : pathWeight q + cLast.w ≤ (incomingChoice potN v cs).val :=
                Nat.le_trans hWq' hInc
              -- the relaxed value is a max with the incoming choice
              have hLeMax : (incomingChoice potN v cs).val ≤ Nat.max (potN.val v) (incomingChoice potN v cs).val :=
                le_max_right' _ _
              -- compute the path weight and finish
              have hWeight : pathWeight (q ++ [cLast]) = pathWeight q + cLast.w := by
                have hApp := pathWeight_append (α := α) q ([cLast] : List (Constraint α))
                -- `pathWeight [cLast] = cLast.w`
                have h1 : pathWeight ([cLast] : List (Constraint α)) = cLast.w := by rfl
                rw [h1] at hApp
                exact hApp
              -- rewrite along `hpq` and `hWeight`
              have hMain : pathWeight (c0 :: ps) ≤ Nat.max (potN.val v) (incomingChoice potN v cs).val := by
                rw [hpq]
                rw [hWeight]
                exact Nat.le_trans hWcand hLeMax
              -- finally, `relaxOncePot` uses this max as its value
              dsimp [relaxOncePot]
              exact hMain

/-!
### Longest-path characterization (identification)

For fixed `n`, the value `(iteratePot n cs).val v` is exactly the **maximum**
total weight among all paths ending at `v` with length ≤ `n`, and this maximum
is *attained* by the witness path carried inside the `Pot` invariant.

This makes the canonical utility values fully combinatorial: they are longest
path values in the revealed-inequality graph (finite, bounded-length).
-/

def IsLongestPathValue {α : Type} (cs : List (Constraint α)) (n : Nat) (v : α) (m : Nat) : Prop :=
  (∃ x : α, ∃ p : List (Constraint α),
      PathIn cs x v p ∧ p.length ≤ n ∧ pathWeight p = m) ∧
    (∀ (x : α) (p : List (Constraint α)),
      PathIn cs x v p → p.length ≤ n → pathWeight p ≤ m)

theorem iteratePot_isLongestPathValue {α : Type} [DecidableEq α] (cs : List (Constraint α)) :
    ∀ (n : Nat) (v : α), IsLongestPathValue cs n v ((iteratePot (α := α) n cs).val v) := by
  intro n v
  refine And.intro ?_ ?_
  · -- attained by the carried witness path
    let pot : Pot α := iteratePot (α := α) n cs
    have hInv : PotInvariant cs pot := iteratePot_invariant (α := α) (cs := cs) n
    have hLen : PotLenInvariant n pot := iteratePot_lenInvariant (α := α) (cs := cs) n
    refine ⟨pot.start v, pot.path v, ?_, ?_, ?_⟩
    · exact (hInv v).1
    · exact hLen v
    · exact (hInv v).2
  · -- any bounded-length path is upper-bounded by the computed value
    intro x p hPath hlen
    exact iteratePot_upperBound (α := α) (cs := cs) (n := n) (v := v) (x := x) (p := p) hPath hlen

theorem canonicalUtility_isLongestPathValue (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    ∀ v : C.Obj,
      IsLongestPathValue (ConstraintsOfDataset C data) C.allObjs.length v (canonicalUtility C data v) := by
  intro v
  have hLP :
      IsLongestPathValue (ConstraintsOfDataset C data) C.allObjs.length v
        ((iteratePot (α := C.Obj) C.allObjs.length (ConstraintsOfDataset C data)).val v) :=
    iteratePot_isLongestPathValue
      (α := C.Obj) (cs := ConstraintsOfDataset C data) C.allObjs.length v
  have hVal :
      (iteratePot (α := C.Obj) C.allObjs.length (ConstraintsOfDataset C data)).val v =
        canonicalUtility C data v := by
    dsimp [canonicalUtility, iteratePot]
    exact
      iterate_relaxOncePot_val_eq_iterate_relaxOnce
        (α := C.Obj) (cs := ConstraintsOfDataset C data) C.allObjs.length v
  -- rewrite the target value and use the longest-path characterization for `iteratePot`
  rw [← hVal]
  exact hLP

/-!
### Completeness (finite): failure ⇒ positive cycle ⇒ (¬cycle ⇒ rationalizer)

We now close the loop constructively:

- if the `n`-step candidate violates some constraint, then one more relaxation
  strictly improves some vertex value;
- strict improvement after `n = C.allObjs.length` rounds forces a repeated
  vertex along the witnessing longest path, hence yields a **positive cycle**
  (weight cannot be `0`, otherwise we could delete the cycle and obtain an
  equally good shorter path, contradicting the `n`-round upper bound);
- therefore, `¬ PositiveCycle` implies solver success and existence of a
  rationalizing utility, giving the clean economic statement:

`(∃ u, RationalizesDataset C u data) ↔ ¬ GARPViolation (ConstraintsOfDataset C data)`.
-/

/-!
#### Constructive list infrastructure: `dedup`, `erase1`, and pigeonhole
-/

theorem mem_split' {α : Type} :
    ∀ {xs : List α} {a : α}, a ∈ xs → ∃ pre suf : List α, xs = pre ++ a :: suf := by
  intro xs a ha
  induction xs with
  | nil =>
      cases ha
  | cons x xs ih =>
      cases ha with
      | head =>
          refine ⟨[], xs, ?_⟩
          rfl
      | tail _ ha' =>
          rcases ih ha' with ⟨pre, suf, hxs⟩
          refine ⟨x :: pre, suf, ?_⟩
          rw [hxs]
          rfl

def erase1 {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then xs else x :: erase1 a xs

theorem mem_erase1_of_mem_ne {α : Type} [DecidableEq α] (a b : α) :
    ∀ {xs : List α}, b ∈ xs → b ≠ a → b ∈ erase1 a xs := by
  intro xs hb hne
  induction xs with
  | nil =>
      cases hb
  | cons x xs ih =>
      dsimp [erase1]
      by_cases hxa : x = a
      · rw [if_pos hxa]
        cases hb with
        | head =>
            cases (hne hxa)
        | tail _ hb' =>
            exact hb'
      · rw [if_neg hxa]
        cases hb with
        | head =>
            exact List.Mem.head (erase1 a xs)
        | tail _ hb' =>
            exact List.Mem.tail x (ih hb')

theorem mem_of_mem_erase1 {α : Type} [DecidableEq α] (a b : α) :
    ∀ {xs : List α}, b ∈ erase1 a xs → b ∈ xs := by
  intro xs hb
  induction xs with
  | nil =>
      dsimp [erase1] at hb
      cases hb
  | cons x xs ih =>
      dsimp [erase1] at hb
      by_cases hxa : x = a
      · rw [if_pos hxa] at hb
        exact List.Mem.tail x hb
      · rw [if_neg hxa] at hb
        cases hb with
        | head =>
            exact List.Mem.head xs
        | tail _ hb' =>
            exact List.Mem.tail x (ih hb')

/-!
`List.Nodup` is defined in Std via `Pairwise` and its convenient constructor
lemmas use `propext`. We therefore use a small inductive variant for all
constructive reasoning about “no duplicates”.
-/

inductive NodupI {α : Type} : List α → Prop
  | nil : NodupI []
  | cons {a : α} {xs : List α} : (¬ a ∈ xs) → NodupI xs → NodupI (a :: xs)

theorem erase1_nodupI {α : Type} [DecidableEq α] (a : α) :
    ∀ {xs : List α}, NodupI xs → NodupI (erase1 a xs) := by
  intro xs hN
  induction hN with
  | nil =>
      dsimp [erase1]
      exact NodupI.nil
  | cons hxnotin hTail ih =>
      rename_i x xs
      dsimp [erase1]
      by_cases hx : x = a
      · rw [if_pos hx]
        exact hTail
      · rw [if_neg hx]
        refine NodupI.cons ?_ ih
        intro hmem
        have : x ∈ xs := mem_of_mem_erase1 (a := a) (b := x) hmem
        exact hxnotin this

theorem length_erase1_of_nodupI_mem {α : Type} [DecidableEq α] (a : α) :
    ∀ {xs : List α}, NodupI xs → a ∈ xs → (erase1 a xs).length + 1 = xs.length := by
  intro xs hN ha
  induction hN with
  | nil =>
      cases ha
  | cons hxnotin hTail ih =>
      rename_i b xsTail
      dsimp [erase1]
      by_cases hb : b = a
      · rw [if_pos hb]
      · rw [if_neg hb]
        cases ha with
        | head =>
            cases (hb rfl)
        | tail _ haTail =>
            have hLen : (erase1 a xsTail).length + 1 = xsTail.length := ih haTail
            dsimp [List.length]
            have hstep :
                Nat.succ (erase1 a xsTail).length + 1 =
                  Nat.succ ((erase1 a xsTail).length + 1) := by
              rfl
            exact Eq.trans hstep (congrArg Nat.succ hLen)

def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let ys := dedup xs
      letI : Decidable (x ∈ ys) := decidableMem x ys
      if _ : x ∈ ys then ys else x :: ys

theorem mem_dedup_of_mem {α : Type} [DecidableEq α] :
    ∀ {xs : List α} {a : α}, a ∈ xs → a ∈ dedup xs := by
  intro xs a ha
  induction xs with
  | nil =>
      cases ha
  | cons x xs ih =>
      dsimp [dedup]
      cases ha with
      | head =>
          -- `a = x`
          -- after the `cases`, the head element is definitionaly `a`
          letI : Decidable (a ∈ dedup xs) := decidableMem a (dedup xs)
          by_cases ha0 : a ∈ dedup xs
          · rw [if_pos ha0]
            exact ha0
          · rw [if_neg ha0]
            exact List.Mem.head (dedup xs)
      | tail _ ha' =>
          have hmem : a ∈ dedup xs := ih ha'
          letI : Decidable (x ∈ dedup xs) := decidableMem x (dedup xs)
          by_cases hx : x ∈ dedup xs
          · rw [if_pos hx]
            exact hmem
          · rw [if_neg hx]
            exact List.Mem.tail x hmem

theorem dedup_nodupI {α : Type} [DecidableEq α] :
    ∀ xs : List α, NodupI (dedup xs) := by
  intro xs
  induction xs with
  | nil =>
      exact NodupI.nil
  | cons x xs ih =>
      dsimp [dedup]
      letI : Decidable (x ∈ dedup xs) := decidableMem x (dedup xs)
      by_cases hx : x ∈ dedup xs
      · rw [if_pos hx]
        exact ih
      · rw [if_neg hx]
        exact NodupI.cons hx ih

theorem dedup_length_le {α : Type} [DecidableEq α] :
    ∀ xs : List α, (dedup xs).length ≤ xs.length := by
  intro xs
  induction xs with
  | nil =>
      exact Nat.le_refl 0
  | cons x xs ih =>
      dsimp [dedup]
      letI : Decidable (x ∈ dedup xs) := decidableMem x (dedup xs)
      by_cases hx : x ∈ dedup xs
      · rw [if_pos hx]
        -- `length (dedup xs) ≤ succ (length xs)`
        exact Nat.le_trans ih (Nat.le_succ _)
      · rw [if_neg hx]
        dsimp [List.length]
        exact Nat.succ_le_succ ih

theorem nodupI_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α},
      NodupI xs →
      NodupI ys →
      (∀ x : α, x ∈ xs → x ∈ ys) →
        xs.length ≤ ys.length := by
  intro xs ys hx hy hsub
  induction hx generalizing ys with
  | nil =>
      exact Nat.zero_le _
  | cons hxnotin hxTail ih =>
      rename_i a xs
      have haMem : a ∈ ys := hsub a (List.Mem.head xs)
      let ys' : List α := erase1 a ys
      have hy' : NodupI ys' := erase1_nodupI (a := a) hy
      have hlen : ys'.length + 1 = ys.length :=
        length_erase1_of_nodupI_mem (a := a) (xs := ys) hy haMem
      have hsub' : ∀ x : α, x ∈ xs → x ∈ ys' := by
        intro x hxmemTail
        have hxInYs : x ∈ ys := hsub x (List.Mem.tail a hxmemTail)
        have hxne : x ≠ a := by
          intro hxeq
          cases hxeq
          exact hxnotin hxmemTail
        exact mem_erase1_of_mem_ne (a := a) (b := x) (xs := ys) hxInYs hxne
      have hTailLen : xs.length ≤ ys'.length := ih (ys := ys') hy' hsub'
      have hSucc : Nat.succ xs.length ≤ Nat.succ ys'.length := Nat.succ_le_succ hTailLen
      have hyEq : Nat.succ ys'.length = ys.length := Eq.trans rfl hlen
      exact hyEq ▸ hSucc

theorem exists_dup_decomp_of_not_nodupI {α : Type} [DecidableEq α] :
    ∀ xs : List α, ¬ NodupI xs → ∃ a : α, ∃ pre mid suf : List α, xs = pre ++ a :: mid ++ a :: suf := by
  intro xs hNot
  induction xs with
  | nil =>
      cases (hNot NodupI.nil)
  | cons x xs ih =>
      letI : Decidable (x ∈ xs) := decidableMem x xs
      by_cases hxmem : x ∈ xs
      · rcases mem_split' (xs := xs) (a := x) hxmem with ⟨pre, suf, hxs⟩
        refine ⟨x, [], pre, suf, ?_⟩
        -- `x :: xs = [] ++ x :: pre ++ x :: suf`
        rw [hxs]
        rfl
      · have hTailNot : ¬ NodupI xs := by
          intro hTailN
          have : NodupI (x :: xs) := NodupI.cons hxmem hTailN
          exact hNot this
        rcases ih hTailNot with ⟨a, pre, mid, suf, hxs⟩
        refine ⟨a, x :: pre, mid, suf, ?_⟩
        rw [hxs]
        rfl

/-!
For *certificate extraction* we need a Type-level duplicate decomposition (cannot
eliminate `∃` into `Type`). We therefore compute either a `NodupI` proof or an
explicit decomposition witnessing a duplicate.
-/

structure DupDecomp {α : Type} (xs : List α) : Type where
  a : α
  pre : List α
  mid : List α
  suf : List α
  eq : xs = pre ++ a :: mid ++ a :: suf

structure SplitAt {α : Type} (a : α) (xs : List α) : Type where
  pre : List α
  suf : List α
  eq : xs = pre ++ a :: suf

def splitAtFirst {α : Type} [DecidableEq α] (a : α) : (xs : List α) → Option (SplitAt a xs)
  | [] => none
  | x :: xs =>
      match decEq x a with
      | isTrue hx =>
          some ⟨[], xs, by cases hx; rfl⟩
      | isFalse _hx =>
          match splitAtFirst a xs with
          | none => none
          | some s =>
              some
                ⟨x :: s.pre, s.suf, by
                  refine Eq.trans (congrArg (fun t => x :: t) s.eq) ?_
                  rfl⟩

theorem splitAtFirst_none_implies_not_mem {α : Type} [DecidableEq α] (a : α) :
    ∀ xs : List α, splitAtFirst (a := a) xs = none → ¬ a ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro _ hmem
      cases hmem
  | cons x xs ih =>
      intro hnone hmem
      dsimp [splitAtFirst] at hnone
      cases hxa : decEq x a with
      | isTrue hx =>
          rw [hxa] at hnone
          cases hnone
      | isFalse hx =>
          rw [hxa] at hnone
          -- membership must come from the tail
          cases hmem with
          | head =>
              -- here `x = a`, contradiction with `hx`
              cases (hx rfl)
          | tail _ htail =>
              -- analyze the recursive call
              cases hSplit : splitAtFirst (a := a) xs with
              | none =>
                  rw [hSplit] at hnone
                  exact ih hSplit htail
              | some s =>
                  rw [hSplit] at hnone
                  cases hnone

def nodupOrDupDecomp {α : Type} [DecidableEq α] : (xs : List α) → Sum (PLift (NodupI xs)) (DupDecomp xs)
  | [] => Sum.inl ⟨NodupI.nil⟩
  | x :: xs =>
      letI : Decidable (x ∈ xs) := decidableMem x xs
      match hSplit : splitAtFirst (a := x) xs with
      | some s =>
          -- `xs = s.pre ++ x :: s.suf`, so `x :: xs = [] ++ x :: s.pre ++ x :: s.suf`
          Sum.inr
            ⟨x, [], s.pre, s.suf, by
              refine Eq.trans (congrArg (fun t => x :: t) s.eq) ?_
              rfl⟩
      | none =>
          have hxnot : ¬ x ∈ xs := splitAtFirst_none_implies_not_mem (a := x) xs hSplit
          match nodupOrDupDecomp xs with
          | Sum.inl hN =>
              Sum.inl ⟨NodupI.cons hxnot hN.down⟩
          | Sum.inr d =>
              Sum.inr
                ⟨d.a, x :: d.pre, d.mid, d.suf, by
                  refine Eq.trans (congrArg (fun t => x :: t) d.eq) ?_
                  rfl⟩

theorem vertexAt_dropN_add {α : Type} (s : α) :
    ∀ (p : List (Constraint α)) (i k : Nat),
      vertexAt s p (i + k) = vertexAt (vertexAt s p i) (dropN i p) k := by
  intro p i k
  induction i generalizing s p with
  | zero =>
      -- `i = 0`
      have h0 : vertexAt s p 0 = s := by
        cases p <;> rfl
      -- `dropN 0 p = p` definitionally, and `0 + k = k`
      rw [Nat.zero_add]
      rw [h0]
      rfl
  | succ i ih =>
      cases p with
      | nil =>
          rfl
      | cons c ps =>
          dsimp [vertexAt, dropN]
          -- reduce to IH on the tail
          simpa [Nat.succ_add] using ih (s := c.dst) (p := ps)

theorem dropN_add {α : Type} :
    ∀ (i k : Nat) (xs : List α), dropN (i + k) xs = dropN k (dropN i xs) := by
  intro i k xs
  induction i generalizing xs with
  | zero =>
      -- `i = 0`
      rw [Nat.zero_add]
      rfl
  | succ i ih =>
      cases xs with
      | nil =>
          cases k with
          | zero => rfl
          | succ k => rfl
      | cons x xs =>
          dsimp [dropN]
          simpa [Nat.succ_add] using ih (xs := xs)

theorem dropN_ne_nil_of_lt_length {α : Type} :
    ∀ (n : Nat) (xs : List α), n < xs.length → dropN n xs ≠ [] := by
  intro n xs hlt
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          dsimp [List.length] at hlt
          cases hlt
      | cons x xs =>
          dsimp [dropN]
          intro h
          cases h
  | succ n ih =>
      cases xs with
      | nil =>
          dsimp [List.length] at hlt
          cases hlt
      | cons x xs =>
          dsimp [dropN]
          -- reduce the length bound to the tail
          dsimp [List.length] at hlt
          have hlt' : n < xs.length := Nat.lt_of_succ_lt_succ hlt
          exact ih xs hlt'

theorem pathIn_takeN' {α : Type} {cs : List (Constraint α)} :
    ∀ {x y : α} {p : List (Constraint α)},
      PathIn cs x y p → ∀ n : Nat, PathIn cs x (vertexAt x p n) (takeN n p) := by
  intro x y p hPath n
  induction n generalizing x y p with
  | zero =>
      cases p with
      | nil =>
          exact PathIn.nil x
      | cons c ps =>
          exact PathIn.nil x
  | succ n ih =>
      cases p with
      | nil =>
          -- `takeN (n+1) [] = []` and `vertexAt x [] (n+1) = x`
          exact PathIn.nil x
      | cons c ps =>
          -- `hPath` must be a `cons`
          cases hPath with
          | cons hcMem hsrc hTail =>
              dsimp [takeN, vertexAt]
              exact PathIn.cons hcMem hsrc (ih (x := c.dst) (y := y) (p := ps) hTail)

theorem pathIn_dropN' {α : Type} {cs : List (Constraint α)} :
    ∀ {x y : α} {p : List (Constraint α)},
      PathIn cs x y p → ∀ n : Nat, PathIn cs (vertexAt x p n) y (dropN n p) := by
  intro x y p hPath n
  induction n generalizing x y p with
  | zero =>
      cases p with
      | nil =>
          -- `vertexAt x [] 0 = x` and `dropN 0 [] = []`
          simpa [dropN, vertexAt] using hPath
      | cons c ps =>
          -- `vertexAt x (c :: ps) 0 = x` and `dropN 0 (c :: ps) = c :: ps`
          simpa [dropN, vertexAt] using hPath
  | succ n ih =>
      cases p with
      | nil =>
          -- `hPath` forces `y = x`
          cases hPath with
          | nil _ =>
              exact PathIn.nil x
      | cons c ps =>
          cases hPath with
          | cons _ _ hTail =>
              dsimp [dropN, vertexAt]
              exact ih (x := c.dst) (y := y) (p := ps) hTail

theorem nodup_length_le_allObjs (C : FiniteDescriptiveCore) :
    ∀ (xs : List C.Obj), NodupI xs → xs.length ≤ C.allObjs.length := by
  intro xs hN
  let univ : List C.Obj := dedup C.allObjs
  have hunivN : NodupI univ := by
    dsimp [univ]
    exact dedup_nodupI C.allObjs
  have hsub : ∀ x : C.Obj, x ∈ xs → x ∈ univ := by
    intro x _hx
    have hxAll : x ∈ C.allObjs := C.allObjs_complete x
    dsimp [univ]
    exact mem_dedup_of_mem (xs := C.allObjs) (a := x) hxAll
  have hlen1 : xs.length ≤ univ.length :=
    nodupI_length_le_of_subset (xs := xs) (ys := univ) hN hunivN hsub
  have hlen2 : univ.length ≤ C.allObjs.length := dedup_length_le (xs := C.allObjs)
  exact Nat.le_trans hlen1 hlen2

def strictImprove_iteratePot_implies_positiveCycle
    (C : FiniteDescriptiveCore) (cs : List (Constraint C.Obj)) :
    ∀ v : C.Obj,
      (iteratePot (α := C.Obj) (C.allObjs.length + 1) cs).val v >
        (iteratePot (α := C.Obj) C.allObjs.length cs).val v →
          PositiveCycleCert cs := by
  intro v hlt
  let n : Nat := C.allObjs.length
  let potN : Pot C.Obj := iteratePot (α := C.Obj) n cs
  let potS : Pot C.Obj := iteratePot (α := C.Obj) (n + 1) cs
  have hInvS : PotInvariant cs potS := iteratePot_invariant (α := C.Obj) (cs := cs) (n := n + 1)
  have hLenS : PotLenInvariant (n + 1) potS := iteratePot_lenInvariant (α := C.Obj) (cs := cs) (n := n + 1)
  have hPathS : PathIn cs (potS.start v) v (potS.path v) := (hInvS v).1
  have hWgtS : pathWeight (potS.path v) = potS.val v := (hInvS v).2
  have hlen_le : (potS.path v).length ≤ n + 1 := hLenS v
  -- the witnessing path must have length exactly `n+1` (otherwise it would be bounded at round `n`)
  have hlen_not_le : ¬ (potS.path v).length ≤ n := by
    intro hlen_le_n
    have hUB :
        pathWeight (potS.path v) ≤ (iteratePot (α := C.Obj) n cs).val v :=
      iteratePot_upperBound (α := C.Obj) (cs := cs) (n := n) (v := v) (x := potS.start v) (p := potS.path v)
        hPathS hlen_le_n
    have hUB' : potS.val v ≤ potN.val v := by
      -- rewrite the LHS along the path-weight invariant
      rw [← hWgtS]
      exact hUB
    exact (Nat.not_lt_of_ge hUB') hlt
  have hlen_gt : n < (potS.path v).length := Nat.lt_of_not_ge hlen_not_le
  have hlen_ge : n + 1 ≤ (potS.path v).length := Nat.succ_le_of_lt hlen_gt
  have hlen_eq : (potS.path v).length = n + 1 := Nat.le_antisymm hlen_le hlen_ge
  -- vertices along the witness path have a repetition (pigeonhole)
  let vs : List C.Obj := verticesOfPath (potS.start v) (potS.path v)
  have hVsLen : vs.length = n + 2 := by
    dsimp [vs, n]
    have h0 := verticesOfPath_length (s := potS.start v) (potS.path v)
    rw [hlen_eq] at h0
    have h1 : (n + 1) + 1 = n + 2 := by
      rfl
    rw [h1] at h0
    exact h0
  have hNotNodup : ¬ NodupI vs := by
    intro hNodup
    have hle : vs.length ≤ n := nodup_length_le_allObjs (C := C) vs hNodup
    -- but `n < n+2 = vs.length`
    have hnlt : n < vs.length := by
      rw [hVsLen]
      -- `n < (n+1).succ`
      exact Nat.lt_succ_of_le (Nat.le_succ n)
    exact (Nat.not_lt_of_ge hle) hnlt
  have hDup : DupDecomp vs := by
    cases hDec : nodupOrDupDecomp (xs := vs) with
    | inl hN =>
        exact False.elim (hNotNodup hN.down)
    | inr d =>
        exact d
  rcases hDup with ⟨x, pre, mid, suf, hvs⟩
  -- indices of the two occurrences in the vertex list
  let i : Nat := pre.length
  let cycleLen : Nat := (x :: mid).length
  let j : Nat := i + cycleLen
  have hi_lt_vs : i < vs.length := by
    dsimp [i]
    rw [hvs]
    -- `pre.length < pre.length + (x :: mid ++ x :: suf).length`
    have hpos : 0 < (x :: mid ++ x :: suf).length := by
      dsimp [List.length]
      exact Nat.succ_pos _
    have hlt : pre.length < pre.length + (x :: mid ++ x :: suf).length :=
      Nat.lt_add_of_pos_right hpos
    have hAssoc : pre ++ x :: mid ++ x :: suf = pre ++ (x :: mid ++ x :: suf) :=
      append_assoc' pre (x :: mid) (x :: suf)
    rw [hAssoc]
    have hLen : (pre ++ (x :: mid ++ x :: suf)).length = pre.length + (x :: mid ++ x :: suf).length :=
      length_append' pre (x :: mid ++ x :: suf)
    rw [hLen]
    exact hlt
  have hj_lt_vs : j < vs.length := by
    dsimp [j, i, cycleLen]
    -- view `vs` as `(pre ++ x :: mid) ++ x :: suf`
    have hvs' : vs = (pre ++ x :: mid) ++ x :: suf := by
      -- `pre ++ x :: mid ++ x :: suf` associates to the left
      -- and `(pre ++ x :: mid) ++ x :: suf` is definitionally `pre ++ x :: (mid ++ x :: suf)`
      exact hvs
    rw [hvs']
    -- show `length (pre ++ x :: mid) < length ((pre ++ x :: mid) ++ x :: suf)`
    have hpos : 0 < (x :: suf).length := by
      dsimp [List.length]
      exact Nat.succ_pos _
    have hlt : (pre ++ x :: mid).length < (pre ++ x :: mid).length + (x :: suf).length :=
      Nat.lt_add_of_pos_right hpos
    -- and the unfolded `j` is that prefix length
    have hJL : pre.length + (mid.length + 1) = (pre ++ x :: mid).length := by
      have hlen : (pre ++ x :: mid).length = pre.length + (x :: mid).length :=
        length_append' pre (x :: mid)
      have hxlen : (x :: mid).length = mid.length + 1 := by
        rfl
      calc
        pre.length + (mid.length + 1) = pre.length + (x :: mid).length := by
          rw [← hxlen]
        _ = (pre ++ x :: mid).length := by
          exact hlen.symm
    rw [hJL]
    have hLen : ((pre ++ x :: mid) ++ x :: suf).length = (pre ++ x :: mid).length + (x :: suf).length :=
      length_append' (pre ++ x :: mid) (x :: suf)
    rw [hLen]
    exact hlt
  have hi_le_p : i ≤ (potS.path v).length := by
    have : i < (potS.path v).length + 1 := by
      -- `vs.length = path.length + 1`
      have hvLen : vs.length = (potS.path v).length + 1 := verticesOfPath_length (s := potS.start v) (potS.path v)
      -- transport `i < vs.length`
      have h := hi_lt_vs
      rw [hvLen] at h
      exact h
    exact (Nat.lt_succ_iff).1 this
  have hj_le_p : j ≤ (potS.path v).length := by
    have : j < (potS.path v).length + 1 := by
      have hvLen : vs.length = (potS.path v).length + 1 := verticesOfPath_length (s := potS.start v) (potS.path v)
      have h := hj_lt_vs
      rw [hvLen] at h
      exact h
    exact (Nat.lt_succ_iff).1 this
  -- identify the repeated vertex as `vertexAt` at those indices
  have hNthI : nthOr (potS.start v) vs i = x := by
    -- `vs = pre ++ x :: (mid ++ x :: suf)`
    have hvs0 : vs = pre ++ x :: (mid ++ x :: suf) := by
      have hR : pre ++ x :: mid ++ x :: suf = pre ++ x :: (mid ++ x :: suf) := by
        exact Eq.trans (append_assoc' pre (x :: mid) (x :: suf)) rfl
      exact Eq.trans hvs hR
    dsimp [i]
    rw [hvs0]
    exact nthOr_append_length (d := potS.start v) pre x (mid ++ x :: suf)
  have hNthJ : nthOr (potS.start v) vs j = x := by
    -- `vs = (pre ++ x :: mid) ++ x :: suf`
    have hvs1 : vs = (pre ++ x :: mid) ++ x :: suf := by
      exact hvs
    rw [hvs1]
    have hjEq : j = (pre ++ x :: mid).length := by
      dsimp [j, i, cycleLen]
      have hlen : (pre ++ x :: mid).length = pre.length + (x :: mid).length := length_append' pre (x :: mid)
      rw [hlen]
      rfl
    rw [hjEq]
    exact nthOr_append_length (d := potS.start v) (pre ++ x :: mid) x suf
  have hVI : vertexAt (potS.start v) (potS.path v) i = x := by
    have hEq := vertexAt_eq_nthOr_verticesOfPath_of_le (s := potS.start v) (p := potS.path v) (n := i) hi_le_p
    rw [hEq]
    dsimp [vs] at hNthI
    exact hNthI
  have hVJ : vertexAt (potS.start v) (potS.path v) j = x := by
    have hEq := vertexAt_eq_nthOr_verticesOfPath_of_le (s := potS.start v) (p := potS.path v) (n := j) hj_le_p
    rw [hEq]
    dsimp [vs] at hNthJ
    exact hNthJ
  -- define the cycle segment in the edge list
  let pAll : List (Constraint C.Obj) := potS.path v
  let pPre : List (Constraint C.Obj) := takeN i pAll
  let pRest : List (Constraint C.Obj) := dropN i pAll
  let pCycle : List (Constraint C.Obj) := takeN cycleLen pRest
  let pSuf : List (Constraint C.Obj) := dropN cycleLen pRest
  have hDecomp : pAll = pPre ++ pCycle ++ pSuf := by
    dsimp [pPre, pRest, pCycle, pSuf]
    have h0 : takeN i pAll ++ dropN i pAll = pAll := takeN_dropN_eq i pAll
    have h1 :
        takeN cycleLen (dropN i pAll) ++ dropN cycleLen (dropN i pAll) = dropN i pAll :=
      takeN_dropN_eq cycleLen (dropN i pAll)
    have hA :
        pAll = takeN i pAll ++ (takeN cycleLen (dropN i pAll) ++ dropN cycleLen (dropN i pAll)) := by
      calc
        pAll = takeN i pAll ++ dropN i pAll := h0.symm
        _ = takeN i pAll ++ (takeN cycleLen (dropN i pAll) ++ dropN cycleLen (dropN i pAll)) := by
            exact congrArg (fun t => takeN i pAll ++ t) h1.symm
    have hAssoc :
        takeN i pAll ++ (takeN cycleLen (dropN i pAll) ++ dropN cycleLen (dropN i pAll)) =
          takeN i pAll ++ takeN cycleLen (dropN i pAll) ++ dropN cycleLen (dropN i pAll) := by
      exact
        (append_assoc'
          (takeN i pAll)
          (takeN cycleLen (dropN i pAll))
          (dropN cycleLen (dropN i pAll))).symm
    exact Eq.trans hA hAssoc
  -- show `pCycle` is a positive cycle (weight ≠ 0)
  have hCyclePath : PathIn cs x x pCycle := by
    -- from `PathIn` on the whole path, extract the `i`-drop and then take `cycleLen`
    have hDrop : PathIn cs (vertexAt (potS.start v) pAll i) v (dropN i pAll) :=
      pathIn_dropN' (cs := cs) (x := potS.start v) (y := v) (p := pAll) hPathS i
    have hTake : PathIn cs (vertexAt (potS.start v) pAll i)
        (vertexAt (vertexAt (potS.start v) pAll i) (dropN i pAll) cycleLen)
        (takeN cycleLen (dropN i pAll)) :=
      pathIn_takeN' (cs := cs) (x := vertexAt (potS.start v) pAll i) (y := v) (p := dropN i pAll) hDrop cycleLen
    -- rewrite the start vertex into `x`
    have hStartEq : vertexAt (potS.start v) pAll i = x := hVI
    have hTake1 :
        PathIn cs x
          (vertexAt x (dropN i pAll) cycleLen)
          (takeN cycleLen (dropN i pAll)) := by
      have hTake' := hTake
      rw [hStartEq] at hTake'
      exact hTake'
    -- relate the endpoint of the taken suffix to `vertexAt ... (i + cycleLen)`
    have hEnd' :
        vertexAt x (dropN i pAll) cycleLen =
          vertexAt (potS.start v) pAll (i + cycleLen) := by
      have h0 := vertexAt_dropN_add (s := potS.start v) (p := pAll) (i := i) (k := cycleLen)
      have h1 :
          vertexAt (potS.start v) pAll (i + cycleLen) =
            vertexAt x (dropN i pAll) cycleLen := by
        have h0' := h0
        rw [hStartEq] at h0'
        exact h0'
      exact h1.symm
    have hTake2 :
        PathIn cs x
          (vertexAt (potS.start v) pAll (i + cycleLen))
          (takeN cycleLen (dropN i pAll)) := by
      have hTake1' := hTake1
      rw [hEnd'] at hTake1'
      exact hTake1'
    -- and `i + cycleLen = j`, so the endpoint is also `x`
    have hEndEq : vertexAt (potS.start v) pAll (i + cycleLen) = x := by
      have hJdef : j = i + cycleLen := rfl
      rw [← hJdef]
      exact hVJ
    have hTake3 : PathIn cs x x (takeN cycleLen (dropN i pAll)) := by
      have hTake2' := hTake2
      rw [hEndEq] at hTake2'
      exact hTake2'
    -- finally, this edge list is exactly `pCycle`
    have hPCycle : pCycle = takeN cycleLen (dropN i pAll) := rfl
    rw [hPCycle]
    exact hTake3
  -- if the cycle weight were 0, we could delete it and obtain a shorter path with the same weight
  have hCyclePos : 0 < pathWeight pCycle := by
    cases hW : pathWeight pCycle with
    | zero =>
        -- build the shortened path
        let pShort : List (Constraint C.Obj) := pPre ++ pSuf
        have hShortPath : PathIn cs (potS.start v) v pShort := by
          -- prefix to `x = vertexAt ... i`
          have hPrePath :
              PathIn cs (potS.start v) (vertexAt (potS.start v) pAll i) pPre :=
            pathIn_takeN' (cs := cs) (x := potS.start v) (y := v) (p := pAll) hPathS i
          -- suffix from `vertexAt ... j` to `v`
          have hSufPath :
              PathIn cs (vertexAt (potS.start v) pAll j) v (dropN j pAll) :=
            pathIn_dropN' (cs := cs) (x := potS.start v) (y := v) (p := pAll) hPathS j
          -- but `dropN j pAll = pSuf` by definition
          have hDropEq : dropN j pAll = pSuf := by
            have hj0 : j = i + cycleLen := rfl
            dsimp [pSuf, pRest]
            rw [hj0]
            exact dropN_add i cycleLen pAll
          have hMidEq : vertexAt (potS.start v) pAll i = vertexAt (potS.start v) pAll j := by
            -- both equal to `x`
            rw [hVI, hVJ]
          -- rewrite intermediate vertex and suffix list, then append
          have hSufPath' : PathIn cs (vertexAt (potS.start v) pAll i) v pSuf := by
            -- transport start along `hMidEq` and list along `hDropEq`
            -- (rewrite both in `hSufPath`)
            have h1 : PathIn cs (vertexAt (potS.start v) pAll i) v (dropN j pAll) := by
              have h1' := hSufPath
              rw [← hMidEq] at h1'
              exact h1'
            have h2 := h1
            rw [hDropEq] at h2
            exact h2
          exact pathIn_append (cs := cs) (x := potS.start v) (y := vertexAt (potS.start v) pAll i) (z := v)
            (p := pPre) (q := pSuf) hPrePath hSufPath'
        have hShortLen : pShort.length ≤ n := by
          -- compute lengths from the decomposition and the fact `pCycle` is nonempty
          -- use `pAll.length = n+1` and `pAll = pPre ++ pCycle ++ pSuf`
          have hpAllLen : pAll.length = n + 1 := by
            -- `pAll = potS.path v`
            dsimp [pAll, n]
            exact hlen_eq
          have hLenDecomp :
              pAll.length = pPre.length + pCycle.length + pSuf.length := by
            -- rewrite along `hDecomp` and compute length of `pPre ++ pCycle ++ pSuf`
            rw [hDecomp]
            have hL1 : (pPre ++ pCycle).length = pPre.length + pCycle.length := length_append' pPre pCycle
            have hL0 : (pPre ++ pCycle ++ pSuf).length = (pPre ++ pCycle).length + pSuf.length :=
              length_append' (pPre ++ pCycle) pSuf
            rw [hL0]
            rw [hL1]
          -- `pShort.length = pPre.length + pSuf.length`
          have hShortLenEq : pShort.length = pPre.length + pSuf.length := by
            dsimp [pShort]
            exact length_append' pPre pSuf
          -- show `1 ≤ pCycle.length` by nonemptiness (cycleLen > 0 and i < j ≤ pAll.length)
          have hCycleLenPos : 0 < cycleLen := by
            have hcl : cycleLen = Nat.succ mid.length := rfl
            rw [hcl]
            exact Nat.succ_pos _
          have hij : i < j := by
            dsimp [j]
            exact Nat.lt_add_of_pos_right hCycleLenPos
          have hj_le : j ≤ pAll.length := hj_le_p
          have hi_lt : i < pAll.length := Nat.lt_of_lt_of_le hij hj_le
          have hRestNe : pRest ≠ [] := by
            dsimp [pRest]
            exact dropN_ne_nil_of_lt_length i pAll (by
              -- `i < pAll.length` is `hi_lt`
              exact hi_lt
            )
          have hCycleNe : pCycle ≠ [] := by
            -- `pRest` is nonempty, and `cycleLen = succ _`, so `takeN cycleLen pRest` is nonempty
            cases hpr : pRest with
            | nil =>
                exact False.elim (hRestNe hpr)
            | cons e es =>
                have hcl : cycleLen = Nat.succ mid.length := rfl
                dsimp [pCycle]
                rw [hpr]
                rw [hcl]
                -- `takeN (succ _) (e :: es) = e :: _`
                dsimp [takeN]
                intro h
                cases h
          have hCycleLenPos' : 0 < pCycle.length := by
            cases hpc : pCycle with
            | nil =>
                exact False.elim (hCycleNe hpc)
            | cons e es =>
                dsimp [List.length]
                exact Nat.succ_pos _
          have hone : 1 ≤ pCycle.length := Nat.succ_le_of_lt hCycleLenPos'
          -- compare lengths via the decomposition
          have hmid : pPre.length + 1 + pSuf.length ≤ pPre.length + pCycle.length + pSuf.length := by
            have h0 : pPre.length + 1 ≤ pPre.length + pCycle.length :=
              Nat.add_le_add_left hone (pPre.length)
            exact Nat.add_le_add_right h0 (pSuf.length)
          have hcomm : pPre.length + 1 + pSuf.length = pPre.length + pSuf.length + 1 := by
            rw [Nat.add_assoc]
            rw [Nat.add_comm 1 pSuf.length]
            rw [Nat.add_assoc]
          have hLe : pPre.length + pSuf.length + 1 ≤ pAll.length := by
            -- rewrite RHS using `hLenDecomp`
            have hrhs : pPre.length + pCycle.length + pSuf.length = pAll.length := by
              rw [hLenDecomp]
            have hmid' : pPre.length + 1 + pSuf.length ≤ pAll.length := by
              rw [← hrhs]
              exact hmid
            exact le_of_eq_of_le hcomm.symm hmid'
          have hLe' : pShort.length + 1 ≤ n + 1 := by
            -- rewrite `pShort.length` and `pAll.length`
            rw [hShortLenEq]
            rw [← hpAllLen]
            exact hLe
          exact Nat.le_of_succ_le_succ hLe'
        -- weight of the shortened path equals the full path weight (since `pathWeight pCycle = 0`)
        have hShortWeight : pathWeight pShort = pathWeight pAll := by
          -- compute weights using the decomposition and `hW`
          have hwApp :
              pathWeight pAll = pathWeight pPre + pathWeight pCycle + pathWeight pSuf := by
            -- use `pathWeight_append` twice
            rw [hDecomp]
            have h0 : pathWeight (pPre ++ pCycle ++ pSuf) = pathWeight (pPre ++ pCycle) + pathWeight pSuf :=
              pathWeight_append (α := C.Obj) (pPre ++ pCycle) pSuf
            have h1 : pathWeight (pPre ++ pCycle) = pathWeight pPre + pathWeight pCycle :=
              pathWeight_append (α := C.Obj) pPre pCycle
            rw [h0, h1]
          have hwShort : pathWeight pShort = pathWeight pPre + pathWeight pSuf := by
            dsimp [pShort]
            exact pathWeight_append (α := C.Obj) pPre pSuf
          -- now substitute `pathWeight pCycle = 0`
          rw [hwShort]
          rw [hwApp]
          rw [hW]
          -- simplify `a + 0 + b = a + b`
          rw [Nat.add_zero]
        -- apply the `n`-round upper bound to the shorter path, contradicting strict improvement
        have hUBShort :
            pathWeight pShort ≤ (iteratePot (α := C.Obj) n cs).val v :=
          iteratePot_upperBound (α := C.Obj) (cs := cs) (n := n) (v := v) (x := potS.start v) (p := pShort)
            hShortPath hShortLen
        have hUBShort' : potS.val v ≤ potN.val v := by
          -- `pathWeight pAll = potS.val v` by invariant, and `pathWeight pShort = pathWeight pAll`
          have : pathWeight pShort = potS.val v := by
            rw [hShortWeight]
            rw [hWgtS]
          -- rewrite and apply bound
          rw [← this]
          exact hUBShort
        exact False.elim ((Nat.not_lt_of_ge hUBShort') hlt)
    | succ w =>
        -- `0 < succ w`
        exact Nat.succ_pos w
  exact ⟨x, pCycle, hCyclePath, hCyclePos⟩

theorem incomingMax_ge_of_edge {α : Type} [DecidableEq α] (u : α → Nat) (v : α) :
    ∀ (cs : List (Constraint α)) (c : Constraint α),
      c ∈ cs → c.dst = v → u c.src + c.w ≤ incomingMax u v cs := by
  intro cs
  induction cs with
  | nil =>
      intro c hc
      cases hc
  | cons c0 cs ih =>
      intro c hcMem hdst
      dsimp [incomingMax]
      by_cases hdst0 : c0.dst = v
      · rw [if_pos hdst0]
        cases hcMem with
        | head =>
            -- `c = c0`
            have hle : u c0.src + c0.w ≤ Nat.max (u c0.src + c0.w) (incomingMax u v cs) :=
              le_max_left' _ _
            exact hle
        | tail _ hcTail =>
            have hTail : u c.src + c.w ≤ incomingMax u v cs := ih c hcTail hdst
            have hle : incomingMax u v cs ≤ Nat.max (u c0.src + c0.w) (incomingMax u v cs) :=
              le_max_right' _ _
            exact Nat.le_trans hTail hle
      · rw [if_neg hdst0]
        have hcMem' : c ∈ cs := by
          cases hcMem with
          | head =>
              cases hdst0 hdst
          | tail _ hcTail =>
              exact hcTail
        exact ih c hcMem' hdst

def solveUtilityResult_fail_implies_positiveCycleCert (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    ∀ {u : C.Obj → Nat} {c : Constraint C.Obj},
      solveUtilityResult C data = SolveResult.fail u c →
        PositiveCycleCert (ConstraintsOfDataset C data) := by
  intro u c hFail
  let cs : List (Constraint C.Obj) := ConstraintsOfDataset C data
  have hSound := solveUtilityResult_fail_sound (C := C) (data := data) (u := u) (c := c) hFail
  have hcMem : c ∈ cs := by
    dsimp [cs]
    exact hSound.1
  have hViol : ¬ SatisfiesConstraint u c := hSound.2
  have hlt : u c.dst < u c.src + c.w := Nat.lt_of_not_ge hViol
  have hInc : u c.src + c.w ≤ incomingMax u c.dst cs :=
    incomingMax_ge_of_edge (u := u) (v := c.dst) (cs := cs) (c := c) hcMem rfl
  have hInc' : u c.dst < incomingMax u c.dst cs := Nat.lt_of_lt_of_le hlt hInc
  -- one more relaxation strictly increases `u` at `c.dst`
  have hNext :
      relaxOnce cs u c.dst > u c.dst := by
    dsimp [relaxOnce]
    have hle : u c.dst ≤ incomingMax u c.dst cs := Nat.le_of_lt hInc'
    -- `max (u dst) incoming = incoming`
    have hmax : max (u c.dst) (incomingMax u c.dst cs) = incomingMax u c.dst cs :=
      Nat.max_eq_right hle
    rw [hmax]
    exact hInc'
  -- transport the strict improvement to `iteratePot` and apply the cycle-extraction theorem
  have hIter :
      (iteratePot (α := C.Obj) (C.allObjs.length + 1) cs).val c.dst >
        (iteratePot (α := C.Obj) C.allObjs.length cs).val c.dst := by
    dsimp [solveUtilityResult] at hFail
    -- expose the computed candidate `uCand`
    let uCand : C.Obj → Nat := iterate C.allObjs.length (relaxOnce cs) (fun _ => 0)
    cases hFind : findFirstViolation uCand cs with
    | none =>
        rw [hFind] at hFail
        cases hFail
    | some c0 =>
        rw [hFind] at hFail
        cases hFail
        -- now `u = uCand` definitionally
        have hSucc :
            iterate (C.allObjs.length + 1) (relaxOnce cs) (fun _ => 0) c.dst >
              iterate C.allObjs.length (relaxOnce cs) (fun _ => 0) c.dst := by
          dsimp [iterate]
          -- `Nat.rec` unfolds to one `relaxOnce` application at the successor step
          exact hNext
        have hEqN :
            (iteratePot (α := C.Obj) C.allObjs.length cs).val c.dst =
              iterate C.allObjs.length (relaxOnce cs) (fun _ => 0) c.dst := by
          dsimp [iteratePot]
          exact
            iterate_relaxOncePot_val_eq_iterate_relaxOnce
              (α := C.Obj) (cs := cs) (n := C.allObjs.length) (v := c.dst)
        have hEqS :
            (iteratePot (α := C.Obj) (C.allObjs.length + 1) cs).val c.dst =
              iterate (C.allObjs.length + 1) (relaxOnce cs) (fun _ => 0) c.dst := by
          dsimp [iteratePot]
          exact
            iterate_relaxOncePot_val_eq_iterate_relaxOnce
              (α := C.Obj) (cs := cs) (n := C.allObjs.length + 1) (v := c.dst)
        have h := hSucc
        rw [hEqS.symm] at h
        rw [hEqN.symm] at h
        exact h
  -- conclude
  exact strictImprove_iteratePot_implies_positiveCycle (C := C) (cs := cs) (v := c.dst) hIter

theorem solveUtilityResult_fail_implies_positiveCycle (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    ∀ {u : C.Obj → Nat} {c : Constraint C.Obj},
      solveUtilityResult C data = SolveResult.fail u c →
        PositiveCycle (ConstraintsOfDataset C data) := by
  intro u c hFail
  exact
    PositiveCycleCert.toPositiveCycle
      (solveUtilityResult_fail_implies_positiveCycleCert (C := C) (data := data) (u := u) (c := c) hFail)

theorem noPositiveCycle_implies_exists_rationalizer (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    ¬ PositiveCycle (ConstraintsOfDataset C data) → ∃ u : C.Obj → Nat, RationalizesDataset C u data := by
  intro hNo
  cases hRes : solveUtilityResult C data with
  | success u =>
      exact ⟨u, solveUtilityResult_success_sound (C := C) (data := data) (u := u) hRes⟩
  | fail u c =>
      have hCycle : PositiveCycle (ConstraintsOfDataset C data) :=
        solveUtilityResult_fail_implies_positiveCycle (C := C) (data := data) (u := u) (c := c) hRes
      exact False.elim (hNo hCycle)

theorem exists_rationalizer_iff_noPositiveCycle (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    (∃ u : C.Obj → Nat, RationalizesDataset C u data) ↔
      ¬ PositiveCycle (ConstraintsOfDataset C data) := by
  constructor
  · exact exists_rationalizer_implies_noPositiveCycle (C := C) (data := data)
  · exact noPositiveCycle_implies_exists_rationalizer (C := C) (data := data)

theorem exists_rationalizer_iff_noGARPViolation (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    (∃ u : C.Obj → Nat, RationalizesDataset C u data) ↔
      ¬ GARPViolation (ConstraintsOfDataset C data) := by
  constructor
  · intro h
    intro hG
    have hCycle : PositiveCycle (ConstraintsOfDataset C data) :=
      (positiveCycle_iff_garpViolation_dataset (C := C) (data := data)).2 hG
    have hNo : ¬ PositiveCycle (ConstraintsOfDataset C data) :=
      (exists_rationalizer_implies_noPositiveCycle (C := C) (data := data)) h
    exact hNo hCycle
  · intro hNoG
    have hNoCycle : ¬ PositiveCycle (ConstraintsOfDataset C data) := by
      intro hCycle
      have hG : GARPViolation (ConstraintsOfDataset C data) :=
        (positiveCycle_iff_garpViolation_dataset (C := C) (data := data)).1 hCycle
      exact hNoG hG
    exact noPositiveCycle_implies_exists_rationalizer (C := C) (data := data) hNoCycle

/-!
### Executable rationality test (double certificate)

Given a dataset, we can **compute** `solveUtilityResult` and then *certify*:

- either a rationalizer `u` (with proof), or
- a positive cycle certificate (explicit cycle path).
-/

abbrev RationalizerCert (C : FiniteDescriptiveCore) (data : List (Observation C)) : Type :=
  { u : C.Obj → Nat // RationalizesDataset C u data }

def rationalityTest (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    Sum (RationalizerCert C data) (PositiveCycleCert (ConstraintsOfDataset C data)) :=
  match h : solveUtilityResult C data with
  | SolveResult.success u =>
      Sum.inl ⟨u, solveUtilityResult_success_sound (C := C) (data := data) (u := u) h⟩
  | SolveResult.fail u c =>
      Sum.inr (solveUtilityResult_fail_implies_positiveCycleCert (C := C) (data := data) (u := u) (c := c) h)

def rationalityTestMinimal (C : FiniteDescriptiveCore) (data : List (Observation C)) :
    Sum (MinimalRationalizerCert C data) (PositiveCycleCert (ConstraintsOfDataset C data)) :=
  match h : solveUtilityResult C data with
  | SolveResult.success u =>
      Sum.inl
        ⟨u,
          solveUtilityResult_success_sound (C := C) (data := data) (u := u) h,
          solveUtilityResult_success_minimal (C := C) (data := data) (u := u) h⟩
  | SolveResult.fail u c =>
      Sum.inr (solveUtilityResult_fail_implies_positiveCycleCert (C := C) (data := data) (u := u) (c := c) h)

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the main results of this module.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.rationalizesDataset_iff_satisfiesConstraints
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.satisfiesConstraints_implies_demandChoice_eq_some
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtility_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_success_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_success_minimal
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_fail_sound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.positiveCycle_implies_not_rationalizable
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.positiveCycle_iff_garpViolation_dataset
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.garpViolation_implies_not_rationalizable
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.satisfiableConstraints_implies_noPositiveCycle
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.iteratePot_upperBound
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.iteratePot_isLongestPathValue
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.canonicalUtility_isLongestPathValue
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.strictImprove_iteratePot_implies_positiveCycle
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_fail_implies_positiveCycleCert
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.solveUtilityResult_fail_implies_positiveCycle
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.noPositiveCycle_implies_exists_rationalizer
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.exists_rationalizer_iff_noPositiveCycle
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.exists_rationalizer_iff_noGARPViolation
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.rationalityTest
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.rationalityTestMinimal
/- AXIOM_AUDIT_END -/

end FiniteDescriptiveCore

end Descriptive.Faithful
