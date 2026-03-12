import Descriptive.NoUniversal

namespace Descriptive

/-!
Representability.

We isolate the closure properties that come *for free* from the relative
description operator (`relDescr`): if a predicate `φ` is represented by some
existing term `a`, then we can represent `φ ∧ ψ` for any `ψ` by filtering `a`.

This is the right level of generality: closure under global negation would
require a universal object, which is impossible (`no_universal`).
-/

def Represents (C : DescriptiveCore) (a : C.Term) (φ : C.Term → Prop) : Prop :=
  C.Ex a ∧ ∀ y : C.Term, C.Mem y a ↔ φ y

def Rep (C : DescriptiveCore) (φ : C.Term → Prop) : Prop :=
  ∃ a : C.Term, Represents C a φ

theorem represents_of_globalDescr (C : DescriptiveCore) (φ : C.Term → Prop)
    (h : C.Ex (C.globalDescr φ)) :
    Represents C (C.globalDescr φ) φ := by
  refine ⟨h, ?_⟩
  intro y
  exact C.global_spec (φ := φ) h (y := y)

theorem represents_filter (C : DescriptiveCore) {a : C.Term} {φ : C.Term → Prop}
    (ha : Represents C a φ) (ψ : C.Term → Prop) :
    Represents C (C.relDescr a ψ) (fun y => φ y ∧ ψ y) := by
  rcases ha with ⟨hEx, hmem⟩
  have hRel := C.rel_spec a ψ hEx
  refine ⟨hRel.1, ?_⟩
  intro y
  have hspec := hRel.2 y
  constructor
  · intro hy
    have hy' := hspec.mp hy
    exact ⟨(hmem y).mp hy'.1, hy'.2⟩
  · intro hy
    exact hspec.mpr ⟨(hmem y).mpr hy.1, hy.2⟩

theorem rep_filter (C : DescriptiveCore) {φ : C.Term → Prop} (hφ : Rep C φ) (ψ : C.Term → Prop) :
    Rep C (fun y => φ y ∧ ψ y) := by
  rcases hφ with ⟨a, ha⟩
  exact ⟨C.relDescr a ψ, represents_filter C ha ψ⟩

theorem rep_and (C : DescriptiveCore) {φ ψ : C.Term → Prop} (hφ : Rep C φ) (_hψ : Rep C ψ) :
    Rep C (fun y => φ y ∧ ψ y) := by
  exact rep_filter C hφ ψ

theorem rep_false_of_rep (C : DescriptiveCore) {φ : C.Term → Prop} (hφ : Rep C φ) :
    Rep C (fun _ : C.Term => False) := by
  rcases hφ with ⟨a, ha⟩
  have h := represents_filter C ha (fun x => x ≠ x)
  refine ⟨derivedEmpty C a, ?_⟩
  rcases h with ⟨hEx, hmem⟩
  refine ⟨hEx, ?_⟩
  intro y
  have hy := hmem y
  constructor
  · intro hMy
    have hy' := hy.mp hMy
    exact False.elim (hy'.2 rfl)
  · intro hf
    cases hf

theorem not_rep_true (C : DescriptiveCore) :
    ¬ Rep C (fun _ : C.Term => True) := by
  intro h
  rcases h with ⟨U, hU⟩
  have hExU : C.Ex U := hU.1
  have hAll : ∀ y : C.Term, C.Mem y U := by
    intro y
    have hy := (hU.2 y)
    exact (hy.mpr True.intro)
  exact no_universal C ⟨U, hExU, hAll⟩

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.rep_filter
#print axioms Descriptive.rep_and
#print axioms Descriptive.rep_false_of_rep
#print axioms Descriptive.not_rep_true
/- AXIOM_AUDIT_END -/

end Descriptive
