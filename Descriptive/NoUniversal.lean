import Descriptive.Core

namespace Descriptive

/-!
Relative Russell obstruction.

Even without any global comprehension principle, the *relative* description
operator already prevents the existence of a "universal" term `U` that contains
every term as a member, provided `U` exists.
-/

def relRussell (C : DescriptiveCore) (U : C.Term) : C.Term :=
  C.relDescr U (fun u => ¬ C.Mem u u)

theorem no_universal (C : DescriptiveCore) :
    ¬ ∃ U : C.Term, C.Ex U ∧ (∀ y : C.Term, C.Mem y U) := by
  intro h
  rcases h with ⟨U, hExU, hAll⟩
  let R : C.Term := relRussell C U
  have hspec :
      C.Mem R R ↔ (C.Mem R U ∧ ¬ C.Mem R R) :=
    (C.rel_spec U (fun u => ¬ C.Mem u u) hExU).2 (y := R)
  have hRU : C.Mem R U := hAll R
  have hmem : C.Mem R R ↔ ¬ C.Mem R R := by
    constructor
    · intro hRR
      exact (hspec.mp hRR).2
    · intro hnotRR
      exact hspec.mpr ⟨hRU, hnotRR⟩
  have hnot : ¬ C.Mem R R := by
    intro hRR
    exact (hmem.mp hRR) hRR
  have hRR : C.Mem R R := hmem.mpr hnot
  exact (hmem.mp hRR) hRR

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for exported results in this file.
-/
#print axioms Descriptive.no_universal
/- AXIOM_AUDIT_END -/

end Descriptive

