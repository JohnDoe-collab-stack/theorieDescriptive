import Descriptive.Syntax
import Descriptive.Semantics
import Descriptive.FreeLogic
import Descriptive.FaithfulRussell
import Descriptive.FaithfulTrajectory
import Descriptive.FaithfulExtensionality
import Descriptive.FiniteMain
import Descriptive.ConcreteInstance4

/-!
Facade module for the stable faithful nucleus (`Descriptive.Faithful`) and the
canonical finite internalized instance `Concrete4`.

This file introduces no new theory; it only imports and re-exports the stable
components:

- Syntax: `PrimConst`, `Formula1`, `Term`, `russell`, `derivedEmpty`
- Semantics: `DescriptiveSemantics`, `Holds`, `Ex`, `MemTerm`, `MemObjTerm`
- Russell obstruction: `russell_not_ex`
- Derived empty: `derivedEmpty_ex`, `derivedEmpty_denotes_emptyObj`,
  `derivedEmpty_emptyTerm`, `derivedEmpty_profile`
- External trajectory: `Trajectory`, `TrajPrecedes`, `primitive_precedes_derivedEmpty`
- Object extensionality: `ExtensionalObj`,
  `derivedEmpty_same_denotation_of_extensional`,
  `derivedEmpty_terms_distinct_same_denotation_of_extensional`
- Finite internalized layers + public facade: `Descriptive.FiniteMain` re-exports
  `FiniteGlobalCore`, `FiniteDescriptiveCore`, `MembersOfCanonical`,
  `MembersOfInjective`, the bridge `FiniteDescriptiveCore.toDescriptiveSemantics`,
  the `membersOf` characterizations, finite extensionality, and the packaged finite
  central theorems (`Descriptive.Faithful.FiniteDescriptiveCore.*`).
- Concrete canonical instance: `Descriptive.Faithful.Concrete4.concreteSemantics4`,
  and the characterization theorem
  `Descriptive.Faithful.Concrete4.ex_global_iff_membersOf`.
-/

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
This module only re-exports existing developments (no new declarations).
-/
-- (no declarations to audit in this file)
/- AXIOM_AUDIT_END -/
