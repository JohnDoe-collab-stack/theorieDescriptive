import Descriptive.FiniteGlobal
import Descriptive.FiniteRelative
import Descriptive.FiniteSemanticsBuilder
import Descriptive.FiniteExtensionality
import Descriptive.FiniteTheorems

namespace Descriptive.Faithful

/-!
`Descriptive.FiniteMain` is the **public** entry point for the *finite internalized*
development.

It introduces no new theory; it only imports and re-exports:

- the finite cores (`FiniteGlobalCore`, `FiniteDescriptiveCore`);
- the key finitary hypotheses (`MembersOfCanonical`, `MembersOfInjective`);
- the finite-to-semantics bridge (`FiniteDescriptiveCore.toDescriptiveSemantics`);
- the main characterizations by `membersOf`;
- the packaged finite central theorems (`Descriptive.Faithful.FiniteDescriptiveCore.*`).

This file is intended as the compact "mathematical API surface" for subsequent work.
-/

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
`#print axioms` for the most public results exposed through this facade.
-/
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.russell_not_ex
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_profile
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_same_denotation
#print axioms Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_terms_distinct_same_denotation
/- AXIOM_AUDIT_END -/

end Descriptive.Faithful

