# Noyau descriptif fidèle, couche finie internalisée et instance concrète canonique

## 1. Objet du document

Ce document décrit exactement ce qui est actuellement formalisé dans le dépôt Lean
`/mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems`, et seulement cela.
Il s’agit d’un noyau descriptif (syntaxe minimale + sémantique partielle), d’une couche abstraite
de compréhension finie internalisée, d’une façade publique finale, et d’une instance concrète canonique finie.

Portée explicite :

- aucune logique du premier ordre générale n’est formalisée ici (pas de variables, quantificateurs, etc.) ;
- aucune instance de ZFC n’est formalisée ;
- la compréhension globale est internalisée uniquement dans le cadre d’un univers fini énuméré, via un test de représentabilité ;
- la trajectoire est une structure externe sur les *termes*, distincte de l’extensionalité sur les *objets*.

Modules de référence (noms Lean) :

- noyau fidèle : `Descriptive.Faithful.Syntax`, `Descriptive.Faithful.Semantics`, `Descriptive.Faithful.FreeLogic`,
  `Descriptive.Faithful.FaithfulRussell`, `Descriptive.Faithful.FaithfulTrajectory`, `Descriptive.Faithful.FaithfulExtensionality` ;
- couche finie internalisée : `Descriptive.FiniteGlobal`, `Descriptive.FiniteRelative`, `Descriptive.FiniteSemanticsBuilder`,
  `Descriptive.FiniteExtensionality`, `Descriptive.FiniteTheorems`, `Descriptive.FiniteMain` ;
- façade générale : `Descriptive.FaithfulMain` ;
- instance canonique : `Descriptive.Faithful.Concrete4` (fichier `Descriptive/ConcreteInstance4.lean`).


## 2. Noyau fidèle minimal

Cette section correspond au noyau `Descriptive.Faithful.*` et à ses théorèmes abstraits, valables pour toute sémantique.

### 2.1 Syntaxe (module `Descriptive.Faithful.Syntax`)

La couche syntaxique est volontairement ciblée.
Elle contient uniquement ce qui est nécessaire aux constructions utilisées par les théorèmes du noyau.

- `Descriptive.Faithful.PrimConst` : constantes primitives (actuellement `PrimConst.mk : Nat → PrimConst`).
- `Descriptive.Faithful.Formula1` : mini-syntaxe de formules unairement ouvertes, avec constructeurs :
  - `Formula1.memSelf`
  - `Formula1.neqSelf`
  - `Formula1.memPrim : PrimConst → Formula1`
  - `Formula1.not`
  - `Formula1.and`
- `Descriptive.Faithful.Term` : mini-syntaxe de termes descriptifs, avec constructeurs :
  - `Term.prim : PrimConst → Term`
  - `Term.global : Formula1 → Term`
  - `Term.relative : Term → Formula1 → Term`

Deux termes syntaxiques distingués (définis dans `Descriptive.Faithful.Syntax`) :

- `Descriptive.Faithful.russell` : description globale associée à `not memSelf`.
- `Descriptive.Faithful.derivedEmpty c` : description relative construite sur base `c` avec la formule `neqSelf`
  (au niveau syntaxique : `Term.relative c Formula1.neqSelf`).

### 2.2 Sémantique partielle (module `Descriptive.Faithful.Semantics`)

Une sémantique est une donnée `S : Descriptive.Faithful.DescriptiveSemantics` comprenant :

- un type d’objets `S.Obj` ;
- une relation d’appartenance `S.MemObj : S.Obj → S.Obj → Prop` ;
- une dénotation partielle `S.denote : Term → Option S.Obj`.

La dénotation est *partielle* au sens où elle renvoie un `Option`.
Le prédicat de dénotation est :

- `Descriptive.Faithful.Ex S t` : il existe `a : S.Obj` tel que `S.denote t = some a`.

### 2.3 Appartenances dérivées et évaluation des formules

Le noyau introduit des notions dérivées, au niveau d’une sémantique `S` :

- `Descriptive.Faithful.MemTerm S s t` : relation “terme-à-terme”, définie via existence de dénotations et `S.MemObj`.
- `Descriptive.Faithful.MemObjTerm S y t` : relation “objet-à-terme”, définie via `S.denote t = some a` et `S.MemObj y a`.

L’évaluation des formules unairement ouvertes est donnée par :

- `Descriptive.Faithful.Holds` (dans `Descriptive.Faithful.Semantics`),
  qui évalue `Formula1` sur un objet, à partir de `MemObj` et d’une dénotation primitive (pour interpréter `memPrim`).

### 2.4 Obstruction russellienne (module `Descriptive.Faithful.FaithfulRussell`)

Théorème abstrait :

- `Descriptive.Faithful.russell_not_ex` : pour toute sémantique `S`, on a `¬ Descriptive.Faithful.Ex S Descriptive.Faithful.russell`.

Contenu : si `russell` dénotait, on obtiendrait une contradiction de la forme `p ↔ ¬ p` sur l’appartenance de l’objet à lui-même.

### 2.5 Vide dérivé (module `Descriptive.Faithful.FaithfulRussell`)

Les résultats abstraits suivants sont prouvés (tous sous hypothèse `Descriptive.Faithful.Ex S c`) :

- `Descriptive.Faithful.derivedEmpty_ex`
- `Descriptive.Faithful.derivedEmpty_denotes_emptyObj`
- `Descriptive.Faithful.derivedEmpty_emptyObjTerm`
- `Descriptive.Faithful.derivedEmpty_emptyTerm`
- `Descriptive.Faithful.derivedEmpty_profile`

Lecture minimale (sans renforcer les énoncés) :

- `derivedEmpty c` dénote (existence de dénotation) ;
- il dénote un objet sans membres au niveau de `S.MemObj` ;
- il n’a pas de membres au niveau `MemObjTerm`, et pas de membres au niveau `MemTerm`.

Distinction explicitement maintenue :

- le terme `derivedEmpty c` est un objet syntaxique (type `Term`) ;
- l’objet dénoté, quand il existe, est un élément de `S.Obj`.

### 2.6 Trajectoire externe sur les termes (module `Descriptive.Faithful.FaithfulTrajectory`)

La trajectoire est une structure *externe* sur les termes :

- `Descriptive.Faithful.Trajectory` : contient une fonction `h : Term → Nat`.
- `Descriptive.Faithful.TrajPrecedes` : relation définie par comparaison stricte des valeurs de `h`.

Théorème abstrait :

- `Descriptive.Faithful.primitive_precedes_derivedEmpty` : sous des hypothèses explicites sur `h`,
  on obtient `TrajPrecedes τ c (derivedEmpty c)`.

Point de portée : `Trajectory` porte sur les termes (`Term`), pas sur les objets (`S.Obj`).
Elle ne se confond donc pas avec une égalité extensionnelle au niveau des objets dénotés.

### 2.7 Extensionalité objet (module `Descriptive.Faithful.FaithfulExtensionality`)

L’extensionalité objet est un prédicat au niveau d’une sémantique `S` :

- `Descriptive.Faithful.ExtensionalObj S` : si deux objets ont les mêmes membres (au sens de `S.MemObj`), ils sont égaux.

Deux théorèmes abstraits centraux :

- `Descriptive.Faithful.derivedEmpty_same_denotation_of_extensional`
- `Descriptive.Faithful.derivedEmpty_terms_distinct_same_denotation_of_extensional`

Ils expriment, sous `ExtensionalObj S`, que :

- les vides dérivés ont la même dénotation (égalité dans `Option S.Obj`) ;
- il est possible d’avoir des termes `derivedEmpty c` et `derivedEmpty c'` distincts, mais une même dénotation,
  lorsque `c ≠ c'` et que les deux bases dénotent.


## 3. Couche finie internalisée abstraite

Cette section décrit la couche `Descriptive.Finite*`, qui formalise un schème finitaire et produit des résultats génériques réutilisables.

### 3.1 Compréhension globale finie internalisée (module `Descriptive.FiniteGlobal`)

La structure `Descriptive.Faithful.FiniteGlobalCore` encapsule les données minimales suivantes :

- un type fini d’objets `Obj` (fini au sens où il est *énuméré* par une liste) ;
- une relation `MemObj : Obj → Obj → Prop` ;
- une énumération `allObjs : List Obj` avec complétude (tout objet apparaît dans la liste) ;
- une fonction `membersOf : Obj → List Obj` et un lemme de correction `y ∈ membersOf a ↔ MemObj y a` ;
- une dénotation des primitives `denotePrim : PrimConst → Option Obj` ;
- une décidabilité explicite de `Holds` (`holdsDec`), utilisée pour calculer des extensions finies.

À partir de ces données, `FiniteGlobalCore` définit :

- l’extension finie d’une formule sur l’univers : `FiniteGlobalCore.extOfFormula` ;
- un test de représentabilité : `FiniteGlobalCore.representableExt` ;
- la dénotation globale internalisée : `FiniteGlobalCore.denoteGlobal`.

Caractérisation clé (niveau “global interne”) :

- `Descriptive.Faithful.FiniteGlobalCore.ex_denoteGlobal_iff_membersOf`

Lecture : une globale dénote (au sens “il existe `a` tel que `denoteGlobal φ = some a`”) si et seulement si
l’extension finie calculée est exactement la liste des membres `membersOf a` d’un objet existant du micro-univers.

### 3.2 Compréhension relative finie internalisée (module `Descriptive.FiniteRelative`)

La couche relative se formule au-dessus de `FiniteGlobalCore` :

- extension relative : `FiniteGlobalCore.relativeExt` (filtrage de `membersOf b` par la formule) ;
- dénotation relative internalisée : `FiniteGlobalCore.denoteRelative`.

Caractérisation clé (niveau “relative interne”) :

- `Descriptive.Faithful.FiniteGlobalCore.ex_denoteRelative_iff_membersOf`

Lecture : une relative dénote si et seulement si l’extension relative filtrée est représentée par les membres d’un objet existant.

### 3.3 Passage à une sémantique descriptive (module `Descriptive.FiniteSemanticsBuilder`)

La structure `Descriptive.Faithful.FiniteDescriptiveCore` étend `FiniteGlobalCore` par une hypothèse de clôture uniforme :

- représentabilité de toutes les extensions relatives (champ `relative_repr`).

Elle fournit alors un constructeur :

- `Descriptive.Faithful.FiniteDescriptiveCore.toDescriptiveSemantics`

qui fabrique une `Descriptive.Faithful.DescriptiveSemantics` dont la dénotation sur les termes suit la règle :

- primitives via `denotePrim` ;
- globales via `FiniteGlobalCore.denoteGlobal` ;
- relatives via `FiniteGlobalCore.denoteRelative` quand la base dénote.

Deux caractérisations au niveau `Ex` (niveau sémantique des termes) :

- `Descriptive.Faithful.FiniteDescriptiveCore.ex_global_iff_membersOf`
- `Descriptive.Faithful.FiniteDescriptiveCore.ex_relative_of_denote_iff_membersOf`

### 3.4 Extensionalité finie générique (module `Descriptive.FiniteExtensionality`)

La couche `Descriptive.FiniteExtensionality` isole des hypothèses finies simples sur `membersOf`, puis en déduit une extensionalité objet
au niveau de la sémantique construite.

Noms Lean publics à retenir :

- hypothèses :
  - `Descriptive.Faithful.FiniteGlobalCore.MembersOfCanonical`
  - `Descriptive.Faithful.FiniteGlobalCore.MembersOfInjective`
- lemme de raccord (passage de l’égalité extensionnelle de `MemObj` à une égalité de listes `membersOf`) :
  - `Descriptive.Faithful.FiniteGlobalCore.membersOf_eq_of_memObj_iff`
- théorème d’extensionalité objet au niveau de `toDescriptiveSemantics` :
  - `Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj_toDescriptiveSemantics`


## 4. API publique finale

### 4.1 Façade finie (module `Descriptive.FiniteMain`)

`Descriptive.FiniteMain` est une façade publique pour la théorie finie internalisée.
Elle n’ajoute aucune puissance logique : c’est un module d’imports et de documentation, avec audit d’axiomes sur les résultats centraux.

Les résultats explicitement audités dans `Descriptive.FiniteMain` (noms Lean) sont :

- `Descriptive.Faithful.FiniteDescriptiveCore.russell_not_ex`
- `Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_profile`
- `Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj`
- `Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_same_denotation`
- `Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_terms_distinct_same_denotation`

### 4.2 Paquet central fini (module `Descriptive.FiniteTheorems`)

Le module `Descriptive.FiniteTheorems` regroupe des corollaires génériques au niveau de
`S := FiniteDescriptiveCore.toDescriptiveSemantics C`.

Les théorèmes publics correspondants (noms Lean exacts) sont :

- `Descriptive.Faithful.FiniteDescriptiveCore.russell_not_ex`
- `Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_profile`
- `Descriptive.Faithful.FiniteDescriptiveCore.extensionalObj`
- `Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_same_denotation`
- `Descriptive.Faithful.FiniteDescriptiveCore.derivedEmpty_terms_distinct_same_denotation`

Ils réutilisent explicitement :

- les théorèmes abstraits du noyau fidèle (`Descriptive.Faithful.*`) ;
- la caractérisation et la construction finitaires (`Descriptive.Finite*`).

### 4.3 Façade générale (module `Descriptive.FaithfulMain`)

`Descriptive.FaithfulMain` assemble :

1) le noyau fidèle (`Descriptive.Faithful.*`) ;
2) la couche finie internalisée (`Descriptive.Finite*`) via la façade `Descriptive.FiniteMain` ;
3) les instances concrètes, dont `Descriptive.Faithful.Concrete4`.

Point de portée : `Concrete4` est une instance canonique, pas la théorie elle-même.


## 5. Instance canonique `Concrete4` (module `Descriptive.Faithful.Concrete4`)

Cette section est alignée sur le fichier `Descriptive/ConcreteInstance4.lean`.

### 5.1 Univers fini et appartenance

`Concrete4` fixe un type inductif fini d’objets (Lean : `Descriptive.Faithful.Concrete4.Obj`) avec quatre constructeurs :

- `Obj.empty`
- `Obj.singletonEmpty`
- `Obj.singletonSingletonEmpty`
- `Obj.pairEmptySingleton`

La relation d’appartenance est `Descriptive.Faithful.Concrete4.MemObj`.

### 5.2 Énumération et membres

`Concrete4` fournit :

- `Descriptive.Faithful.Concrete4.allObjs : List Obj` (énumération) ;
- `Descriptive.Faithful.Concrete4.membersOf : Obj → List Obj` ;
- des lemmes reliant `membersOf` et `MemObj`.

### 5.3 Dénotation primitive et décidabilité de `Holds`

`Concrete4` fixe une dénotation des primitives (fonction locale `denotePrimOpt`) et une décidabilité explicite :

- `holdsDec : ∀ φ x, Decidable (Holds MemObj denotePrimOpt φ x)`.

### 5.4 Représentabilité des relatives et construction du cœur fini

`Concrete4` construit :

- `finiteGlobalCore : Descriptive.Faithful.FiniteGlobalCore`
- `finiteDescriptiveCore4 : Descriptive.Faithful.FiniteDescriptiveCore`
  (en fournissant la preuve de représentabilité uniforme des extensions relatives).

Puis elle définit :

- `concreteSemantics4 : Descriptive.Faithful.DescriptiveSemantics`
  comme `FiniteDescriptiveCore.toDescriptiveSemantics finiteDescriptiveCore4`.

### 5.5 Corollaires concrets principaux (noms Lean exacts)

Caractérisation globale par `membersOf` :

- `Descriptive.Faithful.Concrete4.ex_global_iff_membersOf`

Existence d’au moins une globale dénotante :

- `Descriptive.Faithful.Concrete4.some_global_ex_concrete4`

Russell dans l’instance :

- `Descriptive.Faithful.Concrete4.russell_not_ex_concrete4`

Vide dérivé (existence et valeur de dénotation) :

- `Descriptive.Faithful.Concrete4.derivedEmpty_c0_ex`
- `Descriptive.Faithful.Concrete4.denote_derivedEmpty_empty`

Extensionalité objet dans l’instance (obtenue via la couche finie abstraite) :

- `Descriptive.Faithful.Concrete4.concrete4_extensional`

Même dénotation des vides dérivés (et variante “termes distincts, même dénotation”) :

- `Descriptive.Faithful.Concrete4.derivedEmpty_c0_c1_same_denotation`
- `Descriptive.Faithful.Concrete4.derivedEmpty_c0_c1_distinct_terms_same_denotation`

Portée explicite : ces résultats concrets sont des corollaires spécialisés des résultats génériques
de la couche finie (`Descriptive.Finite*`) et du paquet central (`Descriptive.FiniteTheorems`).


## 6. Ce qui est effectivement acquis

Ce qui est formalisé à ce stade, au sens strict :

- une mini-syntaxe ciblée (`PrimConst`, `Formula1`, `Term`) et deux termes distingués (`russell`, `derivedEmpty`) ;
- une sémantique partielle constructive via `Option` (`DescriptiveSemantics` et `Ex`) ;
- les notions `MemTerm`, `MemObjTerm`, et l’évaluation `Holds` ;
- l’obstruction russellienne abstraite (`Descriptive.Faithful.russell_not_ex`) ;
- le vide dérivé abstrait (profil complet via les théorèmes listés en 2.5) ;
- une trajectoire externe sur les termes et un résultat de précédence (`Descriptive.Faithful.primitive_precedes_derivedEmpty`) ;
- l’extensionalité au niveau des objets (`Descriptive.Faithful.ExtensionalObj`) et ses conséquences sur la dénotation des vides dérivés ;
- une couche finie internalisée abstraite (globales + relatives), avec caractérisations par `membersOf` ;
- un constructeur générique `FiniteDescriptiveCore.toDescriptiveSemantics` ;
- un paquet central fini (`Descriptive.FiniteTheorems`) ;
- une instance canonique finie `Concrete4` et ses corollaires concrets listés en section 5.


## 7. Ce qui n’est pas formalisé

Ce qui n’est pas présent dans l’état actuel (et ne doit pas être attribué au code) :

- une logique du premier ordre générale (variables, quantificateurs, substitution, théorie des paramètres, etc.) ;
- une compréhension globale infinie (au-delà du schème finitaire énuméré) ;
- une instance de ZFC ou une théorie des ensembles “complète” ;
- une construction où les objets dénotés seraient un quotient des termes (aucune couche de quotient n’est introduite ici) ;
- une identification générale “égalité de dénotation = égalité syntaxique” (au contraire, la dissociation est un point central).


## 8. Conclusion courte

Le noyau `Descriptive.Faithful` formalise une syntaxe minimale, une sémantique partielle (via `Option`), des résultats abstraits
(Russell, vide dérivé, trajectoire, extensionalité objet) et distingue explicitement termes et objets dénotés.
La couche `Descriptive.Finite*` internalise la compréhension globale et relative sur un univers fini énuméré, fournit un pont générique
vers `DescriptiveSemantics`, et regroupe les théorèmes centraux dans un paquet stable.
`Concrete4` est une instance canonique finie de ce schème, présentée comme telle.


## 9. Checklist de fidélité

1) Le document ne décrit que des modules existants : `Descriptive.Faithful.*`, `Descriptive.Finite*`, `Descriptive.FiniteMain`, `Descriptive.FaithfulMain`, `Descriptive.Faithful.Concrete4`.
2) Aucun énoncé n’est présenté comme plus fort que sa version Lean (les noms Lean exacts sont explicitement listés).
3) Aucune mention d’une FOL générale (variables/quantificateurs) n’est introduite.
4) Aucune mention d’une formalisation de ZFC n’est introduite.
5) La dénotation est décrite comme partielle via `Option` (et `Ex` comme existence de `some`).
6) La distinction termes/objets est explicitement maintenue (types `Term` vs `S.Obj`).
7) La trajectoire est explicitement décrite comme structure externe sur `Term`.
8) L’extensionalité est explicitement décrite comme propriété sur `S.Obj` (pas sur `Term`).
9) La couche finie est décrite comme un schème d’énumération + calcul d’extensions + représentabilité (pas comme compréhension infinie).
10) `Concrete4` est décrite comme micro-univers fini internalisé et comme instance, non comme théorie générale.
