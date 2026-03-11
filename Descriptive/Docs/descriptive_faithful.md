---
# Noyau descriptif fidèle et instance concrète finie internalisée

Ce document présente exactement ce qui est formalisé dans le namespace Lean `Descriptive.Faithful`, ainsi que l’instance concrète finie `Descriptive.Faithful.Concrete4`. Le texte est volontairement serré et ne dépasse pas le contenu effectivement défini et démontré.

Les fichiers de référence sont :

- noyau abstrait/fidèle : `Descriptive.Faithful.Syntax`, `Descriptive.Faithful.Semantics`, `Descriptive.Faithful.FreeLogic`, `Descriptive.Faithful.FaithfulRussell`, `Descriptive.Faithful.FaithfulTrajectory`, `Descriptive.Faithful.FaithfulExtensionality` ;
- instance concrète canonique finie internalisée : `Descriptive.Faithful.Concrete4` (fichier `Descriptive/ConcreteInstance4.lean`).

Le document ne présuppose pas de logique du premier ordre générale ni de théorie des ensembles au sens usuel. La syntaxe est une mini-syntaxe ciblée, et la sémantique est partielle et constructive via une dénotation de type `Option`.

---

## Section 1 — Objet du document

L’objet de ce texte est double.

Premièrement, il fixe un noyau descriptif fidèle déjà formalisé en Lean, dans lequel on distingue explicitement :

- une couche syntaxique minimale (termes descriptifs et formules unairement ouvertes) ;
- une sémantique partielle (un terme peut ne pas dénoter) ;
- des notions dérivées de “dénotation” et “membership induit” au niveau des termes ;
- une trajectoire externe portant sur les termes (structure sur la syntaxe) ;
- une extensionalité portant sur les objets dénotés.

Deuxièmement, il décrit une instance concrète finie `Concrete4` dont le point central est le suivant : la dénotation des descriptions globales n’est pas donnée par une table ad hoc, mais calculée par une procédure finie d’extension et de représentabilité interne. Autrement dit, dans `Concrete4`, une description globale dénote exactement quand son extension finie est représentée par un objet déjà présent dans le micro-univers.

Dans tout le document, on se limite volontairement à ce qui est formalisé. En particulier, on ne présente pas comme acquis une logique du premier ordre générale, une syntaxe complète avec variables et quantificateurs, une instance zfcienne, ni une compréhension globale infinie.

---

## Section 2 — Syntaxe minimale ciblée

La couche syntaxique est définie dans `Descriptive.Faithful.Syntax`. Elle est intentionnellement ciblée : elle contient uniquement ce qui est nécessaire aux constructions et preuves du noyau.

### 2.1 Constantes primitives (PrimConst)

Le type `Descriptive.Faithful.PrimConst` est un type de constantes primitives. Dans la formalisation actuelle, il est introduit par un unique constructeur `PrimConst.mk : Nat → PrimConst`. Il sert uniquement à former des termes primitifs.

### 2.2 Formules unairement ouvertes (Formula1)

Le type `Descriptive.Faithful.Formula1` est une mini-syntaxe de formules unairement ouvertes. Il a exactement les constructeurs suivants :

- `memSelf` : lecture informelle “x appartient à x” ;
- `neqSelf` : lecture informelle “x est différent de x” ;
- `memPrim p` : lecture informelle “x appartient au donneur primitif p” ;
- `not φ` : négation ;
- `and φ ψ` : conjonction.

Cette syntaxe n’est pas une syntaxe générale du premier ordre : il n’y a ni variables explicites, ni quantificateurs, ni symboles de fonction, ni schémas de paramètres. Elle est suffisante pour les résultats du noyau présentés plus loin.

### 2.3 Termes (Term)

Le type `Descriptive.Faithful.Term` a exactement trois constructeurs :

- `prim p` : terme primitif, formé à partir d’une constante primitive `p : PrimConst` ;
- `global φ` : description globale, formée à partir d’une formule `φ : Formula1` ;
- `relative t φ` : description relative, formée à partir d’un terme de base `t : Term` et d’une formule `φ : Formula1`.

### 2.4 Deux termes distingués : russell et derivedEmpty

Deux termes syntaxiques sont définis dans `Descriptive.Faithful.Syntax` et utilisés dans les théorèmes du noyau.

1) Terme de Russell (`Descriptive.Faithful.russell`).

- Définition syntaxique : `russell = Term.global (Formula1.not Formula1.memSelf)`.
- Lecture informelle : “la description globale des objets qui ne s’appartiennent pas à eux-mêmes”.

2) Vide dérivé (`Descriptive.Faithful.derivedEmpty c`).

- Définition syntaxique : `derivedEmpty c = Term.relative c Formula1.neqSelf`.
- Lecture syntaxique stricte : c’est la description relative construite sur la base `c` avec la formule `neqSelf`.
- Lecture sémantique (quand elle est applicable) : la spécification relative fournit que l’appartenance est une conjonction “appartenance au base” et “satisfaction de `neqSelf`”.

---

## Section 3 — Sémantique partielle constructive

La couche sémantique est définie dans `Descriptive.Faithful.Semantics`. Elle est constructive au sens suivant : la dénotation est une fonction partielle codée par un `Option`.

### 3.1 Structure DescriptiveSemantics

Une sémantique est une donnée `S : Descriptive.Faithful.DescriptiveSemantics` constituée de :

- un type des objets `S.Obj` ;
- une relation d’appartenance sur les objets `S.MemObj : S.Obj → S.Obj → Prop` ;
- une dénotation partielle `S.denote : Term → Option S.Obj`.

La structure comporte aussi deux champs de spécification :

- `global_spec` : si une description globale `Term.global φ` dénote un objet `a`, alors la membership dans `a` est donnée par la satisfaction de `φ` (évaluée par `Holds`) ;
- `rel_ex` et `rel_spec` : si le terme de base d’une description relative dénote, alors la description relative dénote, et sa membership correspond à une intersection (membership dans le base et satisfaction de la formule).

Dans ce document, on ne leur attribue pas de contenu au-delà de ces énoncés.

### 3.2 Lecture de Ex

La proposition `Descriptive.Faithful.Ex S t` signifie que le terme `t : Term` dénote, au sens où il existe un objet `a : S.Obj` tel que `S.denote t = some a`.

Autrement dit, `Ex` n’affirme pas que tout terme dénote : la dénotation est partielle.

### 3.3 Appartenances dérivées : MemTerm et MemObjTerm

Deux prédicats dérivés expriment des formes de membership “induites” par la dénotation :

- `Descriptive.Faithful.MemTerm S s t` : il existe des objets `a b` tels que `s` dénote `a`, `t` dénote `b`, et `S.MemObj a b` ;
- `Descriptive.Faithful.MemObjTerm S y t` : il existe un objet `a` tel que `t` dénote `a`, et `S.MemObj y a`.

Ces définitions garantissent que la membership au niveau des termes ne s’exprime que via des objets effectivement dénotés.

### 3.4 Évaluation des formules : Holds

La fonction `Descriptive.Faithful.Holds` évalue une formule unaire `φ : Formula1` sur un objet `x : S.Obj`. Elle dépend :

- de la relation `MemObj` ;
- d’une dénotation des primitives `denotePrim : PrimConst → Option S.Obj` (dans les champs de `DescriptiveSemantics`, on utilise `fun p => S.denote (Term.prim p)`).

Pour le nouveau constructeur, la lecture formalisée est la suivante :

- `Holds MemObj denotePrim (memPrim p) x` signifie : si `denotePrim p = some a`, alors `MemObj x a`, sinon c’est faux.

Ainsi, `memPrim p` exprime bien une propriété “d’appartenance à un donneur primitif”, en se référant à la dénotation des primitives.

---

## Section 4 — Théorèmes abstraits du noyau fidèle

Les résultats de cette section sont prouvés abstraitement, pour toute sémantique `S : DescriptiveSemantics`. Ils sont formalisés dans `Descriptive.Faithful.FaithfulRussell`, `Descriptive.Faithful.FaithfulTrajectory` et `Descriptive.Faithful.FaithfulExtensionality`.

### 4.1 Obstruction russellienne (russell_not_ex)

Théorème (Lean : `Descriptive.Faithful.russell_not_ex`). Pour toute sémantique `S`, le terme de Russell ne dénote pas :

- `non (Ex S russell)`.

Idée de preuve (fidèle à Lean). Supposons `Ex S russell`. Alors il existe un objet `a` tel que `S.denote russell = some a`. En appliquant `S.global_spec` à la formule `not memSelf` et à l’objet `a`, on obtient une équivalence qui force, au point `y = a`, une contradiction de la forme :

- `S.MemObj a a` ssi `non (S.MemObj a a)`.

Ceci produit une contradiction directe. Conclusion : la forme syntaxique `russell` existe, mais elle ne dénote pas.

### 4.2 Vide dérivé (derivedEmpty_*)

Dans toute sémantique `S`, pour tout terme `c : Term` tel que `Ex S c`, on dispose des résultats suivants.

1) Existence de dénotation (Lean : `Descriptive.Faithful.derivedEmpty_ex`) :

- `Ex S (derivedEmpty c)`.

2) Vacuité de l’objet dénoté (Lean : `Descriptive.Faithful.derivedEmpty_denotes_emptyObj`) :

- il existe un objet `a : S.Obj` tel que `S.denote (derivedEmpty c) = some a` et tel que tout objet `y` n’appartient pas à `a`.

3) Vacuité au niveau `MemObjTerm` (Lean : `Descriptive.Faithful.derivedEmpty_emptyObjTerm`) :

- pour tout `y : S.Obj`, `non (MemObjTerm S y (derivedEmpty c))`.

4) Vacuité au niveau `MemTerm` (Lean : `Descriptive.Faithful.derivedEmpty_emptyTerm`) :

- pour tout terme `y : Term`, `non (MemTerm S y (derivedEmpty c))`.

5) Regroupement (Lean : `Descriptive.Faithful.derivedEmpty_profile`) :

- `Ex S (derivedEmpty c)` et pour tout terme `y`, `non (MemTerm S y (derivedEmpty c))`.

Idée de preuve (fidèle à Lean). La formule `neqSelf` est interprétée comme `x ≠ x`. Donc, si un objet `y` était membre de l’objet dénoté par `derivedEmpty c`, la spécification relative `rel_spec` fournirait en particulier la satisfaction de `neqSelf` par `y`, donc une preuve de `y ≠ y`. Cela contredit `rfl`. On obtient ainsi la vacuité de l’objet dénoté, puis l’absence de membres au niveau `MemObjTerm` et `MemTerm`.

Le point important est la distinction formelle :

- le terme `derivedEmpty c` (syntaxe) ;
- l’objet `a` qu’il dénote (sémantique) ;
- la propriété “a est vide” au niveau de `MemObj`.

### 4.3 Trajectoire externe (Trajectory, TrajPrecedes, primitive_precedes_derivedEmpty)

La couche de trajectoire est définie dans `Descriptive.Faithful.FaithfulTrajectory`.

- `Trajectory` est une structure avec un champ `h : Term → Nat`.
- `TrajPrecedes τ s t` est défini par `τ.h s < τ.h t`.

Théorème (Lean : `Descriptive.Faithful.primitive_precedes_derivedEmpty`). Si `τ` est une trajectoire, si `c : Term` est un terme tel que `τ.h c = 0`, et si l’on a la règle `τ.h (relative t φ) = succ (τ.h t)` pour toute construction relative, alors :

- `TrajPrecedes τ c (derivedEmpty c)`.

La trajectoire porte sur les termes : elle est une structure syntaxique sur `Term`, et ne dépend pas de l’égalité extensionnelle des objets dénotés.

### 4.4 Extensionalité objet et dissociation terme-dénotation

L’extensionalité objet est définie dans `Descriptive.Faithful.FaithfulExtensionality` :

- `ExtensionalObj S` signifie : pour tous objets `a b`, si `MemObj y a` ssi `MemObj y b` pour tout `y`, alors `a = b`.

Deux résultats sont ensuite établis.

1) Égalité de dénotation des vides dérivés (Lean : `Descriptive.Faithful.derivedEmpty_same_denotation_of_extensional`) :

- si `ExtensionalObj S` et si `c` et `c'` dénotent, alors `S.denote (derivedEmpty c) = S.denote (derivedEmpty c')`.

L’énoncé porte sur l’égalité des valeurs de dénotation dans `Option S.Obj`. Dans la preuve Lean, cette égalité provient du fait que les objets dénotés par les deux vides dérivés sont tous deux vides, donc extensionnellement égaux, donc égaux par extensionalité.

2) Termes distincts, même dénotation (Lean : `Descriptive.Faithful.derivedEmpty_terms_distinct_same_denotation_of_extensional`) :

- si `c ≠ c'`, alors `derivedEmpty c ≠ derivedEmpty c'`, tout en conservant l’égalité de dénotation précédente.

On obtient ainsi explicitement :

- égalité de dénotation n’implique pas égalité des termes ;
- l’extensionalité agit au niveau des objets, et ne force pas l’identification syntaxique des termes ;
- la trajectoire, étant une structure sur les termes, n’est pas contrainte par l’égalité de dénotation.

---

## Section 5 — Instance concrète canonique Concrete4

L’instance `Descriptive.Faithful.Concrete4` est une sémantique finie et constructive. Son point central est l’internalisation de la compréhension globale : la dénotation de `Term.global φ` est obtenue par calcul effectif de l’extension de `φ` sur un univers fini, puis test de représentabilité par un objet existant.

### 5.1 Univers fini choisi

Dans `Concrete4`, le type des objets est un type inductif fini (Lean : `Descriptive.Faithful.Concrete4.Obj`) avec quatre constructeurs :

- `empty` : lecture informelle “l’ensemble vide” ;
- `singletonEmpty` : lecture informelle “le singleton de empty”, c’est-à-dire un objet dont l’unique membre est `empty` ;
- `singletonSingletonEmpty` : lecture informelle “le singleton de singletonEmpty” ;
- `pairEmptySingleton` : lecture informelle “la paire {empty, singletonEmpty}”.

Ces lectures sont guidées par la relation d’appartenance définie ci-dessous.

### 5.2 Relation d’appartenance

La relation `Concrete4.MemObj : Obj → Obj → Prop` est définie par cas et réalise la lecture ensembliste suivante :

- aucun objet n’appartient à `empty` ;
- `y ∈ singletonEmpty` ssi `y = empty` ;
- `y ∈ singletonSingletonEmpty` ssi `y = singletonEmpty` ;
- `y ∈ pairEmptySingleton` ssi `y = empty` ou `y = singletonEmpty`.

### 5.3 Énumération finie des objets

Une liste explicite de tous les objets est fixée (Lean : `Concrete4.allObjs`) :

- `allObjs = [empty, singletonEmpty, singletonSingletonEmpty, pairEmptySingleton]`.

Cette liste est utilisée comme domaine fini pour le calcul d’extensions.

### 5.4 Membres de chaque objet : membersOf

Une fonction `Concrete4.membersOf : Obj → List Obj` donne la liste des membres de chaque objet, en accord exact avec `MemObj`. Les cas sont :

- `membersOf empty = []` ;
- `membersOf singletonEmpty = [empty]` ;
- `membersOf singletonSingletonEmpty = [singletonEmpty]` ;
- `membersOf pairEmptySingleton = [empty, singletonEmpty]`.

Un lemme de correction relie explicitement `membersOf` et `MemObj` (Lean : `Concrete4.mem_membersOf_iff`) :

- `y` appartient à la liste `membersOf a` ssi `MemObj y a`.

### 5.5 Extension finie d’une formule : holdsBool et extOfFormula

Pour calculer l’extension d’une formule, `Concrete4` introduit :

- une décidabilité explicite `holdsDec` de la satisfaction `Holds MemObj denotePrimOpt φ y` ;
- une version booléenne `holdsBool φ y`, obtenue en inspectant `holdsDec` ;
- une fonction d’extension finie `extOfFormula φ`, définie comme le filtrage de `allObjs` par `holdsBool φ`.

Un lemme de correction (Lean : `Concrete4.mem_extOfFormula_iff`) établit que, pour tout objet `y` :

- `y` appartient à `extOfFormula φ` ssi `Holds MemObj denotePrimOpt φ y`.

Ainsi, l’extension de `φ` est calculée explicitement sur l’univers fini.

### 5.6 Représentabilité interne : representableExt et denoteGlobal

La représentabilité est une recherche finie. On définit :

- `representableExtFrom` : une fonction qui parcourt une liste d’objets et cherche un objet `a` tel que `membersOf a = L` ;
- `representableExt L = representableExtFrom allObjs L`.

La compréhension globale internalisée est alors définie par :

- `denoteGlobal φ = representableExt (extOfFormula φ)`.

Il s’agit d’une interprétation finie et interne de la description globale.

Un lemme central (Lean : `Concrete4.denoteGlobal_spec`) dit :

- si `denoteGlobal φ = some a`, alors pour tout `y`, `MemObj y a` ssi `Holds MemObj denotePrimOpt φ y`.

Formulation conceptuelle (sans renforcer l’énoncé Lean) : lorsqu’une description globale dénote, l’objet dénoté est précisément celui dont la liste de membres coïncide avec l’extension finie calculée de la formule.

### 5.7 Fonction totale à valeurs partielles sur les termes

La dénotation totale `Concrete4.denote : Term → Option Obj` est définie par récurrence sur `Term` :

- pour `prim p`, la dénotation est donnée par `denotePrimOpt p` ;
- pour `global φ`, la dénotation est `denoteGlobal φ` ;
- pour `relative t φ`, on dénote seulement si `t` dénote ; dans ce cas, on renvoie `some (denoteRelative b φ)` où `b` est l’objet dénoté par `t`.

La dénotation relative utilise une fonction explicite `denoteRelative` qui, pour chaque base `b : Obj`, calcule un objet “intersecté” en fonction des valeurs de `holdsDec φ` sur les membres possibles de `b`. Un lemme `mem_denoteRelative_iff` établit exactement la spécification relative requise par `DescriptiveSemantics.rel_spec`.

Enfin, la structure `concreteSemantics4 : DescriptiveSemantics` est obtenue en regroupant ces définitions, avec une preuve de `global_spec` dérivée de `denoteGlobal_spec` et une preuve de `rel_ex` et `rel_spec` dérivées de `denoteRelative` et `mem_denoteRelative_iff`.

---

## Section 6 — Théorèmes concrets de Concrete4

Dans `Concrete4`, on fixe deux donneurs primitifs concrets :

- `c0 = Term.prim (PrimConst.mk 0)` (Lean : `Concrete4.c0`) ;
- `c1 = Term.prim (PrimConst.mk 1)` (Lean : `Concrete4.c1`).

Ils dénotent dans `concreteSemantics4` (Lean : `Concrete4.c0_ex`, `Concrete4.c1_ex`), et ils sont syntactiquement distincts (Lean : `Concrete4.c0_ne_c1`).

### 6.1 Une globale effectivement dénotante (some_global_ex_concrete4)

On introduit une formule concrète :

- `φ0 = memPrim (PrimConst.mk 0)` (Lean : `Concrete4.φ0`).

Théorème (Lean : `Concrete4.some_global_ex_concrete4`) :

- `Ex concreteSemantics4 (Term.global φ0)`.

Interprétation exacte : l’extension finie de `φ0` sur `allObjs` est représentée par un objet du micro-univers ; ici, elle correspond à la liste `[empty]`, représentée par l’objet `singletonEmpty` via `membersOf`.

### 6.2 Russell dans l’instance concrète (russell_not_ex_concrete4)

Théorème (Lean : `Concrete4.russell_not_ex_concrete4`) :

- `non (Ex concreteSemantics4 russell)`.

Le théorème `russell_not_ex_concrete4` est obtenu par spécialisation du résultat abstrait `russell_not_ex` à l’instance `concreteSemantics4`. Dans cette instance, la dénotation globale est bien internalisée via `denoteGlobal`, mais l’énoncé retenu ici est simplement que `russell` ne dénote pas.

### 6.3 Vide dérivé (derivedEmpty_c0_ex, derivedEmpty_c0_emptyObj, etc.)

On dispose des résultats suivants (Lean : `Concrete4.derivedEmpty_c0_ex`, `Concrete4.derivedEmpty_c1_ex`) :

- `Ex concreteSemantics4 (derivedEmpty c0)` ;
- `Ex concreteSemantics4 (derivedEmpty c1)`.

Et des versions concrètes de vacuité au niveau des objets dénotés (Lean : `Concrete4.derivedEmpty_c0_emptyObj`, `Concrete4.derivedEmpty_c1_emptyObj`) :

- `derivedEmpty c0` dénote un objet `a` tel que tout objet `y` n’appartient pas à `a` ;
- idem pour `derivedEmpty c1`.

Dans `Concrete4`, ces théorèmes sont établis en montrant explicitement que `derivedEmpty c` dénote `empty`, via le fait que `neqSelf` est toujours fausse et que la dénotation relative calcule alors l’objet vide.

### 6.4 Gain d’expressivité dû à memPrim (memPrim0_distinguishes_objects)

Le théorème (Lean : `Concrete4.memPrim0_distinguishes_objects`) affirme un fait concret de distinction :

- la formule `memPrim (PrimConst.mk 0)` est satisfaite par `empty` ;
- elle n’est pas satisfaite par `singletonEmpty`.

Ainsi, l’extension `memPrim` de la mini-syntaxe `Formula1` n’est pas décorative : elle permet effectivement de distinguer des objets dans l’univers fini.

### 6.5 Trajectoire concrète (concreteTrajectory4, c0_precedes_derivedEmpty_c0)

Une trajectoire explicite sur les termes est définie (Lean : `Concrete4.concreteTrajectory4`) : la fonction `h : Term → Nat` compte le nombre de constructions `relative` imbriquées, en donnant 0 aux termes primitifs et globaux.

On obtient alors (Lean : `Concrete4.c0_precedes_derivedEmpty_c0`) :

- `TrajPrecedes concreteTrajectory4 c0 (derivedEmpty c0)`.

Ce résultat illustre que la trajectoire est une structure sur les termes, donc indépendante de toute considération extensionnelle au niveau des objets.

### 6.6 Extensionalité concrète (concrete4_extensional)

Le théorème (Lean : `Concrete4.concrete4_extensional`) établit :

- `ExtensionalObj concreteSemantics4`.

Autrement dit, dans l’univers fini de `Concrete4`, les objets sont déterminés par leur extension au sens de `MemObj`.

### 6.7 Termes distincts, même dénotation

Deux résultats concrets montrent explicitement la dissociation terme/dénotation.

1) Même dénotation pour les deux vides dérivés (Lean : `Concrete4.derivedEmpty_c0_c1_same_denotation`) :

- `concreteSemantics4.denote (derivedEmpty c0) = concreteSemantics4.denote (derivedEmpty c1)`.

2) Termes distincts, même dénotation (Lean : `Concrete4.derivedEmpty_c0_c1_distinct_terms_same_denotation`) :

- `derivedEmpty c0 ≠ derivedEmpty c1` et pourtant les dénotations ci-dessus sont égales.

Ce couple de résultats formalise, dans une instance concrète, que l’égalité de dénotation n’implique pas l’égalité syntaxique des termes. En particulier, une structure de trajectoire sur `Term` n’est pas contrainte par une extensionalité sur `Obj`.

---

## Section 7 — Portée exacte du résultat

### 7.1 Ce qui est effectivement acquis

Les éléments suivants sont effectivement formalisés :

- une mini-syntaxe ciblée `PrimConst`, `Formula1`, `Term`, avec les constructions `russell` et `derivedEmpty` ;
- une sémantique partielle constructive `DescriptiveSemantics` via `denote : Term → Option Obj` ;
- la notion de dénotation `Ex`, et des appartenances induites `MemTerm` et `MemObjTerm` ;
- une évaluation `Holds` des formules, incluant `memPrim` ;
- l’obstruction russellienne `russell_not_ex` ;
- le vide dérivé et son profil de vacuité (`derivedEmpty_ex`, `derivedEmpty_denotes_emptyObj`, `derivedEmpty_emptyObjTerm`, `derivedEmpty_emptyTerm`, `derivedEmpty_profile`) ;
- une trajectoire externe sur les termes (`Trajectory`, `TrajPrecedes`, `primitive_precedes_derivedEmpty`) ;
- une extensionalité au niveau des objets (`ExtensionalObj`) et des résultats montrant la dissociation “termes distincts / même dénotation” sous extensionalité.

L’instance `Concrete4` fournit en plus :

- un micro-univers fini d’objets set-like ;
- une compréhension globale internalisée par calcul d’extension et recherche de représentabilité ;
- des théorèmes concrets montrant une globale dénotante, Russell non dénotant, le vide dérivé, une trajectoire explicite, et des termes distincts de même dénotation.

### 7.2 Ce qui n’est pas encore formalisé

Les points suivants ne sont pas formalisés dans l’état actuel :

- une syntaxe générale de logique du premier ordre (variables, quantificateurs, égalité, connecteurs généraux) ;
- une logique libre complète du premier ordre ;
- une instance zfcienne ou une satisfaction d’axiomes de théorie des ensembles ;
- une théorie générale des paramètres des descriptions ;
- une construction interne complète des descriptions globales/relatives à partir d’un modèle ensembliste “général” ; dans le noyau, la sémantique est spécifiée abstraitement par les champs de `DescriptiveSemantics`, et `Concrete4` n’est qu’une instance finie particulière ;
- une identification des objets dénotés comme quotient des termes, ou toute sémantique “complète” au-delà du `Option`.

### 7.3 Ce que montre réellement Concrete4

`Concrete4` est une instance finie constructive dans laquelle :

- l’extension d’une formule `φ : Formula1` est calculée explicitement sur une liste totale `allObjs` ;
- une description globale `global φ` dénote exactement lorsque cette extension finie est représentée par un objet déjà présent, via `membersOf` et `representableExt` ;
- la spécification `global_spec` exigée par `DescriptiveSemantics` est obtenue à partir de cette construction interne.

Autrement dit, `Concrete4` réalise une compréhension globale finie internalisée, sans postuler une compréhension infinie et sans table manuelle dédiée à chaque formule.

---

## Section 8 — Conclusion courte

Le noyau `Descriptive.Faithful` sépare formellement la syntaxe des termes, la dénotation partielle, une trajectoire externe sur les termes, et une extensionalité au niveau des objets. L’instance `Concrete4` réalise ces structures dans un micro-univers fini set-like, et internalise la dénotation des descriptions globales par un calcul d’extension et un test de représentabilité. Cette base sert de référence exacte pour toute extension ultérieure, sans prétendre formaliser une logique du premier ordre générale ni une théorie des ensembles complète.

---

## Checklist de fidélité

1) Le document ne décrit que des objets et définitions présents dans `Descriptive.Faithful.*` et `Descriptive.Faithful.Concrete4`.
2) La syntaxe `Formula1` est listée avec exactement `memSelf`, `neqSelf`, `memPrim`, `not`, `and`.
3) Il est indiqué explicitement que la syntaxe est ciblée et non générale (pas de quantificateurs, pas de variables).
4) La sémantique est décrite comme partielle et constructive via `denote : Term → Option Obj`, et `Ex` est défini comme existence d’un `some`.
5) `Holds` est présenté avec la lecture exacte de `memPrim` (référence à la dénotation des primitives).
6) Les théorèmes abstraits sont reformulés sans renforcer leurs énoncés, et l’idée de preuve suit le contenu Lean (contradiction p ssi non p, usage de `rfl` pour `neqSelf`).
7) Il est affirmé que la trajectoire porte sur les termes, et non sur les objets dénotés, conformément à `Trajectory`.
8) L’extensionalité est présentée au niveau des objets (`ExtensionalObj`) et la dissociation terme/dénotation est explicitée sans identifier les termes.
9) `Concrete4` est présenté avec son mécanisme internalisé `extOfFormula` + `representableExt` + `denoteGlobal`, sans prétendre à une compréhension globale infinie.
10) Le document indique explicitement ce qui n’est pas formalisé (pas de FOL générale, pas de ZFC, pas de théorie générale des paramètres), et ne laisse pas entendre le contraire.

**Appartenance terme-à-terme (`Descriptive.Faithful.MemTerm`).** La proposition `Descriptive.Faithful.MemTerm S s t` signifie qu’il existe des objets `a b : S.Obj` tels que :
- `S.denote s = some a`,
- `S.denote t = some b`,
- `S.MemObj a b`.

**Appartenance objet-à-terme (`Descriptive.Faithful.MemObjTerm`).** La proposition `Descriptive.Faithful.MemObjTerm S y t` (où `y : S.Obj`) signifie qu’il existe `a : S.Obj` tel que :
- `S.denote t = some a`,
- `S.MemObj y a`.

Remarque courte : `MemTerm` et `MemObjTerm` rendent explicite que les énoncés “appartenance au terme” passent par la dénotation partielle.

---

## 3. Obstruction russellienne

On fixe une sémantique `S : Descriptive.Faithful.DescriptiveSemantics`.

Le terme `Descriptive.Faithful.russell` est la description globale associée à “ne pas s’appartenir à soi-même” (au niveau de `Formula1`, c’est `not memSelf`).

### Proposition 3.1 (`Descriptive.Faithful.russell_not_ex`)

Énoncé. On a :

`not (Descriptive.Faithful.Ex S Descriptive.Faithful.russell)`.

Preuve (suivant l’idée Lean). Supposons `Descriptive.Faithful.Ex S Descriptive.Faithful.russell`. Alors il existe un objet `a : S.Obj` tel que `S.denote russell = some a`.

La clause sémantique associée aux descriptions globales (`global_spec` dans `Descriptive.Faithful.DescriptiveSemantics`) donne alors, en instanciant par `y = a`, une équivalence de la forme :

- `S.MemObj a a` si et seulement si `Descriptive.Faithful.Holds S.MemObj (not memSelf) a`.

Par définition de `Descriptive.Faithful.Holds`, le membre droit est exactement la négation de `S.MemObj a a`. On obtient donc :

- `S.MemObj a a` si et seulement si `not (S.MemObj a a)`.

C’est une contradiction. Donc `Descriptive.Faithful.russell` ne dénote pas. Fin de la preuve.

Conclusion : la forme syntaxique existe, mais elle ne dénote pas.

---

## 4. Vide dérivé

On fixe une sémantique `S : Descriptive.Faithful.DescriptiveSemantics`, et un terme `c : Descriptive.Faithful.Term` tel que `Descriptive.Faithful.Ex S c`.

On considère le terme `Descriptive.Faithful.derivedEmpty c`, défini syntaxiquement comme `relative c neqSelf`.

### 4.1 Existence de dénotation (`Descriptive.Faithful.derivedEmpty_ex`)

Énoncé. Si `Descriptive.Faithful.Ex S c`, alors `Descriptive.Faithful.Ex S (Descriptive.Faithful.derivedEmpty c)`.

Explication. À partir d’un témoin `S.denote c = some b`, la clause `rel_ex` de `Descriptive.Faithful.DescriptiveSemantics` fournit un objet `a` tel que `S.denote (relative c neqSelf) = some a`, donc la dénotation de `derivedEmpty c`.

### 4.2 Le terme dénote un objet vide (`Descriptive.Faithful.derivedEmpty_denotes_emptyObj`)

Énoncé. Si `Descriptive.Faithful.Ex S c`, alors il existe `a : S.Obj` tel que :

- `S.denote (Descriptive.Faithful.derivedEmpty c) = some a`,
- et, pour tout `y : S.Obj`, on a `not (S.MemObj y a)`.

Preuve (idée Lean). On part de `S.denote c = some b`. On obtient ensuite `S.denote (derivedEmpty c) = some a`. Puis la clause `rel_spec` donne, pour tout `y : S.Obj`, une caractérisation de `S.MemObj y a` comme une conjonction dont un des facteurs est `Descriptive.Faithful.Holds S.MemObj neqSelf y`.

Or `Holds S.MemObj neqSelf y` est la proposition `y ≠ y`, contradictoire avec `rfl : y = y`. Donc `S.MemObj y a` est impossible pour tout `y`. Fin de la preuve.

Remarque courte : cet énoncé distingue explicitement le terme `derivedEmpty c` et l’objet `a : S.Obj` qu’il dénote.

### 4.3 Aucun objet n’est membre du terme (`Descriptive.Faithful.derivedEmpty_emptyObjTerm`)

Énoncé. Si `Descriptive.Faithful.Ex S c`, alors pour tout `y : S.Obj`,

`not (Descriptive.Faithful.MemObjTerm S y (Descriptive.Faithful.derivedEmpty c))`.

Explication. `MemObjTerm S y t` signifie “il existe un objet `a` dénoté par `t` tel que `S.MemObj y a`”. En combinant l’existence d’un `a` dénoté par `derivedEmpty c` et la vacuité `forall y, not (S.MemObj y a)` donnée par `derivedEmpty_denotes_emptyObj`, on conclut immédiatement.

### 4.4 Aucun terme n’est membre du terme (`Descriptive.Faithful.derivedEmpty_emptyTerm`)

Énoncé. Si `Descriptive.Faithful.Ex S c`, alors pour tout `y : Term`,

`not (Descriptive.Faithful.MemTerm S y (Descriptive.Faithful.derivedEmpty c))`.

Explication (idée Lean). De `MemTerm S y (derivedEmpty c)`, on extrait un objet dénoté par `y` et un objet dénoté par `derivedEmpty c`, ainsi qu’une appartenance `MemObj` entre ces deux objets. Cela fournit une instance de `MemObjTerm` contredisant `derivedEmpty_emptyObjTerm`.

### 4.5 Profil conjoint (`Descriptive.Faithful.derivedEmpty_profile`)

Énoncé. Si `Descriptive.Faithful.Ex S c`, alors :

- `Descriptive.Faithful.Ex S (Descriptive.Faithful.derivedEmpty c)`,
- et `forall y : Term, not (Descriptive.Faithful.MemTerm S y (Descriptive.Faithful.derivedEmpty c))`.

C’est la conjonction des résultats 4.1 et 4.4 telle qu’elle apparaît dans `Descriptive.Faithful.derivedEmpty_profile`.

---

## 5. Trajectoire externe sur les termes

Cette section est alignée sur `Descriptive.Faithful.FaithfulTrajectory`.

### 5.1 Définition (`Descriptive.Faithful.Trajectory` et `Descriptive.Faithful.TrajPrecedes`)

Une trajectoire est une structure `Descriptive.Faithful.Trajectory` qui consiste en une fonction :

- `h : Descriptive.Faithful.Term → Nat`.

La relation `Descriptive.Faithful.TrajPrecedes` est définie par :

- `TrajPrecedes τ s t` signifie `τ.h s < τ.h t`.

Phrase explicite : la trajectoire est une structure syntaxique sur les termes, non une structure sur les objets dénotés.

### Proposition 5.2 (`Descriptive.Faithful.primitive_precedes_derivedEmpty`)

Énoncé. Soient `τ : Descriptive.Faithful.Trajectory` et `c : Descriptive.Faithful.Term`. Sous les hypothèses :

- `h_c : τ.h c = 0`,
- `h_rel : forall (t : Term) (φ : Formula1), τ.h (relative t φ) = Nat.succ (τ.h t)`,

on a :

- `Descriptive.Faithful.TrajPrecedes τ c (Descriptive.Faithful.derivedEmpty c)`.

Preuve (idée Lean). Par définition, `derivedEmpty c` est `relative c neqSelf`. Donc `h_rel` donne :

- `τ.h (derivedEmpty c) = Nat.succ (τ.h c)`.

En remplaçant `τ.h c` par `0` via `h_c`, on obtient `τ.h c < τ.h (derivedEmpty c)` par le fait élémentaire `0 < succ 0`.

---

## 6. Extensionalité des objets et dissociation terme / dénotation

Cette section est alignée sur `Descriptive.Faithful.FaithfulExtensionality`.

### 6.1 Extensionalité sur les objets (`Descriptive.Faithful.ExtensionalObj`)

On définit `Descriptive.Faithful.ExtensionalObj S` comme l’énoncé suivant :

- pour tous objets `a b : S.Obj`, si pour tout `y : S.Obj` on a `S.MemObj y a` si et seulement si `S.MemObj y b`, alors `a = b`.

Cette extensionalité agit au niveau des objets `Obj` et de la relation `MemObj`.

### 6.2 Même dénotation des vides dérivés (`Descriptive.Faithful.derivedEmpty_same_denotation_of_extensional`)

Énoncé. Si `Descriptive.Faithful.ExtensionalObj S`, et si `Descriptive.Faithful.Ex S c` et `Descriptive.Faithful.Ex S c'`, alors :

- `S.denote (Descriptive.Faithful.derivedEmpty c) = S.denote (Descriptive.Faithful.derivedEmpty c')`.

Phrase explicite : l’énoncé porte d’abord sur l’égalité des **valeurs de dénotation** dans `Option Obj`. Cette égalité est obtenue parce que les objets `a` et `a'` effectivement dénotés sont extensionnellement égaux, donc identifiés par `Descriptive.Faithful.ExtensionalObj`.

Explication (idée Lean). Par `derivedEmpty_denotes_emptyObj`, on obtient des objets `a` et `a'` dénotés par `derivedEmpty c` et `derivedEmpty c'`, et chacun est vide au sens de `MemObj`. On en déduit que `a` et `a'` ont les mêmes membres (aucun), donc ils sont égaux par extensionalité. Les deux dénotations `some a` et `some a'` coïncident donc.

### 6.3 Termes distincts, même dénotation (`Descriptive.Faithful.derivedEmpty_terms_distinct_same_denotation_of_extensional`)

Énoncé. Si `Descriptive.Faithful.ExtensionalObj S`, si `Descriptive.Faithful.Ex S c` et `Descriptive.Faithful.Ex S c'`, et si `c ≠ c'`, alors :

- `Descriptive.Faithful.derivedEmpty c ≠ Descriptive.Faithful.derivedEmpty c'`,
- et `S.denote (Descriptive.Faithful.derivedEmpty c) = S.denote (Descriptive.Faithful.derivedEmpty c')`.

Explication.

1) La différence de termes est un fait purement syntaxique : `derivedEmpty c` est `relative c neqSelf`. Si `relative c neqSelf = relative c' neqSelf`, l’injectivité du constructeur `relative` force `c = c'`, contradiction.

2) L’égalité de dénotation est le résultat de la section 6.2.

On peut donc écrire explicitement :

```
égalité de dénotation ≠ égalité des termes
```

et, en combinant avec la section 5 :

```
égalité de dénotation ≠ identité trajectorielle
```

En effet, la trajectoire porte sur `Term` (donnée par `Trajectory.h`), tandis que l’extensionalité `ExtensionalObj` porte sur `Obj`.

---

## 7. Portée exacte de la formalisation

### 7.1 Ce qui est effectivement formalisé

- une mini-syntaxe ciblée (`Descriptive.Faithful.Formula1`, `Descriptive.Faithful.PrimConst`, `Descriptive.Faithful.Term`) et deux termes définis (`Descriptive.Faithful.russell`, `Descriptive.Faithful.derivedEmpty`) ;
- une sémantique partielle constructive (`Descriptive.Faithful.DescriptiveSemantics` avec `denote : Term → Option Obj`), et les notions `Descriptive.Faithful.Holds`, `Descriptive.Faithful.Ex`, `Descriptive.Faithful.MemTerm`, `Descriptive.Faithful.MemObjTerm` ;
- l’obstruction russellienne (`Descriptive.Faithful.russell_not_ex`) ;
- le vide dérivé, avec existence et vacuité (`Descriptive.Faithful.derivedEmpty_ex`, `Descriptive.Faithful.derivedEmpty_denotes_emptyObj`, `Descriptive.Faithful.derivedEmpty_emptyObjTerm`, `Descriptive.Faithful.derivedEmpty_emptyTerm`, `Descriptive.Faithful.derivedEmpty_profile`) ;
- une trajectoire externe sur les termes (`Descriptive.Faithful.Trajectory`, `Descriptive.Faithful.TrajPrecedes`, `Descriptive.Faithful.primitive_precedes_derivedEmpty`) ;
- l’extensionalité au niveau des objets (`Descriptive.Faithful.ExtensionalObj`) et la possibilité de termes distincts à même dénotation (`Descriptive.Faithful.derivedEmpty_same_denotation_of_extensional`, `Descriptive.Faithful.derivedEmpty_terms_distinct_same_denotation_of_extensional`).

### 7.2 Ce qui ne l’est pas encore

- pas de syntaxe générale du premier ordre (la syntaxe est limitée aux quatre constructeurs de `Formula1`) ;
- pas de formalisation intégrale d’une logique libre du premier ordre (seules les notions et schémas nécessaires au noyau ci-dessus sont présents) ;
- pas de construction interne complète des descriptions globales/relatives à partir d’un modèle ensembliste concret ; la sémantique reste spécifiée abstraitement par les champs de `Descriptive.Faithful.DescriptiveSemantics` ;
- pas d’instance zfcienne formalisée ;
- pas de théorie générale des paramètres pour les descriptions (la couche de formules reste unaire et ciblée) ;
- pas de séparation générale complète entre toutes les couches possibles du langage au-delà des définitions et théorèmes explicitement listés dans ce document.
