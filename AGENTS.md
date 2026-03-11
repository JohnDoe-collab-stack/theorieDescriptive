# Lean rules

Pour tout fichier Lean (`.lean`) créé, modifié ou complété :

## Contraintes obligatoires

- La sortie doit être strictement constructive.
- Il ne doit y avoir aucun axiome.
- Il ne doit y avoir aucune dépendance à `Classical`.
- Il ne doit y avoir aucune dépendance à `propext`.
- Il ne doit y avoir aucune dépendance à `Quot.sound`.
- Ne jamais introduire `axiom`.
- Ne jamais utiliser `open Classical`.
- Ne jamais utiliser `Classical.*`.

## Audit obligatoire

À la toute fin du fichier, ajouter ou mettre à jour un unique bloc :

/- AXIOM_AUDIT_BEGIN -/
#print axioms <declaration_principale_1>
#print axioms <declaration_principale_2>
/- AXIOM_AUDIT_END -/

## Règles d’application

- S’il existe déjà un bloc `AXIOM_AUDIT`, le mettre à jour au lieu d’en ajouter un second.
- Le bloc doit être placé à la toute fin du fichier.
- Remplacer les placeholders par les vrais noms des déclarations principales ajoutées ou modifiées.
- Ne jamais laisser `...` dans une ligne `#print axioms`.
- S’il n’y a qu’une seule déclaration principale, ne mettre qu’une seule ligne `#print axioms`.

## Critère de validation

Le travail n’est acceptable que si :

- il y a exactement un bloc `AXIOM_AUDIT`
- le bloc est à la fin du fichier
- tous les noms passés à `#print axioms` existent
- l’audit final n’affiche aucun axiome
- l’audit final ne mentionne ni `propext`, ni `Quot.sound`, ni `Classical.*`

## En cas d’échec

Si l’audit révèle un axiome ou une dépendance interdite, ne pas livrer la version telle quelle.
Réécrire la preuve ou la définition jusqu’à obtenir une version purement constructive.