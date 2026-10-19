module

public import KIP126.Def.Kervaire.Route.Conditions.Predicates
public import KIP126.Def.Kervaire.Route.Model.Coherent.Data

@[expose] public section

/-! Compatibility import. The unbound Near126Adams and ChoiceConditions
records were removed: their free predicates did not state the paper.
Use KIP126.Kervaire.Route on the actual internal tower instead. -/
