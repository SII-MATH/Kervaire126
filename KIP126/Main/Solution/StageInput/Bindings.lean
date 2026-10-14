module

public import KIP126.Main.Axiom.Challenge2

@[expose] public section

/-! Projections and delivered comparisons from the sole correlated Challenge2 witness. -/
namespace KIP126.Main.StageInput

/-- The one witness used throughout Main. -/
noncomputable def witness : KIP126.Challenge2 :=
  KIP126.Main.Axiom.challenge2

/-- Literature on the bindings stored in the sole stage witness. -/
noncomputable def literature :
    KIP126.Challenge2.LiteratureInterface :=
  witness.literature

/-- C(M) on the presentation stored in that same stage witness. -/
noncomputable def computation :
    KIP126.Challenge2.ComputationInterface literature :=
  witness.computation

/-- All Section 7 consumers use Def's one fixed route, with the source and
program labels supplied by the same Challenge2 witness. -/
noncomputable abbrev routeModel := KIP126.Classical.Adams.standardRouteModel
noncomputable abbrev routeLabels := computation.bindings.routeLabels
noncomputable abbrev tmfLabels := literature.bindings.tmfLabels
noncomputable abbrev routeEta := KIP126.Def.standardRouteEta

/-- C(M) on the same model and labels. This projects existing evidence. -/
noncomputable def routeComputation :
    KIP126.Computation.Route.Inputs routeModel routeLabels tmfLabels :=
  computation.route

/-- Independent infinite-range premises on the same actual standard sphere. -/
theorem sphereVanishing :
    KIP126.Classical.Adams.SphereVanishingLine KIP126.Classical.Adams.standardFoundation.hf2 :=
  literature.results.sphereVanishing

/-- The literature delivery certifies the actual completion source and its
comparisons. Main consumes these certificates on the same binding. -/
theorem completionApplicability :
    KIP126.Literature.Route.BHSCompletionApplicability routeModel
      literature.bindings.route.bhsCompletion :=
  literature.bindings.route.completionApplicability

theorem completionComparison :
    KIP126.Literature.Route.BHSCompletionComparison routeModel
      literature.bindings.route.bhsCompletion :=
  literature.bindings.route.completionComparison

theorem realizationComparison :
    KIP126.Literature.Route.BHSRealizationComparison routeModel
      literature.bindings.route.realization
      literature.bindings.route.bhsCompletion :=
  literature.bindings.route.realizationComparison

end KIP126.Main.StageInput
