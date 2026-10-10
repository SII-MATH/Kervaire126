import KIP126.Def.StageInput.StandardSphere.Background.Proofs

/-! Fix one fully specified comparison context from Def's construction
obligations. All consumers use these same choices. The explicit existence
theorems record the unfinished property proofs; these definitions add no
project axiom and supply no external Moss theorem or computation result. -/

namespace KIP126.Def

open CategoryTheory

/-- The one structural background on Def's selected synthetic route. -/
noncomputable abbrev standardRouteBackground := Solution.standardRouteBackground

/-- The actual detector algebra uses the existing route detector as carrier.
No CSV coordinates or BR21 theorem are built into this algebra object. -/
noncomputable def standardTmfTarget :
    CategoryTheory.Mon KIP126.Classical.Adams.standardFoundation.Spectrum :=
  letI := standardRouteBackground.algebra.classicalSymmetric
  letI := standardRouteBackground.algebra.syntheticSymmetric
  { X := KIP126.Classical.Adams.standardRouteModel.auxiliary.detector
    mon := standardRouteBackground.algebra.detector.classical }

/-- Every detector comparison uses the route's same actual unit. -/
theorem standardTmfTarget_unit :
    KIP126.Classical.Adams.Tmf.unit standardTmfTarget =
      KIP126.Classical.Adams.standardRouteModel.auxiliary.detectorUnit := by
  letI := standardRouteBackground.algebra.classicalSymmetric
  letI := standardRouteBackground.algebra.syntheticSymmetric
  exact standardRouteBackground.algebra.detector.classical_unit

/-- The chosen synthetic η is the actual normalized lift of the route's
classical η, regraded by its stated filtration property. -/
noncomputable def standardRouteEta :
    KIP126.Synthetic.Context.BiHom 1 2
      (KIP126.Synthetic.Context.S_0_0 : standardRouteInput.Syn) :=
  let D := KIP126.Classical.Adams.standardRouteModel
  (KIP126.Kervaire.Route.etaSourceIso D standardEtaExponent).hom ≫
    (D.normalizedMap (.shift 1 .sphere) .sphere D.auxiliary.etaMap).map ≫ D.nu.unitIso.hom

/-- The fixed comparison preserves the prescribed actual cobar cocycles. -/
noncomputable def standardCobarDerivedExt :
    KIP126.Challenge2.CobarDerivedExtComparison
      KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations :=
  Classical.choice standardCobarDerivedExt_exists

/-- The one internal sphere mapping context used by the literature delivery. -/
noncomputable def standardSphereMossContext : KIP126.Challenge2.StandardSphereMossContext :=
  Classical.choice standardSphereMossContext_exists

end KIP126.Def
