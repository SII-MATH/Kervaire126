module

public import KIP126.Def.StageInput.StandardSphere.Background.Data
public import KIP126.Def.StageInput.Milnor
public import KIP126.Def.Comparison.Cobar.Proofs
public import KIP126.Def.Solution.StandardRouteBackground

@[expose] public section

/-! Internal construction obligations for the one standard sphere background.
Their proof status is independent of the external literature and computation
delivery. The Moss context construction remains unfinished. -/

namespace KIP126.Def

/-- The generic cobar/derived-Ext comparison specialized to the same fixed
HF₂ and Milnor construction used by every downstream sphere statement.
The generic comparison theorem still carries its explicit unfinished proof. -/
theorem standardCobarDerivedExt_exists :
    Nonempty (KIP126.Challenge2.CobarDerivedExtComparison
      KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations) :=
  KIP126.Def.Comparison.StageInterfaces.cobarDerivedExtComparison
    KIP126.Classical.Adams.standardFoundation.hf2
    KIP126.Classical.Adams.standardMilnorCooperations

/-- Construct the actual mapping-tower pairing and its convergence, detection
and indeterminacy comparisons on the fixed sphere. This internal theorem
does not assert Moss's external result or choose program coordinates. -/
theorem standardSphereMossContext_exists :
    Nonempty KIP126.Challenge2.StandardSphereMossContext := by
  sorry

/-- The selected classical Hopf map has the precise filtration needed to
regrade its actual normalized synthetic lift to bidegree (1,2). This is a
property of the fixed route construction, not a property of an arbitrary
inhabitant of `RouteInput`. Its internal proof remains unfinished. -/
theorem standardEtaExponent :
    KIP126.Synthetic.Context.normalizedExponent
      KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardRouteModel.auxiliary.etaMap = 1 := by
  exact (open CategoryTheory MonoidalCategory Pretriangulated
    KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
    KIP126.Classical.Adams KIP126.Synthetic.Context in by
    classical
    have positive {C : Type 1} [StableHomotopyCategory.{1, 0} C]
        [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
        (f : HomotopyGroup 1 (SphereSpectrum (C := C))) : normalizedExponent H f = 1 := by
      have hz : CategoryStruct.comp f (adamsUnit H.unit SphereSpectrum) = 0 := by
        apply (cancel_mono (rightUnitor H.HF2).hom).mp
        letI := H.homotopy_vanishes 1 (by decide)
        exact Subsingleton.elim _ _
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂
        (adamsResolutionTriangle H.unit SphereSpectrum 0)
        (adamsResolutionTriangle_distinguished H.unit SphereSpectrum 0) f hz
      have hf : AdamsFiltrationAtLeast H f 1 := by
        refine ⟨g, ?_⟩
        simpa [adamsTowerMap, adamsTowerComposite, adamsResolutionTriangle, Triangle.mk, adamsTower]
          using hg.symm
      simp only [normalizedExponent, if_pos hf]
    exact positive standardFoundation.hf2 standardRouteModel.auxiliary.etaMap)

end KIP126.Def
