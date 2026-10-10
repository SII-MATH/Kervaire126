import KIP126.Def.StageInput.StandardSphere.Background.Data
import KIP126.Def.StageInput.Milnor
import KIP126.Def.Comparison.Cobar.Proofs
import KIP126.Def.Solution.StandardRouteBackground

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
  sorry

end KIP126.Def
