module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.HomotopyGroup.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.AllBasepoints.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Category.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual literal-loop replacement retains T1 separation. -/
instance loopSpectrificationFunctor_level_t1Space (X : Prespectrum.{u})
    [∀ n,T1Space (X.level n)] (n : ℕ) :
    T1Space ((loopSpectrificationFunctor.obj X).level n) :=
  spectrificationStep_level_t1Space (spectrificationTelescope X) n

/-- The constructed literal-loop replacement has actual bijective
stabilization, at every level and in all cubical dimensions. -/
theorem loopSpectrificationFunctor_hasBijectiveStabilization (X : Prespectrum.{u})
    [∀ n,T1Space (X.level n)] : HasBijectiveStabilization (loopSpectrificationFunctor.obj X) :=
  spectrificationStep_hasBijectiveStabilization _ (spectrificationTelescope_hasBijectiveStabilization X)

theorem loopSpectrificationUnit_stableEquivalence (X : Prespectrum.{u})
    [∀ n,T1Space (X.level n)] : stableEquivalences (loopSpectrificationUnit X) := by
  intro d
  change Function.Bijective ((stableHomotopyFunctor d).map
    (spectrificationTelescopeUnit X ≫ spectrificationStepUnit (spectrificationTelescope X)))
  rw [Functor.map_comp]
  exact (spectrificationStepUnit_stableEquivalence (spectrificationTelescope X) d).comp
    (spectrificationTelescopeUnit_stableEquivalence X d)

theorem loopSpectrificationFunctor_map_stableEquivalence
    {X Y : Prespectrum.{u}} [∀ n,T1Space (X.level n)] [∀ n,T1Space (Y.level n)]
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (loopSpectrificationFunctor.map f) :=
  spectrificationStepMap_stableEquivalence _ (spectrificationTelescopeMap_stableEquivalence f hf)

/-- The actual literal-loop replacement turns stable equivalences into
weak equivalences at every point of every original level. -/
theorem loopSpectrificationFunctor_map_homotopy_bijective
    {X Y : Prespectrum.{u}} [∀ n,T1Space (X.level n)] [∀ n,T1Space (Y.level n)]
    (f : X ⟶ Y) (hf : stableEquivalences f) (n r : ℕ)
    (p : (loopSpectrificationFunctor.obj X).level n) :
    Function.Bijective (KIP126.Topology.continuousHomotopyMap
      ((loopSpectrificationFunctor.map f).level n) p
      ((loopSpectrificationFunctor.map f).level n p) rfl r) :=
  spectrificationStepMap_level_homotopy_bijective_at_all_points (spectrificationTelescopeMap f) n r
    ((loopSpectrificationFunctor.map f).levelHomotopy_bijective_of_stableEquivalence
      (loopSpectrificationFunctor_hasBijectiveStabilization X)
      (loopSpectrificationFunctor_hasBijectiveStabilization Y)
      (loopSpectrificationFunctor_map_stableEquivalence f hf) n r) p

/-- Naturality rewrites the replacement unit in the order needed for
the actual coherence of the strict spectrification step. -/
theorem loopSpectrificationUnit_eq (X : Prespectrum.{u}) :
    loopSpectrificationUnit X = spectrificationStepUnit X ≫
      spectrificationStepMap (spectrificationTelescopeUnit X) :=
  spectrificationStepUnit_natural (spectrificationTelescopeUnit X)

/-- On an actual step object, the replacement unit itself is a literal
loop map at each level; this is an equality of original strict maps. -/
theorem loopSpectrificationUnit_step (X : Prespectrum.{u}) :
    loopSpectrificationUnit (spectrificationStep X) =
      spectrificationStepMap (spectrificationStepUnit X ≫
        spectrificationTelescopeUnit (spectrificationStep X)) := by
  rw [loopSpectrificationUnit_eq,← spectrificationStepUnit_coherence]
  exact (spectrificationStepFunctor.map_comp _ _).symm

/-- On its actual stabilized literal-loop outputs, the replacement unit
is a weak equivalence at every point, without an assumed H-space structure. -/
theorem loopSpectrificationUnit_output_homotopy_bijective
    (X : Prespectrum.{u}) [∀ n,T1Space (X.level n)] (n r : ℕ)
    (p : (loopSpectrificationFunctor.obj X).level n) :
    Function.Bijective (KIP126.Topology.continuousHomotopyMap
      ((loopSpectrificationUnit (loopSpectrificationFunctor.obj X)).level n) p
      ((loopSpectrificationUnit (loopSpectrificationFunctor.obj X)).level n p) rfl r) := by
  have hbased := (loopSpectrificationUnit (loopSpectrificationFunctor.obj X)).levelHomotopy_bijective_of_stableEquivalence
    (loopSpectrificationFunctor_hasBijectiveStabilization X)
    (loopSpectrificationFunctor_hasBijectiveStabilization (loopSpectrificationFunctor.obj X))
    (loopSpectrificationUnit_stableEquivalence (loopSpectrificationFunctor.obj X)) n r
  change Function.Bijective (KIP126.Topology.continuousHomotopyMap
    ((loopSpectrificationUnit (spectrificationStep (spectrificationTelescope X))).level n) p
    ((loopSpectrificationUnit (spectrificationStep (spectrificationTelescope X))).level n p) rfl r)
  change Function.Bijective ((loopSpectrificationUnit (spectrificationStep (spectrificationTelescope X))).levelHomotopy n r) at hbased
  rw [loopSpectrificationUnit_step] at hbased ⊢
  exact spectrificationStepMap_level_homotopy_bijective_at_all_points _ n r hbased p

/-- The exact strict mapping-path factor of a replaced stable equivalence
has full cube-boundary lifting at every original spectrum level. -/
theorem loopSpectrificationMap_mappingPathProjection_hasCubeBoundaryLifting
    {X Y : Prespectrum.{u}} [∀ n,T1Space (X.level n)] [∀ n,T1Space (Y.level n)]
    (f : X ⟶ Y) (hf : stableEquivalences f) (n : ℕ) :
    KIP126.Topology.HomotopyLifting.HasCubeBoundaryLifting
      ((mappingPathProjection (loopSpectrificationFunctor.map f)).level n) :=
  mappingPathProjection_level_hasCubeBoundaryLifting _
    (fun n p r => loopSpectrificationFunctor_map_homotopy_bijective f hf n r p) n

end KIP126.StableHomotopy.Implementation.Prespectrum
