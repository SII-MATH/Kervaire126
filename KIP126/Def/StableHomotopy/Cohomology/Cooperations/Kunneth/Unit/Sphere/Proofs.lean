import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Sphere.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The initial sphere coaction is the elementary unit tensor. This is
derived from actual sphere homology and the below-page unit coherence,
not an extra initial condition on the Adams tower. -/
theorem mod2TensorCoaction_sphere (hU : Mod2KunnethUnitCompatible H R K)
    (n : ℤ) (x : Mod2Homology H n SphereSpectrum) :
    mod2TensorCoaction H R K SphereSpectrum n x =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n x := by
  rw [mod2TensorCoaction_apply, mod2CoactionMap_sphere, hU]

/-- Even without unit-coordinate coherence, the independent reduced
step vanishes on sphere coefficient homology: the actual insertions agree. -/
theorem mod2CobarStep_sphere_zero (n : ℤ) (x : Mod2Homology H n SphereSpectrum) :
    mod2CobarStep H R K SphereSpectrum n x = 0 := by
  apply reducedCooperationTensorInclusion_injective H R
    (fun i => mod2HomologyF2 H R i SphereSpectrum) n
  rw [map_zero, mod2CobarStep_inclusion, mod2CoactionMap_sphere, sub_self]
  exact (K.comparison SphereSpectrum n).map_zero

end KIP126.StableHomotopy.Cohomology
