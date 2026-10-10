import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Data

/-! One and two applications of the actual tensor boundary to a degree-64
cooperation. No assertion about products or fixed standard classes is built
into these definitions. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The first actual tensor-boundary representative in degree 63. -/
def sphereH6TensorRepresentative (a : Mod2Cooperations H 64)
    (x : Mod2Homology H 0 SphereSpectrum) :
    Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  exact adamsTensorBoundary H R K SphereSpectrum 64
    (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] x))

/-- Apply the actual boundary once more with the same cooperation.
Degree bookkeeping: 64 + 63 - 1 = 126 at tower stage two. -/
def sphereH6DoubleTensorRepresentative (a : Mod2Cooperations H 64)
    (x : Mod2Homology H 0 SphereSpectrum) :
    Mod2Homology H 126 (adamsTower H.unit SphereSpectrum 2) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  exact adamsTensorBoundary H R K (adamsTower H.unit SphereSpectrum 1) 127
    (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] sphereH6TensorRepresentative H R K a x))

end
end KIP126.Classical.Adams
