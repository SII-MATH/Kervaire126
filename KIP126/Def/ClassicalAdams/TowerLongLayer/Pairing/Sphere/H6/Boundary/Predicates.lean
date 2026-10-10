import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} (M : SphereH6LongLayerMaps H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Only the two nontrivial boundary conditions remain: the boundary input
has degree `(3,65)`. All four conditions with boundary input `(1,64)` are
proved from the actual sphere tower, independently of the table. -/
structure SphereH6LongLayerMaps.CrossBoundaryCompatible : Prop where
  left : ∀ (a : HomotopyGroup (65 - 3) (adamsTowerAt H.unit (𝟙_ C) 3)),
    adamsI H.unit (𝟙_ C) (65 - 3) (3 - 2 + 1) 3 (by omega) a = 0 →
    ∀ b : HomotopyGroup (64 - 1) (adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1),
    (M.leftPairing R).first (adamsJ H.unit (𝟙_ C) 3 65 a)
      (adamsLongLayerToE1 H.unit (𝟙_ C) 2 (by decide) 1 64 b) ∈
        adamsBoundaries H.unit (𝟙_ C) 2 (by decide) (3 + 1) (65 + 64)
  right : ∀ (a : HomotopyGroup (64 - 1) (adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1))
    (b : HomotopyGroup (65 - 3) (adamsTowerAt H.unit (𝟙_ C) 3)),
    adamsI H.unit (𝟙_ C) (65 - 3) (3 - 2 + 1) 3 (by omega) b = 0 →
    (M.rightPairing R).first
      (adamsLongLayerToE1 H.unit (𝟙_ C) 2 (by decide) 1 64 a)
      (adamsJ H.unit (𝟙_ C) 3 65 b) ∈
        adamsBoundaries H.unit (𝟙_ C) 2 (by decide) (1 + 3) (64 + 65)

end
end KIP126.Classical.Adams
