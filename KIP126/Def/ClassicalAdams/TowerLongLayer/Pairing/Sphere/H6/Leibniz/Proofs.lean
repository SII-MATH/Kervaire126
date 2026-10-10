import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Leibniz.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Internal.Leibniz.Proofs

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

/-- The geometric boundary identity reduces square vanishing to cancellation
of the two constructed cross products on the internal page. No Lin data or
fixed-foundation axiom occurs in this reduction. -/
theorem SphereH6LongLayerMaps.internalD_square_eq_zero_of_cross_sum
    (h : M.Compatible R) (hδ : M.RelativeBoundary R h)
    (x : (adamsTowerSSData H.unit (𝟙_ C) 1 64).page (0 : WithTop ℕ))
    (hc : (fun a b : (adamsTowerSSData H.unit (𝟙_ C) 4 129).page (0 : WithTop ℕ) => a + b)
      ((M.leftPairing R).onInternalPage h.left h.left_boundary
        ((adamsTowerInternalD H.unit (𝟙_ C) 0 1 64) x) x)
      ((M.rightPairing R).onInternalPage h.right h.right_boundary
        x ((adamsTowerInternalD H.unit (𝟙_ C) 0 1 64) x)) = 0) :
    (adamsTowerInternalD H.unit (𝟙_ C) 0 2 128)
      ((M.squarePairing R).onInternalPage h.square h.square_boundary x x) = 0 := by
  let dx := (adamsTowerInternalD H.unit (𝟙_ C) 0 1 64) x
  let f := (adamsTowerSSDataPageIso H.unit (𝟙_ C) 4 129 0).hom.hom
  have he := (M.squarePairing R).internalD_of_relativeBoundary (n := 0)
    h.square h.square_boundary ((M.leftPairing R).onPage h.left h.left_boundary)
    ((M.rightPairing R).onPage h.right h.right_boundary) 1 hδ x x
  have hl := (M.leftPairing R).onInternalPage_comparison (n := 0) h.left h.left_boundary dx x
  have hr := (M.rightPairing R).onInternalPage_comparison (n := 0) h.right h.right_boundary x dx
  simp only [Nat.reduceAdd, Nat.cast_ofNat, Int.reduceAdd, Int.reduceSub] at he
  simp only [Int.reduceAdd] at hl hr hc
  have hs := congrArg₂
    (fun a b : adamsPage H.unit (𝟙_ C) 2 (Nat.le_succ 1) 4 129 => a + b)
    hl.symm ((one_smul ℤ _).trans hr.symm)
  have hm := f.map_add
    ((M.leftPairing R).onInternalPage h.left h.left_boundary dx x)
    ((M.rightPairing R).onInternalPage h.right h.right_boundary x dx)
  have hz := congrArg f hc
  have he0 := he.trans (hs.trans (hm.symm.trans (hz.trans f.map_zero)))
  exact (adamsTowerSSDataPageIso H.unit (𝟙_ C) 4 129 0).toLinearEquiv.map_eq_zero_iff.mp he0

end
end KIP126.Classical.Adams
