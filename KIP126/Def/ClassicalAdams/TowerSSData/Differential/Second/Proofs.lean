import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data

/-! The internal differential at the square's bidegree is the actual
exact-couple obstruction, with all numerical reindexing checked. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- At these numerical degrees the PreSS reindexing is the identity. -/
theorem adamsTowerPreSS_d_two_h6_eq :
    (adamsTowerPreSS unit X).d 2 (2, 128) = adamsTowerInternalD unit X 0 2 128 := by
  with_unfolding_all
    change adamsTowerInternalD unit X 0 2 128 ≫ 𝟙 _ = _
    exact Category.comp_id (adamsTowerInternalD unit X 0 2 128)

/-- The second differential in the existing internal SSData sequence agrees
with the tower differential on the actual source and target quotients. -/
theorem adamsTower_d_two_h6_comparison :
    (adamsTowerInternalSpectralSequence unit X).d 2 (2, 128) ≫
      (adamsTowerSSDataPageIso unit X 4 129 0).hom =
        (adamsTowerSSDataPageIso unit X 2 128 0).hom ≫
          ModuleCat.ofHom (adamsDifferential unit X 2 (by decide) 2 128) := by
  have hD := adamsTowerInternalD_comparison unit X 0 2 128
  simp only [Nat.reduceAdd, Nat.cast_ofNat, Int.reduceAdd, Int.reduceSub] at hD
  have hpre := congrArg
    (fun f : (adamsTowerSSData unit X 2 128).page (0 : WithTop ℕ) ⟶
      (adamsTowerSSData unit X 4 129).page (0 : WithTop ℕ) =>
        f ≫ (adamsTowerSSDataPageIso unit X 4 129 0).hom)
    (adamsTowerPreSS_d_two_h6_eq unit X)
  with_unfolding_all
    exact hpre.trans hD

/-- Evaluate the actual internal d₂ on a specified second-page representative. -/
theorem adamsTower_d_two_h6_representative
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 (2, 128))
    (u : adamsCycleAmbient unit X 2 128)
    (hu : (adamsCycleBoundaries unit X 2 (by decide) 2 128).mkQ u =
      (adamsTowerSSDataPageIso unit X 2 128 0).hom x) :
    (adamsTowerSSDataPageIso unit X 4 129 0).hom
      (((adamsTowerInternalSpectralSequence unit X).d 2 (2, 128)).hom x) =
        adamsDifferentialValue unit X 2 (by decide) 2 128 u := by
  have he := congrArg (fun f => f.hom x) (adamsTower_d_two_h6_comparison unit X)
  change (adamsTowerSSDataPageIso unit X 4 129 0).hom
    (((adamsTowerInternalSpectralSequence unit X).d 2 (2, 128)).hom x) =
      adamsDifferential unit X 2 (by decide) 2 128
        ((adamsTowerSSDataPageIso unit X 2 128 0).hom x) at he
  exact he.trans (congrArg (adamsDifferential unit X 2 (by decide) 2 128) hu.symm)

/-- Choosing any actual lift of k(u) to T₄ computes the internal second
differential as the quotient class of its tower-to-layer image. -/
theorem adamsTower_d_two_h6_value_of_lift
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 (2, 128))
    (u : adamsCycleAmbient unit X 2 128)
    (hu : (adamsCycleBoundaries unit X 2 (by decide) 2 128).mkQ u =
      (adamsTowerSSDataPageIso unit X 2 128 0).hom x)
    (y : HomotopyGroup 125 (adamsTowerAt unit X 4))
    (hy : adamsI unit X 125 3 4 (by decide) y = adamsK unit X 2 128 u.val) :
    (adamsTowerSSDataPageIso unit X 4 129 0).hom
      (((adamsTowerInternalSpectralSequence unit X).d 2 (2, 128)).hom x) =
        adamsJToPage unit X 2 (by decide) 4 129 y := by
  exact (adamsTower_d_two_h6_representative unit X x u hu).trans
    (adamsDifferentialValue_eq_of_lift unit X 2 (by decide) 2 128 u y hy)

/-- Such a lift always exists for a second-page representative. Thus the
formula is an actual description of the differential, not a conditional
calculation whose auxiliary lift might be unavailable. -/
theorem adamsTower_d_two_h6_value_exists
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 (2, 128))
    (u : adamsCycleAmbient unit X 2 128)
    (hu : (adamsCycleBoundaries unit X 2 (by decide) 2 128).mkQ u =
      (adamsTowerSSDataPageIso unit X 2 128 0).hom x) :
    ∃ y : HomotopyGroup 125 (adamsTowerAt unit X 4),
      adamsI unit X 125 3 4 (by decide) y = adamsK unit X 2 128 u.val ∧
      (adamsTowerSSDataPageIso unit X 4 129 0).hom
        (((adamsTowerInternalSpectralSequence unit X).d 2 (2, 128)).hom x) =
          adamsJToPage unit X 2 (by decide) 4 129 y := by
  obtain ⟨y, hy⟩ := u.property
  exact ⟨y, hy, adamsTower_d_two_h6_value_of_lift unit X x u hu y hy⟩

/-- The second differential vanishes exactly when the same representative
is a third cycle, equivalently when k(u) lifts one more stage, to T₅. -/
theorem adamsTower_d_two_h6_eq_zero_iff_lift
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 (2, 128))
    (u : adamsCycleAmbient unit X 2 128)
    (hu : (adamsCycleBoundaries unit X 2 (by decide) 2 128).mkQ u =
      (adamsTowerSSDataPageIso unit X 2 128 0).hom x) :
    (((adamsTowerInternalSpectralSequence unit X).d 2 (2, 128)).hom x) = 0 ↔
      ∃ y : HomotopyGroup 125 (adamsTowerAt unit X 5),
        adamsI unit X 125 3 5 (by decide) y = adamsK unit X 2 128 u.val := by
  have he := adamsTower_d_two_h6_representative unit X x u hu
  have hz := (adamsTowerSSDataPageIso unit X 4 129 0).toLinearEquiv.map_eq_zero_iff
    (x := (((adamsTowerInternalSpectralSequence unit X).d 2 (2, 128)).hom x))
  exact hz.symm.trans ((Iff.of_eq (congrArg (fun z => z = 0) he)).trans
    (adamsDifferentialValue_eq_zero_iff unit X 2 (by decide) 2 128 u))

end
end KIP126.Classical.Adams
