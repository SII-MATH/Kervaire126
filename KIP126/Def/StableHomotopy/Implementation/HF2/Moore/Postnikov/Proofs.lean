module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Map.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The Moore extension retains the original normalized coefficient unit. -/
@[reassoc (attr := simp)]
theorem sourceModTwoMooreInclusion_coefficient :
    sourceModTwoMooreInclusion ≫ sourceModTwoMooreCoefficient = sourceHF2Unit := by
  let f := moorePowerMap 2 (Prespectrum.sourceSphere 0) 1
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hz : f ≫ sourceHF2Unit = 0 := by
    have h := congrArg (fun a => sourceHF2Unit ≫ a) sourceHF2_two_id
    simpa only [f, moorePowerMap, pow_one, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id, Limits.comp_zero] using h
  exact (T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished f)
    sourceHF2Unit hz).choose_spec.symm

/-- The truncation comparison extends that same actual Moore map. -/
@[reassoc (attr := simp)]
theorem sourceModTwoMooreHeartToHF2_unit :
    sourcePostnikovUnit sourceModTwoMoore 1 ≫ sourceModTwoMooreHeartToHF2 =
      sourceModTwoMooreCoefficient :=
  ((sourcePostnikovUnit_precomp_bijective sourceModTwoMoore 1
    (sourceLocalization.obj sourceHF2.spectrum)
    (fun d hd => sourceHF2.vanishes d (by omega))).surjective
      sourceModTwoMooreCoefficient).choose_spec

/-- The specified generator is carried to the original fixed HF2 unit. -/
@[reassoc (attr := simp)]
theorem sourceModTwoMooreHeartUnit_toHF2 :
    sourceModTwoMooreHeartUnit ≫ sourceModTwoMooreHeartToHF2 = sourceHF2Unit := by
  rw [sourceModTwoMooreHeartUnit, Category.assoc, sourceModTwoMooreHeartToHF2_unit,
    sourceModTwoMooreInclusion_coefficient]

/-- The resulting coefficient of the specified sphere generator is one. -/
theorem sourceModTwoMooreHeartToHF2_generator :
    sourceHF2.pi0 ((sourceStableHomotopyAddFunctor 0).map sourceModTwoMooreHeartToHF2
      ((sourceStableHomotopyAddFunctor 0).map sourceModTwoMooreHeartUnit
        (Prespectrum.sourceSphereGenerator 0))) = 1 := by
  let G := sourceStableHomotopyAddFunctor 0
  change sourceHF2.pi0 ((G.map sourceModTwoMooreHeartUnit ≫
    G.map sourceModTwoMooreHeartToHF2) (Prespectrum.sourceSphereGenerator 0)) = 1
  rw [← G.map_comp, sourceModTwoMooreHeartUnit_toHF2]
  change sourceHF2.pi0 ((forget AddCommGrpCat).map
    ((sourceStableHomotopyAddFunctor 0).map sourceHF2Unit) (Prespectrum.sourceSphereGenerator 0)) = 1
  rw [sourceStableHomotopyAddFunctor_forget_map]
  exact sourceHF2.sourceUnit_coefficient

/-- The original comparison is surjective on its zeroth actual stable group. -/
theorem sourceModTwoMooreHeartToHF2_homotopy_surjective :
    Function.Surjective ((sourceStableHomotopyAddFunctor 0).map sourceModTwoMooreHeartToHF2) := by
  intro y
  have hy : sourceHF2.pi0 y = 0 ∨ sourceHF2.pi0 y = 1 := by
    have hlt : (sourceHF2.pi0 y).val < 2 := ZMod.val_lt _
    have hval : (sourceHF2.pi0 y).val = 0 ∨ (sourceHF2.pi0 y).val = 1 := by omega
    rcases hval with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hy with hy | hy
  · refine ⟨0, ?_⟩
    apply sourceHF2.pi0.injective
    simpa only [map_zero, sourceHF2.pi0_map_zero] using hy.symm
  · refine ⟨(sourceStableHomotopyAddFunctor 0).map sourceModTwoMooreHeartUnit
      (Prespectrum.sourceSphereGenerator 0), ?_⟩
    apply sourceHF2.pi0.injective
    exact sourceModTwoMooreHeartToHF2_generator.trans hy.symm

/-- This actual truncated Moore object has no stable group away from zero. -/
theorem sourceModTwoMooreHeart_homotopy_subsingleton (d : ℤ) (hd : d ≠ 0) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj sourceModTwoMooreHeart) := by
  by_cases hneg : d < 0
  · letI : Subsingleton ((sourceStableHomotopyAddFunctor d).obj sourceModTwoMoore) :=
      sourceMoorePowerSequence_homotopy_subsingleton 2 (Prespectrum.sourceSphere 0)
      0 (fun i hi => Prespectrum.sourceSphere_homotopy_subsingleton 0 i hi) 1 d hneg
    exact (sourcePostnikovUnit_homotopy_bijective sourceModTwoMoore 1 d (by omega)).surjective.subsingleton
  · exact sourcePostnikovTruncation_homotopy_subsingleton sourceModTwoMoore 1 d (by omega)

end KIP126.StableHomotopy.Implementation
