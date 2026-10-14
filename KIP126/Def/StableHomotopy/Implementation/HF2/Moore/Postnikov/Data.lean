module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Unit
public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Connectivity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The actual mod-two Moore object is the first positive layer of the
already specified Moore tower of the original source sphere. -/
noncomputable def sourceModTwoMoore : SourceCategory.{0} :=
  (moorePowerSequence 2 (Prespectrum.sourceSphere 0)).obj 1

/-- The original cofiber inclusion into the mod-two Moore object. -/
noncomputable def sourceModTwoMooreInclusion : Prespectrum.sourceSphere 0 ⟶ sourceModTwoMoore :=
  HasFunctorialCofiber.cofibι (moorePowerMap 2 (Prespectrum.sourceSphere 0) 1)

/-- The normalized coefficient unit extends over the actual Moore triangle
because the actual coefficient spectrum has characteristic two. -/
noncomputable def sourceModTwoMooreCoefficient :
    sourceModTwoMoore ⟶ sourceLocalization.obj sourceHF2.spectrum := by
  let f := moorePowerMap 2 (Prespectrum.sourceSphere 0) 1
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hz : f ≫ sourceHF2Unit = 0 := by
    have h := congrArg (fun a => sourceHF2Unit ≫ a) sourceHF2_two_id
    simpa only [f, moorePowerMap, pow_one, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id, Limits.comp_zero] using h
  exact (T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished f) sourceHF2Unit hz).choose

/-- The same actual mod-two Moore object truncated to its zeroth stable degree. -/
noncomputable def sourceModTwoMooreHeart : SourceCategory.{0} :=
  sourcePostnikovTruncation sourceModTwoMoore 1

/-- Its specified sphere class is the original Moore inclusion followed
by the original truncation unit. -/
noncomputable def sourceModTwoMooreHeartUnit :
    Prespectrum.sourceSphere 0 ⟶ sourceModTwoMooreHeart :=
  sourceModTwoMooreInclusion ≫ sourcePostnikovUnit sourceModTwoMoore 1

/-- The actual comparison to the fixed coefficient spectrum, obtained
from the proved universal property of the same truncation. -/
noncomputable def sourceModTwoMooreHeartToHF2 :
    sourceModTwoMooreHeart ⟶ sourceLocalization.obj sourceHF2.spectrum :=
  ((sourcePostnikovUnit_precomp_bijective sourceModTwoMoore 1
    (sourceLocalization.obj sourceHF2.spectrum)
    (fun d hd => sourceHF2.vanishes d (by omega))).surjective
      sourceModTwoMooreCoefficient).choose

end KIP126.StableHomotopy.Implementation
