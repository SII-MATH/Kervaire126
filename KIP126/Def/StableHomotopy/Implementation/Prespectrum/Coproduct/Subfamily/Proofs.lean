module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Subfamily.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem coproductSubfamilyMap_retraction {J : Type u}
    (X : J → Prespectrum.{u}) (s : Set J) :
    coproductSubfamilyMap X s ≫ coproductSubfamilyRetraction X s = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro j
  simp only [coproductSubfamilyMap,coproductSubfamilyRetraction,← Category.assoc,
    Sigma.ι_desc,Category.comp_id,dif_pos j.property]

/-- Subfamily inclusion is injective at every actual spectrum level. -/
theorem coproductSubfamilyMap_level_injective {J : Type u}
    (X : J → Prespectrum.{u}) (s : Set J) (n : ℕ) :
    Function.Injective ((coproductSubfamilyMap X s).level n) := by
  have h : Function.LeftInverse ((coproductSubfamilyRetraction X s).level n)
      ((coproductSubfamilyMap X s).level n) := fun z =>
    congrArg (fun f => f.level n z) (coproductSubfamilyMap_retraction X s)
  exact h.injective

end KIP126.StableHomotopy.Implementation.Prespectrum
