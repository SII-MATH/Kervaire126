module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual binary coproduct of any two cubical cofibrations is a
cubical cofibration. Its lift is assembled from the two original lifts. -/
theorem IsCubicalCofibration.coprod {A B C D : Prespectrum.{u}}
    {i : A ⟶ B} {j : C ⟶ D} (hi : IsCubicalCofibration i) (hj : IsCubicalCofibration j) :
    IsCubicalCofibration (coprod.map i j) := by
  intro E F p hp
  letI := hi p hp
  letI := hj p hp
  constructor
  intro t b sq
  let sqi : CommSq (coprod.inl ≫ t) i p (coprod.inl ≫ b) := ⟨by
    rw [Category.assoc,sq.w,coprod.inl_map_assoc]⟩
  let sqj : CommSq (coprod.inr ≫ t) j p (coprod.inr ≫ b) := ⟨by
    rw [Category.assoc,sq.w,coprod.inr_map_assoc]⟩
  refine CommSq.HasLift.mk' {
    l := coprod.desc sqi.lift sqj.lift
    fac_left := ?_
    fac_right := ?_ }
  · apply coprod.hom_ext
    · rw [coprod.inl_map_assoc,coprod.inl_desc]
      exact sqi.fac_left
    · rw [coprod.inr_map_assoc,coprod.inr_desc]
      exact sqj.fac_left
  · apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc]
      exact sqi.fac_right
    · rw [coprod.inr_desc_assoc]
      exact sqj.fac_right

end KIP126.StableHomotopy.Implementation.Prespectrum
