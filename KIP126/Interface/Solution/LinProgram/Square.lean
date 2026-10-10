import KIP126.Interface.Challenge.Challenge2
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Proofs
import KIP126.LinProgram.Certificates.SquareDimension.Proofs
import KIP126.Def.StageInput.StandardSphere.Classes.Proofs

namespace KIP126.Interface.Solution

/-- Deliver the fixed square's nonvanishing, exhaustive degree-(2,128)
description and standard cobar label, using one specified comparison. -/
theorem sphereSquare (P : KIP126.Classical.Adams.LinE2Presentation) :
    KIP126.Challenge2.SphereSquareInterface P := by
  have exhaustive : ∀ x : KIP126.Classical.Adams.sphereAdamsData.Page 2 (2, 128),
      x = 0 ∨ x = P.comparison 2 128 (by decide) KIP126.LinE2.dataH6Sq := by
    intro x
    obtain ⟨a, rfl⟩ := (P.comparison 2 128 (by decide)).surjective x
    rcases KIP126.LinE2.E2At_square_eq_zero_or a with rfl | rfl
    · exact Or.inl (map_zero _)
    · exact Or.inr rfl
  exact
    { nonzero := fun hz => KIP126.LinE2.SquareDetection.dataH6Sq_ne_zero
        ((P.comparison 2 128 (by decide)).map_eq_zero_iff.mp hz)
      exhaustive := exhaustive
      standard_class := ((exhaustive KIP126.Classical.Adams.standardH6Square).resolve_left
        KIP126.Classical.Adams.standardH6Square_ne_zero).symm }

end KIP126.Interface.Solution
