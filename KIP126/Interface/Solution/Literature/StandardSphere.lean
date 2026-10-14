module

public import KIP126.Def.ClassicalAdams.SphereDifferential.Predicates
public import KIP126.Def.ClassicalAdams.SphereClasses.Products.Proofs
public import KIP126.Interface.Challenge.Literature.Delivery

@[expose] public section


set_option maxHeartbeats 1000000

/-! Readable wrappers for literature-backed standard sphere leaves.  The
underlying `LiteratureResults` field remains visible in the proof body and is
not converted into an untracked fact. -/

namespace KIP126.Interface.Solution.Literature

/-- Human-facing form of the standard one-line calculation. -/
theorem h4_d2_h0h3sq
    (literature : KIP126.Challenge2.LiteratureInterface) :
    KIP126.Classical.Adams.StandardSphere.h4D2H0H3Sq := by
  change KIP126.Core.SpectralSequence.HasDifferential KIP126.Classical.Adams.sphereAdamsData 2
    (1, 16) (3, 17)
    (KIP126.Classical.Adams.Sphere.Internal.hi KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations 4)
    (KIP126.Classical.Adams.Sphere.Internal.h0HiSquare KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations 3)
  convert (literature.results.adamsOneLine_d2 4 (by decide)).toHasDifferential using 1 <;>
    norm_num

/-- The literature result also records that the target class is nonzero. -/
theorem h4_d2_h0h3sq_nonzero
    (literature : KIP126.Challenge2.LiteratureInterface) :
    KIP126.Classical.Adams.StandardSphere.h4D2H0H3SqNonzero := by
  change KIP126.Core.SpectralSequence.HasNonzeroDifferential KIP126.Classical.Adams.sphereAdamsData 2
    (1, 16) (3, 17)
    (KIP126.Classical.Adams.Sphere.Internal.hi KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations 4)
    (KIP126.Classical.Adams.Sphere.Internal.h0HiSquare KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations 3)
  convert literature.results.adamsOneLine_d2 4 (by decide) using 1 <;>
    norm_num

/- The same certificate with the uniform list code `[0, 3, 3]`.  The bridge
   theorem identifies this target with the existing mathematical class, so
   this is not a second differential assumption. -/
theorem h4_d2_standard_list
    (literature : KIP126.Challenge2.LiteratureInterface) :
    KIP126.Classical.Adams.StandardSphere.h4D2H033 := by
  unfold KIP126.Classical.Adams.StandardSphere.h4D2H033
  change KIP126.Core.SpectralSequence.HasDifferential KIP126.Classical.Adams.sphereAdamsData 2
    (1, 16) (3, 17)
    (KIP126.Classical.Adams.StandardSphere.standardHi 4)
    (KIP126.Classical.Adams.StandardSphere.standardHProduct [0, 3, 3])
  rw [KIP126.Classical.Adams.StandardSphere.standardHProduct]
  rw [KIP126.Classical.Adams.Sphere.Internal.hMonomial_zero_three_eq_h0HiSquare]
  exact h4_d2_h0h3sq literature

end KIP126.Interface.Solution.Literature
