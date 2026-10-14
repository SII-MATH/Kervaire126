module

public import KIP126.Interface.Challenge.Computation.Delivery
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Hi.Proofs
public import KIP126.LinProgram.Certificates.AdamsOneLine.H4Target

@[expose] public section


/-!
# Interface/Solution/LinProgram/AdamsOneLine/H4

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Producer-side certification of a nonzero database d₂ record on the
actual fixed sphere. Both coordinate identifications follow from independent
degree exhaustion and specified-class nonvanishing. In particular, the
presentation's arbitrary product is not equated with the canonical cobar cup
product. The retained one-line literature result remains an explicit input;
this does not reconstruct the secondary-operation calculation behind `d2`.
-/

namespace KIP126.Interface.Solution.LinProgram

open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.LinE2

/-- The data source spans the full degree-(1,16) component of actual E₂. -/
theorem sphereH4_exhaustive (P : LinE2Presentation)
    (x : sphereAdamsData.Page 2 (1, 16)) :
    x = 0 ∨ x = P.comparison 1 16 (by decide) OneLine.dataH4 := KIP126.Core.Algebra.LinearEquiv.zero_or_of_exhaustion
    (P.comparison 1 16 (by decide)) OneLine.dataH4 OneLine.E2At_h4_eq_zero_or x

/-- CSV h₄ denotes the existing standard Milnor class. -/
theorem sphereH4_standard_class (P : LinE2Presentation) :
    P.comparison 1 16 (by decide) OneLine.dataH4 =
      Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 4 := KIP126.Core.Algebra.LinearEquiv.image_eq_of_exhaustion
    (P.comparison 1 16 (by decide)) OneLine.dataH4 OneLine.E2At_h4_eq_zero_or _
    (MilnorCohomology.internal_hi_ne_zero standardFoundation.hf2 standardMilnorCooperations 4)

/-- Degree-(3,17) exhaustion is a mathematical consequence of the fixed
quotient's generating degrees, without assuming a CSV basis certificate. -/
theorem sphereH0H3Sq_exhaustive (P : LinE2Presentation)
    (x : sphereAdamsData.Page 2 (3, 17)) :
    x = 0 ∨ x = P.comparison 3 17 (by decide) OneLine.dataH0H3Sq := KIP126.Core.Algebra.LinearEquiv.zero_or_of_exhaustion
    (P.comparison 3 17 (by decide)) OneLine.dataH0H3Sq OneLine.E2At_h0h3Sq_eq_zero_or x

/-- The explicit literature result certifies nonvanishing of the canonical
target. At page two its page representative is the same element. -/
theorem sphereH0H3Sq_ne_zero
    (literature : KIP126.Challenge2.LiteratureInterface) :
    Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations 3 ≠ 0 := by
  have h := literature.results.adamsOneLine_d2 4 (by decide)
  obtain ⟨_, _, yr, _, hy, _, hne⟩ := h
  exact fun hz => hne (hy.eq_on_page_two.symm.trans hz)

/-- CSV h₀h₃² denotes the canonical cobar target using its unique nonzero
class. No general comparison of the two multiplications is assumed. -/
theorem sphereH0H3Sq_standard_class
    (literature : KIP126.Challenge2.LiteratureInterface) (P : LinE2Presentation) :
    P.comparison 3 17 (by decide) OneLine.dataH0H3Sq =
      Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations 3 := KIP126.Core.Algebra.LinearEquiv.image_eq_of_exhaustion
    (P.comparison 3 17 (by decide)) OneLine.dataH0H3Sq OneLine.E2At_h0h3Sq_eq_zero_or _
    (sphereH0H3Sq_ne_zero literature)

/-- Exact original source CSV coordinates. -/
theorem h4_hasCoordinates : KIP126.Challenge2.HasCoordinates OneLine.dataH4 [0] := by
  refine ⟨[OneLine.h4Row], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨OneLine.h4Row_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using OneLine.h4_value

/-- Exact original target CSV coordinates. -/
theorem h0h3Sq_hasCoordinates :
    KIP126.Challenge2.HasCoordinates OneLine.dataH0H3Sq [0] := by
  refine ⟨[OneLine.targetRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨OneLine.targetRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using OneLine.target_value

/-- The database's named source and nonzero target satisfy the actual fixed
sphere differential, conditional only on the existing supplied literature
delivery and presentation. -/
theorem row5434_hasNonzeroDifferential
    (literature : KIP126.Challenge2.LiteratureInterface) (P : LinE2Presentation) :
    HasNonzeroDifferential sphereAdamsData 2 (1, 16) (3, 17)
      (P.comparison 1 16 (by decide) OneLine.dataH4)
      (P.comparison 3 17 (by decide) OneLine.dataH0H3Sq) := by
  rw [sphereH4_standard_class, sphereH0H3Sq_standard_class literature]
  exact literature.results.adamsOneLine_d2 4 (by decide)

/-- The same source cannot have a zero d₂ target. This rejects changing the
record's nonzero target into the empty coordinate vector. -/
theorem row5434_rejects_zero
    (literature : KIP126.Challenge2.LiteratureInterface) (P : LinE2Presentation) :
    ¬ HasDifferential sphereAdamsData 2 (1, 16) (3, 17)
      (P.comparison 1 16 (by decide) OneLine.dataH4) 0 := by
  intro hz
  obtain ⟨_, hd⟩ :=
    (row5434_hasNonzeroDifferential literature P).toHasDifferential.eq_on_page_two
  obtain ⟨_, hzero⟩ := hz.eq_on_page_two
  have htargetzero := hd.symm.trans hzero
  rw [sphereH0H3Sq_standard_class literature] at htargetzero
  exact sphereH0H3Sq_ne_zero literature htargetzero

set_option maxHeartbeats 2000000 in
/-- Full mathematical interpretation of proofs.db row 5434, retaining both
literal coordinate checks and page-representative obligations. -/
theorem row5434 (literature : KIP126.Challenge2.LiteratureInterface)
    (P : LinE2Presentation) :
    KIP126.Challenge2.DifferentialStatement P ⟨5434, "d2", 1, 16, 2, [0], [0]⟩ := by
  obtain ⟨h, xr, yr, hx, hy, hd⟩ :=
    (row5434_hasNonzeroDifferential literature P).toHasDifferential
  dsimp only [KIP126.Challenge2.DifferentialStatement]
  refine ⟨by decide, by decide, OneLine.dataH4, OneLine.dataH0H3Sq,
    h4_hasCoordinates, h0h3Sq_hasCoordinates, h, xr, yr, ?_, ?_, ?_⟩
  · exact hx
  · exact hy
  · exact hd

end KIP126.Interface.Solution.LinProgram
