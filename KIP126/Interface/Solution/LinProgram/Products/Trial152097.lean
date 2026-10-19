module

public import KIP126.LinProgram.Certificates.Products.Trial152097Coordinates
public import KIP126.Interface.Challenge.Computation.Presentation

@[expose] public section


/-!
# Interface/Solution/LinProgram/Products/Trial152097

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Transport the two native product identities through one supplied Lin E2
presentation. These are identities for that presentation's product; they do
not construct the presentation, compare its product with a tower pairing,
or prove the trial refutation or the retained differential record 152098. -/
namespace KIP126.Interface.Solution.LinProgram.ReplayProducts
open KIP126.LinE2
open KIP126.Classical.Adams

/-- The image of native (4,42)[1] times native (1,2)[0] is zero. -/
theorem source_mul_multiplier (P : LinE2Presentation) :
    P.product 4 42 1 2
      (P.comparison 4 42 (by decide) ReplayCoordinates.source)
      (P.comparison 1 2 (by decide) dataH1) = 0 := by
  have h := P.comparison_mul 4 42 1 2 (by decide)
    ReplayCoordinates.source dataH1 0
    (congrArg Subtype.val ReplayCoordinates.source_mul_multiplier)
  simpa only [map_zero] using h.symm

/-- The images of native (1,2)[0] and trial target (8,45)[0] multiply
 to the image of native (9,47)[0], using this same comparison throughout. -/
theorem multiplier_mul_trialTarget (P : LinE2Presentation) :
    P.product 1 2 8 45
      (P.comparison 1 2 (by decide) dataH1)
      (P.comparison 8 45 (by decide) ReplayCoordinates.trialTarget) =
      P.comparison 9 47 (by decide) ReplayCoordinates.productTarget := by
  exact (P.comparison_mul 1 2 8 45 (by decide)
    dataH1 ReplayCoordinates.trialTarget ReplayCoordinates.productTarget
    (congrArg Subtype.val ReplayCoordinates.multiplier_mul_trialTarget)).symm

end KIP126.Interface.Solution.LinProgram.ReplayProducts
