import KIP126.Def.StageInput.StandardSphere.Route.Data

/-! Construction of the selected synthetic route on the fixed classical
implementation.

The intended source is the hypercomplete category of spherical sheaves of
spectra on the finite HF₂-projective ∞-site. Its synthetic analogue ν, λ,
Adams tower, λ-inversion recovery, detector and comparisons must all come
from that construction over the same fixed HF₂-local classical category.
This is the construction of one specified background, rather than a choice
from an unqualified `Nonempty StandardRouteInput`.

The source construction is not yet implemented. Its missing proof and data
are exposed by the `sorry` in this Solution declaration; a mere inhabitant
of the abstract route type does not establish its source identification.
No literature conclusion, computation result or Main deduction is supplied
here. Source results and their applicability to this construction remain
separate Interface obligations.
-/
namespace KIP126.Def.Solution

/-- Construct the selected Pstrągowski synthetic background and its actual
route structures over Def's one fixed classical implementation. Completing
this declaration requires the specified source construction and all
structural properties recorded in `RouteInput.model`. -/
noncomputable def standardRouteInput : KIP126.Classical.Adams.StandardRouteInput := by
  sorry

end KIP126.Def.Solution
