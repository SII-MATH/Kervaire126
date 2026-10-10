import KIP126.Def.Solution.StandardRoute

/-! The one synthetic route selected by the explicit Def construction.
The construction remains unfinished in `Def/Solution/StandardRoute`; these
aliases select no second model and prove no external result. -/
namespace KIP126.Def

/-- The same synthetic route is used by every literature, computation and
Main consumer on the fixed classical implementation. -/
noncomputable abbrev standardRouteInput := Solution.standardRouteInput

end KIP126.Def

namespace KIP126.Classical.Adams

/-- The model of Def's one selected synthetic route. -/
noncomputable abbrev standardRouteModel := KIP126.Def.standardRouteInput.model

end KIP126.Classical.Adams
