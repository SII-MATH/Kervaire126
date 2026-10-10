import KIP126.Def.StableHomotopy.Implementation.Fixed

/-! The route model type on the fixed classical foundation. The selected
synthetic construction is supplied by `Route/Fixed`; this module only defines
its type and therefore does not depend on that construction or its proofs. -/
namespace KIP126.Classical.Adams
/-- The complete route-input language over the one fixed classical model. -/
noncomputable abbrev StandardRouteInput :=
  KIP126.Foundation.RouteInput KIP126.Def.fixedImplementation.foundationInput
    KIP126.Def.fixedImplementation.milnorInput

end KIP126.Classical.Adams
