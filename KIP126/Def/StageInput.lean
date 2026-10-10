import KIP126.Def.StableHomotopy.Implementation.Fixed

/-! All target objects use the one implementation fixed in Def. This alias
contains no project-input proof and no consumer axiom. -/
namespace KIP126.Def.StageInput

noncomputable def witness : KIP126.Implementation := KIP126.Def.fixedImplementation

end KIP126.Def.StageInput
