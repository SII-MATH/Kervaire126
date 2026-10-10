import KIP126.Main.Solution.StageInput

/-! Compatibility name for the unique presentation indexing the computation group
in the shared Challenge 2 witness. -/
namespace KIP126.Classical.Adams

noncomputable def linE2Presentation : LinE2Presentation :=
  KIP126.Main.StageInput.computation.bindings.presentation

end KIP126.Classical.Adams
