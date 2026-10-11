module

public import KIP126.Interface.Challenge.Challenge2
public import KIP126.Interface.Solution.Literature.Delivery

@[expose] public section

/-! Construction track for the package Interface must deliver to Main. -/
namespace KIP126.Interface.Solution

noncomputable def challenge2 : KIP126.Challenge2 := by
  refine {
    literature := Literature.Route.sourceLiterature
    computation := ?_ }
  -- All computation bindings and certificates must use this exact literature
  -- delivery. The derived Moss/tmf compatibility views are not producer inputs.
  sorry

/-- The literature part retains its source bindings on Def's fixed model.
This projection carries the source producer's existing proof debt. -/
theorem literatureInterface :
    Nonempty KIP126.Challenge2.LiteratureInterface := by
  let input := challenge2
  exact ⟨input.literature⟩

/-- C(M) retains one presentation for all computation conclusions.
This projection does not combine independently chosen presentation witnesses. -/
theorem computationInterface :
    ∃ literature : KIP126.Challenge2.LiteratureInterface,
      Nonempty (KIP126.Challenge2.ComputationInterface literature) := by
  let input := challenge2
  exact ⟨input.literature, ⟨input.computation⟩⟩

end KIP126.Interface.Solution
