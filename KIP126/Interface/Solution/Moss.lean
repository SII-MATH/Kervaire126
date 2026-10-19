module

public import KIP126.Interface.Challenge.Challenge2
public import KIP126.Interface.Solution.Literature.Delivery

@[expose] public section

namespace KIP126.Interface.Solution

/-- Reassemble the original compatibility package from Def's fixed context and
the Moss conclusion on that exact context. No new composition or convergence
data are chosen, and this adapter does not establish the source premise. -/
theorem sphereMossInterface_of_literature
    (literature : KIP126.Challenge2.LiteratureInterface) :
    Nonempty KIP126.Challenge2.StandardSphereMossInterface := by
  let c := KIP126.Def.StageInput.witness
  letI : KIP126.Foundation.TensorInput c.foundationInput := c.tensorInput
  exact ⟨{
    composition := KIP126.Def.standardSphereMossContext.composition
    coherent := KIP126.Def.standardSphereMossContext.coherent
    convergence := KIP126.Def.standardSphereMossContext.convergence
    weak_convergence := KIP126.Def.standardSphereMossContext.weak_convergence
    detection := KIP126.Def.standardSphereMossContext.detection
    indeterminacy := KIP126.Def.standardSphereMossContext.indeterminacy
    moss := literature.results.moss }⟩

/-- am8/am15 compatibility existence API, derived from the same literature
delivery used by Challenge2. The context construction and source conclusion
retain their explicit unfinished proofs upstream. -/
theorem sphereMossInterface : Nonempty KIP126.Challenge2.StandardSphereMossInterface := by
  exact sphereMossInterface_of_literature Literature.Route.sourceLiterature

end KIP126.Interface.Solution
