module

public import KIP126.Main.Solution.StageInput.Bindings
import KIP126.Main.Solution.StageInput.Toda.Product
import KIP126.Main.Solution.StageInput.Toda.Low
import KIP126.Main.Solution.StageInput.Toda.Symmetric

@[expose] public section

namespace KIP126.Main.StageInput

open KIP126.Synthetic.Context KIP126.Kervaire.Route KIP126.Literature.Route in
@[no_expose]
noncomputable def todaSecondaryComparison :
    KIP126.Literature.Route.TodaSecondaryComparison routeEta
      literature.bindings.route.todaSource := by
  let twoStar : BiHom 1 0 (S_0_0 : KIP126.Def.standardRouteInput.Syn) :=
    lambdaMultiply 2 routeEta
  have hstar : ∀ θ : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn),
      sphereProduct twoStar θ = lambdaMultiply 2 (sphereProduct routeEta θ) := by
    intro θ
    exact Toda.secondary_star_product routeModel routeEta θ
  exact {
    low_bracket := Toda.low_bracket
    twoStar := twoStar
    symmetric := by
      intro θ hθ
      rw [hstar θ]
      exact Toda.symmetric_bracket θ hθ
    star_product := hstar }

end KIP126.Main.StageInput
