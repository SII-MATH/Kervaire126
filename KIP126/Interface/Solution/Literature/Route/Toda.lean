import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

namespace KIP126.Interface.Solution.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.Literature.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Transport the actual secondary-operation calculation, retaining its
star/product identification. BHS ring facts alone are not sufficient. -/
theorem todaApplication_of_secondary (η : BiHom 1 2 (S_0_0 : Syn))
    (S : TodaSourceData (Syn := Syn)) (B : TodaSecondaryComparison η S) :
    TodaApplication η S := by
  refine ⟨B.low_bracket, ?_⟩
  intro θ hθ
  rw [← B.star_product θ]
  exact B.symmetric θ hθ

/-- The public Toda consumer delivery keeps source facts and internal
secondary-operation evidence separate until this final assembly. -/
theorem toda_of_source (η : BiHom 1 2 (S_0_0 : Syn)) (S : TodaSourceData (Syn := Syn))
    (A : TodaSourceResults D η S) (B : TodaSecondaryComparison η S) :
    Nonempty (TodaInputs D η) := by
  exact ⟨todaInputsOfSource D η S A (todaApplication_of_secondary η S B)⟩

end
end KIP126.Interface.Solution.Literature.Route
