import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

/-! Moving the mathematical type to Def must preserve the stage signature. -/
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

example (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn) (X : C) :
    KIP126.Challenge2.FirstQuotientHomotopyComparison H N X =
      KIP126.Comparison.ClassicalSynthetic.FirstQuotientHomotopyComparison H N X := rfl
