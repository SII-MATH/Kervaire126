module

import KIP126.Main.Solution.Route.Section7.ThetaMassey
import KIP126.Main.Solution.Route.Section7.WeakY
import KIP126.Def.Kervaire.Route.Tools.PageExtensionStretching.Proofs
import KIP126.Interface.Solution.Literature.Route.May

/-! Consumers of the public mathematical handoffs.
These examples must elaborate using ordinary imports alone. They preserve the
whole `(7, 70)` source, the same weak representative, and all supplied hypotheses.
Successful compilation checks accessibility and types, not proof completion.
-/
namespace KIP126.Checks.ModuleBoundaries

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Classical.Adams.PageRepresentatives
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Main.StageInput
open KIP126.Main.Solution.Route.Section7

universe u v w

example {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
    {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : TmfLabels H} (I : KIP126.Computation.Route.Inputs D L G) :
    ∀ b : E2 H SphereSpectrum 7 70,
      Sphere.Internal.product H M (s := 2) (t := 64) (s' := 7) (t' := 70)
        (Sphere.Internal.hiSquare H M 5) b = 0 :=
  h5_square_times_entire_770_zero I

example (hc3 : C3 routeLabels)
    (hc5 : C5 standardMilnorCooperations routeModel.toModelData routeLabels routeEta) :
    ∃ y : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      FiniteDetected routeModel 9 (by decide) 11 136 4 eY y ∧
      lambdaMultiply 2 (sphereAction routeLiterature.toda.h0 y) ≠ 0 :=
  weak_y_exists hc3 hc5

example {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
    {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
    (D : Model H M Syn) (synthetic : SyntheticInputs D) (X : ClassicalObject)
    (q : ℕ) (hq : 0 < q) (a s t : ℤ) (x : E2 H (X.obj D.auxiliary) s t)
    (hx : x ∈ cycles H (X.obj D.auxiliary) q (s,t)) :
    ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,a) (.nu X))).obj
        D.nu D.auxiliary)).sequence.ssData (s,t,t+a-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t+a-(0:ℕ))
        (finiteNuLabel D X q a s t 0 x) e :=
  KIP126.Main.Solution.Tools.shifted_finite_source_exists D synthetic X q hq a s t x hx

example {Syn : Type u} [SyntheticCategory.{u,v} Syn] (B : MayContext Syn)
    (hB : MaySourceResults Syn B) : B.SignedBoundary :=
  KIP126.Interface.Solution.Literature.Route.may_signed_boundary_of_source B hB

end KIP126.Checks.ModuleBoundaries
