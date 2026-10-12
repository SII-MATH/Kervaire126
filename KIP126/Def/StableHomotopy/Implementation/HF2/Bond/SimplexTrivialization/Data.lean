module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.Comparison
public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.Fibration
public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open KIP126.Core.SimplicialModule
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The explicit degeneracy lift of a coefficient simplex into the path object. -/
noncomputable def hf2PathSimplexLift (n r : ℕ) (b : (hf2SimplicialModule (n+1)).obj (op ⦋r⦌)) :
    (decalage (hf2SimplicialModule (n+1))).obj (op ⦋r⦌) :=
  (decalageProjectionSplitEpi (hf2SimplicialModule (n+1)) (op ⦋r⦌)).section_ b

/-- The actual endpoint projection is explicitly a product over every
coefficient simplex, with the actual realized simplicial kernel as fiber. -/
noncomputable def hf2PathSimplexHomeomorph (n r : ℕ)
    (b : (hf2SimplicialModule (n+1)).obj (op ⦋r⦌)) :
    (loopRealizationLevel n × |(Δ[r] : SSet.{0})|) ≃ₜ
      principalRealizationPullback (decalageProjection (hf2SimplicialModule (n+1))) b :=
  principalRealizationHomeomorph (decalageProjection (hf2SimplicialModule (n+1)))
    b (hf2PathSimplexLift n r b) (ConcreteCategory.congr_hom (decalageProjectionSplitEpi (hf2SimplicialModule (n+1)) (op ⦋r⦌)).id b)

/-- The same actual product chart with the precise previous coefficient
level as fiber, through its proved normalized coefficient isomorphism. -/
noncomputable def hf2CoefficientSimplexHomeomorph (n r : ℕ)
    (b : (hf2SimplicialModule (n+1)).obj (op ⦋r⦌)) :
    (hf2RealizationLevel n × |(Δ[r] : SSet.{0})|) ≃ₜ
      principalRealizationPullback (decalageProjection (hf2SimplicialModule (n+1))) b :=
  ((coefficientLoopRealizationHomeomorph n).prodCongr (Homeomorph.refl _)).trans
    (hf2PathSimplexHomeomorph n r b)


end KIP126.StableHomotopy.Implementation.HF2Bond
