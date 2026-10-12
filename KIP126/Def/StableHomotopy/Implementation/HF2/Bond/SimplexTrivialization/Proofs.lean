module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.SimplexTrivialization.Data
public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.CubicalComparison.Proofs
public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Lifting

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open KIP126.Core.SimplicialModule KIP126.Topology.HomotopyLifting
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem hf2PathSimplexLift_projection (n r : ℕ)
    (b : (hf2SimplicialModule (n+1)).obj (op ⦋r⦌)) :
    ((decalageProjection (hf2SimplicialModule (n+1))).app (op ⦋r⦌)).hom
      (hf2PathSimplexLift n r b) = b :=
  ConcreteCategory.congr_hom (decalageProjectionSplitEpi (hf2SimplicialModule (n+1)) (op ⦋r⦌)).id b

@[simp] theorem hf2CoefficientSimplexHomeomorph_snd (n r : ℕ)
    (b : (hf2SimplicialModule (n+1)).obj (op ⦋r⦌))
    (x : hf2RealizationLevel n × |(Δ[r] : SSet.{0})|) :
    (hf2CoefficientSimplexHomeomorph n r b x).val.2 = x.2 :=
  principalRealizationHomeomorph_snd _ _ _ _ _

/-- A homotopy through a single specified coefficient simplex has an actual
lift to the HF₂ path object preserving the given bottom and any selected sides. -/
theorem hf2PathProjection_exists_cubeFacesLift_over_simplex (n r d : ℕ)
    (b : (hf2SimplicialModule (n+1)).obj (op ⦋r⦌)) (faces : Set (Fin d × Bool))
    (g : C(CylinderHorn (Fin d → I) (cubeFacesBoundary d faces),
      pathRealizationLevel (hf2SimplicialModule (n+1))))
    (H : C(I × (Fin d → I), |(Δ[r] : SSet.{0})|))
    (hcomm : ∀ w, hf2PathProjection n (g w) =
      SSet.toTop.map ((SSet.yonedaEquiv (X := hf2SimplicialSet (n+1))).symm b) (H w.val)) :
    ∃ L : C(I × (Fin d → I), pathRealizationLevel (hf2SimplicialModule (n+1))),
      (∀ w, hf2PathProjection n (L w) =
        SSet.toTop.map ((SSet.yonedaEquiv (X := hf2SimplicialSet (n+1))).symm b) (H w)) ∧
      (∀ w : CylinderHorn (Fin d → I) (cubeFacesBoundary d faces), L w.val = g w) :=
  principalRealization_exists_cubeFacesLift (decalageProjection (hf2SimplicialModule (n+1)))
    b (hf2PathSimplexLift n r b) (hf2PathSimplexLift_projection n r b) d faces g H hcomm


end KIP126.StableHomotopy.Implementation.HF2Bond
