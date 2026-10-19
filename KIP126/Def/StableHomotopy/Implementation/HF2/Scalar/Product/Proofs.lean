module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Data
public import KIP126.Def.Topology.SimplicialRealization.Product.Weak.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial
open Prespectrum Topology
open scoped unitInterval Topology.Homotopy
set_option backward.isDefEq.respectTransparency false

/-- The actual realization product comparison induces bijections on every
level cubical homotopy set, including degree zero. -/
theorem pairComparison_levelHomotopy_bijective (n r : ℕ) :
    Function.Bijective (pairComparison.levelHomotopy n r) := by
  let K := hf2SimplicialSet n
  let c := (pairLevel n).point
  let ev : C((piPrespectrum (fun _ : Fin 2 => hf2RealizationPrespectrum)).level n,
      |K| × |K|) := ⟨fun x => (x 0,x 1),(continuous_apply 0).prodMk (continuous_apply 1)⟩
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
        intro h
        have H := (Quotient.exact h).comp_continuousMap ev
        apply Quotient.sound
        exact (KIP126.Topology.SimplicialRealization.productComparison_homotopicRel_iff
          K K p.val q.val (Cube.boundary (Fin r))).mp H
  · intro x
    induction x using Quotient.inductionOn with
    | h p =>
      let a : GenLoop (Fin r) (|K| × |K|)
          (KIP126.Topology.SimplicialRealization.productComparison K K c) :=
        ⟨ev.comp p.val,fun t ht => by
          change (p t 0,p t 1) = (SSet.toTop.map _ c,SSet.toTop.map _ c)
          exact (congrArg ev (p.property t ht)).trans
            (Prod.ext (pairLevel_fst_point n).symm (pairLevel_snd_point n).symm)⟩
      obtain ⟨q,hq⟩ := KIP126.Topology.SimplicialRealization.genLoop_lift_productComparison
        K K c r a
      refine ⟨⟦q⟧,congrArg Quotient.mk'' ?_⟩
      apply GenLoop.ext
      intro t
      funext i
      fin_cases i
      · exact congrArg Prod.fst (ContinuousMap.congr_fun hq t)
      · exact congrArg Prod.snd (ContinuousMap.congr_fun hq t)

/-- The realized simplicial pair and the actual pointwise product agree
in the original stable localization. -/
theorem pairComparison_stableEquivalence : stableEquivalences pairComparison :=
  stableEquivalence_of_levelHomotopy_bijective pairComparison
    pairComparison_levelHomotopy_bijective

end KIP126.StableHomotopy.Implementation.HF2Scalar
