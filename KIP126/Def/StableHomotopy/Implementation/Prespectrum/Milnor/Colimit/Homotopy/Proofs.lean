module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Cocone.Proofs
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Coproduct.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Homological.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual Milnor cofiber arrow gives the cokernel on the unchanged
stable homotopy groups. Injectivity of the shifted direct-sum difference
kills the boundary in the actual long exact sequence. -/
noncomputable def sourceHomotopyColimit_stableHomotopy_isCokernel
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ) :
    IsColimit (CokernelCofork.ofπ
      ((sourceStableHomotopyAddFunctor d).map (sourceHomotopyColimitFromCoproduct F))
      (show (sourceStableHomotopyAddFunctor d).map (sourceSequentialOneSubShift F) ≫
          (sourceStableHomotopyAddFunctor d).map (sourceHomotopyColimitFromCoproduct F) = 0 from by
        rw [← Functor.map_comp, ← Functor.map_zero (sourceStableHomotopyAddFunctor d)]
        exact congrArg ((sourceStableHomotopyAddFunctor d).map)
          (comp_distTriang_mor_zero₁₂ _ (sourceHomotopyColimit_distinguished F)))) := by
  let G := sourceStableHomotopyAddFunctor d
  let T := Triangle.mk (sourceSequentialOneSubShift F) (sourceHomotopyColimitFromCoproduct F)
    (sourceHomotopyColimitBoundary F)
  have hT : T ∈ distTriang SourceCategory := sourceHomotopyColimit_distinguished F
  haveI : Mono (G.map (T.mor₁⟦(1 : ℤ)⟧')) :=
    sourceSequentialOneSubShift_map_mono F (shiftFunctor SourceCategory (1 : ℤ) ⋙ G)
  have hz : G.map T.mor₃ = 0 := by
    apply (cancel_mono (G.map (T.mor₁⟦(1 : ℤ)⟧'))).mp
    rw [zero_comp, ← G.map_comp, comp_distTriang_mor_zero₃₁ _ hT, G.map_zero]
  haveI : Epi (G.map T.mor₂) :=
    (G.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).epi_f hz
  haveI : Epi (((shortComplexOfDistTriangle T hT).map G).g) := by
    change Epi (G.map T.mor₂)
    infer_instance
  exact (G.map_distinguished_exact T hT).gIsCokernel

/-- Stable homotopy sends the actual Milnor cocone to the genuine colimit
of the original sequence of abelian groups, in every degree. -/
noncomputable def sourceHomotopyColimit_stableHomotopy_isColimit
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ) :
    IsColimit ((sourceStableHomotopyAddFunctor d).mapCocone (sourceHomotopyColimitCocone F)) := by
  let G := sourceStableHomotopyAddFunctor d
  let c : Cofan (F ⋙ G).obj := Cofan.mk (G.obj (∐ F.obj))
    (fun n => G.map (Sigma.ι F.obj n))
  have hc : IsColimit c := isColimitOfHasCoproductOfPreservesColimit G F.obj
  have hd (n : ℕ) : c.inj n ≫ G.map (sourceSequentialOneSubShift F) =
      c.inj n - (F ⋙ G).map (homOfLE (Nat.le_succ n)) ≫ c.inj (n+1) := by
    change G.map (Sigma.ι F.obj n) ≫ G.map (sourceSequentialOneSubShift F) = _
    rw [← G.map_comp, sourceSequentialOneSubShift_inclusion, G.map_sub, G.map_comp]
    rfl
  let q := CokernelCofork.ofπ (G.map (sourceHomotopyColimitFromCoproduct F))
    (show G.map (sourceSequentialOneSubShift F) ≫
        G.map (sourceHomotopyColimitFromCoproduct F) = 0 from by
      rw [← G.map_comp, ← G.map_zero]
      exact congrArg G.map
        (comp_distTriang_mor_zero₁₂ _ (sourceHomotopyColimit_distinguished F)))
  have hq : IsColimit q := sourceHomotopyColimit_stableHomotopy_isCokernel F d
  let h := Foundation.sequenceCokernelCocone_isColimit (F ⋙ G) c hc
    (G.map (sourceSequentialOneSubShift F)) hd q hq
  refine IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _) ?_)
  intro n
  change (G.map (Sigma.ι F.obj n) ≫ G.map (sourceHomotopyColimitFromCoproduct F)) ≫ 𝟙 _ =
    G.map (Sigma.ι F.obj n ≫ sourceHomotopyColimitFromCoproduct F)
  rw [Category.comp_id, G.map_comp]

/-- The same actual colimit computation holds for the original underlying
stable homotopy sets, since the indexing sequence is filtered. -/
noncomputable def sourceHomotopyColimit_homotopy_isColimit
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ) :
    IsColimit ((sourceStableHomotopyFunctor d).mapCocone (sourceHomotopyColimitCocone F)) := by
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  rw [← sourceStableHomotopyAddFunctor_forget]
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves (forget AddCommGrpCat)
      (sourceHomotopyColimit_stableHomotopy_isColimit F d))
    (Functor.mapCoconeMapCocone (sourceHomotopyColimitCocone F))

end KIP126.StableHomotopy.Implementation
