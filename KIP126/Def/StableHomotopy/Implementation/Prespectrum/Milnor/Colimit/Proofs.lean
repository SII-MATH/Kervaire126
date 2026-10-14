module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- The displayed Milnor triangle is genuinely distinguished, using the
proved source coproduct and actual source distinguished-cofiber construction. -/
theorem sourceHomotopyColimit_distinguished (F : ℕ ⥤ SourceCategory.{u}) :
    Triangle.mk (sourceSequentialOneSubShift F) (sourceHomotopyColimitFromCoproduct F)
      (sourceHomotopyColimitBoundary F) ∈ distTriang SourceCategory :=
  HasFunctorialCofiber.cofib_distinguished (sourceSequentialOneSubShift F)

/-- The actual stage inclusions commute with each original adjacent map. -/
theorem sourceHomotopyColimitInclusion_step (F : ℕ ⥤ SourceCategory.{u}) (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ sourceHomotopyColimitInclusion F (n+1) =
      sourceHomotopyColimitInclusion F n := by
  have h := comp_distTriang_mor_zero₁₂ _ (sourceHomotopyColimit_distinguished F)
  have hn := congrArg (fun f => Sigma.ι F.obj n ≫ f) h
  change Sigma.ι F.obj n ≫
    ((𝟙 _ - sourceSequentialShiftMap F) ≫ sourceHomotopyColimitFromCoproduct F) = _ at hn
  simp only [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
    ← Category.assoc, sourceSequentialShiftMap, Sigma.ι_desc, comp_zero] at hn
  simpa only [sourceHomotopyColimitInclusion, Category.assoc] using (sub_eq_zero.mp hn).symm

/-- Every compatible family extends to the actual Milnor homotopy colimit.
Uniqueness is not asserted: its possible obstruction is retained by the triangle. -/
theorem sourceHomotopyColimit_exists_desc (F : ℕ ⥤ SourceCategory.{u}) {Y : SourceCategory.{u}}
    (a : ∀ n, F.obj n ⟶ Y)
    (ha : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n+1) = a n) :
    ∃ b : sourceHomotopyColimit F ⟶ Y, ∀ n, sourceHomotopyColimitInclusion F n ≫ b = a n := by
  let T := Triangle.mk (sourceSequentialOneSubShift F) (sourceHomotopyColimitFromCoproduct F)
    (sourceHomotopyColimitBoundary F)
  have hzero : sourceSequentialOneSubShift F ≫ Sigma.desc a = 0 := by
    apply Sigma.hom_ext
    intro n
    simp only [sourceSequentialOneSubShift, Preadditive.sub_comp, Category.id_comp,
      Preadditive.comp_sub, sourceSequentialShiftMap, Sigma.ι_desc_assoc, Sigma.ι_desc,
      Category.assoc, ha n, sub_self, comp_zero]
  obtain ⟨b, hb⟩ := T.yoneda_exact₂ (sourceHomotopyColimit_distinguished F) (Sigma.desc a) hzero
  change sourceHomotopyColimit F ⟶ Y at b
  change Sigma.desc a = sourceHomotopyColimitFromCoproduct F ≫ b at hb
  refine ⟨b, fun n => ?_⟩
  change (Sigma.ι F.obj n ≫ sourceHomotopyColimitFromCoproduct F) ≫ b = a n
  rw [Category.assoc, ← hb, Sigma.ι_desc]

end KIP126.StableHomotopy.Implementation
