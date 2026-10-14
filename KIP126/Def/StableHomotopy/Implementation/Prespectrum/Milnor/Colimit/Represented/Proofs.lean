module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Cocone.Proofs
public import KIP126.Def.Algebra.InverseSequence.Surjective.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- Surjective precomposition along the mapped sequence solves the
actual coproduct Milnor difference equation on maps into the target. -/
theorem sourceSequentialOneSubShift_map_precomp_surjective
    (F : ℕ ⥤ SourceCategory.{u}) (G : SourceCategory.{u} ⥤ SourceCategory.{u})
    [G.Additive] [PreservesColimit (Discrete.functor F.obj) G] (Y : SourceCategory.{u})
    (hF : ∀ k, Function.Surjective (fun a : G.obj (F.obj (k+1)) ⟶ Y =>
      G.map (F.map (homOfLE (Nat.le_succ k))) ≫ a)) :
    Function.Surjective (fun a : G.obj (∐ F.obj) ⟶ Y =>
      G.map (sourceSequentialOneSubShift F) ≫ a) := by
  intro b
  let c : Cofan (F ⋙ G).obj := Cofan.mk (G.obj (∐ F.obj))
    (fun n => G.map (Sigma.ι F.obj n))
  let hc : IsColimit c := isColimitOfHasCoproductOfPreservesColimit G F.obj
  let f (k : ℕ) : (G.obj (F.obj (k+1)) ⟶ Y) →+ (G.obj (F.obj k) ⟶ Y) :=
    { toFun := fun a => G.map (F.map (homOfLE (Nat.le_succ k))) ≫ a
      map_zero' := by simp
      map_add' := by intros; simp only [Preadditive.comp_add] }
  obtain ⟨a, ha⟩ := KIP126.Core.InverseSequence.surjective_sub_shift_of_surjective
    (fun k => G.obj (F.obj k) ⟶ Y) f hF (fun k => c.inj k ≫ b)
  have hdesc (k : ℕ) : G.map (Sigma.ι F.obj k) ≫ hc.desc (Cofan.mk Y a) = a k :=
    hc.fac _ ⟨k⟩
  refine ⟨hc.desc (Cofan.mk Y a), ?_⟩
  apply Cofan.IsColimit.hom_ext hc
  intro k
  change G.map (Sigma.ι F.obj k) ≫
    (G.map (sourceSequentialOneSubShift F) ≫ hc.desc (Cofan.mk Y a)) = _
  rw [← Category.assoc, ← G.map_comp, sourceSequentialOneSubShift_inclusion,
    G.map_sub, G.map_comp, Preadditive.sub_comp, Category.assoc]
  rw [hdesc, hdesc]
  exact congrFun ha k

/-- Surjectivity of the shifted represented transitions removes exactly
the Milnor ambiguity for maps out of this actual homotopy colimit. -/
theorem sourceHomotopyColimit_hom_ext_of_step_precomp_surjective
    (F : ℕ ⥤ SourceCategory.{u}) (Y : SourceCategory.{u})
    (hF : ∀ k, Function.Surjective (fun a : (F.obj (k+1))⟦(1 : ℤ)⟧ ⟶ Y =>
      (F.map (homOfLE (Nat.le_succ k)))⟦(1 : ℤ)⟧' ≫ a))
    {a b : sourceHomotopyColimit F ⟶ Y}
    (hab : ∀ k, sourceHomotopyColimitInclusion F k ≫ a =
      sourceHomotopyColimitInclusion F k ≫ b) : a = b := by
  let T := Triangle.mk (sourceSequentialOneSubShift F) (sourceHomotopyColimitFromCoproduct F)
    (sourceHomotopyColimitBoundary F)
  have hT : T ∈ distTriang SourceCategory := sourceHomotopyColimit_distinguished F
  have hz : T.mor₂ ≫ (a-b) = 0 := by
    apply Sigma.hom_ext
    intro k
    simpa only [Preadditive.comp_sub, ← Category.assoc,
      sourceHomotopyColimitInclusion, T, Triangle.mk_mor₂, comp_zero, sub_eq_zero] using hab k
  obtain ⟨q, hq⟩ := T.yoneda_exact₃ hT (a-b) hz
  obtain ⟨r, hr⟩ := sourceSequentialOneSubShift_map_precomp_surjective F
    (shiftFunctor SourceCategory (1 : ℤ)) Y hF q
  apply sub_eq_zero.mp
  rw [hq, ← hr, ← Category.assoc]
  exact (congrArg (fun t => t ≫ r) (comp_distTriang_mor_zero₃₁ T hT)).trans (zero_comp)

/-- If the original represented transitions are bijective and the shifted
ones surjective, the actual zero-stage inclusion gives a bijection on maps
into the target. -/
theorem sourceHomotopyColimitInclusion_zero_precomp_bijective
    (F : ℕ ⥤ SourceCategory.{u}) (Y : SourceCategory.{u})
    (hF : ∀ k, Function.Bijective (fun a : F.obj (k+1) ⟶ Y =>
      F.map (homOfLE (Nat.le_succ k)) ≫ a))
    (hS : ∀ k, Function.Surjective (fun a : (F.obj (k+1))⟦(1 : ℤ)⟧ ⟶ Y =>
      (F.map (homOfLE (Nat.le_succ k)))⟦(1 : ℤ)⟧' ≫ a)) :
    Function.Bijective (fun a : sourceHomotopyColimit F ⟶ Y =>
      sourceHomotopyColimitInclusion F 0 ≫ a) := by
  constructor
  · intro a b hab
    apply sourceHomotopyColimit_hom_ext_of_step_precomp_surjective F Y hS
    intro k
    induction k with
    | zero => exact hab
    | succ k hk =>
      apply (hF k).1
      simpa only [← Category.assoc, sourceHomotopyColimitInclusion_step] using hk
  · intro a₀
    classical
    let r (k : ℕ) : (F.obj k ⟶ Y) → (F.obj (k+1) ⟶ Y) :=
      Function.surjInv (hF k).2
    let a : ∀ k, F.obj k ⟶ Y := Nat.rec (motive := fun k => F.obj k ⟶ Y) a₀ r
    have ha (k : ℕ) : F.map (homOfLE (Nat.le_succ k)) ≫ a (k+1) = a k :=
      Function.surjInv_eq (hF k).2 (a k)
    obtain ⟨b, hb⟩ := sourceHomotopyColimit_exists_desc F a ha
    exact ⟨b, hb 0⟩

end KIP126.StableHomotopy.Implementation
