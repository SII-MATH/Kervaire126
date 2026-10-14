module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Map.Square.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every commuting square in the original source lifts to a map of
the actual fiber sequences, including compatibility with the connecting maps. -/
theorem source_fiberMap_exists {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ⟶ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Y')
    (hf : sourceLocalization.map f ≫ b = a ≫ sourceLocalization.map g) :
    ∃ k : sourceLocalization.obj (fiber f) ⟶ sourceLocalization.obj (fiber g),
      k ≫ sourceLocalization.map (fiberProjection g) =
        sourceLocalization.map (fiberProjection f) ≫ a ∧
      sourceLocalization.map (fiberConnecting f) ≫ k =
        sourceLoopFunctor.map b ≫ sourceLocalization.map (fiberConnecting g) := by
  obtain ⟨P,Q,h,s,t,a',b',hs,ht,ha,hb,⟨H⟩,⟨K⟩⟩ :=
    source_square_exists_homotopy_roof f g a b hf
  let α := fiberHomotopyMap h f s t H
  let β := fiberHomotopyMap h g a' b' K
  letI := stableEquivalences.Q_inverts α (fiberHomotopyMap_stableEquivalence h f s t H hs ht)
  letI := stableEquivalences.Q_inverts t ht
  have hα : sourceLocalization.map α ≫ sourceLocalization.map (fiberProjection f) =
      sourceLocalization.map (fiberProjection h) ≫ sourceLocalization.map s := by
    rw [← CategoryTheory.Functor.map_comp, fiberHomotopyMap_projection,
      CategoryTheory.Functor.map_comp]
  have hβ : sourceLocalization.map β ≫ sourceLocalization.map (fiberProjection g) =
      sourceLocalization.map (fiberProjection h) ≫ sourceLocalization.map a' := by
    rw [← CategoryTheory.Functor.map_comp, fiberHomotopyMap_projection,
      CategoryTheory.Functor.map_comp]
  have cα : sourceLocalization.map (fiberConnecting h) ≫ sourceLocalization.map α =
      sourceLoopFunctor.map (sourceLocalization.map t) ≫
        sourceLocalization.map (fiberConnecting f) := by
    simpa only [sourceLoopFunctor_map] using source_fiberConnecting_homotopyMap h f s t H
  have cβ : sourceLocalization.map (fiberConnecting h) ≫ sourceLocalization.map β =
      sourceLoopFunctor.map (sourceLocalization.map b') ≫
        sourceLocalization.map (fiberConnecting g) := by
    simpa only [sourceLoopFunctor_map] using source_fiberConnecting_homotopyMap h g a' b' K
  refine ⟨inv (sourceLocalization.map α) ≫ sourceLocalization.map β, ?_, ?_⟩
  · apply (cancel_epi (sourceLocalization.map α)).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [hβ, ← Category.assoc, hα, Category.assoc, ha]
  · apply (cancel_epi (sourceLoopFunctor.map (sourceLocalization.map t))).mp
    calc
      sourceLoopFunctor.map (sourceLocalization.map t) ≫
          sourceLocalization.map (fiberConnecting f) ≫
            inv (sourceLocalization.map α) ≫ sourceLocalization.map β =
        (sourceLocalization.map (fiberConnecting h) ≫ sourceLocalization.map α) ≫
          inv (sourceLocalization.map α) ≫ sourceLocalization.map β := by
            rw [cα, Category.assoc]
      _ = sourceLocalization.map (fiberConnecting h) ≫ sourceLocalization.map β := by simp
      _ = sourceLoopFunctor.map (sourceLocalization.map b') ≫
          sourceLocalization.map (fiberConnecting g) := cβ
      _ = sourceLoopFunctor.map (sourceLocalization.map t) ≫ sourceLoopFunctor.map b ≫
          sourceLocalization.map (fiberConnecting g) := by
        rw [← hb, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Isomorphic source squares induce some isomorphism of the actual fiber
sequences, with the prescribed source and target components. -/
theorem source_fiberIso_exists {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ≅ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ≅ sourceLocalization.obj Y')
    (hf : sourceLocalization.map f ≫ b.hom = a.hom ≫ sourceLocalization.map g) :
    ∃ e : sourceLocalization.obj (fiber f) ≅ sourceLocalization.obj (fiber g),
      e.hom ≫ sourceLocalization.map (fiberProjection g) =
        sourceLocalization.map (fiberProjection f) ≫ a.hom ∧
      sourceLocalization.map (fiberConnecting f) ≫ e.hom =
        sourceLoopFunctor.map b.hom ≫ sourceLocalization.map (fiberConnecting g) := by
  obtain ⟨k, hp, hc⟩ := source_fiberMap_exists f g a.hom b.hom hf
  letI := source_fiber_map_isIso f g a.hom b.hom k hf hp hc
  exact ⟨asIso k, hp, hc⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
