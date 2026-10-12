module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Exact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Functor.Proofs
public import Mathlib.Algebra.FiveLemma

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- A map between the actual fiber sequences is invertible when the
source and target comparison maps are invertible in the original source.
The proof uses the actual represented exact sequences and the five lemma. -/
theorem source_fiber_map_isIso {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ⟶ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Y')
    (k : sourceLocalization.obj (fiber f) ⟶ sourceLocalization.obj (fiber g))
    [IsIso a] [IsIso b]
    (hf : sourceLocalization.map f ≫ b = a ≫ sourceLocalization.map g)
    (hp : k ≫ sourceLocalization.map (fiberProjection g) =
      sourceLocalization.map (fiberProjection f) ≫ a)
    (hc : sourceLocalization.map (fiberConnecting f) ≫ k =
      sourceLoopFunctor.map b ≫ sourceLocalization.map (fiberConnecting g)) : IsIso k := by
  have hl : sourceLocalization.map (loopMap f) ≫ sourceLoopFunctor.map b =
      sourceLoopFunctor.map a ≫ sourceLocalization.map (loopMap g) := by
    simpa only [CategoryTheory.Functor.map_comp, sourceLoopFunctor_map] using
      congrArg (fun v => sourceLoopFunctor.map v) hf
  apply isIso_of_yoneda_map_bijective
  intro A
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.rightComp A (sourceLocalization.map (loopMap f)))
    (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting f)))
    (Preadditive.rightComp A (sourceLocalization.map (fiberProjection f)))
    (Preadditive.rightComp A (sourceLocalization.map f))
    (Preadditive.rightComp A (sourceLocalization.map (loopMap g)))
    (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting g)))
    (Preadditive.rightComp A (sourceLocalization.map (fiberProjection g)))
    (Preadditive.rightComp A (sourceLocalization.map g))
    (Preadditive.rightComp A (sourceLoopFunctor.map a))
    (Preadditive.rightComp A (sourceLoopFunctor.map b))
    (Preadditive.rightComp A k) (Preadditive.rightComp A a) (Preadditive.rightComp A b)
    (by
      ext z
      change (z ≫ sourceLoopFunctor.map a) ≫ sourceLocalization.map (loopMap g) =
      (z ≫ sourceLocalization.map (loopMap f)) ≫ sourceLoopFunctor.map b
      simpa only [Category.assoc] using congrArg (fun v => z ≫ v) hl.symm)
    (by
      ext z
      change (z ≫ sourceLoopFunctor.map b) ≫ sourceLocalization.map (fiberConnecting g) =
      (z ≫ sourceLocalization.map (fiberConnecting f)) ≫ k
      simpa only [Category.assoc] using congrArg (fun v => z ≫ v) hc.symm)
    (by
      ext z
      change (z ≫ k) ≫ sourceLocalization.map (fiberProjection g) =
      (z ≫ sourceLocalization.map (fiberProjection f)) ≫ a
      simpa only [Category.assoc] using congrArg (fun v => z ≫ v) hp)
    (by
      ext z
      change (z ≫ a) ≫ sourceLocalization.map g =
      (z ≫ sourceLocalization.map f) ≫ b
      simpa only [Category.assoc] using congrArg (fun v => z ≫ v) hf.symm)
    (source_loopMap_fiberConnecting_hom_exact f A)
    (source_fiberConnecting_hom_exact f A) (source_fiberProjection_hom_exact f A)
    (source_loopMap_fiberConnecting_hom_exact g A)
    (source_fiberConnecting_hom_exact g A) (source_fiberProjection_hom_exact g A)
    ((isIso_iff_yoneda_map_bijective _).mp inferInstance A).2
    ((isIso_iff_yoneda_map_bijective _).mp inferInstance A)
    ((isIso_iff_yoneda_map_bijective _).mp inferInstance A)
    ((isIso_iff_yoneda_map_bijective _).mp inferInstance A).1

end KIP126.StableHomotopy.Implementation.Prespectrum
