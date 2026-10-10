import KIP126.Def.Comparison.Pages.Predicates
import KIP126.Def.SpectralSequence.Computation.Morphism.Proofs

/-! am3：由 canonical 商映射的真实自然性定理组装，不使用 Challenge 占位。 -/
namespace KIP126.Def.Comparison.StageInterfaces

open Core.SpectralSequence

universe u v

theorem internalNaturality {R : Type u} [Ring R]
    (E E' : Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (f : SpectralSequenceMorphism E E') : KIP126.Challenge2.MorphismCalculus E E' f := by
  exact {
    differential_comm := f.pageMap_comm_d
    page_identity := SpectralSequenceMorphism.pageMap_id E
    page_composition := fun _ g => SpectralSequenceMorphism.pageMap_comp f g
    infinity_identity := SpectralSequenceMorphism.eInftyMap_id E
    infinity_composition := fun _ g => SpectralSequenceMorphism.eInftyMap_comp f g
    representatives := fun _ _ _ _ h => f.representsOnPage h
    differential := fun _ _ _ _ _ h => f.hasDifferential h }

end KIP126.Def.Comparison.StageInterfaces
