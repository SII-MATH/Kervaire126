module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Stable.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum.HomotopyMap

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u
variable {X Y : Prespectrum.{u}} (f : HomotopyMap X Y)

/-- The carried paths identify the strictly induced target map with the
original map on the actual stable quotient. -/
theorem stableMap_sourceProjection (d : ℤ) (x : StableHomotopy f.pathSpectrum d) :
    f.stableMap d (stableHomotopyMap f.sourceProjection d x) =
      stableHomotopyMap f.targetProjection d x := by
  induction x using Quot.inductionOn with
  | h a =>
    apply Quot.sound
    apply StableRelation.homotopy (f.mapRepresentative (a.map f.sourceProjection))
    refine ⟨{
      toFun := fun z => (a.loop z.2).val.2 z.1
      continuous_toFun := (a.loop.val.continuous.subtype_val.snd.comp continuous_snd).eval continuous_fst
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      exact (a.loop t).property
    · intro t
      rfl
    · intro s t ht
      change (a.loop t).val.2 s = f.level a.stage (a.loop t).val.1
      have hp : a.loop t = (f.pathLevel a.stage).point := a.loop.property t ht
      rw [hp]
      exact (f.point a.stage).symm

/-- Bijectivity of the explicitly induced stable map proves that both
arrows of the strict replacement zigzag are stable equivalences. -/
theorem targetProjection_stableEquivalence
    (hf : ∀ d : ℤ, Function.Bijective (f.stableMap d)) :
    stableEquivalences f.targetProjection := by
  intro d
  have heq : stableHomotopyMap f.targetProjection d =
      f.stableMap d ∘ stableHomotopyMap f.sourceProjection d := by
    funext x
    exact (f.stableMap_sourceProjection d x).symm
  rw [heq]
  exact (hf d).comp (f.sourceProjection_stableEquivalence d)

/-- The strict zigzag gives an isomorphism in the specified source category
once its actual stable map has been proved bijective. -/
theorem source_isomorphic_of_stableMap_bijective
    (hf : ∀ d : ℤ, Function.Bijective (f.stableMap d)) :
    Nonempty (sourceLocalization.obj X ≅ sourceLocalization.obj Y) := by
  letI := f.sourceProjection_isIso
  letI := stableEquivalences.Q_inverts _ (f.targetProjection_stableEquivalence hf)
  exact ⟨(asIso (sourceLocalization.map f.sourceProjection)).symm ≪≫
    asIso (sourceLocalization.map f.targetProjection)⟩

end KIP126.StableHomotopy.Implementation.Prespectrum.HomotopyMap
