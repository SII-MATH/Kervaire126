module

public import KIP126.Def.StableHomotopy.Implementation.Generators

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual zero-sphere quotient maps to every based space, without
a compact-generation or CW hypothesis on that space. -/
theorem smashUnitComparison_exists (A : BasedSpace.{0}) :
    ∃! f : zeroSphere.smash A ⟶ A,
      ∀ a, f.map (smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) a) = a := by
  classical
  letI : DiscreteTopology zeroSphere := inferInstanceAs (DiscreteTopology (Fin 2))
  let raw : zeroSphere × A → A := fun p => if p.1 = zeroSphere.point then A.point else p.2
  have hc : Continuous raw := by
    apply continuous_prod_of_discrete_left.mpr
    intro x
    dsimp [raw]
    split_ifs
    · exact continuous_const
    · exact continuous_id
  have collapsed (p : zeroSphere × A)
      (hp : p.1 = zeroSphere.point ∨ p.2 = A.point) : raw p = A.point := by
    rcases hp with h | h
    · simp [raw, h]
    · simp [raw, h]
  have hr : ∀ a b, SmashRelation zeroSphere A a b → raw a = raw b :=
    fun a b h => (collapsed a h.1).trans (collapsed b h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (zeroSphere × A),
      inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (zeroSphere × A) :=
    TopologicalSpace.compactlyGenerated.{0} (zeroSphere × A)
  let f : zeroSphere.smash A ⟶ A :=
    { map := ⟨Quot.lift raw hr, continuous_quot_lift hr hck⟩
      point := collapsed _ (Or.inl rfl) }
  refine ⟨f, ?_, ?_⟩
  · intro a
    change raw ((1 : Fin 2), a) = a
    simp [raw, zeroSphere, Prespectrum.sphereLevel]
  · intro g hg
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,a⟩
    change g.map (smashPoint zeroSphere A x a) = raw (x,a)
    change Fin 2 at x
    fin_cases x
    · change g.map (smashPoint zeroSphere A zeroSphere.point a) = raw (zeroSphere.point,a)
      rw [smashPoint_base_left, g.point]
      simp [raw]
    · simpa [raw, zeroSphere, Prespectrum.sphereLevel] using hg a

end KIP126.StableHomotopy.Implementation.BasedSpace
