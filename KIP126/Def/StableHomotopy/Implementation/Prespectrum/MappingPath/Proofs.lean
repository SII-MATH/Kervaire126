module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

@[simp] theorem mappingPathInclusion_retraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathInclusion f ≫ mappingPathRetraction f = 𝟙 X := rfl

@[simp] theorem mappingPathInclusion_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathInclusion f ≫ mappingPathProjection f = f := rfl

/-- The existing actual based level contraction proves that the new strict
retraction is a stable equivalence; its proof does not require the old bonds. -/
theorem mappingPathRetraction_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (mappingPathRetraction f) := by
  apply stableEquivalence_of_levelwise_loops
  · intro n r p q hpq
    exact ((strictHomotopyMap f).sourceProjection_loop_deformation n r p).symm.trans
      ((hpq.comp_continuousMap ((strictHomotopyMap f).sourceSection n)).trans
        ((strictHomotopyMap f).sourceProjection_loop_deformation n r q))
  · intro n r p
    let q : GenLoop (Fin r) (mappingPathLevel f n) (mappingPathLevel f n).point :=
      ⟨((mappingPathInclusion f).level n).comp p.val, by
        intro t ht
        change (mappingPathInclusion f).level n (p t) = _
        exact (congrArg ((mappingPathInclusion f).level n) (p.property t ht)).trans
          ((mappingPathInclusion f).point n)⟩
    exact ⟨q,GenLoop.Homotopic.refl p⟩

/-- The constant-path inclusion is the inverse stable equivalence. -/
theorem mappingPathInclusion_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (mappingPathInclusion f) := by
  intro d
  have hl (x : StableHomotopy X d) :
      stableHomotopyMap (mappingPathRetraction f) d
        (stableHomotopyMap (mappingPathInclusion f) d x) = x := by
    induction x using Quot.inductionOn with
    | h a => rfl
  have hr := mappingPathRetraction_stableEquivalence f d
  exact ⟨fun x y h => (hl x).symm.trans
      ((congrArg (stableHomotopyMap (mappingPathRetraction f) d) h).trans (hl y)),
    fun z => ⟨stableHomotopyMap (mappingPathRetraction f) d z,hr.1 (hl _)⟩⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
