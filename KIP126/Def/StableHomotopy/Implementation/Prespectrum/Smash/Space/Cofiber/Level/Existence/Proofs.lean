module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Universal
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Continuity.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- Compact generation of the codomain level suffices to move the
image-collapse quotient past the actual smash factor. -/
theorem spaceSmashCofiberInverseLevel_exists (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (Y.level n)] :
    ∃! q : A.smash (cofiberLevel f n) ⟶ cofiberLevel (spaceSmashMap (𝟙 A) f) n,
      ∀ a y, q.map (BasedSpace.smashPoint A (cofiberLevel f n) a (Quot.mk _ y)) =
        Quot.mk _ (BasedSpace.smashPoint A (Y.level n) a y) := by
  let g := spaceSmashMap (𝟙 A) f
  have hr (a : A) : ∀ y z, CofiberRelation f n y z →
      Quot.mk (CofiberRelation g n) (BasedSpace.smashPoint A (Y.level n) a y) =
        Quot.mk (CofiberRelation g n) (BasedSpace.smashPoint A (Y.level n) a z) := by
    rintro y z ⟨⟨x,rfl⟩,⟨x',rfl⟩⟩
    apply Quot.sound
    exact ⟨⟨BasedSpace.smashPoint A (X.level n) a x,spaceSmashMap_apply (𝟙 A) f n a x⟩,
      ⟨BasedSpace.smashPoint A (X.level n) a x',spaceSmashMap_apply (𝟙 A) f n a x'⟩⟩
  let raw : A × cofiberLevel f n → cofiberLevel g n :=
    fun p => Quot.lift (fun y => Quot.mk (CofiberRelation g n) (BasedSpace.smashPoint A (Y.level n) p.1 y)) (hr p.1) p.2
  have rawK (K : CompHaus.{0}) (α : C(K,A)) :
      Continuous (fun p : cofiberLevel f n × K => raw (α p.2,p.1)) := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    letI := BasedSpace.compactlyGenerated_prod_compHaus (Y.level n) K
    exact continuous_quot_mk.comp (BasedSpace.continuous_smashPoint A (Y.level n)
      (α.comp ContinuousMap.snd) ContinuousMap.fst)
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × cofiberLevel f n),inferInstance] raw := by
    apply continuous_from_compactlyGenerated
    intro K k
    exact (rawK K ⟨fun s => (k s).1,k.continuous.fst⟩).comp
      (k.continuous.snd.prodMk continuous_id)
  have collapsed (p : A × cofiberLevel f n)
      (hp : p.1 = A.point ∨ p.2 = (cofiberLevel f n).point) : raw p = (cofiberLevel g n).point := by
    rcases p with ⟨a,z⟩
    rcases hp with h | h
    · change a = A.point at h
      subst a
      refine Quot.inductionOn z ?_
      intro y
      change Quot.mk (CofiberRelation g n) (BasedSpace.smashPoint A (Y.level n) A.point y) = _
      rw [BasedSpace.smashPoint_base_left]
      rfl
    · change z = (cofiberLevel f n).point at h
      subst z
      change Quot.mk (CofiberRelation g n) (BasedSpace.smashPoint A (Y.level n) a (Y.level n).point) = _
      rw [BasedSpace.smashPoint_base_right]
      rfl
  have respects : ∀ p q, BasedSpace.SmashRelation A (cofiberLevel f n) p q → raw p = raw q :=
    fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
  letI : TopologicalSpace (A × cofiberLevel f n) := TopologicalSpace.compactlyGenerated.{0} (A × cofiberLevel f n)
  let q : A.smash (cofiberLevel f n) ⟶ cofiberLevel g n :=
    { map := ⟨Quot.lift raw respects,continuous_quot_lift respects hc⟩
      point := collapsed (A.point,(cofiberLevel f n).point) (Or.inl rfl) }
  refine ⟨q,fun _ _ => rfl,?_⟩
  intro q' hq'
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,z⟩
  refine Quot.inductionOn z ?_
  intro y
  exact hq' a y
end KIP126.StableHomotopy.Implementation.Prespectrum
