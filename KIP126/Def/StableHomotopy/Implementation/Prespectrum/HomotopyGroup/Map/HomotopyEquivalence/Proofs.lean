module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy
universe u
set_option backward.isDefEq.respectTransparency false

/-- Explicit based homotopy inverses of level maps induce bijections on
the original cubical homotopy quotients, in every degree including zero. -/
theorem Hom.levelHomotopy_bijective_of_basedHomotopyInverse
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (j : C(Y.level n,X.level n)) (jp : j (Y.level n).point = (X.level n).point)
    (hjf : (j.comp (f.level n)).HomotopicRel (ContinuousMap.id _) {(X.level n).point})
    (hfj : ((f.level n).comp j).HomotopicRel (ContinuousMap.id _) {(Y.level n).point}) :
    Function.Bijective (f.levelHomotopy n r) := by
  have precomp {A : Type u} [TopologicalSpace A] {a : A} {e : C(A,A)}
      (H : e.HomotopicRel (ContinuousMap.id A) {a}) (p : GenLoop (Fin r) A a) :
      (e.comp p.val).HomotopicRel p.val (Cube.boundary (Fin r)) := by
    obtain ⟨H⟩ := H
    exact ⟨{
      toContinuousMap := ⟨fun z => H (z.1,p z.2),H.continuous.comp
        (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))⟩
      map_zero_left := fun x => H.apply_zero (p x)
      map_one_left := fun x => H.apply_one (p x)
      prop' := fun t x hx => H.eq_fst t (by exact Set.mem_singleton_iff.mpr (p.property x hx)) }⟩
  let lift (p : GenLoop (Fin r) (Y.level n) (Y.level n).point) :
      GenLoop (Fin r) (X.level n) (X.level n).point :=
    ⟨j.comp p.val,fun t ht => (congrArg j (p.property t ht)).trans jp⟩
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
        intro h
        have hp := precomp hjf p
        have hq := precomp hjf q
        have hh := (Quotient.exact h).comp_continuousMap j
        exact Quotient.sound (hp.symm.trans (hh.trans hq))
  · intro x
    induction x using Quotient.inductionOn with
    | h p =>
      refine ⟨⟦lift p⟧,Quotient.sound ?_⟩
      exact precomp hfj p

/-- Levelwise actual based homotopy equivalences imply the specified
stable equivalence, without a coherent choice of level inverse maps. -/
theorem stableEquivalence_of_level_basedHomotopyInverse {X Y : Prespectrum.{u}}
    (f : X ⟶ Y)
    (hf : ∀ n, ∃ j : C(Y.level n,X.level n),
      j (Y.level n).point = (X.level n).point ∧
      (j.comp (f.level n)).HomotopicRel (ContinuousMap.id _) {(X.level n).point} ∧
      ((f.level n).comp j).HomotopicRel (ContinuousMap.id _) {(Y.level n).point}) :
    stableEquivalences f := by
  apply stableEquivalence_of_levelHomotopy_bijective
  intro n r
  obtain ⟨j,jp,hjf,hfj⟩ := hf n
  exact f.levelHomotopy_bijective_of_basedHomotopyInverse n r j jp hjf hfj
end KIP126.StableHomotopy.Implementation.Prespectrum
