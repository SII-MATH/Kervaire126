module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Compact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Subfamily.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual stable homotopy class of a strict coproduct of T1
prespectra already comes from a finite subfamily of those same spectra.
The factor is constructed from its original compact cubical representative. -/
theorem stableHomotopy_coproduct_finite_support {J : Type u}
    (X : J → Prespectrum.{u}) [∀ j n, T1Space ((X j).level n)] (d : ℤ)
    (a : StableHomotopy (∐ X) d) :
    ∃ (s : Finset J) (b : StableHomotopy (∐ fun j : (s : Set J) => X j.val) d),
      stableHomotopyMap (coproductSubfamilyMap X (s : Set J)) d b = a := by
  induction a using Quot.inductionOn with
  | h a =>
    letI (j : J) : T1Space ((X j).level a.stage) := inferInstance
    obtain ⟨s,g,hg⟩ := continuousMap_coproduct_level_factor_finite X a.stage a.loop.val
    let q := coproductSubfamilyMap X (s : Set J)
    let p : GenLoop (Fin a.dimension) ((∐ fun j : (s : Set J) => X j.val : Prespectrum.{u}).level a.stage)
        ((∐ fun j : (s : Set J) => X j.val : Prespectrum.{u}).level a.stage).point :=
      ⟨g,by
        intro z hz
        apply coproductSubfamilyMap_level_injective X (s : Set J) a.stage
        exact (congrArg (fun k => k z) hg).trans ((a.loop.property z hz).trans (q.point a.stage).symm)⟩
    refine ⟨s,loopClass _ d a.stage a.dimension a.degree p,?_⟩
    have hp : (⟨(q.level a.stage).comp p.val,by
        intro z hz
        exact (congrArg (q.level a.stage) (p.property z hz)).trans (q.point a.stage)⟩ :
          GenLoop (Fin a.dimension) ((∐ X : Prespectrum.{u}).level a.stage)
            ((∐ X : Prespectrum.{u}).level a.stage).point) = a.loop := by
      apply Subtype.ext
      exact hg
    change Quot.mk _ ⟨a.stage,a.dimension,a.degree,_⟩ = Quot.mk _ a
    rw [hp]

end KIP126.StableHomotopy.Implementation.Prespectrum
