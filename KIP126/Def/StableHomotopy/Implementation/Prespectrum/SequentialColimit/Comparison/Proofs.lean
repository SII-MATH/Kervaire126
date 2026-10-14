module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Homotopy.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits _root_.Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original stable homotopy functor preserves every actual colimit
presentation of a sequential diagram of closed inclusions of T1 levels. -/
theorem stableHomotopyFunctor_preserves_closedSequentialColimit
    (F : ℕ ⥤ Prespectrum.{u}) [∀ k n, T1Space ((F.obj k).level n)]
    (hF : ∀ k n, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n))
    (d : ℤ) : PreservesColimit F (stableHomotopyFunctor d) :=
  preservesColimit_of_preserves_colimit_cocone (sequentialColimitCocone_isColimit F)
    (sequentialStableHomotopyCocone_isColimit F hF d)

/-- A stagewise stable equivalence of actual closed sequential diagrams
induces a stable equivalence on any specified actual colimit cocones. -/
theorem stableEquivalence_of_sequentialColimit_map
    {F G : ℕ ⥤ Prespectrum.{u}}
    [∀ k n, T1Space ((F.obj k).level n)] [∀ k n, T1Space ((G.obj k).level n)]
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ k n, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n))
    (hG : ∀ k n, IsClosedEmbedding ((G.map (homOfLE (Nat.le_succ k))).level n))
    (α : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ k, c.ι.app k ≫ g = α.app k ≫ d.ι.app k)
    (hα : ∀ k, stableEquivalences (α.app k)) : stableEquivalences g := by
  intro q
  let H := stableHomotopyFunctor q
  letI : PreservesColimit F H := stableHomotopyFunctor_preserves_closedSequentialColimit F hF q
  letI : PreservesColimit G H := stableHomotopyFunctor_preserves_closedSequentialColimit G hG q
  let β := Functor.whiskerRight α H
  haveI (k : ℕ) : IsIso (β.app k) := (bijective_iff_isIso_ofHom _).mp (hα k q)
  haveI : IsIso β := NatIso.isIso_of_isIso_app β
  let e := (isColimitOfPreserves H hc).coconePointsIsoOfNatIso
    (isColimitOfPreserves H hd) (asIso β)
  have he : H.map g = e.hom := by
    apply (isColimitOfPreserves H hc).hom_ext
    intro k
    change H.map (c.ι.app k) ≫ H.map g = _
    rw [← H.map_comp,hg,H.map_comp]
    exact ((isColimitOfPreserves H hc).comp_coconePointsIsoOfNatIso_hom
      (isColimitOfPreserves H hd) (asIso β) k).symm
  apply (bijective_iff_isIso_ofHom _).mpr
  change IsIso (H.map g)
  rw [he]
  infer_instance

end KIP126.StableHomotopy.Implementation.Prespectrum
