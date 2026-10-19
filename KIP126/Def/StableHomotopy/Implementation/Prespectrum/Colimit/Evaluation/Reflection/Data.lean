module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- A strict cocone whose actual based-space cocones are colimiting
at every level is itself colimiting. Compatibility with the original
bonds follows from their actual loop adjoints and the level universal
properties. -/
noncomputable def isColimit_of_evaluation
    {J : Type v} [Category.{w} J] {F : J ⥤ Prespectrum.{u}}
    (c : Cocone F) (hc : ∀ n, IsColimit ((evaluationFunctor n).mapCocone c)) :
    IsColimit c where
  desc s := {
    level n := ((hc n).desc ((evaluationFunctor n).mapCocone s)).map
    point n := ((hc n).desc ((evaluationFunctor n).mapCocone s)).point
    bond n x t := by
      have he : BasedSpace.basedLoopCurry (c.pt.bond n) (c.pt.bond_point n)
          (c.pt.bond_zero n) (c.pt.bond_one n) ≫
          BasedSpace.basedLoopMap ((hc (n+1)).desc ((evaluationFunctor (n+1)).mapCocone s)) =
          (hc n).desc ((evaluationFunctor n).mapCocone s) ≫
          BasedSpace.basedLoopCurry (s.pt.bond n) (s.pt.bond_point n)
            (s.pt.bond_zero n) (s.pt.bond_one n) := by
        apply (hc n).hom_ext
        intro j
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro y
        apply Path.ext
        funext r
        have h₀ := congrArg (fun f => f.map y)
          ((hc n).fac ((evaluationFunctor n).mapCocone s) j)
        have h₁ := congrArg (fun f => f.map ((F.obj j).bond n (y,r)))
          ((hc (n+1)).fac ((evaluationFunctor (n+1)).mapCocone s) j)
        change ((hc n).desc ((evaluationFunctor n).mapCocone s)).map
          ((c.ι.app j).level n y) = (s.ι.app j).level n y at h₀
        change ((hc (n+1)).desc ((evaluationFunctor (n+1)).mapCocone s)).map
          ((c.ι.app j).level (n+1) ((F.obj j).bond n (y,r))) =
            (s.ι.app j).level (n+1) ((F.obj j).bond n (y,r)) at h₁
        change ((hc (n+1)).desc ((evaluationFunctor (n+1)).mapCocone s)).map
          (c.pt.bond n ((c.ι.app j).level n y,r)) =
          s.pt.bond n (((hc n).desc ((evaluationFunctor n).mapCocone s)).map
            ((c.ι.app j).level n y),r)
        exact (congrArg ((hc (n+1)).desc ((evaluationFunctor (n+1)).mapCocone s)).map
          ((c.ι.app j).bond n y r).symm).trans
            (h₁.trans (((s.ι.app j).bond n y r).trans
              (congrArg (fun z => s.pt.bond n (z,r)) h₀.symm)))
      exact congrArg (fun f => f.map x t) he }
  fac s j := by
    apply Hom.ext
    funext n
    exact congrArg BasedSpace.Hom.map ((hc n).fac ((evaluationFunctor n).mapCocone s) j)
  uniq s m hm := by
    apply Hom.ext
    funext n
    have he : (⟨m.level n,m.point n⟩ : c.pt.level n ⟶ s.pt.level n) =
        (hc n).desc ((evaluationFunctor n).mapCocone s) := by
      apply (hc n).uniq ((evaluationFunctor n).mapCocone s)
      intro j
      apply BasedSpace.Hom.ext
      exact congrArg (fun f => f.level n) (hm j)
    exact congrArg BasedSpace.Hom.map he

end KIP126.StableHomotopy.Implementation.Prespectrum
