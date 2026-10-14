module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Naturality.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy
universe u
set_option backward.isDefEq.respectTransparency false
namespace HomotopyMap
variable {A B C D : Prespectrum.{u}} (f : HomotopyMap A B) (g : HomotopyMap C D)
  (a : A ⟶ C) (b : B ⟶ D)
  (hl : ∀ n x, b.level n (f.level n x) = g.level n (a.level n x))
  (hh : ∀ n s x t, b.level (n+1) (f.bondHomotopy n (s,(x,t))) =
    g.bondHomotopy n (s,(a.level n x,t)))

theorem pathSpectrumMap_sourceProjection :
    pathSpectrumMap f g a b hl hh ≫ g.sourceProjection = f.sourceProjection ≫ a := rfl

theorem pathSpectrumMap_targetProjection :
    pathSpectrumMap f g a b hl hh ≫ g.targetProjection = f.targetProjection ≫ b := rfl


include hl hh in
theorem sourceMap_natural :
    sourceLocalization.map a ≫ g.sourceMap = f.sourceMap ≫ sourceLocalization.map b := by
  letI := f.sourceProjection_isIso
  letI := g.sourceProjection_isIso
  apply (cancel_epi (sourceLocalization.map f.sourceProjection)).mp
  dsimp [sourceMap]
  have hs := congrArg sourceLocalization.map (pathSpectrumMap_sourceProjection f g a b hl hh)
  have ht := congrArg sourceLocalization.map (pathSpectrumMap_targetProjection f g a b hl hh)
  simp only [Functor.map_comp] at hs ht
  rw [← Category.assoc, ← hs, Category.assoc, ← Category.assoc
    (sourceLocalization.map g.sourceProjection)]
  simp only [IsIso.hom_inv_id, Category.id_comp]
  rw [← Category.assoc (sourceLocalization.map f.sourceProjection)]
  simp only [IsIso.hom_inv_id_assoc]
  exact ht

end HomotopyMap
end KIP126.StableHomotopy.Implementation.Prespectrum
