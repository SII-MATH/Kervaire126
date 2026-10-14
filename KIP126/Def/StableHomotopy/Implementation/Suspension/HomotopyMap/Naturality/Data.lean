module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Proofs

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

def pathLevelMap (n : ℕ) : C(f.pathLevel n, g.pathLevel n) := by
  let raw : C(f.pathLevel n, C.level n × C(I, D.level n)) :=
    ⟨fun z => (a.level n z.val.1, (b.level n).comp z.val.2),
      ((a.level n).continuous.comp continuous_subtype_val.fst).prodMk
        ((ContinuousMap.continuous_postcomp (b.level n)).comp continuous_subtype_val.snd)⟩
  have hr (z : f.pathLevel n) : (raw z).2 0 = g.level n (raw z).1 := by
    change b.level n (z.val.2 0) = g.level n (a.level n z.val.1)
    rw [z.property, hl]
  exact ⟨fun z => ⟨raw z, hr z⟩, raw.continuous.subtype_mk hr⟩

def pathSpectrumMap : f.pathSpectrum ⟶ g.pathSpectrum where
  level := pathLevelMap f g a b hl
  point n := by
    apply Subtype.ext
    apply Prod.ext
    · exact a.point n
    · apply ContinuousMap.ext
      intro s
      exact b.point n
  bond n z t := by
    apply Subtype.ext
    apply Prod.ext
    · exact a.bond n z.val.1 t
    · apply ContinuousMap.ext
      intro s
      change b.level (n+1) ((f.bondFirstPath n (z,t) |>.trans (f.bondSecondPath n (z,t))) s) =
        (g.bondFirstPath n (pathLevelMap f g a b hl n z,t) |>.trans
          (g.bondSecondPath n (pathLevelMap f g a b hl n z,t))) s
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact hh n _ z.val.1 t
      · exact b.bond n _ t

noncomputable def sourceMap {X Y : Prespectrum.{u}} (h : HomotopyMap X Y) :
    sourceLocalization.obj X ⟶ sourceLocalization.obj Y := by
  letI := h.sourceProjection_isIso
  exact inv (sourceLocalization.map h.sourceProjection) ≫ sourceLocalization.map h.targetProjection

end HomotopyMap
end KIP126.StableHomotopy.Implementation.Prespectrum
