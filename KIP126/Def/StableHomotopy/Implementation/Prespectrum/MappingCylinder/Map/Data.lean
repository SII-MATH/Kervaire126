module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- A strict commutative square acts on the actual reduced mapping cylinders. -/
noncomputable def mappingCylinderMap {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) : mappingCylinder f ⟶ mappingCylinder g where
  level n := mappingCylinderLift f n
    ⟨Sum.elim (fun z => mappingCylinderMk g n (.inl (a.level n z.1,z.2)))
        (fun y => mappingCylinderMk g n (.inr (b.level n y))),
      ((mappingCylinderMk g n).continuous.comp (continuous_inl.comp
        (((a.level n).continuous.comp continuous_fst).prodMk continuous_snd))).sumElim
        ((mappingCylinderMk g n).continuous.comp (continuous_inr.comp (b.level n).continuous))⟩
    (by intro t; change mappingCylinderMk g n (.inl (a.level n (X.level n).point,t)) =
          mappingCylinderMk g n (.inr (b.level n (Y.level n).point))
        rw [a.point,mappingCylinderMk_point,b.point]; rfl)
    (by
      intro x
      change mappingCylinderMk g n (.inl (a.level n x,1)) = _
      rw [mappingCylinderMk_top]
      exact congrArg (fun y => mappingCylinderMk g n (.inr y))
        (congrArg (fun k : X ⟶ Y' => k.level n x) h).symm)
  point n := by change mappingCylinderMk g n (.inr (b.level n (Y.level n).point)) = _
                rw [b.point]; rfl
  bond n z t := by
    obtain ⟨p,rfl⟩ := mappingCylinderMk_surjective f n z
    rcases p with ⟨x,s⟩ | y
    · change mappingCylinderMk g (n+1) (.inl (a.level (n+1) (X.bond n (x,t)),s)) = _
      rw [a.bond]
      rfl
    · change mappingCylinderMk g (n+1) (.inr (b.level (n+1) (Y.bond n (y,t)))) = _
      rw [b.bond]
      rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
