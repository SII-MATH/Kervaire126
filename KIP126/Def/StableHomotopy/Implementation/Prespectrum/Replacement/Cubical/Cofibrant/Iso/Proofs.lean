module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Actual strict isomorphisms transport the original cubical lifting
property by their actual inverse maps. -/
theorem IsCubicallyCofibrant.of_iso {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (e : X ≅ Y) : IsCubicallyCofibrant Y := by
  intro E B p hp
  constructor
  intro t b sq
  obtain ⟨l,hl⟩ := hX.lift p hp (e.hom ≫ b)
  exact CommSq.HasLift.mk' {
    l := e.inv ≫ l
    fac_left := zeroPrespectrum_isZero.eq_of_src _ _
    fac_right := by rw [Category.assoc, hl, e.inv_hom_id_assoc] }

end KIP126.StableHomotopy.Implementation.Prespectrum
