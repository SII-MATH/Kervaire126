module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual telescope functor preserves stable equivalences between
prespectra with actual T₁ levels. -/
theorem spectrificationTelescopeMap_stableEquivalence {X Y : Prespectrum.{u}}
    [∀ n, T1Space (X.level n)] [∀ n, T1Space (Y.level n)] (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (spectrificationTelescopeMap f) := by
  intro d
  have hX := spectrificationTelescopeUnit_stableEquivalence X d
  have hY := spectrificationTelescopeUnit_stableEquivalence Y d
  have hc (x : StableHomotopy X d) :
      stableHomotopyMap (spectrificationTelescopeMap f) d
        (stableHomotopyMap (spectrificationTelescopeUnit X) d x) =
      stableHomotopyMap (spectrificationTelescopeUnit Y) d (stableHomotopyMap f d x) := by
    have hn := congrArg ((stableHomotopyFunctor d).map) (spectrificationTelescopeUnit_natural f)
    rw [(stableHomotopyFunctor d).map_comp,(stableHomotopyFunctor d).map_comp] at hn
    exact (ConcreteCategory.congr_hom hn x).symm
  constructor
  · intro x y h
    obtain ⟨a,rfl⟩ := hX.surjective x
    obtain ⟨b,rfl⟩ := hX.surjective y
    exact congrArg (stableHomotopyMap (spectrificationTelescopeUnit X) d)
      ((hf d).injective (hY.injective ((hc a).symm.trans (h.trans (hc b)))))
  · intro y
    obtain ⟨a,rfl⟩ := hY.surjective y
    obtain ⟨b,hb⟩ := (hf d).surjective a
    exact ⟨stableHomotopyMap (spectrificationTelescopeUnit X) d b,
      (hc b).trans (congrArg (stableHomotopyMap (spectrificationTelescopeUnit Y) d) hb)⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
