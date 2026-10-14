module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- The actual strict fiber over the specified basepoint, as a strict pullback. -/
abbrev strictFiber {A B : Prespectrum.{u}} (p : A ⟶ B) : Prespectrum.{u} :=
  pullbackPrespectrum p (zeroMap zeroPrespectrum B)

/-- A strict fiber point determines a homotopy-fiber point with constant path. -/
def strictFiberInclusion {A B : Prespectrum.{u}} (p : A ⟶ B) : strictFiber p ⟶ fiber p where
  level n :=
    { toFun z := ⟨(z.val.1,ContinuousMap.const I (B.level n).point),⟨z.property.symm,rfl⟩⟩
      continuous_toFun := (continuous_subtype_val.fst.prodMk continuous_const).subtype_mk _ }
  point _ := rfl
  bond n z t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext; intro s; exact (B.bond_point n t).symm

/-- Evaluate an actual lift of every retained fiber path at its endpoint,
which lies in the strict fiber by the proved projection equation. -/
def strictFiberRetraction {A B : Prespectrum.{u}} (p : A ⟶ B)
    (L : fiber p ⟶ pathPrespectrum A)
    (hp : ∀ s : I, L ≫ pathEvaluation A s ≫ p = fiberNullPath p ≫ pathEvaluation B s) :
    fiber p ⟶ strictFiber p :=
  pullbackLift (L ≫ pathEvaluation A 1) (zeroMap (fiber p) zeroPrespectrum) (by
    rw [Category.assoc,hp 1,fiberNullPath_one]
    rfl)

end KIP126.StableHomotopy.Implementation.Prespectrum
