module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary actual coproduct maps retain levelwise based homotopy
extension, using evaluation of the original colimit cocones. -/
theorem level_hasBasedHomotopyExtension_of_cofan_map
    {J : Type u} {X Y : J → Prespectrum.{u}}
    (c : Cofan X) (d : Cofan Y) (hc : IsColimit c) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.inj j ≫ g = f j ≫ d.inj j)
    (hf : ∀ j n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map (f j)))
    (n : ℕ) : BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map g) := by
  let E := evaluationFunctor.{u} n
  let c' := Cofan.mk (E.obj c.pt) (fun j => E.map (c.inj j))
  let d' := Cofan.mk (E.obj d.pt) (fun j => E.map (d.inj j))
  have hc' : IsColimit c' :=
    (Cofan.isColimitMapCoconeEquiv E X c) (isColimitOfPreserves E hc)
  have hd' : IsColimit d' :=
    (Cofan.isColimitMapCoconeEquiv E Y d) (isColimitOfPreserves E hd)
  exact BasedSpace.hasBasedHomotopyExtension_of_coproduct
    (fun j => E.map (f j)) (fun j => hf j n) c' d' hc' hd' (E.map g)
    (fun j => by
      change E.map (c.inj j) ≫ E.map g = E.map (f j) ≫ E.map (d.inj j)
      rw [← E.map_comp, ← E.map_comp, hg])

end KIP126.StableHomotopy.Implementation.Prespectrum
