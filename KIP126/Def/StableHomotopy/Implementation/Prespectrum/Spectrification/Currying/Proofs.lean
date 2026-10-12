module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Currying.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem loopCurryFirst_uncurry (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    loopCurryFirst A r (loopUncurryFirst A r p) = p := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  rfl

@[simp] theorem loopUncurryFirst_curry (A : BasedSpace.{u}) (r : ℕ)
    (p : GenLoop (Fin (r+1)) A A.point) :
    loopUncurryFirst A r (loopCurryFirst A r p) = p := by
  apply GenLoop.ext
  intro t
  change p (Fin.cases (t 0) (fun j => t j.succ)) = p t
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end KIP126.StableHomotopy.Implementation.Prespectrum
