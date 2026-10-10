import KIP126.Main.Solution.Literature.HopfCofiber.Predicates

namespace KIP126.Classical.Adams
open CategoryTheory KIP126.StableHomotopy

theorem sphereMapCofiber_first_zero (f : SphereThreeMap) :
    f ≫ sphereMapCofiberInclusion f = 0 :=
  (sphereMapCofiberTriangle f).fg_zero

theorem sphereMapCofiber_cells_zero (f : SphereThreeMap) :
    sphereMapCofiberInclusion f ≫ sphereMapCofiberProjection f = 0 :=
  (sphereMapCofiberTriangle f).gh_zero

theorem sphereMapCofiberInclusionTower_step (f : SphereThreeMap) (s : ℕ) :
    sphereMapCofiberInclusionTower f (s + 1) ≫
        adamsTowerStep standardFoundation.hf2.unit (sphereMapCofiber f) s =
      adamsTowerStep standardFoundation.hf2.unit SphereSpectrum s ≫
        sphereMapCofiberInclusionTower f s :=
  adamsTowerInduced_step _ _ _

end KIP126.Classical.Adams
