import KIP126.LinProgram.Interpretation.Near126.Classes.Data
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data
import KIP126.Main.Solution.Literature.HopfCofiber.Predicates
import KIP126.Main.Solution.Literature.HopfCofiber.Pages.Data

namespace KIP126.Computation.Near126
open KIP126.Classical.Adams

/-- Explicit missing geometric input on the already fixed sphere. Its h₂
condition is a statement about an actual filtration-one tower lift, not a
name, an arbitrary page map, or a freely chosen auxiliary spectral sequence.
There is no global inhabitant or claim that h₂ detection chooses a unique ν. -/
structure SphereHopfInput where
  map : SphereThreeMap
  represents_h2 :
    (SphereFiltrationOneRepresents map (linToSphereE2 1 4 (by decide) (atom .h2)))

noncomputable def SphereHopfInput.ybar (N : SphereHopfInput) :=
  sphereMapCofiberBottomE2 N.map (11, 136) (linToSphereE2 11 136 (by decide) Y)

noncomputable def SphereHopfInput.tbar (N : SphereHopfInput) :=
  sphereMapCofiberBottomE2 N.map (14, 139) (linToSphereE2 14 139 (by decide) T)

/-- The bottom-cell correction is fixed by the CSV and induced inclusion.
The remaining topLift must still be identified with X[4] using the top-cell
map and a suspension comparison; no such identification is asserted here. -/
noncomputable def SphereHopfInput.xbar (N : SphereHopfInput)
    (topLift : (sphereMapCofiberAdams N.map).Page 2 (8, 134)) :=
  topLift + sphereMapCofiberBottomE2 N.map (8, 134)
    (linToSphereE2 8 134 (by decide) (atom .x_126_8)) +
    sphereMapCofiberBottomE2 N.map (8, 134)
      (linToSphereE2 8 134 (by decide) (atom .x_126_8_2))

/-- The cofiber sequence and bottom-cell classes are now determined by the
fixed sphere and N.map. The topLift comparison and all external evidence
values are still explicit outstanding inputs. -/
abbrev SphereHopfInput.ComputationFacts (N : SphereHopfInput)
    (topLift : (sphereMapCofiberAdams N.map).Page 2 (8, 134)) :=
  HopfCofiberFacts (sphereMapCofiberAdams N.map) (N.xbar topLift) N.ybar N.tbar

end KIP126.Computation.Near126
