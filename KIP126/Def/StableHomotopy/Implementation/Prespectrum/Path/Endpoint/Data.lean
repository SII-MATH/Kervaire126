module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Data
public import KIP126.Def.Topology.HomotopyLifting.Path.Endpoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u

/-- The actual endpoint pullback: a base path and two lifted endpoints,
with bonds induced by the original strict map. -/
abbrev pathEndpointPrespectrum {E B : Prespectrum.{u}} (f : E ⟶ B) : Prespectrum.{u} where
  level n := {
    space := TopCat.of (PathEndpointSpace (f.level n))
    point := ⟨(((E.level n).point,(E.level n).point),
      ContinuousMap.const _ (B.level n).point), (f.point n).symm, (f.point n).symm⟩ }
  bond n := ⟨fun z => ⟨((E.bond n (z.1.val.1.1,z.2),E.bond n (z.1.val.1.2,z.2)),
      (⟨fun w : (PathEndpointSpace (f.level n) × I) × I =>
        B.bond n (w.1.1.val.2 w.2,w.1.2),
        (B.bond n).continuous.comp
          ((continuous_fst.fst.subtype_val.snd.eval continuous_snd).prodMk continuous_fst.snd)⟩ :
            C((PathEndpointSpace (f.level n) × I) × I,B.level (n+1))).curry z),
      by change B.bond n (z.1.val.2 0,z.2) = _
         rw [z.1.property.1, f.bond],
      by change B.bond n (z.1.val.2 1,z.2) = _
         rw [z.1.property.2, f.bond]⟩,
    ((((E.bond n).continuous.comp
      (continuous_fst.subtype_val.fst.fst.prodMk continuous_snd)).prodMk
      ((E.bond n).continuous.comp
        (continuous_fst.subtype_val.fst.snd.prodMk continuous_snd))).prodMk
      (⟨fun w : (PathEndpointSpace (f.level n) × I) × I =>
          B.bond n (w.1.1.val.2 w.2,w.1.2),
        (B.bond n).continuous.comp
          ((continuous_fst.fst.subtype_val.snd.eval continuous_snd).prodMk continuous_fst.snd)⟩ :
            C((PathEndpointSpace (f.level n) × I) × I,B.level (n+1))).curry.continuous).subtype_mk _⟩
  bond_point n t := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (E.bond_point n t) (E.bond_point n t)
    · exact ContinuousMap.ext (fun _ => B.bond_point n t)
  bond_zero n z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (E.bond_zero n _) (E.bond_zero n _)
    · exact ContinuousMap.ext (fun _ => B.bond_zero n _)
  bond_one n z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (E.bond_one n _) (E.bond_one n _)
    · exact ContinuousMap.ext (fun _ => B.bond_one n _)

/-- Send a strict path to its two endpoints and its image under the map. -/
def pathEndpointMap {E B : Prespectrum.{u}} (f : E ⟶ B) :
    pathPrespectrum E ⟶ pathEndpointPrespectrum f where
  level n := pathEndpointComparison (f.level n)
  point n := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ContinuousMap.ext (fun _ => f.point n)
  bond n p t := by
    change C(I,E.level n) at p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ContinuousMap.ext (fun s => f.bond n (p s) t)

/-- A specified strict base homotopy and lifted endpoint maps give a
strict map into the actual endpoint pullback. -/
def pathEndpointLift {A E B : Prespectrum.{u}} (f : E ⟶ B)
    (a b : A ⟶ E) (H : A ⟶ pathPrespectrum B)
    (h0 : H ≫ pathEvaluation B 0 = a ≫ f)
    (h1 : H ≫ pathEvaluation B 1 = b ≫ f) : A ⟶ pathEndpointPrespectrum f where
  level n := ⟨fun x => ⟨((a.level n x,b.level n x),H.level n x),
      congrArg (fun k : A ⟶ B => k.level n x) h0,
      congrArg (fun k : A ⟶ B => k.level n x) h1⟩,
    (((a.level n).continuous.prodMk (b.level n).continuous).prodMk
      (H.level n).continuous).subtype_mk _⟩
  point n := Subtype.ext (Prod.ext (Prod.ext (a.point n) (b.point n)) (H.point n))
  bond n x t := Subtype.ext (Prod.ext (Prod.ext (a.bond n x t) (b.bond n x t)) (H.bond n x t))

end KIP126.StableHomotopy.Implementation.Prespectrum
