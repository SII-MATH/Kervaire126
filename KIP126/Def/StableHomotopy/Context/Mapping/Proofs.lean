import KIP126.Def.StableHomotopy.Context.Mapping.Data
import KIP126.Def.StableHomotopy.Context.Connecting.Proofs

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Iterated application uses the composite functor's canonical shift structure. -/
theorem HoCofiberSequence.map_comp (T : HoCofiberSequence (C := C))
    (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] :
    (T.map F).map G = T.map (F ⋙ G) := by
  cases T
  simp [HoCofiberSequence.map, Functor.commShiftIso_comp_hom_app,
    Functor.map_comp, Category.assoc]

/-- The iterated and composite triangle constructions have the same boundary
on their definitionally identical represented groups. -/
theorem connectingHomomorphism_map_comp (T : HoCofiberSequence (C := C))
    (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    (n : ℤ) (x : HomotopyGroup n (G.obj (F.obj T.Z))) :
    connectingHomomorphism ((T.map F).map G) n x =
      connectingHomomorphism (T.map (F ⋙ G)) n x := by
  have hlast : 𝟙 _ ≫ (T.map (F ⋙ G)).h =
      ((T.map F).map G).h ≫ (𝟙 (G.obj (F.obj T.X)))⟦(1 : ℤ)⟧' := by
    simp [HoCofiberSequence.map, Functor.commShiftIso_comp_hom_app,
      Functor.map_comp, Category.assoc]
  have h := connectingHomomorphism_naturality ((T.map F).map G) (T.map (F ⋙ G))
    (𝟙 _) (𝟙 _) hlast n x
  simpa [inducedMap] using h.symm

/-- The last square of mapped triangles follows from naturality and shift
coherence; it is not an independent exactness or boundary hypothesis. -/
theorem HoCofiberSequence.map_last_square (T : HoCofiberSequence (C := C))
    (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) [α.CommShift ℤ] :
    α.app T.Z ≫ (T.map G).h = (T.map F).h ≫ (α.app T.X)⟦(1 : ℤ)⟧' := by
  change α.app T.Z ≫ G.map T.h ≫ (G.commShiftIso (1 : ℤ)).hom.app T.X =
    (F.map T.h ≫ (F.commShiftIso (1 : ℤ)).hom.app T.X) ≫ _
  rw [← Category.assoc, ← α.naturality T.h, Category.assoc,
    ← NatTrans.shift_app_comm, ← Category.assoc]

/-- Any shift-compatible natural transformation of exact functors commutes
with the represented connecting homomorphisms of every distinguished triangle. -/
theorem connectingHomomorphism_map_naturality (T : HoCofiberSequence (C := C))
    (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) [α.CommShift ℤ] (n : ℤ) (x : HomotopyGroup n (F.obj T.Z)) :
    connectingHomomorphism (T.map G) n (inducedMap (α.app T.Z) n x) =
      inducedMap (α.app T.X) (n - 1) (connectingHomomorphism (T.map F) n x) :=
  connectingHomomorphism_naturality (T.map F) (T.map G) (α.app T.X) (α.app T.Z)
    (T.map_last_square F G α) n x

end KIP126.StableHomotopy
