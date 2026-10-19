module

public import KIP126.LinProgram.Certificates.NativeModuleCertificates

@[expose] public section


namespace KIP126.LinE2.NativeModuleCertificates.Support
open NamedElementCertificates
open scoped BigOperators
noncomputable section

/-- Native map graphs use the empty string for zero. This is deliberately
separate from the existing module relation parser, whose empty token is
read as generator index zero. The target is the full original module. -/
def nativeModuleImage (n : Nat) (relations : List String) (code : String) :
    KIP126.LinModule.Presentation.Model n relations :=
  if code = "" then 0 else KIP126.LinModule.Presentation.projection n relations
    (KIP126.LinModule.Presentation.relationVector n code)

@[simp] theorem nativeModuleImage_empty (n : Nat) (relations : List String) :
    nativeModuleImage n relations "" = 0 := rfl

def restrict (e : Fin k ↪ Fin n) (x : ModuleExpressions.Expression n) :
    ModuleExpressions.Expression k := fun i => x (e i)

def embed (e : Fin k ↪ Fin n) (x : ModuleExpressions.Expression k) :
    ModuleExpressions.Expression n := fun j =>
  if h : ∃ i, e i = j then x (Classical.choose h) else []

@[simp] theorem embed_apply (e : Fin k ↪ Fin n) (x : ModuleExpressions.Expression k)
    (i : Fin k) : embed e x (e i) = x i := by
  simp only [embed, dif_pos (show ∃ j, e j = e i from ⟨i, rfl⟩)]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ j, e j = e i from ⟨i, rfl⟩))

theorem evaluate_restrict {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : Nat → R) (g : Fin n → M) (e : Fin k ↪ Fin n)
    (x : ModuleExpressions.Expression n)
    (hx : ∀ j, j ∉ Set.range e → x j = []) :
    ModuleExpressions.evaluate v (g ∘ e) (restrict e x) =
      ModuleExpressions.evaluate v g x := by
  classical
  unfold ModuleExpressions.evaluate restrict
  calc
    (∑ i, NamedElementCertificates.evaluate v (x (e i)) • (g ∘ e) i) =
        ∑ j ∈ Finset.univ.map e, NamedElementCertificates.evaluate v (x j) • g j :=
      (Finset.sum_map Finset.univ e (fun j => NamedElementCertificates.evaluate v (x j) • g j)).symm
    _ = _ := ?_
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hzero : x j = [] := hx j (by simpa using hj)
  simp only [hzero, NamedElementCertificates.evaluate, List.map_nil, List.sum_nil, zero_smul]

theorem evaluate_embed {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : Nat → R) (g : Fin n → M) (e : Fin k ↪ Fin n)
    (x : ModuleExpressions.Expression k) :
    ModuleExpressions.evaluate v g (embed e x) =
      ModuleExpressions.evaluate v (g ∘ e) x := by
  have h := evaluate_restrict v g e (embed e x) (by
    intro j hj
    simp only [embed, Set.mem_range] at *
    exact dif_neg hj)
  have he : restrict e (embed e x) = x := by
    funext i
    exact embed_apply e x i
  rw [he] at h
  exact h.symm

/-- The checker runs only on the supplied support. Its conclusion is an
equality in the original full module, with the original scalar action. -/
theorem check_sound_embed_projection {M : Type*} [AddCommGroup M] [Module E2 M]
    (v : Nat → Poly) (g : Fin n → M) (e : Fin k ↪ Fin n)
    (rels : List (ModuleExpressions.Expression k))
    (input output : ModuleExpressions.Expression k) (terms : List Term)
    (hc : ModuleExpressions.check rels input output terms = true)
    (hr : ∀ r ∈ rels,
      ModuleExpressions.evaluate (fun i => projection (v i)) g (embed e r) = 0) :
    ModuleExpressions.evaluate (fun i => projection (v i)) g (embed e input) =
      ModuleExpressions.evaluate (fun i => projection (v i)) g (embed e output) := by
  simp only [evaluate_embed] at hr ⊢
  exact check_sound_projection v (g ∘ e) rels input output terms hc hr

/-- Restriction is sound only after proving every omitted coordinate is
empty. Every input, output and relation retains this full-family condition. -/
theorem check_sound_restrict_projection {M : Type*} [AddCommGroup M] [Module E2 M]
    (v : Nat → Poly) (g : Fin n → M) (e : Fin k ↪ Fin n)
    (rels : List (ModuleExpressions.Expression n))
    (input output : ModuleExpressions.Expression n) (terms : List Term)
    (hs : ∀ x ∈ input :: output :: rels, ∀ j, j ∉ Set.range e → x j = [])
    (hc : ModuleExpressions.check (rels.map (restrict e))
      (restrict e input) (restrict e output) terms = true)
    (hr : ∀ r ∈ rels, ModuleExpressions.evaluate (fun i => projection (v i)) g r = 0) :
    ModuleExpressions.evaluate (fun i => projection (v i)) g input =
      ModuleExpressions.evaluate (fun i => projection (v i)) g output := by
  have he (x) (hx : x ∈ input :: output :: rels) :=
    evaluate_restrict (fun i => projection (v i)) g e x (hs x hx)
  rw [← he input (by simp), ← he output (by simp)]
  apply check_sound_projection v (g ∘ e) _ _ _ terms hc
  intro r h
  obtain ⟨r, hrmem, rfl⟩ := List.mem_map.mp h
  rw [he r (by simp [hrmem])]
  exact hr r hrmem

end
end KIP126.LinE2.NativeModuleCertificates.Support
