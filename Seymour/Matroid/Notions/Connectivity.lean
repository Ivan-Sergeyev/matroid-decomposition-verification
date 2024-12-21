import Seymour.Matroid.Notions.Circuit
import Seymour.Matroid.Notions.Loop
import Seymour.Matroid.Notions.Coloop


/-- Connectivity relation, aka ξ in Oxley's book. -/
def Matroid.ConnectivityRelation {α : Type*} (M : Matroid α) (e f : α) : Prop :=
  (e = f) ∨ (∃ C, C ⊆ M.E ∧ M.Circuit C ∧ e ∈ C ∧ f ∈ C)

/-- Connectivity relation is an equivalence relation on M.E. -/
lemma Matroid.ConnectivityRelation.isEquivRel {α : Type*} (M : Matroid α) :
    ∀ e f : α, M.ConnectivityRelation e f → M.ConnectivityRelation f e := by
  intro e f hef
  cases hef with
  | inl hef => tauto
  | inr hef =>
      right
      obtain ⟨C, hCE, hCcirc, heC, hfC⟩ := hef
      use C

/-- Component is an equivalence class under the connectivity relation, i.e., a ξ-equivalence class. -/
def Matroid.Component {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f ↔ f ∈ X

/-- Separator is a union of components. -/
def Matroid.Separator {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f → f ∈ X

/-- Every loop is a separator. -/
lemma Matroid.Separator.Loop {α : Type*} {M : Matroid α} {x : α} (hx : M.Loop x) :
    M.Separator {x} := by
  intro e hex f hfE hf
  cases hf with
  | inl hef => exact Set.mem_of_eq_of_mem hef.symm hex
  | inr hfC =>
      obtain ⟨C, hCE, hCcirc, heC, hfC⟩ := hfC
      rw [hex, ←Set.singleton_subset_iff] at heC
      rw [Matroid.Loop.iff_circuit] at hx
      apply Matroid.Circuit.not_ssubset_circuit hCcirc at hx
      rw [Set.ssubset_def] at hx
      push_neg at hx
      exact hx heC hfC

/-- Every coloop is a separator. -/
lemma Matroid.Separator.Coloop {α : Type*} {M : Matroid α} {x : α} (hx : M.Coloop x) :
    M.Separator {x} := by
  intro e hex f hfE hf
  cases hf with
  | inl hef => exact Set.mem_of_eq_of_mem hef.symm hex
  | inr hfC =>
      rw [Matroid.Coloop.iff_in_no_circuit] at hx
      obtain ⟨_hxE, hxC⟩ := hx
      obtain ⟨C, _hCE, hCcirc, heC, hfC⟩ := hfC
      rw [hex, ←Set.singleton_subset_iff] at heC
      specialize hxC C hCcirc
      tauto

/-- Every singleton separator is a loop or a coloop. -/
lemma Matroid.Separator.Singleton {α : Type*} {M : Matroid α} {x : α}
    (hx : x ∈ M.E) : M.Separator {x} → M.Loop x ∨ M.Coloop x := by
  intro hSep
  by_contra h
  push_neg at h
  obtain ⟨hnLoop, hnColoop⟩ := h
  rw [Matroid.Loop.iff_circuit] at hnLoop
  rw [Matroid.Coloop.iff_in_no_circuit] at hnColoop
  push_neg at hnColoop
  specialize hnColoop hx
  obtain ⟨C, hCcirc, hxC⟩ := hnColoop

  let hf : ∃ f, f ∈ C ∧ f ≠ x := by
    by_contra hf
    push_neg at hf
    let hCx : ∀ f ∈ C, f ∈ ({x} : Set α) := by
      by_contra hg
      push_neg at hg
      obtain ⟨f', hf'⟩ := hg
      specialize hf f' hf'.1
      exact (hf ▸ hf'.2) rfl
    let hCsubx : C ⊆ {x} := hf
    let hxsubC : {x} ⊆ C := Set.singleton_subset_iff.mpr hxC
    let hCeqx : {x} = C := Set.Subset.antisymm hxsubC hf
    rw [hCeqx] at hnLoop
    exact hnLoop hCcirc
  obtain ⟨f, hfC, hfx⟩ := hf

  let hCE := hCcirc.subset_ground
  specialize hSep x rfl f (hCE hfC) (Or.inr (by use C))
  exact hfx hSep

/-- Equivalence statement. -/
lemma Matroid.Separator.SingletonIff {α : Type*} {M : Matroid α} (x : α) :
    x ∈ M.E ∧ M.Separator {x} ↔ M.Loop x ∨ M.Coloop x := by
  constructor
  · intro hxE
    apply Matroid.Separator.Singleton hxE.1 hxE.2
  · intro hxx
    cases hxx with
    | inl hxLoop => exact ⟨hxLoop.1, Matroid.Separator.Loop hxLoop⟩
    | inr hxColoop => exact ⟨hxColoop.1, Matroid.Separator.Coloop hxColoop⟩
