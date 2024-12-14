import Seymour.MatroidCircuit


section MatroidConnectivity

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
      rw [Matroid.Loop.IffCircuit] at hx
      apply Matroid.Circuit.CircuitNotSsubsetCircuit hCcirc at hx
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
      rw [Matroid.Coloop.IffInNoCircuit] at hx
      obtain ⟨_hxE, hxC⟩ := hx
      obtain ⟨C, _hCE, hCcirc, heC, hfC⟩ := hfC
      rw [hex, ←Set.singleton_subset_iff] at heC
      specialize hxC C hCcirc
      tauto

/-- Every singleton separator is a loop or a coloop. -/
lemma Matroid.Separator.Singleton {α : Type*} {M : Matroid α} {x : α}
    (hx : x ∈ M.E) : M.Separator {x} → M.Loop x ∨ M.Coloop x := by
  sorry

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
