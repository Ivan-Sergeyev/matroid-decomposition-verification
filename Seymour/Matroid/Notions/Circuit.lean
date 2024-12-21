import Mathlib.Data.Matroid.Basic


/-- Circuit is minimal dependent subset. -/
def Matroid.Circuit {α : Type*} (M : Matroid α) (C : Set α) : Prop :=
  Minimal M.Dep C

/-- Every circuit is dependent. -/
lemma Matroid.Circuit.dep {α : Type*} (M : Matroid α) {C : Set α}
  (hC : M.Circuit C) : M.Dep C := hC.1

/-- Every circuit is a subset of the ground set. -/
lemma Matroid.Circuit.subset_ground {α : Type*} (M : Matroid α) {C : Set α}
  (hC : M.Circuit C) : C ⊆ M.E := hC.1.2

/-- Equivalence with explicit definition of circuits. -/
lemma Matroid.Circuit.circuit_iff_def {α : Type*} {M : Matroid α} {C : Set α} :
    M.Circuit C ↔ M.Dep C ∧ ∀ I, M.Dep I → I ⊆ C → C ⊆ I :=
  rfl.to_iff

/-- Every strict subset of a circuit is independent. -/
lemma Matroid.Circuit.indep_ssub {α : Type*} {M : Matroid α} {C C' : Set α}
    (hC : M.Circuit C) (hC' : C' ⊂ C) : M.Indep C' := by
  by_contra h
  let hC'subC : C' ⊆ C := subset_of_ssubset hC'
  let hCsubE : C ⊆ M.E := Matroid.Circuit.subset_ground M hC
  let hC'subE : C' ⊆ M.E := Set.Subset.trans hC'subC hCsubE
  let hCmin_dep := (Matroid.Circuit.circuit_iff_def.mpr hC).2
  specialize hCmin_dep (Matroid.dep_of_not_indep h hC'subE) hC'subC
  exact (ne_of_lt hC').symm (Set.Subset.antisymm hCmin_dep hC'subC)

/-- Deleting one element from a circuit produces an independent set. -/
lemma Matroid.Circuit.indep_diff_singleton  {α : Type*} {M : Matroid α} {C : Set α} {a : α}
    (hC : M.Circuit C) (ha : a ∈ C) : M.Indep (C \ {a}) :=
  Matroid.Circuit.indep_ssub hC (Set.diff_singleton_sSubset.mpr ha)

/-- Empty set is not a circuit. -/
lemma Matroid.Circuit.not_circuit_empty {α : Type*} (M : Matroid α) : ¬M.Circuit ∅ :=
  fun h => h.1.1 M.empty_indep

/-- Every circuit is nonempty. -/
lemma Matroid.Circuit.nonempty {α : Type*} {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty := by
  by_contra hC'
  push_neg at hC'
  rw [hC'] at hC
  apply Matroid.Circuit.not_circuit_empty at hC
  exact hC

/-- Independent set is not a circuit. -/
lemma Matroid.Circuit.not_circuit_indep {α : Type*} {M : Matroid α} {I : Set α} (hI : M.Indep I) : ¬M.Circuit I :=
  fun h => h.1.1 hI

/-- No circuit is a subset of another circuit -/
lemma Matroid.Circuit.not_ssubset_circuit {α : Type*} {M : Matroid α} {C C' : Set α}
    (hC : M.Circuit C) (hC' : M.Circuit C') : ¬C' ⊂ C := by
  intro h
  let hCmin := hC.2
  specialize hCmin hC'.1 (le_of_lt h)
  exact h.2 hCmin

/-- Strict subset of a circuit is not a circuit. -/
lemma Matroid.Circuit.ssubset_not_circuit {α : Type*} {M : Matroid α} {C C' : Set α}
    (hC : M.Circuit C) (hC' : C' ⊂ C) : ¬M.Circuit C' := by
  intro h
  exact (Matroid.Circuit.not_ssubset_circuit hC h) hC'

/-- A set is dependent iff it contains a circuit. -/
lemma Matroid.Circuit.dep_iff_has_circuit {α : Type*} {M : Matroid α} {D : Set α} :
    M.Dep D ↔ ∃ C, M.Circuit C ∧ C ⊆ D := by
  constructor
  · sorry
  · sorry

/-- todo: desc -/
lemma Matroid.Circuit.indep_ext_dep_has_circuit_w_ext {α : Type*} {M : Matroid α} {I : Set α} {a : α}
    (hI : M.Indep I) (hIa : M.Dep (insert a I)) : ∃ C, M.Circuit C ∧ C ⊆ insert a I ∧ a ∈ C := by
  obtain ⟨C, hC, hCIa⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hIa
  use C
  exact ⟨
    hC,
    hCIa,
    by
      by_contra h
      exact hC.1.1 (Indep.subset hI (Disjoint.subset_right_of_subset_union hCIa (Set.disjoint_singleton_right.mpr h)))
  ⟩

/-- If two matroids have the same ground sets and sets of circuits, then they are equal. -/
theorem Matroid.eq_if_eq_all_circuits {α : Type*} {M₁ M₂ : Matroid α}
    (hE : M₁.E = M₂.E) (h : ∀ C ⊆ M₁.E, (M₁.Circuit C ↔ M₂.Circuit C)) : M₁ = M₂ := by
  sorry

/-- Two matroids are equal iff they have the same ground sets and sets of circuits. -/
theorem Matroid.eq_iff_eq_all_circuits {α : Type*} {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ C ⊆ M₁.E, (M₁.Circuit C ↔ M₂.Circuit C) :=
  ⟨fun h ↦ by (subst h; simp), fun h ↦ Matroid.eq_if_eq_all_circuits h.1 h.2⟩
