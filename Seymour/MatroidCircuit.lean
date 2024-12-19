import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual


section MatroidCircuit

/-- Circuit is a minimal dependent subset. -/
def Matroid.Circuit {α : Type*} (M : Matroid α) (C : Set α) : Prop :=
  (C ⊆ M.E) ∧ ¬M.Indep C ∧ (∀ C', C' ⊂ C → M.Indep C') -- todo : switch to Minimal M.Dep?

/-- Every circuit is a subset of the ground set. -/
lemma Matroid.Circuit.SubsetGround {α : Type*} (M : Matroid α) {C : Set α}
  (hC : M.Circuit C) : C ⊆ M.E := hC.1

/-- Every circuit is not independent. -/
lemma Matroid.Circuit.NotIndep {α : Type*} (M : Matroid α) {C : Set α}
  (hC : M.Circuit C) : ¬M.Indep C := hC.2.1

/-- Every strict subset of a circuit is independent. -/
lemma Matroid.Circuit.SsubIndep {α : Type*} {M : Matroid α} {C C' : Set α}
  (hC : M.Circuit C) (hC' : C' ⊂ C) : M.Indep C' := hC.2.2 C' hC'

/-- Deleting one element from a circuit produces an independent set. -/
lemma Matroid.Circuit.DelSingleIndep  {α : Type*} {M : Matroid α} {C : Set α} {a : α}
    (hC : M.Circuit C) (ha : a ∈ C) : M.Indep (C \ {a}) :=
  Matroid.Circuit.SsubIndep hC (Set.diff_singleton_sSubset.mpr ha)

/-- Empty set is not a circuit. -/
lemma Matroid.Circuit.NotCircuitEmpty {α : Type*} (M : Matroid α) : ¬M.Circuit ∅ := by
  by_contra h
  apply h.NotIndep
  exact M.empty_indep

/-- Every circuit is nonempty. -/
lemma Matroid.Circuit.Nonempty {α : Type*} {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty := by
  by_contra hC'
  push_neg at hC'
  rw [hC'] at hC
  apply Matroid.Circuit.NotCircuitEmpty at hC
  exact hC

/-- Independent set is not a circuit. -/
lemma Matroid.Circuit.NotCircuitIndep {α : Type*} {M : Matroid α} {I : Set α} (hI : M.Indep I) : ¬M.Circuit I := by
  unfold Matroid.Circuit
  tauto

/-- No circuit is a subset of another circuit -/
lemma Matroid.Circuit.CircuitNotSsubsetCircuit {α : Type*} {M : Matroid α} {C C' : Set α}
    (hC : M.Circuit C) (hC' : M.Circuit C') : ¬C' ⊂ C := by
  unfold Matroid.Circuit at hC
  obtain ⟨_hCsubground, _hCnindep, hCsubindep⟩ := hC
  by_contra hC'C
  apply hCsubindep at hC'C
  unfold Matroid.Circuit at hC'
  tauto

/-- Strict subset of a circuit is not a circuit. -/
lemma Matroid.Circuit.SsubsetNotCircuit {α : Type*} {M : Matroid α} {C C' : Set α}
    (hC : M.Circuit C) (hC'C : C' ⊂ C) : ¬M.Circuit C' := by
  obtain ⟨_hCground, _hCnindep, hCssub⟩ := hC
  specialize hCssub C' hC'C
  exact Matroid.Circuit.NotCircuitIndep hCssub

/-- Alternative proof of lemma above. -/
lemma Matroid.Circuit.SsubsetNotCircuit_alt {α : Type*} {M : Matroid α} {C C' : Set α}
    (hC : M.Circuit C) (hC'C : C' ⊂ C) : ¬M.Circuit C' := by
  by_contra hC'
  apply Matroid.Circuit.CircuitNotSsubsetCircuit hC at hC'
  tauto

/-- Every dependent set contains a circuit. -/
lemma Matroid.Circuit.DepHasCircuit {α : Type*} {M : Matroid α} {D : Set α}
    (hDM : D ⊆ M.E) (hD : ¬M.Indep D) : ∃ C, C ⊆ D ∧ M.Circuit C := by
  sorry -- todo: adapt from Lemma 3.8 in Bruhn et al.

/-- todo: desc -/
lemma Matroid.Circuit.IndepExtDepHasCircuit {α : Type*} {M : Matroid α} {I : Set α} {a : α}
    (hI : M.Indep I) (ha : a ∈ M.E) (hIa : ¬M.Indep (I ∪ {a})) : ∃ C, a ∈ C ∧ C ⊆ I ∪ {a} ∧ M.Circuit C := by
  sorry -- todo: should be similar to above

-- todo:
-- /-- Axiom (C3) from Bruhn et al. -/
-- (circuit_c3 : ∀ ⦃X C⦄, ∀ F : CircPred.ValidXFamily CircuitPred C X,
--   ∀ z ∈ C \ F.Union, ∃ C', CircuitPred C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.Union) \ X)

-- todo:
-- /-- Corresponding family of independent sets satisfies has the maximal subset property -/
-- (circuit_maximal : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (CircPredToIndep CircuitPred E) X)

-- todo: `CircuitMatroid` constructed from `Circuit`'s of a `Matroid` produces the same `Matroid`


section EqualityCircuits

theorem Matroid.eq_of_circuit_iff_circuit_forall {α : Type*} {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ C, C ⊆ M₁.E → (M₁.Circuit C ↔ M₂.Circuit C)) : M₁ = M₂ := by
  sorry

/-- Two matroids are equal iff they have the same circuits. -/
theorem Matroid.eq_iff_circuit_iff_circuit_forall {α : Type*} {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ C, C ⊆ M₁.E → (M₁.Circuit C ↔ M₂.Circuit C) :=
  ⟨fun h ↦ by (subst h; simp), fun h ↦ eq_of_circuit_iff_circuit_forall h.1 h.2⟩


section MatroidLoop

/-- Loop is an element of the ground set that is not independent when viewed as a singleton set. -/
def Matroid.Loop {α : Type*} (M : Matroid α) (a : α) : Prop :=
  a ∈ M.E ∧ ¬M.Indep {a}

/-- An element is a loop iff its singleton set is a circuit. -/
lemma Matroid.Loop.IffCircuit {α : Type*} (M : Matroid α) {a : α} :
    M.Loop a ↔ M.Circuit {a} := by
  constructor
  · intro ha
    exact ⟨
      Set.singleton_subset_iff.mpr ha.1,
      ha.2,
      by
        intro C' hC'
        rw [Set.ssubset_singleton_iff.mp hC']
        exact M.empty_indep
    ⟩
  · intro ha
    exact ⟨ha.1 rfl, Circuit.NotIndep M ha⟩

/-- Coloop is a loop in the dual matroid. -/
def Matroid.Coloop {α : Type*} (M : Matroid α) (a : α) : Prop :=
  M.dual.Loop a

/-- An element is a coloop iff it belongs to no circuit. -/
lemma Matroid.Coloop.IffInNoCircuit {α : Type*} (M : Matroid α) {a : α} :
    M.Coloop a ↔ a ∈ M.E ∧ ∀ C, M.Circuit C → a ∉ C := by
  constructor
  · intro ha
    obtain ⟨haE, hanIndep⟩ := ha
    unfold Matroid.dual Matroid.dualIndepMatroid at hanIndep
    simp at haE
    simp at hanIndep
    constructor
    · exact haE
    · intro C hC
      apply hanIndep at haE
      by_contra haC
      have hCmaIndep : M.Indep (C \ {a}) := Matroid.Circuit.DelSingleIndep hC haC
      apply Matroid.Indep.exists_base_superset at hCmaIndep
      obtain ⟨B, hBbase, hCmaB⟩ := hCmaIndep
      specialize haE B hBbase

      rw [←Set.singleton_subset_iff] at haE
      rw [←Set.singleton_subset_iff] at haC
      apply Set.union_subset_union_left {a} at hCmaB
      rw [Set.diff_union_of_subset haC, Set.union_eq_self_of_subset_right haE] at hCmaB

      apply Matroid.Indep.subset (Base.indep hBbase) at hCmaB
      apply Matroid.Circuit.NotIndep M at hC
      tauto
  · intro ha
    obtain ⟨haE, haC⟩ := ha
    unfold Coloop Matroid.dual Matroid.dualIndepMatroid Loop
    simp
    constructor
    · exact haE
    · intro haE' B hB
      by_contra haB
      have hBIndep : M.Indep B := Base.indep hB
      have hBinsanIndep : ¬M.Indep (insert a B) := by
        have hBins : B ⊂ insert a B := Set.ssubset_insert haB
        apply Matroid.Base.dep_of_ssubset hB at hBins
        unfold Dep at hBins
        tauto
      have hBanIndep : ¬M.Indep (B ∪ {a}) := Eq.mpr_not (congrArg M.Indep Set.union_singleton) hBinsanIndep
      have hC : ∃ C, a ∈ C ∧ C ⊆ B ∪ {a} ∧ M.Circuit C := Matroid.Circuit.IndepExtDepHasCircuit hBIndep haE hBanIndep
      obtain ⟨C, hCBa, _hCIndep, hCCirc⟩ := hC
      specialize haC C hCCirc
      tauto
