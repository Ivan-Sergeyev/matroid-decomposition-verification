import Mathlib.Order.RelClasses
import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Matroid.Restrict
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Sum

import Seymour.ForMathlib.SetTheory
import Seymour.Matroid.Notions.DisjointCircuitFamily
import Seymour.Matroid.Constructors.CircuitMatroid
import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Operations.Sum2


section GeneralDefinition

/-- Ground set of Δ-sum is symmetric difference of ground sets of summand matroids. -/
@[simp]
def DeltaSum.E {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : Set α := symmDiff M₁.E M₂.E

/-- Circuits in `M₁ Δ M₂` are of form `X₁ Δ X₂` where `X₁`, `X₂` are disjoint unions of circuits in `M₁`, `M₂`, resp. -/
def DeltaSum.CircuitForm {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  C.Nonempty ∧ C ⊆ DeltaSum.E M₁ M₂ ∧
    ∃ X₁, ∃ X₂, X₁ ⊆ M₁.E ∧ X₂ ⊆ M₂.E ∧
    C = symmDiff X₁ X₂ ∧ M₁.matroid.UnionDisjointCircuits X₁ ∧ M₂.matroid.UnionDisjointCircuits X₂

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where X₁ and X₂ is a disjoint union of circuits of M₁ and M₂, respectively. -/
def DeltaSum.CircuitPred {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : Set α → Prop :=
  fun C => Minimal (DeltaSum.CircuitForm M₁ M₂) C

/-- In circuit construction of Δ-sum, empty set is not circuit. -/
lemma DeltaSum.CircuitPred.empty_not_circuit {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ¬DeltaSum.CircuitPred M₁ M₂ ∅ := by
  unfold DeltaSum.CircuitPred Minimal CircuitForm
  simp only [Set.not_nonempty_empty, false_and, Set.le_eq_subset, Set.subset_empty_iff,
    Set.empty_subset, implies_true, and_imp, and_true, not_false_eq_true]

/-- In circuit construction of Δ-sum, no circuit is strict subset of another circuit. -/
lemma DeltaSum.CircuitPred.circuit_not_subset {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α)
    {C C' : Set α } (hC : DeltaSum.CircuitPred M₁ M₂ C) (hC' : DeltaSum.CircuitPred M₁ M₂ C') : ¬(C' ⊂ C) := by
  sorry

/-- In circuit construction of Δ-sum, circuit predicate satisfies axiom (C3). -/
lemma DeltaSum.CircuitPred.circuit_c3 {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α)
    {X C : Set α} {F : ValidXFamily (CircuitPred M₁ M₂) C X} {z : α} (hz : z ∈ C \ F.union) :
    ∃ C', DeltaSum.CircuitPred M₁ M₂ C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.union) \ X := by
  sorry

/-- In circuit construction of Δ-sum, set of all circuit-independent sets has the maximal subset property. -/
lemma DeltaSum.CircuitPred.circuit_maximal {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ∀ X, X ⊆ E M₁ M₂ → Matroid.ExistsMaximalSubsetProperty (CircuitPredicate.ToIndepPredicate (DeltaSum.CircuitPred M₁ M₂) (DeltaSum.E M₁ M₂)) X := by
  sorry

/-- In circuit construction of Δ-sum, every circuit is subset of ground set. -/
lemma DeltaSum.CircuitPred.subset_ground {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ∀ C, CircuitPred M₁ M₂ C → C ⊆ E M₁ M₂ :=
  fun _ hC => hC.1.2.1

/-- Construction of Δ-sum via circuits. -/
def DeltaSum.CircuitMatroid {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : CircuitMatroid α where
  E := DeltaSum.E M₁ M₂
  CircuitPred := DeltaSum.CircuitPred M₁ M₂
  not_circuit_empty := DeltaSum.CircuitPred.empty_not_circuit M₁ M₂
  circuit_not_subset _ _ := fun hC hC' => DeltaSum.CircuitPred.circuit_not_subset M₁ M₂ hC hC'
  circuit_c3 _ _ _ _ :=  DeltaSum.CircuitPred.circuit_c3 M₁ M₂
  circuit_maximal :=  DeltaSum.CircuitPred.circuit_maximal M₁ M₂
  subset_ground := DeltaSum.CircuitPred.subset_ground M₁ M₂

/-- Matroid corresponding to Δ-sum. -/
def DeltaSum.matroid {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : Matroid α :=
  (DeltaSum.CircuitMatroid M₁ M₂).matroid

@[simp]
lemma DeltaSum.E_eq {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
  (DeltaSum.matroid M₁ M₂).E = symmDiff M₁.E M₂.E := rfl

@[simp]
lemma DeltaSum.circuit_iff {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) {C : Set α} :
    (DeltaSum.matroid M₁ M₂).Circuit C ↔ DeltaSum.CircuitPred M₁ M₂ C := by
  unfold matroid
  rw [CircuitMatroid.circuit_iff]
  rfl


section GeneralObservations

/-- todo: desc -/
lemma symmDiff_subset_parent_left {α : Type*} {X₁ X₂ E : Set α} (h : symmDiff X₁ X₂ ⊆ E) (hX₁ : X₁ ⊆ E) : X₂ ⊆ E := by
  rw [symmDiff_def] at h
  rw [←Set.diff_union_inter X₂ X₁]
  exact Set.union_subset (Set.subset_union_right.trans h) (inter_subset_parent_right hX₁)

/-- todo: desc -/
lemma symmDiff_subset_parent_right {α : Type*} {X₁ X₂ E : Set α} (h : symmDiff X₁ X₂ ⊆ E) (hX₂ : X₂ ⊆ E) : X₁ ⊆ E := by
  rw [symmDiff_def] at h
  rw [←Set.diff_union_inter X₁ X₂]
  exact Set.union_subset (Set.subset_union_left.trans h) (inter_subset_parent_right hX₂)

/-- Nonempty union of disjoint circuits of `M₁` satisfies circuit form of `M₁ Δ M₂ . -/
lemma DeltaSum.CircuitForm_left {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCnempty : C.Nonempty) (hCE : C ⊆ DeltaSum.E M₁ M₂) (hC : M₁.matroid.UnionDisjointCircuits C) :
    DeltaSum.CircuitForm M₁ M₂ C := by
  constructor
  · exact hCnempty
  constructor
  · exact hCE
  use C, ∅
  exact ⟨
    hC.subset_ground,
    Set.empty_subset M₂.E,
    symmDiff_empty_eq C,
    hC,
    Matroid.UnionDisjointCircuits.empty M₂.matroid,
  ⟩

/-- Nonempty union of disjoint circuits of `M₂` satisfies circuit form of `M₁ Δ M₂ . -/
lemma DeltaSum.CircuitForm_right {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCnempty : C.Nonempty) (hCE : C ⊆ DeltaSum.E M₁ M₂) (hC : M₂.matroid.UnionDisjointCircuits C) :
    DeltaSum.CircuitForm M₁ M₂ C := by
  constructor
  · exact hCnempty
  constructor
  · exact hCE
  use ∅, C
  exact ⟨
    Set.empty_subset M₁.E,
    hC.subset_ground,
    empty_symmDiff_eq C,
    Matroid.UnionDisjointCircuits.empty M₁.matroid,
    hC,
  ⟩

/-- Circuit of `M₁` contained in `M₁.E \ M₂.E` satisfies circuit form of `M₁ Δ M₂. -/
lemma DeltaSum.CircuitForm_circuit_left {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : M₁.matroid.Circuit C) (hCE : Disjoint C M₂.E) : DeltaSum.CircuitForm M₁ M₂ C :=
  DeltaSum.CircuitForm_left hC.nonempty (by
    simp only [DeltaSum.E, symmDiff_def, Set.sup_eq_union]
    exact (Set.subset_diff.mpr ⟨hC.subset_ground, hCE⟩).trans Set.subset_union_left
  ) (Matroid.UnionDisjointCircuits.circuit hC)

/-- Circuit of `M₂` contained in `M₂.E \ M₁.E` satisfies circuit form of `M₁ Δ M₂. -/
lemma DeltaSum.CircuitForm_circuit_right {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : M₂.matroid.Circuit C) (hCE : Disjoint C M₁.E) : DeltaSum.CircuitForm M₁ M₂ C :=
  DeltaSum.CircuitForm_right hC.nonempty (by
    simp only [DeltaSum.E, symmDiff_def, Set.sup_eq_union]
    exact (Set.subset_diff.mpr ⟨hC.subset_ground, hCE⟩).trans Set.subset_union_right
  ) (Matroid.UnionDisjointCircuits.circuit hC)

/-- Circuit of `M₁` that lies in `M₁.E \ M₂.E` is circuit in `M₁ Δ M₂`. -/
lemma DeltaSum.CircuitPred_left_circuit {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCM₁ : M₁.matroid.Circuit C) (hCE : C ⊆ M₁.E \ M₂.E) : DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact DeltaSum.CircuitForm_circuit_left hCM₁ (Set.subset_diff.mp hCE).2
  · intro D ⟨hDnempty, hD⟩ hDC
    obtain ⟨hDE, X₁, X₂, hX₁E, hX₂E, hDX₁X₂, hX₁, hX₂⟩ := hD
    unfold E at hDE

    let t1 : C ⊆ M₁.E := sub_union_diff_sub_union hCE
    let t2 : D ⊆ M₁.E \ M₂.E := hDC.trans hCE
    let t3 : Disjoint (M₁.E \ M₂.E) M₂.E := Set.disjoint_sdiff_left
    let t4 : Disjoint D X₂ := Set.disjoint_of_subset t2 hX₂E t3

    let t5a : D ⊆ M₁.E := hDC.trans t1
    let t5 : X₂ ⊆ M₁.E := symmDiff_subset_parent_left (hDX₁X₂ ▸ t5a) hX₁E

    let t := hCM₁.2
    sorry


section MatrixCharacterization

/-- Sets that are circuits in `M₁` or `M₂`. -/
def BinaryMatroid.JointCircuits {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroid α) :=
  {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C}

/-- Matrix whose rows are incidence vectors of all circuits in `M₁` and `M₂`. -/
def BinaryMatroid.JointCircuitMatrix {α : Type*} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroid α) :
    Matrix {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C} (M₁.E ∪ M₂.E : Set α) Z2 :=
  Matrix.of fun C e => (if (e : α) ∈ (C : Set α) then 1 else 0)
  -- todo: use `M₁.JointCircuitRows M₂` as first dimension of matrix;
  -- compiler doesn't "see through" definition and complains about type mismatch

/-- If `A` is a matrix over GF(2) whose columns are indexed by the elements of `M₁.E ∪ M₂.E`
    and whose rows consist of the incidence vectors of all the circuits of `M₁` and all the circuits of `M₂`, then
    `M₁ Δ M₂ = (M[A])* \ (M₁.E ∩ M₂.E)` -/
lemma DeltaSum.matrix_iff {α : Type*} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroid α) :
    DeltaSum.matroid M₁ M₂ = (M₁.JointCircuitMatrix M₂).VectorMatroid.matroid.dual.restrict (M₁.E ∩ M₂.E) := by
  sorry -- see Lemma 9.3.1 in Oxley


section SpecialCase1Sum

lemma ssubset_disjoint_union_nonempty {α : Type*} {X₁ X₂ : Set α}
    (hX₁X₂ : Disjoint X₁ X₂) (hX₂ : X₂.Nonempty) : X₁ ⊂ X₁ ∪ X₂ := by
  rw [Set.ssubset_iff_of_subset Set.subset_union_left]
  obtain ⟨x, hx⟩ := hX₂
  use x
  exact ⟨Set.mem_union_right X₁ hx, Disjoint.ni_of_in hX₁X₂.symm hx⟩

lemma ssubset_disjoint_nonempty_union {α : Type*} {X₁ X₂ : Set α}
    (hX₁X₂ : Disjoint X₁ X₂) (hX₁ : X₁.Nonempty) : X₂ ⊂ X₁ ∪ X₂ := by
  rw [Set.ssubset_iff_of_subset Set.subset_union_right]
  obtain ⟨x, hx⟩ := hX₁
  use x
  exact ⟨Set.mem_union_left X₂ hx, Disjoint.ni_of_in hX₁X₂ hx⟩

/-- Dependent set in disjoint sum is depenent in one of summand matroids. -/
lemma Matroid.disjointSum_dep_iff {α : Type*} {M N : Matroid α} {h D} :
    (M.disjointSum N h).Dep D ↔ (M.Dep (D ∩ M.E) ∨ N.Dep (D ∩ N.E)) ∧ D ⊆ M.E ∪ N.E := by
  constructor
  · intro hD
    constructor
    · let hDE := Matroid.disjointSum_ground_eq ▸ hD.subset_ground
      apply Matroid.Dep.not_indep at hD
      rw [Matroid.disjointSum_indep_iff] at hD
      push_neg at hD
      if hDM : M.Indep (D ∩ M.E) then
        if hDN : N.Indep (D ∩ N.E) then
          exact False.elim (hD hDM hDN hDE)
        else
          exact Or.inr ⟨hDN, Set.inter_subset_right⟩
      else
        exact Or.inl ⟨hDM, Set.inter_subset_right⟩
    · exact Matroid.disjointSum_ground_eq ▸ hD.subset_ground
  · intro ⟨hD, hDE⟩
    cases hD with
    | inl hDM => exact ⟨
        fun hD => False.elim ((Matroid.Dep.not_indep hDM) (Matroid.disjointSum_indep_iff.mp hD).1),
        Matroid.disjointSum_ground_eq ▸ hDE
      ⟩
    | inr hDN => exact ⟨
        fun hD => False.elim ((Matroid.Dep.not_indep hDN) (Matroid.disjointSum_indep_iff.mp hD).2.1),
        Matroid.disjointSum_ground_eq ▸ hDE
      ⟩

/-- Circuit in disjoint sum is circuit in one of summand matroids. -/
lemma Matroid.disjointSum_circuit_iff {α : Type*} (M N : Matroid α) (h : Disjoint M.E N.E) {C : Set α} :
    (M.disjointSum N h).Circuit C ↔ M.Circuit C ∨ N.Circuit C := by
  constructor
  · intro ⟨hCdep, hCmin⟩
    let ⟨hC, hCE⟩ := Matroid.disjointSum_dep_iff.mp hCdep
    cases hC with
    | inl hCM =>
        let hCMMeq : C ∩ M.E ∩ M.E = C ∩ M.E := Set.inter_eq_left.mpr Set.inter_subset_right
        let hCinterM : (M.disjointSum N h).Dep (C ∩ M.E) := Matroid.disjointSum_dep_iff.mpr ⟨
          Or.inl (hCMMeq.symm ▸ hCM),
          inter_subset_parent_left hCE
        ⟩
        let hCMeq : C = C ∩ M.E := Set.Subset.antisymm (hCmin hCinterM Set.inter_subset_left) Set.inter_subset_left

        left
        constructor
        · exact hCMeq ▸ hCM
        · intro D hD hDC
          let hDM : D ⊆ D ∩ M.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          let hDM : D = D ∩ M.E := Set.Subset.antisymm hDM Set.inter_subset_left
          let hDdep : (M.disjointSum N h).Dep D := Matroid.disjointSum_dep_iff.mpr ⟨
            Or.inl (hDM ▸ hD),
            hDC.trans hCE
          ⟩
          exact hCmin hDdep hDC
    | inr hCN =>
        let hCNNeq : C ∩ N.E ∩ N.E = C ∩ N.E := Set.inter_eq_left.mpr Set.inter_subset_right
        let hCinterN : (M.disjointSum N h).Dep (C ∩ N.E) := Matroid.disjointSum_dep_iff.mpr ⟨
          Or.inr (hCNNeq.symm ▸ hCN),
          inter_subset_parent_left hCE
        ⟩
        let hCMeq : C = C ∩ N.E := Set.Subset.antisymm (hCmin hCinterN Set.inter_subset_left) Set.inter_subset_left

        right
        constructor
        · exact hCMeq ▸ hCN
        · intro D hD hDC
          let hDN : D ⊆ D ∩ N.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          let hDN : D = D ∩ N.E := Set.Subset.antisymm hDN Set.inter_subset_left
          let hDdep : (M.disjointSum N h).Dep D := Matroid.disjointSum_dep_iff.mpr ⟨
            Or.inr (hDN ▸ hD),
            hDC.trans hCE
          ⟩
          exact hCmin hDdep hDC
  · intro hC
    cases hC with
    | inl hCM =>
        let hCMeq : C = C ∩ M.E := Set.left_eq_inter.mpr hCM.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inl (hCMeq ▸ hCM.dep), (hCM.subset_ground).trans Set.subset_union_left⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          let ⟨hD, hDE⟩ := hD
          let hDMeq : D ⊆ D ∩ M.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          let hDMeq : D = D ∩ M.E := Set.Subset.antisymm hDMeq Set.inter_subset_left
          let hDNeq : D ∩ N.E = ∅ := Disjoint.inter_eq (Set.disjoint_of_subset_left (Set.inter_eq_left.mp hDMeq.symm) h)
          rw [←hDMeq, hDNeq] at hD
          cases hD with
          | inl hD => exact hCM.2 hD hDC
          | inr hD => exact False.elim (Set.Nonempty.ne_empty (Matroid.Dep.nonempty hD) rfl)
    | inr hCN =>
        let hCNeq : C = C ∩ N.E := Set.left_eq_inter.mpr hCN.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inr (hCNeq ▸ hCN.dep), (hCN.subset_ground).trans Set.subset_union_right⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          let ⟨hD, hDE⟩ := hD
          let hDNeq : D ⊆ D ∩ N.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCNeq.symm))
          let hDNeq : D = D ∩ N.E := Set.Subset.antisymm hDNeq Set.inter_subset_left
          let hDMeq : D ∩ M.E = ∅ := Disjoint.inter_eq (Set.disjoint_of_subset_left (Set.inter_eq_left.mp hDNeq.symm) h.symm)
          rw [←hDNeq, hDMeq] at hD
          cases hD with
          | inl hD => exact False.elim (Set.Nonempty.ne_empty (Matroid.Dep.nonempty hD) rfl)
          | inr hD => exact hCN.2 hD hDC

-- todo: replace by more general `DeltaSum.CircuitPred_circuit_left` etc.
/-- Circuits of `M₁` are circuits in Δ-sum of disjoint matroids. -/
lemma DeltaSum.Disjoint_circuit_left_circuit {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) {C : Set α} (hC : M₁.matroid.Circuit C) :
    DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact DeltaSum.CircuitForm_circuit_left hC (Set.disjoint_of_subset_left hC.subset_ground hM₁M₂)
  · intro C' hC' hC'subC
    if hCC' : C' = C then
      exact le_of_eq_of_le hCC'.symm (Set.Subset.refl C')
    else
      obtain ⟨hC'nonempty, hC'E, X₁, X₂, hX₁, hX₂, hC'X₁X₂, hX₁M₁, hX₂M₂⟩ := hC'
      let hC'M₁ : C' ⊆ M₁.E := Set.Subset.trans hC'subC hC.subset_ground
      let hC'M₂ : Disjoint C' M₂.E := Set.disjoint_of_subset hC'M₁ (Set.Subset.refl M₂.E) hM₁M₂
      -- ^ question: fix false flag "unused variable"?
      let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁ hX₂ hM₁M₂
      rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hC'X₁X₂

      let hX₂C' : X₂ ⊆ C' := Set.Subset.trans Set.subset_union_right hC'X₁X₂.symm.subset
      let hX₂empty : X₂ = ∅ := Set.subset_eq_empty (hC'M₂ hX₂C' hX₂) rfl
      simp only [Set.sup_eq_union] at hC'X₁X₂
      rw [hX₂empty, Set.union_empty] at hC'X₁X₂

      let hC'C : C' ⊂ C := HasSubset.Subset.ssubset_of_ne hC'subC hCC'
      let hC'indep := Matroid.Circuit.indep_ssub hC hC'C
      let hC'empty : C' = ∅ := Matroid.UnionDisjointCircuits.indep_empty (hC'X₁X₂ ▸ hX₁M₁) hC'indep
      exfalso
      exact False.elim (Set.not_nonempty_empty (hC'empty ▸ hC'nonempty))

/-- Circuits of `M₂` are circuits in Δ-sum of disjoint matroids. -/
lemma DeltaSum.Disjoint_circuit_right_circuit {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) {C : Set α} (hC : M₂.matroid.Circuit C) :
    DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact DeltaSum.CircuitForm_circuit_right hC (Set.disjoint_of_subset_right hC.subset_ground hM₁M₂).symm
  · intro C' hC' hC'subC
    if hCC' : C' = C then
      exact le_of_eq_of_le hCC'.symm (Set.Subset.refl C')
    else
      obtain ⟨hC'nonempty, hC'E, X₁, X₂, hX₁, hX₂, hC'X₁X₂, hX₁M₁, hX₂M₂⟩ := hC'
      let hC'M₂ : C' ⊆ M₂.E := Set.Subset.trans hC'subC hC.subset_ground
      let hC'M₁ : Disjoint C' M₁.E := Set.disjoint_of_subset hC'M₂ (Set.Subset.refl M₁.E) hM₁M₂.symm
      -- ^ question: fix false flag "unused variable"?
      let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁ hX₂ hM₁M₂
      rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hC'X₁X₂

      let hX₁C' : X₁ ⊆ C' := Set.Subset.trans Set.subset_union_left hC'X₁X₂.symm.subset
      let hX₁empty : X₁ = ∅ := Set.subset_eq_empty (hC'M₁ hX₁C' hX₁) rfl
      simp only [Set.sup_eq_union] at hC'X₁X₂
      rw [hX₁empty, Set.empty_union] at hC'X₁X₂

      let hC'C : C' ⊂ C := HasSubset.Subset.ssubset_of_ne hC'subC hCC'
      let hC'indep := Matroid.Circuit.indep_ssub hC hC'C
      let hC'empty : C' = ∅ := Matroid.UnionDisjointCircuits.indep_empty (hC'X₁X₂ ▸ hX₂M₂) hC'indep
      exfalso
      exact False.elim (Set.not_nonempty_empty (hC'empty ▸ hC'nonempty))

lemma subset_left_subset_symmDiff_of_Dijoint {α : Type*} {A B X : Set α} (hAB : Disjoint A B) (hX : X ⊆ A) :
    X ⊆ symmDiff A B := by
  simp [symmDiff_def, Set.sup_eq_union]
  exact Set.subset_union_of_subset_left (Set.subset_diff.mpr ⟨hX, Set.disjoint_of_subset_left hX hAB⟩) (B \ A)

lemma subset_right_subset_symmDiff_of_Dijoint {α : Type*} {A B X : Set α} (hAB : Disjoint A B) (hX : X ⊆ B) :
    X ⊆ symmDiff A B := by
  simp [symmDiff_def, Set.sup_eq_union]
  exact Set.subset_union_of_subset_right (Set.subset_diff.mpr ⟨hX, (Set.disjoint_of_subset_right hX hAB).symm⟩) (A \ B)

lemma ssubset_union_nonempty_disjoint {α : Type*} {A B : Set α} (h : Disjoint A B) (hB : B.Nonempty) : A ⊂ A ∪ B := by
  exact ssubset_disjoint_union_nonempty h hB

/-- If `M₁.E ∩ M₂.E = ∅`, then `M₁ Δ M₂ = M₁ ⊕ M₂`. -/
lemma DeltaSum.SpecialCase1Sum {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) : Matroid.disjointSum M₁ M₂ hM₁M₂ = DeltaSum.matroid M₁ M₂ := by
  rw [Matroid.eq_iff_eq_all_circuits]
  constructor
  · rw [Matroid.disjointSum_ground_eq,
        BinaryMatroid.E_eq, ←BinaryMatroid.E,
        BinaryMatroid.E_eq, ←BinaryMatroid.E,
        DeltaSum.E_eq, Disjoint.symmDiff_eq_sup hM₁M₂]
    rfl
  · intro C hCE
    rw [Matroid.disjointSum_ground_eq, BinaryMatroid.E_eq, BinaryMatroid.E_eq] at hCE
    rw [Matroid.disjointSum_circuit_iff, DeltaSum.circuit_iff]
    constructor
    · intro hCcirc
      cases hCcirc with
      | inl hCM₁ => exact DeltaSum.Disjoint_circuit_left_circuit hM₁M₂ hCM₁
      | inr hCM₂ => exact DeltaSum.Disjoint_circuit_right_circuit hM₁M₂ hCM₂
    · intro ⟨⟨hCnempty, hCE, X₁, X₂, hX₁, hX₂, hCX₁X₂, hX₁duc, hX₂duc⟩, hCmin⟩
      let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁ hX₂ hM₁M₂
      rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hCX₁X₂
      simp only [Set.sup_eq_union] at hCX₁X₂

      if hX₁empty : X₁ = ∅ then
        right
        let hCeq := hCX₁X₂
        rw [hX₁empty, Set.empty_union] at hCeq
        rw [hCeq] at hCnempty ⊢
        constructor
        · exact Matroid.UnionDisjointCircuits.nonempty_dep hX₂duc hCnempty
        · intro D hD hDX₂
          let ⟨D', hD', hD'D⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hD
          let hD'form : DeltaSum.CircuitForm M₁ M₂ D' := DeltaSum.CircuitForm_circuit_right hD'
            ((Set.disjoint_of_subset_right ((hD'D.trans hDX₂).trans hX₂) hM₁M₂).symm)
          specialize hCmin hD'form (hD'D.trans (hCeq ▸ hDX₂))
          exact (hCeq.symm ▸ hCmin).trans hD'D
      else
        let hX₂empty : X₂ = ∅ := by
          by_contra hX₂nempty
          apply Set.nonempty_iff_ne_empty.mpr at hX₁empty
          apply Set.nonempty_iff_ne_empty.mpr at hX₂nempty
          specialize hCmin (DeltaSum.CircuitForm_left hX₁empty (subset_left_subset_symmDiff_of_Dijoint hM₁M₂ hX₁) hX₁duc)
          specialize hCmin (hCX₁X₂.symm ▸ Set.subset_union_left)
          apply Set.ssubset_of_ssubset_of_subset (hCX₁X₂ ▸ ssubset_disjoint_union_nonempty hX₁X₂ hX₂nempty) at hCmin
          exact (HasSSubset.SSubset.ne hCmin) rfl
        left
        let hCeq := hCX₁X₂
        rw [hX₂empty, Set.union_empty] at hCeq
        rw [hCeq] at hCnempty ⊢
        constructor
        · exact Matroid.UnionDisjointCircuits.nonempty_dep hX₁duc hCnempty
        · intro D hD hDX₂
          let ⟨D', hD', hD'D⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hD
          let hD'form : DeltaSum.CircuitForm M₁ M₂ D' := DeltaSum.CircuitForm_circuit_left hD'
            (Set.disjoint_of_subset_left ((hD'D.trans hDX₂).trans hX₁) hM₁M₂)
          specialize hCmin hD'form (hD'D.trans (hCeq ▸ hDX₂))
          exact (hCeq.symm ▸ hCmin).trans hD'D


section SpecialCase2Sum

/-- If `M₁.E ∩ M₂.E = {p}` and neither `M₁` nor `M₂` has `p` as loop or coloop, then `M₁ Δ M₂ = M₁ ⊕₂ M₂`. -/
lemma DeltaSum.SpecialCase2Sum {α : Type*} [DecidableEq α] {p : α} {M₁ M₂ : BinaryMatroid α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid p) :
    Matroid.TwoSum.matroid Assumptions = DeltaSum.matroid M₁ M₂ := by
  sorry


section SpecialCase3Sum

/-- Assumptions for Δ-sum . -/
structure DeltaSum.ThreeSumAssumptions {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) where
  /-- `M₁` and `M₂` are finite -/
  hM₁_finite : M₁.E.Finite
  hM₂_finite : M₂.E.Finite
  /-- `M₁` and `M₂` contain at least 7 elements -/
  hM₁_card : M₁.E.encard ≥ 7
  hM₂_card : M₂.E.encard ≥ 7
  /-- `M₁` and `M₂` meet at a set `T` that is a triangle in both -/
  hT : (M₁.E ∩ M₂.E).encard = 3
  hTM₁ : M₁.matroid.Circuit (M₁.E ∩ M₂.E)
  hTM₂ : M₂.matroid.Circuit (M₁.E ∩ M₂.E)
  /-- Neither `M₁` nor `M₂` has a cocircuit contained in `T` -/
  hT_no_sub_cocircuit : ∀ T' ⊆ M₁.E ∩ M₂.E, ¬M₁.matroid.dual.Circuit T' ∧ ¬M₂.matroid.dual.Circuit T'

-- todo: Lemma 9.3.3
-- todo: Lemma 9.3.4
