import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Matroid.Restrict
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Sum

import Seymour.SetTheory
import Seymour.MatroidCircuit
import Seymour.ForMathlib.CircuitMatroid
import Seymour.BinaryMatroid
import Seymour.Sum2General


section DisjointCircuitFamily

/-- Family of disjoint circuits of matroid `M`. -/
structure DisjointCircuitFamily {α : Type*} (M : Matroid α) (Idx : Set α) where
  /-- Set family indexed by `Idx` -/
  -- question: upgrade from indexing by Set β to indexing by Sort v (see Set.iUnion in Mathlib.Order.SetNotation)?
  -- note: if we know that `C` is a disjoint union of circuits of `M`,
  -- then wlog we can choose `Idx` to be set of representatives of those circuits
  F : Idx → Set α
  /-- All sets in family are circuits in `M` -/
  hCircuit : ∀ x, M.Circuit (F x)
  /-- All sets in family are disjoint -/
  hDisjoint : ∀ x y, x ≠ y → Disjoint (F x) (F y)

/-- Shorthand for union of sets in `DisjointCircuitFamily`. -/
@[simp]
def DisjointCircuitFamily.union {α : Type*} {M : Matroid α} {Idx : Set α} (F : DisjointCircuitFamily M Idx) : Set α :=
  Set.iUnion F.F

/-- Every element in `DisjointCircuitFamily` is subset of ground set. -/
lemma DisjointCircuitFamily.mem_subset_ground {α : Type*} {M : Matroid α} {Idx : Set α} {F : DisjointCircuitFamily M Idx}
    {x : Idx} : F.F x ⊆ M.E := (F.hCircuit x).1

/-- Union of sets in `DisjointCircuitFamily` is subset of ground set. -/
lemma DisjointCircuitFamily.union_subset_ground {α : Type*} {M : Matroid α} {Idx : Set α} {F : DisjointCircuitFamily M Idx} :
    F.union ⊆ M.E := by
  simp only [union, Set.iUnion_coe_set, Set.iUnion_subset_iff]
  exact fun _ _ => DisjointCircuitFamily.mem_subset_ground

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma DisjointCircuitFamily.union_indep_empty {α : Type*} {M : Matroid α} {Idx : Set α} {F : DisjointCircuitFamily M Idx} :
    M.Indep F.union → F.union = ∅ := by
  sorry

/-- Empty family of disjoint circuits. -/
def DisjointCircuitFamily.Empty {α : Type*} (M : Matroid α) :
    DisjointCircuitFamily M ∅ where
  F := fun _ => ∅
  hCircuit := fun x => False.elim x.2
  hDisjoint := fun x => False.elim x.2

/-- Union of sets in empty family is empty. -/
lemma DisjointCircuitFamily.Empty_union {α : Type*} {M : Matroid α} :
    (DisjointCircuitFamily.Empty M).union = ∅ := Set.iUnion_empty

/-- Family of one circuit, indexed by one element --- that circuit. -/
def DisjointCircuitFamily.One {α : Type*} {M : Matroid α} {C : Set α} (p : α) (hC : M.Circuit C) :
    DisjointCircuitFamily M {p} where
  F := fun _ => C
  hCircuit := fun _ => hC
  hDisjoint := fun x y hxy => False.elim ((x.2 ▸ y.2 ▸ (Subtype.coe_ne_coe.mpr hxy)) rfl)

/-- Union of sets in family of one circuit is that circuit. -/
lemma DisjointCircuitFamily.One_union {α : Type*} {M : Matroid α} {C : Set α} (p : α) (hC : M.Circuit C) :
    (DisjointCircuitFamily.One p hC).union = C := by
  simp only [One, union, Set.iUnion_coe_set, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]

/-- Set `C` can be represented as disjoint union of circuits of `M`. -/
def Matroid.UnionDisjointCircuits {α : Type*} (M : Matroid α) (C : Set α) : Prop :=
  ∃ Idx, ∃ F : DisjointCircuitFamily M Idx, C = F.union

/-- Empty set is disjoint union of circuits. -/
lemma Matroid.UnionDisjointCircuits.empty {α : Type*} (M : Matroid α) :
    M.UnionDisjointCircuits ∅ := by
  use ∅
  use DisjointCircuitFamily.Empty M
  exact DisjointCircuitFamily.Empty_union.symm

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.UnionDisjointCircuits.indep_empty {α : Type*} {M : Matroid α} {X : Set α} :
    M.UnionDisjointCircuits X → M.Indep X → X = ∅ :=
  fun ⟨_, _, hXF⟩ hXindep => DisjointCircuitFamily.union_indep_empty (hXF ▸ hXindep) ▸ hXF

/-- One circuit is disjoint union of circuits. -/
lemma Matroid.UnionDisjointCircuits.circuit {α : Type*} {M : Matroid α} {C : Set α} (hC : M.Circuit C) :
    M.UnionDisjointCircuits C := by
  obtain ⟨x, _hxC⟩ := Matroid.Circuit.Nonempty hC
  use {x}
  use DisjointCircuitFamily.One x hC
  exact (DisjointCircuitFamily.One_union x hC).symm

/-- Union of disjoint circuits is subset of ground set. -/
lemma Matroid.UnionDisjointCircuits.subset_ground {α : Type*} {M : Matroid α} {X : Set α} :
    M.UnionDisjointCircuits X → X ⊆ M.E :=
  fun ⟨_, _, hXF⟩ => hXF ▸ DisjointCircuitFamily.union_subset_ground


section GeneralDefinition

/-- Ground set of Δ-sum is symmetric difference of ground sets of summand matroids. -/
def DeltaSum.E {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Set α := symmDiff M₁.E M₂.E

/-- Circuits in `M₁ Δ M₂` are of form `X₁ Δ X₂` where `X₁`, `X₂` are disjoint unions of circuits in `M₁`, `M₂`, resp. -/
def DeltaSum.CircuitForm {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) (C : Set α) : Prop :=
  C.Nonempty ∧
  ∃ X₁ ⊆ M₁.E, ∃ X₂ ⊆ M₂.E, C = symmDiff X₁ X₂ ∧ M₁.matroid.UnionDisjointCircuits X₁ ∧ M₂.matroid.UnionDisjointCircuits X₂

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where X₁ and X₂ is a disjoint union of circuits of M₁ and M₂, respectively. -/
def DeltaSum.CircuitPred {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Set α → Prop :=
  fun C => Minimal (DeltaSum.CircuitForm M₁ M₂) C

lemma DeltaSum.CircuitPred_left_circuit {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroidStandardRepr α} {C : Set α}
    (hC : DeltaSum.CircuitPred M₁ M₂ C) (hCM₁ : C ⊆ M₁.E) (hCM₂ : Disjoint C M₂.E) : M₁.matroid.Circuit C := by
  unfold CircuitPred Minimal at hC
  -- rw []
  obtain ⟨hC, hCmin⟩ := hC
  sorry
  -- fun C => Minimal (DeltaSum.CircuitForm M₁ M₂) C

lemma subset_not_ssubset_eq {α : Type*} {A B : Set α} (h : A ⊆ B) (h' : ¬A ⊂ B) : A = B := by
  by_contra hAneqB
  exact h' (HasSubset.Subset.ssubset_of_ne h hAneqB)

lemma set_minimal_p_iff_no_ssubset_p {α : Type*} (P : Set α → Prop) (X : Set α) :
    Minimal P X ↔ P X ∧ ∀ X' ⊂ X, ¬P X' := by
  constructor
  · intro ⟨hPX, hX⟩
    constructor
    · exact hPX
    · intro X' hX' hPX'
      specialize hX hPX' (le_of_lt hX')
      exact (and_not_self_iff (X' ⊆ X')).mp (Set.ssubset_of_ssubset_of_subset hX' hX)
  · intro ⟨hPX, hX⟩
    unfold Minimal
    constructor
    · exact hPX
    · intro X' hX' hXX'
      let hX'X : ¬X' ⊂ X := by
        intro hX'X
        specialize hX X' hX'X
        exact hX hX'
      exact le_of_eq_of_le (subset_not_ssubset_eq hXX' hX'X).symm fun ⦃a⦄ a => a

/-- In circuit construction of Δ-sum, empty set is not circuit. -/
lemma DeltaSum.CircuitPred.empty_not_circuit {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
    ¬DeltaSum.CircuitPred M₁ M₂ ∅ := by
  unfold DeltaSum.CircuitPred Minimal CircuitForm
  simp only [Set.not_nonempty_empty, false_and, Set.le_eq_subset, Set.subset_empty_iff,
    Set.empty_subset, implies_true, and_imp, and_true, not_false_eq_true]

/-- In circuit construction of Δ-sum, no circuit is strict subset of another circuit. -/
lemma DeltaSum.CircuitPred.circuit_not_subset {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α)
    {C C' : Set α } (hC : DeltaSum.CircuitPred M₁ M₂ C) (hC' : DeltaSum.CircuitPred M₁ M₂ C') : ¬(C' ⊂ C) := by
  sorry

/-- In circuit construction of Δ-sum, circuit predicate satisfies axiom (C3). -/
lemma DeltaSum.CircuitPred.circuit_c3 {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α)
    {X C : Set α} {F : ValidXFamily (CircuitPred M₁ M₂) C X} {z : α} (hz : z ∈ C \ F.union) :
    ∃ C', DeltaSum.CircuitPred M₁ M₂ C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.union) \ X := by
  sorry

/-- In circuit construction of Δ-sum, set of all circuit-independent sets has the maximal subset property. -/
lemma DeltaSum.CircuitPred.circuit_maximal {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
    ∀ X, X ⊆ E M₁ M₂ → Matroid.ExistsMaximalSubsetProperty (SetPredicate.CircuitToIndep (DeltaSum.CircuitPred M₁ M₂) (DeltaSum.E M₁ M₂)) X := by
  sorry

/-- In circuit construction of Δ-sum, every circuit is subset of ground set. -/
lemma DeltaSum.CircuitPred.subset_ground {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
    ∀ C, CircuitPred M₁ M₂ C → C ⊆ E M₁ M₂ := by
  intro C hC
  obtain ⟨⟨hCnempty, X₁, hX₁, X₂, hX₂, hX₁X₂, hX₁duc, hX₂duc⟩, hCmin⟩ := hC
  rw [hX₁X₂]

  sorry

/-- Construction of Δ-sum via circuits. -/
def DeltaSum.GeneralConstruction {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : CircuitMatroid α where
  E := DeltaSum.E M₁ M₂
  CircuitPred := DeltaSum.CircuitPred M₁ M₂
  not_circuit_empty := DeltaSum.CircuitPred.empty_not_circuit M₁ M₂
  circuit_not_subset _ _ := fun hC hC' => DeltaSum.CircuitPred.circuit_not_subset M₁ M₂ hC hC'
  circuit_c3 _ _ _ _ :=  DeltaSum.CircuitPred.circuit_c3 M₁ M₂
  circuit_maximal :=  DeltaSum.CircuitPred.circuit_maximal M₁ M₂
  subset_ground := DeltaSum.CircuitPred.subset_ground M₁ M₂

/-- Matroid corresponding to Δ-sum. -/
def DeltaSum.matroid {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Matroid α :=
  (DeltaSum.GeneralConstruction M₁ M₂).matroid

@[simp]
lemma DeltaSum.E_eq {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
  (DeltaSum.matroid M₁ M₂).E = symmDiff M₁.E M₂.E := rfl

@[simp]
lemma DeltaSum.circuit_eq {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
    (DeltaSum.matroid M₁ M₂).Circuit = DeltaSum.CircuitPred M₁ M₂ := by
  unfold matroid
  rw [CircuitMatroid.circuit_eq]
  rfl


section MatrixCharacterization

/-- Sets that are circuits in `M₁` or `M₂`. -/
def BinaryMatroidStandardRepr.JointCircuits {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :=
  {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C}

/-- Matrix whose rows are incidence vectors of all circuits in `M₁` and `M₂`. -/
def BinaryMatroidStandardRepr.JointCircuitMatrix {α : Type*} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :
    Matrix {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C} (M₁.E ∪ M₂.E : Set α) Z2 :=
  Matrix.of fun C e => (if (e : α) ∈ (C : Set α) then 1 else 0)
  -- todo: use `M₁.JointCircuitRows M₂` as first dimension of matrix;
  -- compiler doesn't "see through" definition and complains about type mismatch

/-- If `A` is a matrix over GF(2) whose columns are indexed by the elements of `M₁.E ∪ M₂.E`
    and whose rows consist of the incidence vectors of all the circuits of `M₁` and all the circuits of `M₂`, then
    `M₁ Δ M₂ = (M[A])* \ (M₁.E ∩ M₂.E)` -/
lemma DeltaSum.matrix_iff {α : Type*} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :
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

lemma eq_symmDiff_empty {α : Type*} (X : Set α) : X = symmDiff X ∅ := by
  rw [symmDiff_def_alt, Set.union_empty, Set.inter_empty, Set.diff_empty]

lemma eq_empty_symmDiff {α : Type*} (X : Set α) : X = symmDiff ∅ X := by
  rw [symmDiff_def_alt, Set.empty_union, Set.empty_inter, Set.diff_empty]

lemma eq_inter_inter {α : Type*} {X Y : Set α} : X ∩ Y ∩ Y = X ∩ Y := by
  -- let t1 : X ∩ Y ⊆ Y := by exact Set.inter_subset_right
  -- let t2 : X ∩ Y ⊆ X := by exact Set.inter_subset_left
  exact Set.inter_eq_left.mpr Set.inter_subset_right
  -- sorry

/-- Circuit in disjoint sum is circuit in on of summand matroids. -/
lemma Matroid.disjointSum_circuit_iff {α : Type*} (M N : Matroid α) (h : Disjoint M.E N.E) {C : Set α} :
    (M.disjointSum N h).Circuit C ↔ M.Circuit C ∨ N.Circuit C := by
  constructor
  · intro ⟨hCE, hCdep, hCmin⟩
    rw [disjointSum_ground_eq] at hCE
    rw [disjointSum_indep_iff, not_and] at hCdep
    simp only [disjointSum_indep_iff] at hCmin
    rw [imp_iff_not_or, Classical.not_and_iff_or_not_not] at hCdep

    let hCpart : Disjoint (C ∩ M.E) (C ∩ N.E) := Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right h

    cases hCdep with
    | inl hCdep =>
        left
        let hCM : C ∩ N.E = ∅ := by
          by_contra hCN
          apply Set.nonempty_iff_ne_empty.mpr at hCN
          let hCMsub : C ∩ M.E ⊂ C ∩ M.E ∪ C ∩ N.E := ssubset_disjoint_union_nonempty hCpart hCN
          let hCMssubC : C ∩ M.E ⊂ C := HasSSubset.SSubset.trans_eq hCMsub (sub_parts_eq hCE)
          specialize hCmin (C ∩ M.E) hCMssubC
          exact hCdep (Set.inter_eq_left.mpr Set.inter_subset_right ▸ hCmin.1)

        let hCeq : C ∩ M.E = C := by
          apply sub_parts_eq at hCE
          rw [hCM, Set.union_empty] at hCE
          exact hCE

        rw [hCeq] at hCdep

        unfold Circuit
        constructor
        · exact Set.inter_eq_left.mp hCeq
        · constructor
          · exact hCdep
          · intro C' hC'
            specialize hCmin C' hC'
            let hC'eq := Set.left_eq_inter.mpr (Set.Subset.trans (subset_of_ssubset hC') (Set.inter_eq_left.mp hCeq))
            exact hC'eq ▸ hCmin.1
    | inr hCdep => cases hCdep with
      | inl hCdep =>
          right
          let hCM : C ∩ M.E = ∅ := by
            by_contra hCM
            apply Set.nonempty_iff_ne_empty.mpr at hCM
            let hCNsub : C ∩ N.E ⊂ C ∩ M.E ∪ C ∩ N.E := ssubset_disjoint_nonempty_union hCpart hCM
            let hCNssubC : C ∩ N.E ⊂ C := HasSSubset.SSubset.trans_eq hCNsub (sub_parts_eq hCE)
            specialize hCmin (C ∩ N.E) hCNssubC
            exact hCdep (Set.inter_eq_left.mpr Set.inter_subset_right ▸ hCmin.2.1)

          let hCeq : C ∩ N.E = C := by
            apply sub_parts_eq at hCE
            rw [hCM, Set.empty_union] at hCE
            exact hCE

          rw [hCeq] at hCdep

          unfold Circuit
          constructor
          · exact Set.inter_eq_left.mp hCeq
          · constructor
            · exact hCdep
            · intro C' hC'
              specialize hCmin C' hC'
              let hC'eq := Set.left_eq_inter.mpr (Set.Subset.trans (subset_of_ssubset hC') (Set.inter_eq_left.mp hCeq))
              exact hC'eq ▸ hCmin.2.1
      | inr hCdep => exact False.elim (hCdep hCE)
  · intro hC
    cases hC with
    | inl hC =>
        constructor
        · rw [disjointSum_ground_eq]
          exact Set.subset_union_of_subset_left hC.1 N.E
        · constructor
          · rw [disjointSum_indep_iff]
            let hCdep := hC.2.1
            rw [Set.left_eq_inter.mpr hC.1] at hCdep
            exact not_and.mpr fun a _ => hCdep a
          · intro C' hC'
            let hC'C := hC.2.2
            specialize hC'C C' hC'
            let hC'M : C' ⊆ M.E := Set.Subset.trans hC'.1 hC.1
            let hC'N : C' ∩ N.E = ∅ := Disjoint.inter_eq (Disjoint.mono_left hC'M h)
            rw [disjointSum_indep_iff]
            exact ⟨Indep.inter_right hC'C M.E, hC'N ▸ N.empty_indep, Set.subset_union_of_subset_left hC'M N.E⟩
    | inr hC =>
        constructor
        · rw [disjointSum_ground_eq]
          exact Set.subset_union_of_subset_right hC.1 M.E
        · constructor
          · rw [disjointSum_indep_iff]
            intro ⟨_, hCN, _⟩
            let hCdep := hC.2.1
            rw [Set.left_eq_inter.mpr hC.1] at hCdep
            exact hCdep hCN
          · intro C' hC'
            let hC'C := hC.2.2
            specialize hC'C C' hC'
            let hC'N : C' ⊆ N.E := Set.Subset.trans hC'.1 hC.1
            let hC'M : C' ∩ M.E = ∅ := Disjoint.inter_eq (Disjoint.mono_left hC'N h.symm)
            rw [disjointSum_indep_iff]
            exact ⟨hC'M ▸ M.empty_indep, Indep.inter_right hC'C N.E, Set.subset_union_of_subset_right hC'N M.E⟩

lemma DeltaSum.Disjoint_circuit_left_circuit {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroidStandardRepr α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) {C : Set α} (hC : M₁.matroid.Circuit C) :
    DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · constructor
    · exact Matroid.Circuit.Nonempty hC
    · use C
      constructor
      · exact hC.1
      · use ∅
        exact
        ⟨
          Set.empty_subset M₂.E,
          by simp [symmDiff_def],
          Matroid.UnionDisjointCircuits.circuit hC,
          Matroid.UnionDisjointCircuits.empty M₂.matroid,
        ⟩
  · intro C' hC' hC'subC
    if hCC' : C' = C then
      exact le_of_eq_of_le hCC'.symm (Set.Subset.refl C')
    else
      obtain ⟨hC'nonempty, X₁, hX₁, X₂, hX₂, hC'X₁X₂, hX₁M₁, hX₂M₂⟩ := hC'
      let hC'M₁ : C' ⊆ M₁.E := Set.Subset.trans hC'subC hC.1
      let hC'M₂ : Disjoint C' M₂.E := Set.disjoint_of_subset hC'M₁ (Set.Subset.refl M₂.E) hM₁M₂
      -- ^ question: fix false flag "unused variable"?
      let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁ hX₂ hM₁M₂
      rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hC'X₁X₂

      let hX₂C' : X₂ ⊆ C' := Set.Subset.trans Set.subset_union_right hC'X₁X₂.symm.subset
      let hX₂empty : X₂ = ∅ := Set.subset_eq_empty (hC'M₂ hX₂C' hX₂) rfl
      rw [hX₂empty] at hC'X₁X₂
      simp only [Set.le_eq_subset, Set.empty_subset, sup_of_le_left] at hC'X₁X₂

      let hC'C : C' ⊂ C := HasSubset.Subset.ssubset_of_ne hC'subC hCC'
      let hC'indep := hC.2.2
      specialize hC'indep C' hC'C
      let hC'empty : C' = ∅ := Matroid.UnionDisjointCircuits.indep_empty (hC'X₁X₂ ▸ hX₁M₁) hC'indep
      rw [hC'empty] at hC'nonempty
      simp only [Set.not_nonempty_empty] at hC'nonempty

lemma DeltaSum.Disjoint_circuit_right_circuit {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroidStandardRepr α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) {C : Set α} (hC : M₂.matroid.Circuit C) :
    DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · constructor
    · exact Matroid.Circuit.Nonempty hC
    · use ∅
      constructor
      · exact Set.empty_subset M₁.E
      · use C
        exact
        ⟨
          hC.1,
          by simp [symmDiff_def],
          Matroid.UnionDisjointCircuits.empty M₁.matroid,
          Matroid.UnionDisjointCircuits.circuit hC,
        ⟩
  · intro C' hC' hC'subC
    if hCC' : C' = C then
      exact le_of_eq_of_le hCC'.symm (Set.Subset.refl C')
    else
      obtain ⟨hC'nonempty, X₁, hX₁, X₂, hX₂, hC'X₁X₂, hX₁M₁, hX₂M₂⟩ := hC'
      let hC'M₁ : C' ⊆ M₂.E := Set.Subset.trans hC'subC hC.1
      let hC'M₂ : Disjoint C' M₁.E := Set.disjoint_of_subset hC'M₁ (Set.Subset.refl M₁.E) hM₁M₂.symm
      -- ^ question: fix false flag "unused variable"?
      let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁ hX₂ hM₁M₂
      rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hC'X₁X₂

      let hX₁C' : X₁ ⊆ C' := Set.Subset.trans Set.subset_union_left hC'X₁X₂.symm.subset
      let hX₁empty : X₁ = ∅ := Set.subset_eq_empty (hC'M₂ hX₁C' hX₁) rfl
      rw [hX₁empty] at hC'X₁X₂
      simp only [Set.le_eq_subset, Set.empty_subset, sup_of_le_right] at hC'X₁X₂

      let hC'C : C' ⊂ C := HasSubset.Subset.ssubset_of_ne hC'subC hCC'
      let hC'indep := hC.2.2
      specialize hC'indep C' hC'C
      let hC'empty : C' = ∅ := Matroid.UnionDisjointCircuits.indep_empty (hC'X₁X₂ ▸ hX₂M₂) hC'indep
      rw [hC'empty] at hC'nonempty
      simp only [Set.not_nonempty_empty] at hC'nonempty

/-- If `M₁.E ∩ M₂.E = ∅`, then `M₁ Δ M₂ = M₁ ⊕ M₂`. -/
lemma DeltaSum.SpecialCase1Sum {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroidStandardRepr α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) : Matroid.disjointSum M₁ M₂ hM₁M₂ = DeltaSum.matroid M₁ M₂ := by
  rw [Matroid.eq_iff_circuit_iff_circuit_forall]
  constructor
  · rw [Matroid.disjointSum_ground_eq,
        BinaryMatroidStandardRepr.E_eq, ←BinaryMatroidStandardRepr.E,
        BinaryMatroidStandardRepr.E_eq, ←BinaryMatroidStandardRepr.E,
        DeltaSum.E_eq, Disjoint.symmDiff_eq_sup hM₁M₂]
    rfl
  · intro C hCE
    rw [Matroid.disjointSum_ground_eq, BinaryMatroidStandardRepr.E_eq, BinaryMatroidStandardRepr.E_eq] at hCE
    rw [Matroid.disjointSum_circuit_iff, DeltaSum.circuit_eq]
    constructor
    · intro hCcirc
      unfold CircuitPred
      cases hCcirc with
      | inl hCM₁ =>
          constructor
          · constructor
            · exact Matroid.Circuit.Nonempty hCM₁
            · use C
              constructor
              · exact hCM₁.1
              · use ∅
                exact
                ⟨
                    Set.empty_subset M₂.E,
                    eq_symmDiff_empty C,
                    Matroid.UnionDisjointCircuits.circuit hCM₁,
                    Matroid.UnionDisjointCircuits.empty M₂.matroid,
                ⟩
          · intro C' hC' hC'subC
            obtain ⟨hC'nempty, ⟨X₁, hX₁M₁, X₂, hX₂M₂, hC'X₁X₂, hX₁, hX₂⟩⟩ := hC'
            let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁M₁ hX₂M₂ hM₁M₂
            rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hC'X₁X₂
            simp only [Set.sup_eq_union] at hC'X₁X₂

            let hC'M₁ : C' ⊆ M₁.E := Set.Subset.trans hC'subC hCM₁.1
            rw [hC'X₁X₂] at hC'M₁
            let hX₂M₁ : X₂ ⊆ M₁.E := Set.Subset.trans Set.subset_union_right hC'M₁
            let hX₂empty : X₂ = ∅ := Set.subset_eq_empty (hM₁M₂ hX₂M₁ hX₂M₂) rfl
            rw [hX₂empty, Set.union_empty] at hC'X₁X₂

            if hC'C : C' = C then
              exact le_of_eq_of_le hC'C.symm fun ⦃a⦄ a => a
            else
              apply HasSubset.Subset.ssubset_of_ne hC'subC at hC'C
              let hCssubindep := hCM₁.2.2
              specialize hCssubindep C' hC'C
              rw [hC'X₁X₂] at hCssubindep hC'nempty
              apply Matroid.UnionDisjointCircuits.indep_empty hX₁ at hCssubindep
              rw [hCssubindep] at hC'nempty
              exfalso
              exact Set.not_nonempty_empty hC'nempty
      | inr hCM₂ =>
          constructor
          · constructor
            · exact Matroid.Circuit.Nonempty hCM₂
            · use ∅
              constructor
              · exact Set.empty_subset M₁.E
              · use C
                exact
                ⟨
                    hCM₂.1,
                    eq_empty_symmDiff C,
                    Matroid.UnionDisjointCircuits.empty M₁.matroid,
                    Matroid.UnionDisjointCircuits.circuit hCM₂,
                ⟩
          · intro C' hC' hC'subC
            obtain ⟨hC'nempty, ⟨X₁, hX₁M₁, X₂, hX₂M₂, hC'X₁X₂, hX₁, hX₂⟩⟩ := hC'
            let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁M₁ hX₂M₂ hM₁M₂
            rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hC'X₁X₂
            simp only [Set.sup_eq_union] at hC'X₁X₂

            let hC'M₂ : C' ⊆ M₂.E := Set.Subset.trans hC'subC hCM₂.1
            rw [hC'X₁X₂] at hC'M₂
            let hX₁M₂ : X₁ ⊆ M₂.E := Set.Subset.trans Set.subset_union_left hC'M₂
            let hX₁empty : X₁ = ∅ := Set.subset_eq_empty (hM₁M₂ hX₁M₁ hX₁M₂) rfl
            rw [hX₁empty, Set.empty_union] at hC'X₁X₂

            if hC'C : C' = C then
              exact le_of_eq_of_le hC'C.symm fun ⦃a⦄ a => a
            else
              apply HasSubset.Subset.ssubset_of_ne hC'subC at hC'C
              let hCssubindep := hCM₂.2.2
              specialize hCssubindep C' hC'C
              rw [hC'X₁X₂] at hCssubindep hC'nempty
              apply Matroid.UnionDisjointCircuits.indep_empty hX₂ at hCssubindep
              rw [hCssubindep] at hC'nempty
              exfalso
              exact Set.not_nonempty_empty hC'nempty
    · unfold CircuitPred
      rw [set_minimal_p_iff_no_ssubset_p]
      intro ⟨⟨hCnempty, X₁, hX₁, X₂, hX₂, hCX₁X₂, hX₁duc, hX₂duc⟩, hCmin⟩
      let hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_of_subset hX₁ hX₂ hM₁M₂
      rw [Disjoint.symmDiff_eq_sup hX₁X₂] at hCX₁X₂
      simp only [Set.sup_eq_union] at hCX₁X₂

      if hX₁C : X₁ ⊂ C then
        right
        let hX₁empty : X₁ = ∅ := by
          by_contra hX₁nempty
          apply Set.nonempty_iff_ne_empty.mpr at hX₁nempty

          unfold CircuitForm at hCmin
          push_neg at hCmin
          specialize hCmin X₁ hX₁C hX₁nempty X₁ hX₁ ∅ (Set.empty_subset M₂.E) (eq_symmDiff_empty X₁) hX₁duc
          exact hCmin (Matroid.UnionDisjointCircuits.empty M₂.matroid)

        rw [hX₁empty, Set.empty_union] at hCX₁X₂
        rw [←hCX₁X₂] at hX₂ hX₂duc
        constructor
        · exact hX₂
        · constructor
          · by_contra hCindep
            apply Matroid.UnionDisjointCircuits.indep_empty hX₂duc at hCindep
            rw [hCindep] at hCnempty
            simp only [Set.not_nonempty_empty] at hCnempty
          · intro C' hC'C
            by_contra hC'dep

            obtain ⟨T, hTC', hTcircuit⟩ := (Matroid.Circuit.DepHasCircuit (Set.Subset.trans (subset_of_ssubset hC'C) hX₂) hC'dep)
            let hTC := Set.ssubset_of_subset_of_ssubset hTC' hC'C
            let hTM₂ := Set.Subset.trans (subset_of_ssubset hTC) hX₂
            specialize hCmin T hTC

            unfold CircuitForm at hCmin
            push_neg at hCmin
            specialize hCmin (Matroid.Circuit.Nonempty hTcircuit) ∅ (Set.empty_subset M₁.E) T hTM₂ (eq_empty_symmDiff T)
            apply Matroid.UnionDisjointCircuits.circuit at hTcircuit
            exact (hCmin (Matroid.UnionDisjointCircuits.empty M₁.matroid)) hTcircuit
      else
        left
        apply subset_not_ssubset_eq (subset_of_subset_of_eq Set.subset_union_left hCX₁X₂.symm) at hX₁C
        rw [hX₁C] at hX₁ hX₁duc
        constructor
        · exact hX₁
        · constructor
          · by_contra hCindep
            apply Matroid.UnionDisjointCircuits.indep_empty hX₁duc at hCindep
            rw [hCindep] at hCnempty
            simp only [Set.not_nonempty_empty] at hCnempty
          · intro C' hC'C
            by_contra hC'dep

            obtain ⟨T, hTC', hTcircuit⟩ := (Matroid.Circuit.DepHasCircuit (Set.Subset.trans (subset_of_ssubset hC'C) hX₁) hC'dep)
            let hTC := Set.ssubset_of_subset_of_ssubset hTC' hC'C
            let hTM₁ := Set.Subset.trans (subset_of_ssubset hTC) hX₁
            specialize hCmin T hTC

            unfold CircuitForm at hCmin
            push_neg at hCmin
            specialize hCmin (Matroid.Circuit.Nonempty hTcircuit) T hTM₁ ∅ (Set.empty_subset M₂.E) (eq_symmDiff_empty T)
            apply Matroid.UnionDisjointCircuits.circuit at hTcircuit
            exact (hCmin hTcircuit) (Matroid.UnionDisjointCircuits.empty M₂.matroid)


section SpecialCase2Sum

/-- If `M₁.E ∩ M₂.E = {p}` and neither `M₁` nor `M₂` has `p` as loop or coloop, then `M₁ Δ M₂ = M₁ ⊕₂ M₂`. -/
lemma DeltaSum.SpecialCase2Sum {α : Type*} [DecidableEq α] {p : α} {M₁ M₂ : BinaryMatroidStandardRepr α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid p) :
    Matroid.TwoSum.matroid Assumptions = DeltaSum.matroid M₁ M₂ := by
  rw [Matroid.eq_iff_circuit_iff_circuit_forall]
  constructor
  · rw [DeltaSum.E_eq]
    sorry
  · sorry
  -- see Lemma 9.3.2 in Oxley


section SpecialCase3Sum

/-- Assumptions for Δ-sum . -/
structure DeltaSum.ThreeSumAssumptions {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) where
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
