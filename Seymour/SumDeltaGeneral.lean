import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Matroid.Restrict
import Mathlib.Data.Matroid.Dual

import Seymour.SetTheory
import Seymour.MatroidCircuit
import Seymour.ForMathlib.CircuitMatroid
import Seymour.BinaryMatroid


section GeneralDeltaSum

/-- Ground set of Δ-sum is symmetric difference of ground sets of summand matroids. -/
def DeltaSum.E {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Set α := symmDiff M₁.E M₂.E

/-- Family of disjoint circuits of matroid `M`. -/
structure FamilyDisjointUnionCircuits {α : Type*} [DecidableEq α] (M : Matroid α) (Idx : Set α) where
  /-- Set family indexed by `Idx` -/
  -- todo: upgrade from indexing by Set β to indexing by Sort v (see Set.iUnion in Mathlib.Order.SetNotation)?
  F : Idx → Set α
  /-- All sets in family are circuits in `M` -/
  hCircuit : ∀ x, M.Circuit (F x)
  /-- All sets in family are disjoint -/
  hDisjoint : ∀ x y, x ≠ y → Disjoint (F x) (F y)

/-- Shorthand for union of sets in `FamilyDisjointUnionCircuits` -/
def FamilyDisjointUnionCircuits.union {α : Type*} [DecidableEq α] {M : Matroid α} {Idx : Set α}
    (F : FamilyDisjointUnionCircuits M Idx) : Set α :=
  Set.iUnion F.F

/-- Set `C` can be represented as disjoint union of circuits of `M`. -/
-- note: if we know that `C` is a disjoint union of circuits of `M`,
-- then we can choose `Idx` to be set of representatives of those circuits
def BinaryMatroidStandardRepr.DisjointUnionCircuits {α : Type*} [DecidableEq α]
    (M : BinaryMatroidStandardRepr α) (C : Set α) : Prop :=
  ∃ Idx, ∃ F : FamilyDisjointUnionCircuits M.matroid Idx, C = F.union

/-- Circuits in `M₁ Δ M₂` are of form `X₁ Δ X₂` where `X₁`, `X₂` are disjoint unions of circuits in `M₁`, `M₂`, resp. -/
def DeltaSum.CircuitForm {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) (C : Set α) : Prop :=
  ∃ X₁ ⊆ M₁.E, ∃ X₂ ⊆ M₂.E, C = symmDiff X₁ X₂ ∧ M₁.DisjointUnionCircuits X₁ ∧ M₂.DisjointUnionCircuits X₂

-- note : definition below is not equivalent because of how union of circuits of Mi may behave on M₁.E ∩ M₂.E
-- todo: erase definition below, it's incorrect
-- /-- Alternative way to define form of circuits in `M₁ Δ M₂`. -/
-- def DeltaSum.CircuitForm_alt {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) (C : Set α) : Prop :=
--   ∃ X ⊆ M₁.E ∩ M₂.E, Disjoint X C ∧ M₁.DisjointUnionCircuits ((C ∩ M₁.E) ∪ X) ∧ M₂.DisjointUnionCircuits ((C ∩ M₂.E) ∪ X)

-- todo: erase lemma below, it's incorrect
-- /-- Definitions of form of circuits in `M₁ Δ M₂` are equivalent. -/
-- lemma DeltaSum.Circuit_equiv {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) (C : Set α) :
--     DeltaSum.CircuitForm M₁ M₂ C ↔ DeltaSum.CircuitForm_alt M₁ M₂ C := by
--   constructor
--   · unfold CircuitForm CircuitForm_alt
--     intro hC
--     obtain ⟨X₁, hX₁E₁, X₂, hX₂E₂, hC, hX₁, hX₂⟩ := hC
--     use X₁ ∩ X₂
--     constructor
--     · exact Set.inter_subset_inter hX₁E₁ hX₂E₂
--     · constructor
--       · rw [hC]
--         exact (symmDiff_disjoint_inter X₁ X₂).symm
--       · constructor
--         · have t : X₁ = C \ M₂.E ∪ X₁ ∩ X₂ := by
--             have t1 : X₁ ∩ X₂ ⊆ M₁.E := inter_subset_parent_left hX₁E₁
--             have t2 : X₁ ∩ X₂ = X₁ ∩ X₂ ∩ M₁.E := sorry --Eq.symm ((fun {α} {s t} => Set.inter_eq_left.mpr) t1)
--             rw [hC, Set.symmDiff_def_alt]
--             nth_rewrite 2 [t2]
--             rw [←Set.union_inter_distrib_right, Set.diff_union_self, Set.union_eq_self_of_subset_right inter_subset_union]
--             sorry
--           rw [←t]
--           exact hX₁
--         · sorry
--   · unfold CircuitForm CircuitForm_alt
--     intro hX
--     obtain ⟨X, hXE, hXC, hX₁, hX₂⟩ := hX
--     use C ∩ M₁.E ∪ X
--     constructor
--     · have t1 : C ∩ M₁.E ⊆ M₁.E := by exact inter_subset_parent_right fun ⦃a⦄ a => a
--       have t2 : X ⊆ M₁.E := by rw [Set.subset_inter_iff] at hXE; exact hXE.1
--       exact Set.union_subset t1 t2
--       -- todo: simplify
--     use C ∩ M₂.E ∪ X
--     constructor
--     · have t1 : C ∩ M₂.E ⊆ M₂.E := by exact inter_subset_parent_right fun ⦃a⦄ a => a
--       have t2 : X ⊆ M₂.E := by rw [Set.subset_inter_iff] at hXE; exact hXE.2
--       exact Set.union_subset t1 t2
--       -- todo: simplify
--     · constructor
--       · rw [Set.symmDiff_def_alt]
--         sorry
--       · sorry


/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where X₁ and X₂ is a disjoint union of circuits of M₁ and M₂, respectively. -/
def DeltaSum.CircuitPred {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Set α → Prop :=
  fun C =>
  -- `C` is of necessary form
  (DeltaSum.CircuitForm M₁ M₂ C) ∧
  -- `C` is minimal w.r.t. above condition
  (∀ C' ⊂ C, ¬DeltaSum.CircuitForm M₁ M₂ C') ∧
  -- `C` is non-empty
  (C ≠ ∅)

lemma DeltaSum.empty_not_circuit {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
    ¬CircuitPred M₁ M₂ ∅ := by
  sorry

/-- Every circuit in definition of Δ-sum is subset of ground set. -/
lemma DeltaSum.CircuitPred_subset_ground {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) :
    ∀ C, CircuitPred M₁ M₂ C → C ⊆ E M₁ M₂ := by
  intro C hC
  obtain ⟨⟨X₁, hX₁, X₂, hX₂, hX₁X₂, _⟩, _⟩ := hC
  rw [hX₁X₂]
  exact symmDiff_subset_subset_symmDiff hX₁ hX₂

/-- Construction of Δ-sum via circuits. -/
def DeltaSum.GeneralConstruction {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : CircuitMatroid α :=
  ⟨
    DeltaSum.E M₁ M₂,
    DeltaSum.CircuitPred M₁ M₂,
    DeltaSum.empty_not_circuit M₁ M₂,
    sorry, -- todo: create lemma
    sorry, -- todo: create lemma
    sorry, -- todo: create lemma
    DeltaSum.CircuitPred_subset_ground M₁ M₂,
  ⟩

/-- Matroid corresponding to Δ-sum. -/
def DeltaSum.matroid {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Matroid α :=
  (DeltaSum.GeneralConstruction M₁ M₂).matroid

/-- Sets that are circuits in `M₁` or `M₂`. -/
def BinaryMatroidStandardRepr.JointCircuits {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :=
  {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C}

/-- Matrix whose rows are incidence vectors of all circuits in `M₁` and `M₂`. -/
def BinaryMatroidStandardRepr.JointCircuitMatrix {α : Type*} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :
    Matrix {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C} (M₁.E ∪ M₂.E : Set α) Z2 :=
  fun C e => (if (e : α) ∈ (C : Set α) then 1 else 0)
  -- todo: use `M₁.JointCircuitRows M₂` as first dimension of matrix;
  -- compiler doesn't "see through" definition and complains about type mismatch

/-- If `A` is a matrix over GF(2) whose columns are indexed by the elements of `M₁.E ∪ M₂.E`
    and whose rows consist of the incidence vectors of all the circuits of `M₁` and all the circuits of `M₂`, then
    `M₁ Δ M₂ = (M[A])* \ (M₁.E ∩ M₂.E)` -/
lemma DeltaSum.matrix_iff {α : Type*} [DecidableEq α]  [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :
    DeltaSum.matroid M₁ M₂ = (M₁.JointCircuitMatrix M₂).VectorMatroid.matroid.dual.restrict (M₁.E ∩ M₂.E) := by
  sorry -- see Lemma 9.3.1 in Oxley


section SpecialCase1Sum
section SpecialCase2Sum

-- todo: equivalence to 1-sum and 2-sum in special cases
-- see Lemma 9.3.2 in Oxley


section SpecialCase3Sum

-- todo: assumptions for analog of 3-sum
structure DeltaSum.ThreeSumAssumptions {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) where
  -- 1) the ground sets of binary matroids M1 and M2 meet in  a set T that is a triangle of both
  -- 2) both |E(M1)| and |E(M2)| exceed six
  -- 3) neither M1 nor M2 has a cocircuit contained in T

-- todo: Lemma 9.3.3
-- todo: Lemma 9.3.4
