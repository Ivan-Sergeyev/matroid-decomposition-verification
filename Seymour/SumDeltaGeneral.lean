import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Matroid.Restrict
import Mathlib.Data.Matroid.Dual

import Seymour.MatroidCircuit
import Seymour.ForMathlib.CircuitMatroid
import Seymour.BinaryMatroid


section GeneralDeltaSum

/-- Ground set of Δ-sum is symmetric difference of ground sets of summand matroids. -/
def DeltaSum.E {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Set α := symmDiff M₁.E M₂.E

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where X₁ and X₂ is a disjoint union of circuits of M₁ and M₂, respectively. -/
def DeltaSum.CircuitPred {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Set α → Prop :=
  fun C => sorry -- todo: CONTINUE HERE

/-- Construction of Δ-sum via circuits. -/
def DeltaSum.GeneralConstruction {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : CircuitMatroid α :=
  ⟨
    DeltaSum.E M₁ M₂,
    DeltaSum.CircuitPred M₁ M₂,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
  ⟩

/-- Matroid corresponding to Δ-sum. -/
def DeltaSum.matroid {α : Type*} [DecidableEq α] (M₁ M₂ : BinaryMatroidStandardRepr α) : Matroid α :=
  (DeltaSum.GeneralConstruction M₁ M₂).matroid

@[inline]
def BinaryMatroidStandardRepr.JointCircuitRows {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroidStandardRepr α) :=
  {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C}

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
