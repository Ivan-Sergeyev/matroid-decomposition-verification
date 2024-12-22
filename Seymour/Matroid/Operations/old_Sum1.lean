import Mathlib.Data.Matroid.Sum
import Seymour.Matroid.Classes.IsRegular

/-!
This file contains everything about 1-sum of binary matroids.
-/

variable {α : Type*}

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices. -/
abbrev Matrix_1sumComposition {β : Type*} [Zero β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 0 A₂

variable [DecidableEq α] {M₁ M₂ : BinaryMatroid α}

/-- `BinaryMatroid`-level 1-sum of two matroids.
It checks that everything is disjoint (returned as `.snd` of the output). -/
def BinaryMatroid_1sum (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) :
    BinaryMatroid α × Prop :=
  ⟨
    ⟨
      M₁.X ∪ M₂.X,
      M₁.Y ∪ M₂.Y,
      inferInstance,
      inferInstance,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨M₁.hXY, hYX.symm⟩, ⟨hXY, M₂.hXY⟩⟩,
      (Matrix_1sumComposition M₁.B M₂.B).toMatrixUnionUnion
    ⟩,
    M₁.X ⫗ M₂.X ∧ M₁.Y ⫗ M₂.Y
  ⟩

/-- Binary matroid `M` is a result of 1-summing `M₁` and `M₂` (should be equivalent to disjoint sums). -/
def BinaryMatroid.Is1sumOf (M : BinaryMatroid α) (M₁ M₂ : BinaryMatroid α) : Prop :=
  ∃ hXY : M₁.X ⫗ M₂.Y, ∃ hYX : M₁.Y ⫗ M₂.X,
    let M₀ := BinaryMatroid_1sum hXY hYX
    M.matroid = M₀.fst.matroid ∧ M₀.snd

/-- Matroid constructed from a valid 1-sum of binary matroids is the same as disjoint sum of matroids constructed from them. -/
lemma BinaryMatroid_1sum_as_disjoint_sum {hXY : M₁.X ⫗ M₂.Y} {hYX : M₁.Y ⫗ M₂.X}
    (valid : (BinaryMatroid_1sum hXY hYX).snd) :
    (BinaryMatroid_1sum hXY hYX).fst.matroid = Matroid.disjointSum M₁.matroid M₂.matroid (by
      simp [Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
  apply Matroid.eq_of_indep_iff_indep_forall -- after bumping Mathlib, this line can become `ext`
  · unfold BinaryMatroid_1sum
    aesop
  · intro I hI
    sorry -- TODO

/-- A valid 1-sum of binary matroids is commutative. -/
lemma BinaryMatroid_1sum_comm {hXY : M₁.X ⫗ M₂.Y} {hYX : M₁.Y ⫗ M₂.X}
    (valid : (BinaryMatroid_1sum hXY hYX).snd) :
    (BinaryMatroid_1sum hXY hYX).fst.matroid = (BinaryMatroid_1sum hYX.symm hXY.symm).fst.matroid := by
    rw [
      BinaryMatroid_1sum_as_disjoint_sum valid,
      BinaryMatroid_1sum_as_disjoint_sum ⟨valid.left.symm, valid.right.symm⟩,
      Matroid.disjointSum_comm]

variable {M : BinaryMatroid α}

lemma BinaryMatroid_1sum_Regular [Fintype M₁.X] [Fintype M₁.Y] [Fintype M₂.X] [Fintype M₂.Y]
    (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    (BinaryMatroid_1sum hXY hYX).fst.IsRegular := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hM₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hM₂
  have hB : (BinaryMatroid_1sum hXY hYX).fst.B = (Matrix_1sumComposition M₁.B M₂.B).toMatrixUnionUnion
  · rfl
  let B' := Matrix_1sumComposition B₁ B₂ -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · exact (Matrix.fromBlocks_isTotallyUnimodular hB₁ hB₂).toMatrixUnionUnion
  · intro i j
    simp only [hB, B', Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hBB₁ i₁ j₁
        simp_all
      | inr j₂ =>
        simp_all
    | inr i₂ =>
      cases j.toSum with
      | inl j₁ =>
        simp_all
      | inr j₂ =>
        specialize hBB₂ i₂ j₂
        simp_all

/-- Any 1-sum of regular matroids is a regular matroid.
This is the first of the three parts of the easy direction of the Seymour's theorem. -/
theorem BinaryMatroid.Is1sumOf.IsRegular [Fintype M₁.X] [Fintype M₁.Y] [Fintype M₂.X] [Fintype M₂.Y]
    (hM : M.Is1sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨hXY, hYX, hMM, -⟩ := hM
  rw [BinaryMatroid_toMatroid_isRegular_iff hMM]
  exact BinaryMatroid_1sum_Regular hXY hYX hM₁ hM₂

/-- If a regular matroid is a 1-sum, then the left summand of the 1-sum is regular. -/
lemma BinaryMatroid.Is1sumOf.IsRegular_left (hMsum : M.Is1sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₁.IsRegular := by
  obtain ⟨B', hB', hBB'⟩ := hMreg
  sorry

/-- If a regular matroid is a 1-sum, then the right summand of the 1-sum is regular. -/
lemma BinaryMatroid.Is1sumOf.IsRegular_right (hMsum : M.Is1sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₂.IsRegular := by
  obtain ⟨B', hB', hBB'⟩ := hMreg
  sorry