import Seymour.BinaryMatroid
import Mathlib.Data.Matroid.Sum


variable {α : Type*}

/-- Matrix-level 1-sum for matroids defined by their standard representation matrices. -/
abbrev Matrix_1sumComposition {β : Type*} [CommRing β] {X₁ Y₁ : Set α} {X₂ Y₂ : Set α} (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 0 A₂

variable [DecidableEq α] {M₁ M₂ : BinaryMatroid α}

/-- BinaryMatroid-level 1-sum of two matroids. It checks that everything is disjoint (returned as `.snd` of the output). -/
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

/-- Matroid `M` is a result of 1-summing `M₁` and `M₂` (should be equivalent to direct sums). -/
def BinaryMatroid.Is1sumOf (M : BinaryMatroid α) (M₁ M₂ : BinaryMatroid α) : Prop :=
  ∃ hXY : M₁.X ⫗ M₂.Y, ∃ hYX : M₁.Y ⫗ M₂.X,
    let M₀ := BinaryMatroid_1sum hXY hYX
    M = M₀.fst ∧ M₀.snd

/-- 1-sum is commutative. -/
lemma BinaryMatroid_1sum_comm (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) :
    BinaryMatroid_1sum hXY hYX = BinaryMatroid_1sum hYX.symm hXY.symm := by
  sorry

/-- 1-sum is the same as direct sum. -/
lemma BinaryMatroid_1sum.equiv_direct_sum (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) (valid : (BinaryMatroid_1sum hXY hYX).snd) :
    (BinaryMatroid_1sum hXY hYX).fst.toMatroid = Matroid.disjointSum M₁.toMatroid M₂.toMatroid (by
      simp [Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
  sorry

variable {M : BinaryMatroid α}

-- API for access to individual fields in definition of 1-sum

lemma BinaryMatroid.Is1sumOf.X_eq (hM : M.Is1sumOf M₁ M₂) :
    M.X = M₁.X ∪ M₂.X := by
  obtain ⟨_, _, rfl, -⟩ := hM
  rfl

lemma BinaryMatroid.Is1sumOf.Y_eq (hM : M.Is1sumOf M₁ M₂) :
    M.Y = M₁.Y ∪ M₂.Y := by
  obtain ⟨_, _, rfl, -⟩ := hM
  rfl

lemma BinaryMatroid.Is1sumOf.B_eq (hM : M.Is1sumOf M₁ M₂) :
    M.B = hM.X_eq ▸ hM.Y_eq ▸ (Matrix_1sumComposition M₁.B M₂.B).toMatrixUnionUnion := by
  obtain ⟨_, _, rfl, -⟩ := hM
  rfl

/-- Any 1-sum of regular matroids is a regular matroid. -/
theorem BinaryMatroid.Is1sumOf.isRegular [Fintype M₁.X] [Fintype M₁.Y] [Fintype M₂.X] [Fintype M₂.Y]
    (hM : M.Is1sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hM₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hM₂
  let B' := Matrix_1sumComposition B₁ B₂
  have hB' : B'.TU
  · apply Matrix.fromBlocks_TU
    · rwa [Matrix.TU_adjoin_id_left_iff] at hB₁
    · rwa [Matrix.TU_adjoin_id_left_iff] at hB₂
  have hMB : M.B = (Matrix_1sumComposition M₁.B M₂.B).toMatrixElemElem hM.X_eq hM.Y_eq
  · rewrite [hM.B_eq]
    rfl
  use B'.toMatrixElemElem hM.X_eq hM.Y_eq
  constructor
  · rw [Matrix.TU_adjoin_id_left_iff]
    exact hB'.toMatrixElemElem hM.X_eq hM.Y_eq
  · intro i j
    simp only [hMB, Matrix_1sumComposition, Matrix.toMatrixElemElem_eq]
    cases hi : (hM.X_eq ▸ i).toSum with
    | inl i₁ =>
      cases hj : (hM.Y_eq ▸ j).toSum with
      | inl j₁ =>
        specialize hBB₁ i₁ j₁
        simp_all [B']
      | inr j₂ =>
        simp_all [B']
    | inr i₂ =>
      cases hj : (hM.Y_eq ▸ j).toSum with
      | inl j₁ =>
        simp_all [B']
      | inr j₂ =>
        specialize hBB₂ i₂ j₂
        simp_all [B']

/-- If a regular matroid is a 1-sum, then the left summand of the 1-sum is regular. -/
lemma BinaryMatroid.Is1sumOf.isRegular_left (hMsum : M.Is1sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₁.IsRegular := by
  sorry

/-- If a regular matroid is a 1-sum, then the right summand of the 1-sum is regular. -/
lemma BinaryMatroid.Is1sumOf.isRegular_right (hMsum : M.Is1sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₂.IsRegular := by
  sorry
