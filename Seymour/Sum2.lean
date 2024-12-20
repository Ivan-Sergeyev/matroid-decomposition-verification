import Seymour.BinaryMatroid

/-!
This file contains everything about 2-sum of binary matroids.
-/

variable {α : Type*}

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev Matrix_2sumComposition {β : Type*} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

variable [DecidableEq α] {M₁ M₂ : StandardRepresentation α}

/-- `StandardRepresentation`-level 2-sum of two matroids.
The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def StandardRepresentation_2sum {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    StandardRepresentation α × Prop :=
  let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
  let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
  let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
  let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
  ⟨
    ⟨
      (M₁.X \ {a}) ∪ M₂.X,
      M₁.Y ∪ (M₂.Y \ {a}),
      inferInstance,
      inferInstance,
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨M₁.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_intersection_both_wo ha, M₂.hXY.disjoint_sdiff_right⟩⟩,
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion
    ⟩,
    (M₁.X ⫗ M₂.X ∧ M₁.Y ⫗ M₂.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

/-- Binary matroid `M` is a result of 2-summing `M₁` and `M₂` in some way. -/
def StandardRepresentation.Is2sumOf (M : StandardRepresentation α) (M₁ M₂ : StandardRepresentation α) : Prop :=
  ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a}, ∃ hXY : M₂.X ⫗ M₁.Y,
    let M₀ := StandardRepresentation_2sum ha hXY
    M.toMatroid = M₀.fst.toMatroid ∧ M₀.snd

variable {M : StandardRepresentation α}

-- API for access to individual assumptions and identities in the definition of 2-sum

lemma StandardRepresentation.Is2sumOf.disjoXX (hM : M.Is2sumOf M₁ M₂) :
    M₁.X ⫗ M₂.X := by
  obtain ⟨a, -, -, -, ⟨hXX, -⟩, -⟩ := hM
  exact hXX

lemma StandardRepresentation.Is2sumOf.disjoYY (hM : M.Is2sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.Y := by
  obtain ⟨a, -, -, -, ⟨-, hYY⟩, -⟩ := hM
  exact hYY

lemma StandardRepresentation.Is2sumOf.interXY (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, M₁.X ∩ M₂.Y = {a} := by
  obtain ⟨a, ha, -⟩ := hM
  exact ⟨a, ha⟩

lemma StandardRepresentation.Is2sumOf.disjoYX (hM : M.Is2sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.X := by
  obtain ⟨a, -, hXY, -⟩ := hM
  exact hXY.symm

lemma StandardRepresentation.Is2sumOf.indep (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a},
      let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
      let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
      let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rewrite [ha]; rfl)⟩ -- the bottom row of `B₁`
      let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rewrite [ha]; rfl)⟩) -- the left column of `B₂`
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion.IndepCols =
      M.toMatroid.Indep := by
  obtain ⟨a, ha, _, hMM, -⟩ := hM
  use a, ha
  rewrite [hMM]
  rfl

lemma Matrix_2sumComposition_IsTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) (x : Y₁ → ℚ) (y : X₂ → ℚ) :
    (Matrix_2sumComposition A₁ x A₂ y).IsTotallyUnimodular := by
  sorry

lemma Matrix_2sumComposition_IsTotallyUnimodular_left {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ}
    {x : Y₁ → ℚ} {y : X₂ → ℚ} (hA : (Matrix_2sumComposition A₁ x A₂ y).IsTotallyUnimodular) :
    A₁.IsTotallyUnimodular := by
  sorry

lemma Matrix_2sumComposition_IsTotallyUnimodular_right {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ}
    {x : Y₁ → ℚ} {y : X₂ → ℚ} (hA : (Matrix_2sumComposition A₁ x A₂ y).IsTotallyUnimodular) :
    A₂.IsTotallyUnimodular := by
  sorry

lemma StandardRepresentation_2sum_B {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    ∃ haX₁ : a ∈ M₁.X, ∃ haY₂ : a ∈ M₂.Y,
      (StandardRepresentation_2sum ha hXY).fst.B =
      (Matrix_2sumComposition
        (M₁.B ∘ Set.diff_subset.elem)
        (M₁.B ⟨a, haX₁⟩)
        (M₂.B · ∘ Set.diff_subset.elem)
        (M₂.B · ⟨a, haY₂⟩)
      ).toMatrixUnionUnion :=
  have haXY : a ∈ M₁.X ∩ M₂.Y := ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma StandardRepresentation_2sum_isRegular {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y)
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    (StandardRepresentation_2sum ha hXY).fst.IsRegular := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hM₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hM₂
  obtain ⟨haX₁, haY₂, hB⟩ := StandardRepresentation_2sum_B ha hXY
  let x' : M₁.Y.Elem → ℚ := B₁ ⟨a, haX₁⟩
  let y' : M₂.X.Elem → ℚ := (B₂ · ⟨a, haY₂⟩)
  let A₁' : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem ℚ := B₁ ∘ Set.diff_subset.elem
  let A₂' : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem ℚ := (B₂ · ∘ Set.diff_subset.elem)
  have hA₁ : -- cannot be inlined
    ∀ i : (M₁.X \ {a}).Elem, ∀ j : M₁.Y.Elem,
      if M₁.B (Set.diff_subset.elem i) j = 0 then A₁' i j = 0 else A₁' i j = 1 ∨ A₁' i j = -1
  · intro i j
    exact hBB₁ (Set.diff_subset.elem i) j
  have hA₂ : -- cannot be inlined
    ∀ i : M₂.X.Elem, ∀ j : (M₂.Y \ {a}).Elem,
      if M₂.B i (Set.diff_subset.elem j) = 0 then A₂' i j = 0 else A₂' i j = 1 ∨ A₂' i j = -1
  · intro i j
    exact hBB₂ i (Set.diff_subset.elem j)
  have hx' : ∀ j, if M₁.B ⟨a, haX₁⟩ j = 0 then x' j = 0 else x' j = 1 ∨ x' j = -1
  · intro j
    exact hBB₁ ⟨a, haX₁⟩ j
  have hy' : ∀ i, if M₂.B i ⟨a, haY₂⟩ = 0 then y' i = 0 else y' i = 1 ∨ y' i = -1
  · intro i
    exact hBB₂ i ⟨a, haY₂⟩
  let B' := Matrix_2sumComposition A₁' x' A₂' y' -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · apply Matrix.IsTotallyUnimodular.toMatrixUnionUnion
    apply Matrix_2sumComposition_IsTotallyUnimodular
    · apply hB₁.comp_rows
    · apply hB₂.comp_cols
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hA₁ i₁ j₁
        simp_all [B']
      | inr j₂ =>
        simp_all [B']
    | inr i₂ =>
      cases hj : j.toSum with
      | inl j₁ =>
        split <;> rename_i h0 <;> simp only [B', Matrix.of_apply, Matrix.fromBlocks_apply₂₁, mul_eq_zero, hi, hj] at h0 ⊢
        · cases h0 with
          | inl hi₂ =>
            left
            specialize hy' i₂
            simp_all [x', y', A₁', A₂']
          | inr hj₁ =>
            right
            specialize hx' j₁
            simp_all [x', y', A₁', A₂']
        · rw [not_or] at h0
          obtain ⟨hyi₂, hxj₁⟩ := h0
          specialize hy' i₂
          specialize hx' j₁
          simp only [hyi₂, ite_false] at hy'
          simp only [hxj₁, ite_false] at hx'
          cases hx' <;> cases hy' <;> simp_all
      | inr j₂ =>
        specialize hA₂ i₂ j₂
        simp_all [x', y', A₁', A₂', B']

lemma StandardRepresentation_2sum_isRegular_left {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y)
    (hM : (StandardRepresentation_2sum ha hXY).fst.IsRegular) :
    M₁.IsRegular := by
  obtain ⟨B', hB', hBB'⟩ := hM
  obtain ⟨haX₁, haY₂, hB⟩ := StandardRepresentation_2sum_B ha hXY
  use B'.submatrix (fun i => ⟨i.val, by sorry⟩) (fun j => ⟨j.val, by sorry⟩)
  constructor
  · sorry
  · sorry

lemma StandardRepresentation_2sum_isRegular_right {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y)
    (hM : (StandardRepresentation_2sum ha hXY).fst.IsRegular) :
    M₂.IsRegular := by
  obtain ⟨B', hB', hBB'⟩ := hM
  obtain ⟨haX₁, haY₂, hB⟩ := StandardRepresentation_2sum_B ha hXY
  sorry

/-- Any 2-sum of regular matroids is a regular matroid.
This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem StandardRepresentation.Is2sumOf.isRegular [Fintype M₁.X] [Fintype M₁.Y] [Fintype M₂.X] [Fintype M₂.Y]
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨a, ha, hXY, hMM, -⟩ := hM
  rw [StandardRepresentation_toMatroid_isRegular_iff hMM]
  exact StandardRepresentation_2sum_isRegular ha hXY hM₁ hM₂

/-- If a regular matroid is a 2-sum, then the left summand of the 2-sum is regular. -/
lemma StandardRepresentation.Is2sumOf.isRegular_left (hMsum : M.Is2sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₁.IsRegular := by
  obtain ⟨a, ha, hXY, hMM, -⟩ := hMsum
  rw [StandardRepresentation_toMatroid_isRegular_iff hMM] at hMreg
  exact StandardRepresentation_2sum_isRegular_left ha hXY hMreg

/-- If a regular matroid is a 2-sum, then the right summand of the 2-sum is regular. -/
lemma StandardRepresentation.Is2sumOf.isRegular_right (hMsum : M.Is2sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₂.IsRegular := by
  obtain ⟨a, ha, hXY, hMM, -⟩ := hMsum
  rw [StandardRepresentation_toMatroid_isRegular_iff hMM] at hMreg
  exact StandardRepresentation_2sum_isRegular_right ha hXY hMreg
