import Seymour.BinaryMatroid


variable {α : Type*}

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev Matrix_2sumComposition {β : Type*} [CommRing β] {X₁ Y₁ : Set α} {X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

variable [DecidableEq α] {M₁ M₂ : BinaryMatroid α}

/-- `BinaryMatroid`-level 2-sum of two matroids.
The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def BinaryMatroid_2sum {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    BinaryMatroid α × Prop :=
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
def BinaryMatroid.Is2sumOf (M : BinaryMatroid α) (M₁ M₂ : BinaryMatroid α) : Prop :=
  ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a}, ∃ hXY : M₂.X ⫗ M₁.Y,
    let M₀ := BinaryMatroid_2sum ha hXY
    M = M₀.fst ∧ M₀.snd

variable {M : BinaryMatroid α}

-- API for access to individual fields and assumptions in the definition of 2-sum

lemma BinaryMatroid.Is2sumOf.disjoXX (hM : M.Is2sumOf M₁ M₂) :
    M₁.X ⫗ M₂.X := by
  obtain ⟨a, -, -, -, ⟨hXX, -⟩, -⟩ := hM
  exact hXX

lemma BinaryMatroid.Is2sumOf.disjoYY (hM : M.Is2sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.Y := by
  obtain ⟨a, -, -, -, ⟨-, hYY⟩, -⟩ := hM
  exact hYY

lemma BinaryMatroid.Is2sumOf.interXY (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, M₁.X ∩ M₂.Y = {a} := by
  obtain ⟨a, ha, -⟩ := hM
  exact ⟨a, ha⟩

lemma BinaryMatroid.Is2sumOf.disjoYX (hM : M.Is2sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.X := by
  obtain ⟨a, -, hXY, -⟩ := hM
  exact hXY.symm

lemma BinaryMatroid.Is2sumOf.indep (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a},
      let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
      let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
      let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
      let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion.IndepCols =
      M.toMatroid.Indep := by
  obtain ⟨a, ha, _, rfl, -⟩ := hM
  exact ⟨a, ha, rfl⟩

lemma BinaryMatroid.Is2sumOf.x_non0 (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a},
      M₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ ≠ 0 := by
  obtain ⟨a, ha, _, rfl, -, hx, -⟩ := hM
  exact ⟨a, ha, hx⟩

lemma BinaryMatroid.Is2sumOf.y_non0 (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a},
      (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) ≠ 0 := by
  obtain ⟨a, ha, _, rfl, -, -, hy⟩ := hM
  exact ⟨a, ha, hy⟩

lemma Matrix_2sumComposition_TU {X₁ Y₁ : Set α} {X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℤ} {A₂ : Matrix X₂ Y₂ ℤ}
    (hA₁ : A₁.TU) (hA₂ : A₂.TU) (x : Y₁ → ℤ) (y : X₂ → ℤ) :
    (Matrix_2sumComposition A₁ x A₂ y).TU := by
  sorry

lemma BinaryMatroid_2sum_B {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    ∃ haX₁ : a ∈ M₁.X, ∃ haY₂ : a ∈ M₂.Y,
      (BinaryMatroid_2sum ha hXY).fst.B =
      (Matrix_2sumComposition
        (M₁.B ∘ Set.diff_subset.elem)
        (M₁.B ⟨a, haX₁⟩)
        (M₂.B · ∘ Set.diff_subset.elem)
        (M₂.B · ⟨a, haY₂⟩)
      ).toMatrixUnionUnion :=
  have haXY : a ∈ M₁.X ∩ M₂.Y := ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma BinaryMatroid_2sum_isRegular {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y)
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    (BinaryMatroid_2sum ha hXY).fst.IsRegular := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hM₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hM₂
  obtain ⟨haX₁, haY₂, hB⟩ := BinaryMatroid_2sum_B ha hXY
  let x' : M₁.Y.Elem → ℤ := B₁ ⟨a, haX₁⟩
  let y' : M₂.X.Elem → ℤ := (B₂ · ⟨a, haY₂⟩)
  let A₁' : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem ℤ := B₁ ∘ Set.diff_subset.elem
  let A₂' : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem ℤ := (B₂ · ∘ Set.diff_subset.elem)
  have hB' : (Matrix_2sumComposition A₁' x' A₂' y').TU
  · apply Matrix_2sumComposition_TU
    · rw [Matrix.TU_adjoin_id_left_iff] at hB₁
      apply hB₁.comp_rows
    · rw [Matrix.TU_adjoin_id_left_iff] at hB₂
      apply hB₂.comp_cols
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
  use (Matrix_2sumComposition A₁' x' A₂' y').toMatrixUnionUnion
  constructor
  · rw [Matrix.TU_adjoin_id_left_iff]
    exact hB'.toMatrixUnionUnion
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hA₁ i₁ j₁
        simp_all
      | inr j₂ =>
        simp_all
    | inr i₂ =>
      cases hj : j.toSum with
      | inl j₁ =>
        split <;> rename_i h0 <;> simp only [Matrix.of_apply, Matrix.fromBlocks_apply₂₁, mul_eq_zero, hi, hj] at h0 ⊢
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
        simp_all [x', y', A₁', A₂']

/-- Any 2-sum of regular matroids is a regular matroid.
This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem BinaryMatroid.Is2sumOf.isRegular [Fintype M₁.X] [Fintype M₁.Y] [Fintype M₂.X] [Fintype M₂.Y]
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨a, ha, hXY, rfl, -⟩ := hM
  exact BinaryMatroid_2sum_isRegular ha hXY hM₁ hM₂

/-- If a regular matroid is a 2-sum, then the left summand of the 2-sum is regular. -/
lemma BinaryMatroid.Is2sumOf.isRegular_left (hMsum : M.Is2sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₁.IsRegular := by
  sorry

/-- If a regular matroid is a 2-sum, then the right summand of the 2-sum is regular. -/
lemma BinaryMatroid.Is2sumOf.isRegular_right (hMsum : M.Is2sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₂.IsRegular := by
  sorry
