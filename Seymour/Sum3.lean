import Seymour.BinaryMatroid


variable {α : Type*}

/-- Matrix-level 3-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
noncomputable abbrev Matrix_3sumComposition {β : Type*} [CommRing β] {X₁ Y₁ : Set α} {X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) β) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ β)
    (z₁ : Y₁ → β) (z₂ : X₂ → β) (D : Matrix (Fin 2) (Fin 2) β) (D₁ : Matrix (Fin 2) Y₁ β) (D₂ : Matrix X₂ (Fin 2) β) :
    Matrix ((X₁ ⊕ Unit) ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ (Unit ⊕ Y₂)) β :=
  -- Unfortunately `Ring.inverse` is `noncomputable` and upgrading `β` to `Field` does not help.
  let D₁₂ : Matrix X₂ Y₁ β := D₂ * D⁻¹ * D₁
  Matrix.fromBlocks
    (Matrix.fromRows A₁ (Matrix.row Unit (Sum.elim z₁ ![1, 1]))) 0
    (Matrix.fromBlocks D₁ D D₁₂ D₂) (Matrix.fromColumns (Matrix.col Unit (Sum.elim ![1, 1] z₂)) A₂)

variable [DecidableEq α] {M₁ M₂ : BinaryMatroid α}

/-- BinaryMatroid-level 3-sum of two matroids.
The second part checks legitimacy (TODO document very specific conditions about the standard representation matrices). -/
noncomputable def BinaryMatroid_3sum {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : M₁.X ∩ M₂.X = {x₁, x₂, x₃}) (hYY : M₁.Y ∩ M₂.Y = {y₁, y₂, y₃}) (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) :
    BinaryMatroid α × Prop :=
  have hxxx₁ : {x₁, x₂, x₃} ⊆ M₁.X := hXX.symm.subset.trans Set.inter_subset_left
  have hxxx₂ : {x₁, x₂, x₃} ⊆ M₂.X := hXX.symm.subset.trans Set.inter_subset_right
  have hyyy₁ : {y₁, y₂, y₃} ⊆ M₁.Y := hYY.symm.subset.trans Set.inter_subset_left
  have hyyy₂ : {y₁, y₂, y₃} ⊆ M₂.Y := hYY.symm.subset.trans Set.inter_subset_right
  have x₁inX₁ : x₁ ∈ M₁.X := hxxx₁ (Set.mem_insert x₁ {x₂, x₃})
  have x₁inX₂ : x₁ ∈ M₂.X := hxxx₂ (Set.mem_insert x₁ {x₂, x₃})
  have x₂inX₁ : x₂ ∈ M₁.X := hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
  have x₂inX₂ : x₂ ∈ M₂.X := hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
  have x₃inX₁ : x₃ ∈ M₁.X := hxxx₁ (by simp)
  have x₃inX₂ : x₃ ∈ M₂.X := hxxx₂ (by simp)
  have y₃inY₁ : y₃ ∈ M₁.Y := hyyy₁ (by simp)
  have y₃inY₂ : y₃ ∈ M₂.Y := hyyy₂ (by simp)
  have y₂inY₁ : y₂ ∈ M₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₂inY₂ : y₂ ∈ M₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₁inY₁ : y₁ ∈ M₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
  have y₁inY₂ : y₁ ∈ M₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
  -- The actual definition starts here:
  let A₁ : Matrix (M₁.X \ {x₁, x₂, x₃}).Elem ((M₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
    Matrix.of (fun i j => M₁.B
        ⟨i.val, Set.mem_of_mem_diff i.property⟩
        (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩]))
  let A₂ : Matrix (Fin 2 ⊕ (M₂.X \ {x₁, x₂, x₃}).Elem) (M₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
    Matrix.of (fun i j => M₂.B
        (i.casesOn ![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
        ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₁ : (M₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
    (fun j => M₁.B ⟨x₁, x₁inX₁⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₂ : (M₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
    (fun i => M₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, y₃inY₂⟩)
  let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
    Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩] j))
  let D_₂ : Matrix (Fin 2) (Fin 2) Z2 := -- the middle left 2x2 submatrix
    Matrix.of (fun i j => M₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
  let D₁ : Matrix (Fin 2) (M₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let D₂ : Matrix (M₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => M₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
  ⟨
    ⟨
      (M₁.X \ {x₁, x₂, x₃}) ∪ M₂.X,
      M₁.Y ∪ (M₂.Y \ {y₁, y₂, y₃}),
      inferInstance,
      inferInstance,
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨M₁.hXY.disjoint_sdiff_left, hYX.symm⟩, ⟨hXY.disjoint_sdiff_right.disjoint_sdiff_left, M₂.hXY.disjoint_sdiff_right⟩⟩,
      Matrix.of (fun i j =>
        Matrix_3sumComposition A₁ A₂ z₁ z₂ D_₁ D₁ D₂ (
          if hi₁ : i.val ∈ M₁.X \ {x₁, x₂, x₃} then Sum.inl (Sum.inl ⟨i, hi₁⟩) else
          if hi₂ : i.val ∈ M₂.X \ {x₁, x₂, x₃} then Sum.inr (Sum.inr ⟨i, hi₂⟩) else
          if hx₁ : i.val = x₁ then Sum.inl (Sum.inr ()) else
          if hx₂ : i.val = x₂ then Sum.inr (Sum.inl 0) else
          if hx₃ : i.val = x₃ then Sum.inr (Sum.inl 1) else
          (i.property.elim hi₁ (by simp_all)).elim
          -- TODO can `Matrix.toMatrixUnionUnion` be combined with something else to simplify this definition?
        ) (
          if hj₁ : j.val ∈ M₁.Y \ {y₁, y₂, y₃} then Sum.inl (Sum.inl ⟨j, hj₁⟩) else
          if hj₂ : j.val ∈ M₂.Y \ {y₁, y₂, y₃} then Sum.inr (Sum.inr ⟨j, hj₂⟩) else
          if hy₁ : j.val = y₁ then Sum.inl (Sum.inr 1) else
          if hy₂ : j.val = y₂ then Sum.inl (Sum.inr 0) else
          if hy₃ : j.val = y₃ then Sum.inr (Sum.inl ()) else
          (j.property.elim (by simp_all) hj₂).elim
        )
      )
    ⟩,
    IsUnit D_₁ ∧ D_₁ = D_₂ -- the matrix `D_₁ = D_₂` (called D-bar in the book) is invertible
    ∧ M₁.B ⟨x₁, x₁inX₁⟩ ⟨y₁, y₁inY₁⟩ = 1
    ∧ M₁.B ⟨x₁, x₁inX₁⟩ ⟨y₂, y₂inY₁⟩ = 1
    ∧ M₁.B ⟨x₂, x₂inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
    ∧ M₁.B ⟨x₃, x₃inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
    ∧ M₂.B ⟨x₁, x₁inX₂⟩ ⟨y₁, y₁inY₂⟩ = 1
    ∧ M₂.B ⟨x₁, x₁inX₂⟩ ⟨y₂, y₂inY₂⟩ = 1
    ∧ M₂.B ⟨x₂, x₂inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
    ∧ M₂.B ⟨x₃, x₃inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ M₁.X, x ≠ x₂ ∧ x ≠ x₃ → M₁.B ⟨x, hx⟩ ⟨y₃, y₃inY₁⟩ = 0) -- the rest of the rightmost column is `0`s
    ∧ (∀ y : α, ∀ hy : y ∈ M₂.Y, y ≠ y₂ ∧ y ≠ y₁ → M₂.B ⟨x₁, x₁inX₂⟩ ⟨y, hy⟩ = 0) -- the rest of the topmost row is `0`s
  ⟩

/-- Matroid `M` is a result of 3-summing `M₁` and `M₂` in some way. -/
def BinaryMatroid.Is3sumOf (M : BinaryMatroid α) (M₁ M₂ : BinaryMatroid α) : Prop :=
  ∃ x₁ x₂ x₃ y₁ y₂ y₃ : α,
    ∃ hXX : M₁.X ∩ M₂.X = {x₁, x₂, x₃}, ∃ hYY : M₁.Y ∩ M₂.Y = {y₁, y₂, y₃}, ∃ hXY : M₁.X ⫗ M₂.Y, ∃ hYX : M₁.Y ⫗ M₂.X,
      let M₀ := BinaryMatroid_3sum hXX hYY hXY hYX
      M = M₀.fst ∧ M₀.snd

variable {M : BinaryMatroid α}

-- API for access to individual fields and assumptions in the definition of 2-sum

lemma BinaryMatroid.Is3sumOf.X_eq (hM : M.Is3sumOf M₁ M₂) :
    M.X = M₁.X ∪ M₂.X := by
  obtain ⟨_, _, _, _, _, _, hXX, _, _, _, rfl, -⟩ := hM
  simp [BinaryMatroid_3sum, ←hXX, setminus_inter_union_eq_union]

lemma BinaryMatroid.Is3sumOf.Y_eq (hM : M.Is3sumOf M₁ M₂) :
    M.Y = M₁.Y ∪ M₂.Y := by
  obtain ⟨_, _, _, _, _, _, _, hYY, _, _, rfl, -⟩ := hM
  simp [BinaryMatroid_3sum, ←hYY, setminus_inter_union_eq_union]

lemma BinaryMatroid.Is3sumOf.interXX (hM : M.Is3sumOf M₁ M₂) :
    ∃ x₁ x₂ x₃ : α, M₁.X ∩ M₂.X = {x₁, x₂, x₃} := by
  obtain ⟨x₁, x₂, x₃, -, -, -, hXX, -⟩ := hM
  exact ⟨x₁, x₂, x₃, hXX⟩

lemma BinaryMatroid.Is3sumOf.interYY (hM : M.Is3sumOf M₁ M₂) :
    ∃ y₁ y₂ y₃ : α, M₁.Y ∩ M₂.Y = {y₁, y₂, y₃} := by
  obtain ⟨-, -, -, y₁, y₂, y₃, -, hYY, -⟩ := hM
  exact ⟨y₁, y₂, y₃, hYY⟩

lemma BinaryMatroid.Is3sumOf.disjoXY (hM : M.Is3sumOf M₁ M₂) :
    M₁.X ⫗ M₂.Y := by
  obtain ⟨-, -, -, -, -, -, -, -, hXY, -⟩ := hM
  exact hXY

lemma BinaryMatroid.Is3sumOf.disjoYX (hM : M.Is3sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.X := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hYX, -⟩ := hM
  exact hYX

lemma BinaryMatroid.Is3sumOf.indep (hM : M.Is3sumOf M₁ M₂) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃ : α,
    ∃ x₁inX₁ : x₁ ∈ M₁.X,
    ∃ x₂inX₁ : x₂ ∈ M₁.X,
    ∃ x₂inX₂ : x₂ ∈ M₂.X,
    ∃ x₃inX₁ : x₃ ∈ M₁.X,
    ∃ x₃inX₂ : x₃ ∈ M₂.X,
    ∃ y₃inY₂ : y₃ ∈ M₂.Y,
    ∃ y₂inY₁ : y₂ ∈ M₁.Y,
    ∃ y₂inY₂ : y₂ ∈ M₂.Y,
    ∃ y₁inY₁ : y₁ ∈ M₁.Y,
    ∃ y₁inY₂ : y₁ ∈ M₂.Y,
      let A₁ : Matrix (M₁.X \ {x₁, x₂, x₃}).Elem ((M₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
        Matrix.of (fun i j => M₁.B
            ⟨i.val, Set.mem_of_mem_diff i.property⟩
            (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩]))
      let A₂ : Matrix (Fin 2 ⊕ (M₂.X \ {x₁, x₂, x₃}).Elem) (M₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
        Matrix.of (fun i j => M₂.B
            (i.casesOn ![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
            ⟨j.val, Set.mem_of_mem_diff j.property⟩)
      let z₁ : (M₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
        (fun j => M₁.B ⟨x₁, x₁inX₁⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
      let z₂ : (M₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
        (fun i => M₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, y₃inY₂⟩)
      let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
        Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩] j))
      let D₁ : Matrix (Fin 2) (M₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
        Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
      let D₂ : Matrix (M₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
        Matrix.of (fun i j => M₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
      (Matrix.of (
        fun i : ((M₁.X \ {x₁, x₂, x₃}) ∪ M₂.X).Elem =>
        fun j : (M₁.Y ∪ (M₂.Y \ {y₁, y₂, y₃})).Elem =>
          Matrix_3sumComposition A₁ A₂ z₁ z₂ D_₁ D₁ D₂ (
            if hi₁ : i.val ∈ M₁.X \ {x₁, x₂, x₃} then Sum.inl (Sum.inl ⟨i, hi₁⟩) else
            if hi₂ : i.val ∈ M₂.X \ {x₁, x₂, x₃} then Sum.inr (Sum.inr ⟨i, hi₂⟩) else
            if hx₁ : i.val = x₁ then Sum.inl (Sum.inr ()) else
            if hx₂ : i.val = x₂ then Sum.inr (Sum.inl 0) else
            if hx₃ : i.val = x₃ then Sum.inr (Sum.inl 1) else
            (i.property.elim hi₁ (by simp_all)).elim
          ) (
            if hj₁ : j.val ∈ M₁.Y \ {y₁, y₂, y₃} then Sum.inl (Sum.inl ⟨j, hj₁⟩) else
            if hj₂ : j.val ∈ M₂.Y \ {y₁, y₂, y₃} then Sum.inr (Sum.inr ⟨j, hj₂⟩) else
            if hy₁ : j.val = y₁ then Sum.inl (Sum.inr 1) else
            if hy₂ : j.val = y₂ then Sum.inl (Sum.inr 0) else
            if hy₃ : j.val = y₃ then Sum.inr (Sum.inl ()) else
            (j.property.elim (by simp_all) hj₂).elim
          )
        )
      ).IndepCols = M.toMatroid.Indep := by
  obtain ⟨x₁, x₂, x₃, y₁, y₂, y₃, hXX, hYY, -, -, rfl, -⟩ := hM
  have hxxx₁ : {x₁, x₂, x₃} ⊆ M₁.X := hXX.symm.subset.trans Set.inter_subset_left
  have hxxx₂ : {x₁, x₂, x₃} ⊆ M₂.X := hXX.symm.subset.trans Set.inter_subset_right
  have hyyy₁ : {y₁, y₂, y₃} ⊆ M₁.Y := hYY.symm.subset.trans Set.inter_subset_left
  have hyyy₂ : {y₁, y₂, y₃} ⊆ M₂.Y := hYY.symm.subset.trans Set.inter_subset_right
  exact ⟨x₁, x₂, x₃, y₁, y₂, y₃,
    hxxx₁ (Set.mem_insert x₁ {x₂, x₃}),
    hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃}),
    hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃}),
    hxxx₁ (by simp),
    hxxx₂ (by simp),
    hyyy₂ (by simp),
    hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃}),
    hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃}),
    hyyy₁ (Set.mem_insert y₁ {y₂, y₃}),
    hyyy₂ (Set.mem_insert y₁ {y₂, y₃}),
    rfl⟩

lemma BinaryMatroid.Is3sumOf.invertibilityD_₁ (hM : M.Is3sumOf M₁ M₂) :
    ∃ x₂ x₃ y₁ y₂ : α, ∃ x₂inX₁ : x₂ ∈ M₁.X, ∃ x₃inX₁ : x₃ ∈ M₁.X, ∃ y₂inY₁ : y₂ ∈ M₁.Y, ∃ y₁inY₁ : y₁ ∈ M₁.Y,
      IsUnit (Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩] j))) := by
  obtain ⟨x₁, x₂, x₃, y₁, y₂, y₃, hXX, hYY, _, _, rfl, valid⟩ := hM
  use x₂, x₃, y₁, y₂
  have hxxx : {x₁, x₂, x₃} ⊆ M₁.X := hXX.symm.subset.trans Set.inter_subset_left
  use hxxx (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃}), hxxx (by simp)
  have hyyy : {y₁, y₂, y₃} ⊆ M₁.Y := hYY.symm.subset.trans Set.inter_subset_left
  use hyyy (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃}), hyyy (Set.mem_insert y₁ {y₂, y₃})
  exact valid.left

lemma BinaryMatroid.Is3sumOf.invertibilityD_₂ (hM : M.Is3sumOf M₁ M₂) :
    ∃ x₂ x₃ y₁ y₂ : α, ∃ x₂inX₂ : x₂ ∈ M₂.X, ∃ x₃inX₂ : x₃ ∈ M₂.X, ∃ y₂inY₂ : y₂ ∈ M₂.Y, ∃ y₁inY₂ : y₁ ∈ M₂.Y,
      IsUnit (Matrix.of (fun i j => M₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))) := by
  obtain ⟨x₁, x₂, x₃, y₁, y₂, y₃, hXX, hYY, _, _, rfl, valid⟩ := hM
  use x₂, x₃, y₁, y₂
  have hxxx : {x₁, x₂, x₃} ⊆ M₂.X := hXX.symm.subset.trans Set.inter_subset_right
  use hxxx (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃}), hxxx (by simp)
  have hyyy : {y₁, y₂, y₃} ⊆ M₂.Y := hYY.symm.subset.trans Set.inter_subset_right
  use hyyy (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃}), hyyy (Set.mem_insert y₁ {y₂, y₃})
  rw [←valid.right.left]
  exact valid.left

/- TODO missing API for all of the following parts of the 3-sum definition:
M₁.B ⟨x₁, x₁inX₁⟩ ⟨y₁, y₁inY₁⟩ = 1
M₁.B ⟨x₁, x₁inX₁⟩ ⟨y₂, y₂inY₁⟩ = 1
M₁.B ⟨x₂, x₂inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
M₁.B ⟨x₃, x₃inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
M₂.B ⟨x₁, x₁inX₂⟩ ⟨y₁, y₁inY₂⟩ = 1
M₂.B ⟨x₁, x₁inX₂⟩ ⟨y₂, y₂inY₂⟩ = 1
M₂.B ⟨x₂, x₂inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
M₂.B ⟨x₃, x₃inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
(∀ x : α, ∀ hx : x ∈ M₁.X, x ≠ x₂ ∧ x ≠ x₃ → M₁.B ⟨x, hx⟩ ⟨y₃, y₃inY₁⟩ = 0)
(∀ y : α, ∀ hy : y ∈ M₂.Y, y ≠ y₂ ∧ y ≠ y₁ → M₂.B ⟨x₁, x₁inX₂⟩ ⟨y, hy⟩ = 0)
-/

/-- Any 3-sum of regular matroids is a regular matroid. -/
theorem BinaryMatroid.Is3sumOf.isRegular (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  sorry

/-- If a regular matroid is a 3-sum, then the left summand of the 3-sum is regular. -/
lemma BinaryMatroid.Is3sumOf.isRegular_left (hMsum : M.Is3sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₁.IsRegular := by
  sorry

/-- If a regular matroid is a 3-sum, then the right summand of the 3-sum is regular. -/
lemma BinaryMatroid.Is3sumOf.isRegular_right (hMsum : M.Is3sumOf M₁ M₂) (hMreg : M.IsRegular) :
    M₂.IsRegular := by
  sorry
