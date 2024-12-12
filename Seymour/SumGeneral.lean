import Seymour.Basic
import Seymour.BinaryMatroid


section ChosenSubmatrix

/-- todo: desc -/
def BinaryMatroidStandardRepr.ChosenRow {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroidStandardRepr α) (ha : {a} ⊆ M.X) : M.Y.Elem → Z2 :=
  M.B ⟨a, ha rfl⟩

/-- todo: desc -/
def BinaryMatroidStandardRepr.ChosenRowComplement {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroidStandardRepr α) (ha : {a} ⊆ M.X) : Matrix (M.X \ {a}).Elem M.Y.Elem Z2 :=
  M.B ∘ Set.diff_subset.elem

/-- todo: desc -/
def BinaryMatroidStandardRepr.ChosenCol {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroidStandardRepr α) (ha : {a} ⊆ M.Y) : M.X.Elem → Z2 :=
  (M.B · ⟨a, ha rfl⟩)

/-- todo: desc -/
def BinaryMatroidStandardRepr.ChosenColComplement {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroidStandardRepr α) (ha : {a} ⊆ M.Y) : Matrix M.X.Elem (M.Y \ {a}).Elem Z2 :=
 (M.B · ∘ Set.diff_subset.elem)

/-- todo: desc -/
lemma set_inter_eq_singleton_subset_left {α : Type*} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ X := by
  have haXY : a ∈ X ∩ Y := by rw [ha]; rfl
  have haX : a ∈ X := Set.mem_of_mem_inter_left haXY
  exact Set.singleton_subset_iff.mpr haX
  -- todo: simplify

/-- todo: desc -/
lemma set_inter_eq_singleton_subset_right {α : Type*} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ Y := by
  have haXY : a ∈ X ∩ Y := by rw [ha]; rfl
  have haY : a ∈ Y := Set.mem_of_mem_inter_right haXY
  exact Set.singleton_subset_iff.mpr haY
  -- todo: simplify


section TwoSum

/-- todo: desc -/
def BinaryMatroidStandardRepr.TwoSum.x {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroidStandardRepr α) (ha : M₁.X ∩ M₂.Y = {a}) : M₁.Y.Elem → Z2 :=
  M₁.ChosenRow (by
    apply set_inter_eq_singleton_subset_left
    exact ha
  ) -- todo: simplify

/-- todo: desc -/
def BinaryMatroidStandardRepr.TwoSum.A₁ {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroidStandardRepr α) (ha : M₁.X ∩ M₂.Y = {a}) : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 :=
  M₁.ChosenRowComplement (by
    apply set_inter_eq_singleton_subset_left
    exact ha
  ) -- todo: simplify

/-- todo: desc -/
def BinaryMatroidStandardRepr.TwoSum.y {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroidStandardRepr α) (ha : M₁.X ∩ M₂.Y = {a}) : M₂.X.Elem → Z2 :=
  M₂.ChosenCol (by
    apply set_inter_eq_singleton_subset_right
    exact ha
  ) -- todo: simplify

/-- todo: desc -/
def BinaryMatroidStandardRepr.TwoSum.A₂ {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroidStandardRepr α) (ha : M₁.X ∩ M₂.Y = {a}) : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 :=
  M₂.ChosenColComplement (by
    apply set_inter_eq_singleton_subset_right
    exact ha
  ) -- todo: simplify

/-- todo: desc -/
structure BinaryMatroidStandardRepr.TwoSum.Assumptions {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroidStandardRepr α) (a : α) where
  /-- rows of `M₁` and columns of `M₂` have exactly `a` in common -/
  ha : M₁.X ∩ M₂.Y = {a}
  /-- other than `a`, ground sets of `M₁` and `M₂` are disjoint -/
  hYX : M₁.Y ⫗ M₂.X
  hXX : M₁.X ⫗ M₂.X
  hYY: M₁.Y ⫗ M₂.Y
  /-- row of `a` in `M₁` is nonzero -/
  hx: BinaryMatroidStandardRepr.TwoSum.x M₁ M₂ ha ≠ 0
  /-- column of `a` in `M₂` is nonzero -/
  hy: BinaryMatroidStandardRepr.TwoSum.y M₁ M₂ ha ≠ 0

/-- todo: desc -/
def BinaryMatroidStandardRepr.TwoSum.BinaryMatroidStandardRepr {α : Type*} [DecidableEq α]
    {M₁ M₂ : BinaryMatroidStandardRepr α} {a : α}
    (Assumptions : BinaryMatroidStandardRepr.TwoSum.Assumptions M₁ M₂ a) : BinaryMatroidStandardRepr α :=
  let x := BinaryMatroidStandardRepr.TwoSum.x M₁ M₂ Assumptions.ha
  let y := BinaryMatroidStandardRepr.TwoSum.y M₁ M₂ Assumptions.ha
  let A₁ := BinaryMatroidStandardRepr.TwoSum.A₁ M₁ M₂ Assumptions.ha
  let A₂ := BinaryMatroidStandardRepr.TwoSum.A₂ M₁ M₂ Assumptions.ha
  ⟨
    (M₁.X \ {a}) ∪ M₂.X,
    M₁.Y ∪ (M₂.Y \ {a}),
    inferInstance,
    inferInstance,
    by
      rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
      exact ⟨
        ⟨M₁.hXY.disjoint_sdiff_left, id (Disjoint.symm Assumptions.hYX)⟩,
        ⟨disjoint_of_singleton_intersection_both_wo Assumptions.ha, M₂.hXY.disjoint_sdiff_right⟩
      ⟩, (Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂).toMatrixUnionUnion
  ⟩

-- todo: lemma: `TwoSum.BinaryMatroidStandardRepr` is a special case of `GeneralSum.BinaryMatroidStandardRepr`
-- todo: theorems about regularity


section GeneralSum

-- todo: generalize above construction

/-- General sum of two binary matroids given by their standard representations. -/
def BinaryMatroidStandardRepr.GeneralSum.BinaryMatroidStandardRepr {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroidStandardRepr α) : BinaryMatroidStandardRepr α :=
  sorry
  -- todo: merge two arbitrary binary matroids using formulas (8.3.3), (8.3.4), and (8.3.7) (aka k-sum)

-- example: 2-sum
-- def StandardRepresentation_2sum {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
--     StandardRepresentation α × Prop :=
--   let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
--   let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
--   let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
--   let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
--   ⟨
--     ⟨
--       (M₁.X \ {a}) ∪ M₂.X,
--       M₁.Y ∪ (M₂.Y \ {a}),
--       inferInstance,
--       inferInstance,
--       by
--         rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
--         exact ⟨⟨M₁.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_intersection_both_wo ha, M₂.hXY.disjoint_sdiff_right⟩⟩,
--       (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion
--     ⟩,
--     (M₁.X ⫗ M₂.X ∧ M₁.Y ⫗ M₂.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
--   ⟩


section ThreeSum

-- todo: same for 3-sum
