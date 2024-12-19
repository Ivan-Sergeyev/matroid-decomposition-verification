import Seymour.Basic
import Seymour.ForMathlib.SetTheory
import Seymour.Matroid.Constructors.BinaryMatroid


section ChosenSubmatrix

/-- todo: desc -/
def BinaryMatroid.ChosenRow {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroid α) (ha : {a} ⊆ M.X) : M.Y.Elem → Z2 :=
  M.B ⟨a, ha rfl⟩

/-- todo: desc -/
def BinaryMatroid.ChosenRowComplement {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroid α) (ha : {a} ⊆ M.X) : Matrix (M.X \ {a}).Elem M.Y.Elem Z2 :=
  M.B ∘ Set.diff_subset.elem

/-- todo: desc -/
def BinaryMatroid.ChosenCol {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroid α) (ha : {a} ⊆ M.Y) : M.X.Elem → Z2 :=
  (M.B · ⟨a, ha rfl⟩)

/-- todo: desc -/
def BinaryMatroid.ChosenColComplement {α : Type*} [DecidableEq α] {a : α}
    (M : BinaryMatroid α) (ha : {a} ⊆ M.Y) : Matrix M.X.Elem (M.Y \ {a}).Elem Z2 :=
 (M.B · ∘ Set.diff_subset.elem)


section TwoSum

/-- todo: desc -/
def BinaryMatroid.TwoSum.x {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroid α) (ha : M₁.X ∩ M₂.Y = {a}) : M₁.Y.Elem → Z2 :=
  M₁.ChosenRow (singleton_inter_subset_left ha)

/-- todo: desc -/
def BinaryMatroid.TwoSum.A₁ {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroid α) (ha : M₁.X ∩ M₂.Y = {a}) : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 :=
  M₁.ChosenRowComplement (singleton_inter_subset_left ha)

/-- todo: desc -/
def BinaryMatroid.TwoSum.y {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroid α) (ha : M₁.X ∩ M₂.Y = {a}) : M₂.X.Elem → Z2 :=
  M₂.ChosenCol (singleton_inter_subset_right ha)

/-- todo: desc -/
def BinaryMatroid.TwoSum.A₂ {α : Type*} [DecidableEq α] {a : α}
    (M₁ M₂ : BinaryMatroid α) (ha : M₁.X ∩ M₂.Y = {a}) : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 :=
  M₂.ChosenColComplement (singleton_inter_subset_right ha)

/-- todo: desc -/
structure BinaryMatroid.TwoSum.Assumptions {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroid α) (a : α) where
  /-- rows of `M₁` and columns of `M₂` have exactly `a` in common -/
  ha : M₁.X ∩ M₂.Y = {a}
  /-- other than `a`, ground sets of `M₁` and `M₂` are disjoint -/
  hYX : M₁.Y ⫗ M₂.X
  hXX : M₁.X ⫗ M₂.X
  hYY: M₁.Y ⫗ M₂.Y
  /-- row of `a` in `M₁` is nonzero -/
  hx: BinaryMatroid.TwoSum.x M₁ M₂ ha ≠ 0
  /-- column of `a` in `M₂` is nonzero -/
  hy: BinaryMatroid.TwoSum.y M₁ M₂ ha ≠ 0

/-- todo: desc -/
def BinaryMatroid.TwoSum.BinaryMatroid {α : Type*} [DecidableEq α]
    {M₁ M₂ : BinaryMatroid α} {a : α}
    (Assumptions : BinaryMatroid.TwoSum.Assumptions M₁ M₂ a) : BinaryMatroid α :=
  let x := BinaryMatroid.TwoSum.x M₁ M₂ Assumptions.ha
  let y := BinaryMatroid.TwoSum.y M₁ M₂ Assumptions.ha
  let A₁ := BinaryMatroid.TwoSum.A₁ M₁ M₂ Assumptions.ha
  let A₂ := BinaryMatroid.TwoSum.A₂ M₁ M₂ Assumptions.ha
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
      ⟩,
      (Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂).toMatrixUnionUnion
  ⟩

-- todo: lemma: `TwoSum.BinaryMatroid` is a special case of `GeneralSum.BinaryMatroid`
-- todo: theorems about regularity


section GeneralSum

-- todo: generalize above construction

/-- General sum of two binary matroids given by their standard representations. -/
def BinaryMatroid.GeneralSum.BinaryMatroid {α : Type*} [DecidableEq α]
    (M₁ M₂ : BinaryMatroid α) : BinaryMatroid α :=
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
