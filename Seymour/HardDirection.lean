import Mathlib.Data.Matroid.Map
import Seymour.Matroid.Operations.old_Sum1
import Seymour.Matroid.Operations.old_Sum2
import Seymour.Matroid.Operations.old_Sum3

/-!
This file states the Seymour decomposition theorem. Proving `hardSeymour` is the ultimate goal of this project.
-/

variable {α : Type} [DecidableEq α]

/-- TODO define graphics matroids. -/
def BinaryMatroid.IsGraphic (M : BinaryMatroid α) : Prop :=
  sorry

/-- TODO define cographics matroids. -/
def BinaryMatroid.IsCographic (M : BinaryMatroid α) : Prop :=
  sorry

/-- TODO define R10. -/
def MatroidR10 : BinaryMatroid α :=
  sorry -- inside we have some `Fin 10 ↪ α` whose image is `E`

/-- Given matroid can be constructed from graphic matroids & cographic matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive BinaryMatroid.IsGood : BinaryMatroid α → Prop
-- leaf constructors
| graphic {M : BinaryMatroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : BinaryMatroid α} (hM : M.IsCographic) : M.IsGood
| theR10 {M : BinaryMatroid α} {e : α ≃ Fin 10} (hM : M.matroid.mapEquiv e = MatroidR10.matroid) : M.IsGood
-- fork constructors
| is1sum {M M₁ M₂ : BinaryMatroid α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M M₁ M₂ : BinaryMatroid α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
| is3sum {M M₁ M₂ : BinaryMatroid α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

theorem hardSeymour {M : BinaryMatroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry
