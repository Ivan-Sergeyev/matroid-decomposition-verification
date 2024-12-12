import Mathlib.Data.Matroid.Map
import Seymour.Sum1
import Seymour.Sum2
import Seymour.Sum3

/-!
This file states the Seymour decomposition theorem. Proving `hardSeymour` is the ultimate goal of this project.
-/

variable {α : Type} [DecidableEq α]

/-- TODO define graphics matroids. -/
def BinaryMatroidStandardRepr.IsGraphic (M : BinaryMatroidStandardRepr α) : Prop :=
  sorry

/-- TODO define cographics matroids. -/
def BinaryMatroidStandardRepr.IsCographic (M : BinaryMatroidStandardRepr α) : Prop :=
  sorry

/-- TODO define R10. -/
def MatroidR10 : BinaryMatroidStandardRepr α :=
  sorry -- inside we have some `Fin 10 ↪ α` whose image is `E`

/-- Given matroid can be constructed from graphic matroids, cographics matroids, and R10 using 1-sums, 2-sums, and 3-sums. -/
inductive BinaryMatroidStandardRepr.IsGood : BinaryMatroidStandardRepr α → Prop
-- leaf constructors
| graphic {M : BinaryMatroidStandardRepr α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : BinaryMatroidStandardRepr α} (hM : M.IsCographic) : M.IsGood
| theR10 {M : BinaryMatroidStandardRepr α} {e : α ≃ Fin 10} (hM : M.matroid.mapEquiv e = MatroidR10.matroid) : M.IsGood
-- fork constructors
| is1sum {M M₁ M₂ : BinaryMatroidStandardRepr α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M M₁ M₂ : BinaryMatroidStandardRepr α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
| is3sum {M M₁ M₂ : BinaryMatroidStandardRepr α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

theorem hardSeymour {M : BinaryMatroidStandardRepr α} (hM : M.Regular) : M.IsGood := by
  sorry
