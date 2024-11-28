import Mathlib.Data.Matroid.Map
import Seymour.Sum1
import Seymour.Sum2
import Seymour.Sum3


variable {α : Type} [DecidableEq α]

def BinaryMatroid.IsGraphic (M : BinaryMatroid α) : Prop :=
  sorry

def BinaryMatroid.IsCographic (M : BinaryMatroid α) : Prop :=
  sorry

def MatroidR10 : BinaryMatroid α :=
  sorry -- inside we have some `Fin 10 ↪ α` whose image is `E`

inductive BinaryMatroid.IsGood : BinaryMatroid α → Prop
-- leaf constructors
| graphic {M : BinaryMatroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : BinaryMatroid α} (hM : M.IsCographic) : M.IsGood
| theR10 {M : BinaryMatroid α} {e : α ≃ Fin 10} (hM : M.toMatroid.mapEquiv e = MatroidR10.toMatroid) : M.IsGood
-- fork constructorsw
| is1sum {M₁ : BinaryMatroid α} {M₂ : BinaryMatroid α} {M : BinaryMatroid α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M₁ : BinaryMatroid α} {M₂ : BinaryMatroid α} {M : BinaryMatroid α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
| is3sum {M₁ : BinaryMatroid α} {M₂ : BinaryMatroid α} {M : BinaryMatroid α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

theorem hardSeymour {M : BinaryMatroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry
