import MatroidDecompositionTheoremVerification.EasyDirection


variable {α : Type} [DecidableEq α]

def BinaryMatroid.IsGraphic (M : BinaryMatroid α) : Prop :=
  sorry

def BinaryMatroid.IsCographic (M : BinaryMatroid α) : Prop :=
  sorry

-- TODO separate the ground set from the type
def MatroidR10 : BinaryMatroid (Fin 10) :=
  sorry

inductive BinaryMatroid.IsGood : BinaryMatroid α → Prop
-- leaf constructors
| graphic {M : BinaryMatroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : BinaryMatroid α} (hM : M.IsCographic) : M.IsGood
| theR10 {M : BinaryMatroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = MatroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M₁ : BinaryMatroid α} {M₂ : BinaryMatroid α} {M : BinaryMatroid α} (hM : M.Is1sum M₁ M₂) : M.IsGood
| is2sum {M₁ : BinaryMatroid α} {M₂ : BinaryMatroid α} {M : BinaryMatroid α} (hM : M.Is2sum M₁ M₂) : M.IsGood
| is3sum {M₁ : BinaryMatroid α} {M₂ : BinaryMatroid α} {M : BinaryMatroid α} (hM : M.Is3sum M₁ M₂) : M.IsGood
-- TODO is additional `mapEquiv` constructor needed?

theorem hardSeymour {M : BinaryMatroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry
