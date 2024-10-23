import MatroidDecompositionTheoremVerification.EasyDirection


variable {T : Type} [DecidableEq T]

def BinaryMatroid.IsGraphic (M : BinaryMatroid T) : Prop :=
  sorry

def BinaryMatroid.IsCographic (M : BinaryMatroid T) : Prop :=
  sorry

-- TODO separate the ground set from the type
def MatroidR10 : BinaryMatroid (Fin 10) :=
  sorry

inductive BinaryMatroid.IsGood : BinaryMatroid T → Prop
-- leaf constructors
| graphic {M : BinaryMatroid T} (hM : M.IsGraphic) : M.IsGood
| cographic {M : BinaryMatroid T} (hM : M.IsCographic) : M.IsGood
| theR10 {M : BinaryMatroid T} {e : T ≃ Fin 10} (hM : M.mapEquiv e = MatroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M₁ : BinaryMatroid T} {M₂ : BinaryMatroid T} {M : BinaryMatroid T} (hM : M.Is1sum M₁ M₂) : M.IsGood
| is2sum {M₁ : BinaryMatroid T} {M₂ : BinaryMatroid T} {M : BinaryMatroid T} (hM : M.Is2sum M₁ M₂) : M.IsGood
--| is3sum {M₁ : BinaryMatroid T} {M₂ : BinaryMatroid T} {M : BinaryMatroid T} (hM : M.Is3sum M₁ M₂) : M.IsGood

theorem hardSeymour {M : BinaryMatroid T} (hM : M.IsRegular) : M.IsGood := by
  sorry
