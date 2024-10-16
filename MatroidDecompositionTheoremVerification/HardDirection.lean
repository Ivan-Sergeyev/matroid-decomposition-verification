import MatroidDecompositionTheoremVerification.EasyDirection


variable {T : Type} [DecidableEq T]

def IndepMatroid.IsGraphic (M : IndepMatroid T) : Prop :=
  sorry

def IndepMatroid.IsCographic (M : IndepMatroid T) : Prop :=
  sorry

def IndepMatroidR10 : IndepMatroid (Fin 10) :=
  sorry

inductive IndepMatroid.IsGood : IndepMatroid T → Prop
-- leaf constructors
| graphic {M : IndepMatroid T} (hM : M.IsGraphic) : M.IsGood
| cographic {M : IndepMatroid T} (hM : M.IsCographic) : M.IsGood
| theR10 {M : IndepMatroid T} {e : T ≃ Fin 10} (hM : M.mapEquiv e = IndepMatroidR10) : M.IsGood
-- fork constructors
| is1sum
    {X X₁ X₂ : Type} [DecidableEq X] [DecidableEq X₁] [DecidableEq X₂]
    {Y Y₁ Y₂ : Type} [DecidableEq Y] [DecidableEq Y₁] [DecidableEq Y₂]
    {M₁ : BinaryMatroid X₁ Y₁} {M₂ : BinaryMatroid X₂ Y₂} {M : BinaryMatroid X Y} (hM : M.Is1sum M₁ M₂)
    (hT : (X ⊕ Y) = T) : (M.toIndepMatroid.cast hT).IsGood
| is2sum
    {X X₁ X₂ : Type} [DecidableEq X] [DecidableEq X₁] [DecidableEq X₂]
    {Y Y₁ Y₂ : Type} [DecidableEq Y] [DecidableEq Y₁] [DecidableEq Y₂]
    {M₁ : BinaryMatroid X₁ Y₁} {M₂ : BinaryMatroid X₂ Y₂} {M : BinaryMatroid X Y} (hM : M.Is2sum M₁ M₂)
    (hT : (X ⊕ Y) = T) : (M.toIndepMatroid.cast hT).IsGood
| is3sum
    {X X₁ X₂ : Type} [DecidableEq X] [DecidableEq X₁] [DecidableEq X₂]
    {Y Y₁ Y₂ : Type} [DecidableEq Y] [DecidableEq Y₁] [DecidableEq Y₂]
    {M₁ : BinaryMatroid X₁ Y₁} {M₂ : BinaryMatroid X₂ Y₂} {M : BinaryMatroid X Y} (hM : M.Is3sum M₁ M₂)
    (hT : (X ⊕ Y) = T) : (M.toIndepMatroid.cast hT).IsGood

theorem hardSeymour {X Y : Type} [DecidableEq X] [DecidableEq Y] (M : RegularMatroid X Y) :
    M.toBinaryMatroid.IsGood := by
  sorry
