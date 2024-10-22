import MatroidDecompositionTheoremVerification.EasyDirection


variable {T : Type} [DecidableEq T]

def Matroid.IsGraphic (M : Matroid T) : Prop :=
  sorry

def Matroid.IsCographic (M : Matroid T) : Prop :=
  sorry

def MatroidR10 : Matroid (Fin 10) :=
  sorry

inductive Matroid.IsGood : Matroid T → Prop
-- leaf constructors
| graphic {M : Matroid T} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid T} (hM : M.IsCographic) : M.IsGood
/-
| theR10 {M : Matroid T} {e : Fin 10 ≃ T} (hM : M.mapEquiv e = IndepMatroidR10) : M.IsGood
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
-/
theorem hardSeymour {X Y : Set T} [∀ x, Decidable (x ∈ X)] [∀ y, Decidable (y ∈ Y)] {M : BinaryMatroid X Y}
    (hM : M.IsRegular) :
    M.IsGood := by
  sorry
