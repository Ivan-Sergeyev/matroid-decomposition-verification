-- import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular -- todo: adopt
import Seymour.Basic
import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Classes.Representable


/-- Matrix `B` has a TU signing if there is a TU matrix `B'` whose entries are the same as in `B` up to signs. -/
def Matrix.Regular {α : Type*} {X Y : Set α} (B : Matrix X Y Z2) :=
  ∃ B' : Matrix X Y ℚ, B'.TU ∧ ∀ i : X, ∀ j : Y, if B i j = 0 then B' i j = 0 else B' i j = 1 ∨ B' i j = -1

/-- Binary matroid is regular if its standard representation matrix has a TU signing. -/
def BinaryMatroid.Regular {α : Type*} [DecidableEq α] (M : BinaryMatroid α) : Prop :=
  M.B.Regular

-- todo: is this useful or redundant?
-- /-- Regular matroid given as a binary matroid whose standard matrix representation has a TU signing. -/
-- structure RegularMatroid (α : Type*) [DecidableEq α] extends BinaryMatroidStandard α where
--   RegularRepr: B.Regular -- there exists a TU signing of `B`

-- todo: is this useful or redundant?
-- /-- Regular matroid as a structure defined above is regular when viewed as a binary matroid. -/
-- lemma RegularMatroid.isRegular {α : Type*} [DecidableEq α] (M : RegularMatroid α) : M.Regular := M.RegularRepr


/-- If matroid is represented by a totally unimodular matrix `A` over `ℚ`, then it is represented by `A` over any field `F`. -/
theorem Matroid.RepresentableTU_RepresentableAnyField {α X : Type*} {Y : Set α} {A : Matrix X Y ℚ}
    (M : Matroid α) (hM : M.RepresentedBy A) (hA : A.TU) :
    ∀ F : Type*, ∃ hF : Field F, M.RepresentableOver F := by -- todo: check correctness of Field F
  sorry
  -- todo: show that `A` defines the same matroid over `ℚ` and over `F`
  -- key steps:
  -- * all square submatrices of `A` have `ℚ` determinant `0` or `±1`
  -- * every square submatrix of `A` is `ℚ`-nonsingular iff it is `F`-nonsingular

/-- Binary matroid is regular iff the entire matrix has a totally unimodular signing. -/
lemma StandardRepresentation.isRegularIff0 {α : Type*} [DecidableEq α] (M : BinaryMatroid α) :
    M.Regular ↔ ∃ B' : Matrix M.X M.Y ℚ,
      (Matrix.fromColumns (1 : Matrix M.X M.X ℚ) B').TU ∧ ∀ i : M.X, ∀ j : M.Y,
        if M.B i j = 0 then B' i j = 0 else B' i j = 1 ∨ B' i j = -1
    := by
  simp [BinaryMatroid.Regular, Matrix.Regular, Matrix.TU_adjoin_id_left_iff]

/-- The following statements are parts of Theorem (9.2.9) from Truemper's book. -/
theorem BinaryMatroid.isRegularIff1 {α : Type*} [DecidableEq α] (M : BinaryMatroid α) :
    M.Regular ↔ ∃ A : Matrix M.X M.Y ℚ, A.TU ∧ M.matroid.RepresentedBy A := by
  sorry

theorem BinaryMatroid.isRegularIff2 {α : Type*} [DecidableEq α] (M : BinaryMatroid α) :
    M.Regular ↔ ∀ F : Type*, ∃ hF : Field F, M.matroid.RepresentableOver F := by -- todo: check correctness of Field F
  sorry

theorem BinaryMatroid.isRegularIff3 {α : Type*} [DecidableEq α] (M : BinaryMatroid α) :
    M.Regular ↔ M.matroid.RepresentableOver Z2 ∧ M.matroid.RepresentableOver (ZMod 3) := by -- todo: check correctness of Field F
  sorry

theorem BinaryMatroid.isRegularIff4 {α : Type*} [DecidableEq α] (M : BinaryMatroid α) :
    M.Regular ↔ M.matroid.RepresentableOver (ZMod 3) ∧
    (∀ A : Matrix M.X M.Y (ZMod 3), M.matroid.RepresentedBy A → A.TU) := by -- todo: check correctness of Field F
  sorry

-- todo: corollaries:
-- * if M is regular, every binary representation matrix of M is regular
-- * if M is regular, every minor of M is regular
-- * if M is regular, dual of M is regular

-- todo: more corollaries:
-- * if M is graphic, M is regular
-- * if M is cographic, M is regular


-- TODO very high priority!
lemma BinaryMatroid_toMatroid_isRegular_iff {α : Type*} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
  (hM : M₁.matroid = M₂.matroid) : M₁.Regular ↔ M₂.Regular := by
  sorry
