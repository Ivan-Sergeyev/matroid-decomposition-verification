import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

import Seymour.Matroid.Constructors.VectorMatroid


-- question: replace Field F with CommRing R everywhere?

/-- todo: desc -/
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column: 1x "+1", 1x "-1", and 0 elsewhere
def Matrix.IsGraphic {X α F : Type*} [Field F] {Y : Set α} (A : Matrix X Y F) : Prop :=
  ∀ y : Y, ∃ x₁ x₂ : X, (A x₁ y = 1) ∧ (A x₂ y = -1) ∧ (∀ x : X, x ≠ x₁ → x ≠ x₂ → A x y = 0)

/-- todo: desc -/
def VectorMatroid.IsGraphic {X α F : Type*} [Field F] (M : VectorMatroid X α F) : Prop :=
  M.A.IsGraphic

/-- todo: desc -/
def Matroid.IsGraphic {α : Type*} (M : Matroid α) : Prop :=
  ∃ X F : Type*, ∃ _ : Field F, ∃ Y : Set α, ∃ A : Matrix X Y F,
  A.IsGraphic ∧ M = (⟨Y, A⟩ : VectorMatroid X α F).matroid -- todo: use VectorMatroid.IsGraphic

/-- todo: desc -/
def VectorMatroid.IsCographic {α F : Type*} {X : Set α} [Field F] (M : VectorMatroid X α F) : Prop :=
  M.A.transpose.IsGraphic

/-- todo: desc -/
def Matroid.IsCographic {α : Type*} (M : Matroid α) : Prop :=
  ∃ F : Type*, ∃ _ : Field F, ∃ X Y : Set α, ∃ A : Matrix X Y F,
  A.transpose.IsGraphic ∧ M = (⟨Y, A⟩ : VectorMatroid X α F).matroid -- todo: use VectorMatroid.IsCographic

/-- todo: desc -/
lemma Matroid.IsGraphic_iff {α : Type*} (M : Matroid α) : M.IsGraphic ↔ M.dual.IsCographic := by sorry

/-- todo: desc -/
lemma Matroid.IsCoraphic_iff {α : Type*} (M : Matroid α) : M.IsCographic ↔ M.dual.IsGraphic := by sorry

-- /-- todo: desc -/
-- def Matroid.IsPlanar {α : Type*} (M : Matroid α) : Prop := M.IsGraphic ∧ M.IsCoraphic
