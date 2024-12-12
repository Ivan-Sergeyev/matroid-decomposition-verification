import Seymour.CircuitMatroid


section MatroidConnectivity

/-- Circuit is a minimal dependent subset. -/
def Matroid.Circuit {α : Type*} (M : Matroid α) (C : Set α) : Prop :=
  ¬M.Indep C ∧ (∀ C', C' ⊂ C → M.Indep C')

/-- Connectivity relation, aka ξ in Oxley's book. -/
def Matroid.ConnectivityRelation {α : Type*} (M : Matroid α) (e f : α) : Prop :=
  (e = f) ∨ (∃ C, C ⊆ M.E ∧ M.Circuit C ∧ e ∈ C ∧ f ∈ C)

/-- Connectivity relation is an equivalence relation on M.E. -/
lemma Matroid.ConnectivityRelation.isEquivRel {α : Type*} (M : Matroid α) :
  ∀ e f : α, M.ConnectivityRelation e f → M.ConnectivityRelation f e := by sorry

/-- Component is an equivalence class under the connectivity relation, i.e., a ξ-equivalence class. -/
def Matroid.Component {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f ↔ f ∈ X

/-- Separator is a union of components. -/
def Matroid.Separator {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f → f ∈ X


section MatroidTwoSum

/-- todo: desc -/
structure Matroid.TwoSum.Assumptions {α : Type*} (M₁ M₂ : Matroid α) (a : α) where
  /-- `M₁` and `M₂` are finite -/
  hM₁fin : M₁.Finite
  hM₂fin : M₂.Finite
  /-- `M₁` and `M₂` contain at least 2 elements -/
  hM₁card : M₁.E.encard ≥ 2
  hM₂card : M₂.E.encard ≥ 2
  /-- `M₁` and `M₂` have exactly `a` in common -/
  ha : M₁.E ∩ M₂.E = {a}
  -- /-- `M₁` and `M₂`  -/
  hM₁sep : ¬M₁.Separator {a}
  hM₂sep : ¬M₂.Separator {a}

/-- todo: desc -/
def Matroid.TwoSum {α : Type*} (M₁ M₂ : Matroid α) (a : α) : Matroid α := sorry
  --S(m1, m2) / p
  -- equiv: P(m1, m2) \ p
