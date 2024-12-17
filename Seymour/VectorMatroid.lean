import Mathlib.Data.Matroid.IndepAxioms
import Seymour.Basic


section VectorMatroid

/-- Vector matroid `M[A]` of matrix `A`. -/
structure VectorMatroid (X α F : Type*) [Field F] where
  -- X -- row index set
  Y : Set α -- column index set
  A : Matrix X Y F -- matrix defining a vector matroid

/-- Vector matroid corresponding to matrix `A`. -/
def Matrix.VectorMatroid {X α F : Type*} [Field F] {Y : Set α} (A : Matrix X Y F) : VectorMatroid X α F :=
  ⟨Y, A⟩

/-- todo: remove after 2-sum is fixed -/
def Matrix.IndepCols {X α F : Type*} [Field F] {Y : Set α} (A : Matrix X Y F) (S : Set α) : Prop :=
  ∃ hS : S ⊆ Y, LinearIndependent F (A.submatrix id hS.elem).transpose

/-- A set `S` is independent in `M[A]` iff `S` is a subset of linearly independent columns in `A`. -/
def VectorMatroid.IndepCols {X α F : Type*} [Field F] (M : VectorMatroid X α F) (S : Set α) : Prop :=
  ∃ hS : S ⊆ M.Y, LinearIndependent F (M.A.submatrix id hS.elem).transpose

/-- Empty set is independent. -/
theorem VectorMatroid.IndepCols_empty {X α F : Type*} [Field F] (M : VectorMatroid X α F) : M.IndepCols ∅ := by
  use Set.empty_subset M.Y
  exact linearIndependent_empty_type

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem VectorMatroid.IndepCols_subset {X α F : Type*} [Field F] (M : VectorMatroid X α F)
    (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) : M.IndepCols I := by
  obtain ⟨hJ, hM⟩ := hMJ
  use hIJ.trans hJ
  show LinearIndependent F (fun i j => M.A j (hJ.elem (Subtype.map id hIJ i)))
  apply hM.comp
  intro _ _ hf
  apply Subtype.eq
  simpa [Subtype.map] using hf

/-- A non-maximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem VectorMatroid.IndepCols_aug {X α F : Type*} [Field F] (M : VectorMatroid X α F) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  sorry

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.IndepCols_maximal {X α F : Type*} [Field F] (M : VectorMatroid X α F) (S : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols S := by
  sorry

/-- Vector matroid expressed as `IndepMatroid`. -/
def VectorMatroid.IndepMatroid {X α F : Type*} [Field F] (M : VectorMatroid X α F) : IndepMatroid α where
  E := M.Y
  Indep := M.IndepCols
  indep_empty := M.IndepCols_empty
  indep_subset := M.IndepCols_subset
  indep_aug := M.IndepCols_aug
  indep_maximal S _ := M.IndepCols_maximal S
  subset_ground S := by
    unfold IndepCols
    intro hS
    obtain ⟨hS', _⟩ := hS
    exact hS'

/-- Vector matroid converted to `Matroid`. -/
def VectorMatroid.matroid {X α F : Type*} [Field F] (M : VectorMatroid X α F) : Matroid α :=
  M.IndepMatroid.matroid


section Representability

def Matroid.RepresentedBy {X α F : Type*} {Y : Set α} [Field F] (M : Matroid α) (A : Matrix X Y F) : Prop :=
  M = (⟨Y, A⟩ : VectorMatroid X α F).IndepMatroid.matroid

def Matroid.RepresentableOver {α : Type*} (M : Matroid α) (F : Type*) [Field F] : Prop :=
  ∃ X : Type*, ∃ M' : VectorMatroid X α F, M'.IndepMatroid.matroid = M

-- todo: this doesn't compile due to "universe-level metavariables"
-- def Matroid.Representable {α : Type*} (M : Matroid α) : Prop :=
--   ∃ F : Type*, ∃ _ : Field F, M.RepresentableOver F -- todo: check correctness of Field F


section API

@[simp]
lemma VectorMatroid.E_eq {X α F : Type*} [Field F]
    (M : VectorMatroid X α F) : M.matroid.E = M.Y := by rfl

@[simp]
lemma VectorMatroid.indep_eq {X α F : Type*} [Field F]
  (M : VectorMatroid X α F) : M.matroid.Indep = M.IndepCols := rfl
