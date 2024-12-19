import Seymour.Basic
import Seymour.Matroid.Constructors.VectorMatroid


/-- Binary matroid given by its standard matrix representation. -/
structure BinaryMatroid (α : Type*) [DecidableEq α] where
  X : Set α -- row index set
  Y : Set α -- column index set
  decmemX : ∀ a, Decidable (a ∈ X) -- able to check if an element is in `X`
  decmemY : ∀ a, Decidable (a ∈ Y) -- able to check if an element is in `Y`
  hXY : X ⫗ Y -- `X` and `Y` are disjoint
  B : Matrix X Y Z2 -- standard representation matrix

-- Automatically infer decidability when `BinaryMatroid` is present.
attribute [instance] BinaryMatroid.decmemX
attribute [instance] BinaryMatroid.decmemY

/-- Maps a matrix with columns indexed by a sum of two sets to a matrix with columns indexed by union of these sets. -/
def Matrix.GlueColumns {α : Type*} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]
    (M : Matrix X (X ⊕ Y) Z2) : Matrix X (X ∪ Y).Elem Z2 :=
  fun i j => M i j.toSum

/-- Ground set of a binary matroid is union of row and column index sets of its standard matrix representation. -/
def BinaryMatroid.E {α : Type*} [DecidableEq α]
    (M : BinaryMatroid α) : Set α := M.X ∪ M.Y

/-- Full representation matrix of binary matroid is `[I | B]`. -/
def BinaryMatroid.A {α : Type*} [DecidableEq α]
    (M : BinaryMatroid α) : Matrix M.X (M.X ∪ M.Y).Elem Z2 :=
  (Matrix.fromColumns 1 M.B).GlueColumns

/-- Binary matroid converted to `VectorMatroid`. -/
def BinaryMatroid.VectorMatroid {α : Type*} [DecidableEq α]
    (M : BinaryMatroid α) : VectorMatroid M.X α Z2 :=
  ⟨M.X ∪ M.Y, M.A⟩

/-- Binary matroid converted to `Matroid`. -/
def BinaryMatroid.matroid {α : Type*} [DecidableEq α]
    (M : BinaryMatroid α) : Matroid α :=
  M.VectorMatroid.matroid

@[simp]
lemma BinaryMatroid.E_eq {α : Type*} [DecidableEq α]
  (M : BinaryMatroid α) : M.matroid.E = M.X ∪ M.Y := rfl

@[simp]
lemma BinaryMatroid.indep_eq {α : Type*} [DecidableEq α]
  (M : BinaryMatroid α) : M.matroid.Indep = M.VectorMatroid.IndepCols := rfl

/-- Registered conversion from `BinaryMatroid` to `Matroid`. -/
instance {α : Type*} [DecidableEq α] : Coe (BinaryMatroid α) (Matroid α) where
  coe := BinaryMatroid.matroid
