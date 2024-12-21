import Seymour.Matroid.Constructors.VectorMatroid


/-- Matroid `M` is represented by matrix `A` if vector matroid `M[A]` is exactly `M`. -/
def Matroid.IsRepresentedBy {X α F : Type*} {Y : Set α} [Field F] (M : Matroid α) (A : Matrix X Y F) : Prop :=
  M = (⟨Y, A⟩ : VectorMatroid X α F).matroid

/-- Matroid `M` can be represented over field `F` if it can be represented by some matrix with entries in `F`. -/
def Matroid.IsRepresentableOver {α : Type*} (M : Matroid α) (F : Type*) [Field F] : Prop :=
  ∃ X : Type*, ∃ M' : VectorMatroid X α F, M'.matroid = M

-- /-- Matroid `M` is representable if it is representable over some field. -/
-- -- todo: this doesn't compile due to "universe-level metavariables"
-- def Matroid.IsRepresentable {α : Type*} (M : Matroid α) : Prop :=
--   ∃ F : Type*, ∃ _ : Field F, M.RepresentableOver F -- todo: check correctness of Field F
