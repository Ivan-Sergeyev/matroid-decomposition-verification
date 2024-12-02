import Seymour.Mathlib.Sets
import Seymour.ForMathlib.MatrixTU


/-- The finite field on two elements; write `Z2` for "value" type but `Fin 2` for "indexing" type. -/
abbrev Z2 : Type := ZMod 2

/-- Roughly speaking `a ᕃ A = A ∪ {a}`. -/
infixr:66 " ᕃ " => Insert.insert -- TODO (low priority) use `syntax` and write a custom delaborator

/-- Writing `X ⫗ Y` is slightly more general than writing `X ∩ Y = ∅`. -/
infix:61 " ⫗ " => Disjoint


variable {α : Type*}

/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
def HasSubset.Subset.elem {X Y : Set α} (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

/-- Convert `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem`. -/
def Subtype.toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) : X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

/-- Convert `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem`. -/
def Sum.toUnion {X Y : Set α} (i : X.Elem ⊕ Y.Elem) : (X ∪ Y).Elem :=
  i.casesOn Set.subset_union_left.elem Set.subset_union_right.elem

/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
lemma toSum_toUnion {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    i.toSum.toUnion = i := by
  if hiX : i.val ∈ X then
    simp_all [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem]
  else if hiY : i.val ∈ Y then
    simp_all [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem]
  else
    exfalso
    exact i.property.elim hiX hiY

/-- Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
`X` and `Y` are disjoint. -/
lemma toUnion_toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i := by
  cases i <;> simp [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem, hXY.symm.ni_of_in]

variable {T₁ T₂ S₁ S₂ : Set α} {β : Type*}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

/-- Convert a block matrix to a matrix over set unions. -/
def Matrix.toMatrixUnionUnion (C : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  ((C ∘ Subtype.toSum) · ∘ Subtype.toSum)

/-- Convert a matrix over set unions to a block matrix. -/
def Matrix.toMatrixSumSum (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β :=
  ((C ∘ Sum.toUnion) · ∘ Sum.toUnion)

/-- Converting a block matrix to a matrix over set unions and back to a block matrix gives the original matrix, assuming
that both said unions are disjoint. -/
lemma toMatrixUnionUnion_toMatrixSumSum (hT : T₁ ⫗ T₂) (hS : S₁ ⫗ S₂) (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) :
    C.toMatrixUnionUnion.toMatrixSumSum = C := by
  ext
  simp_all [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toUnion_toSum]

/-- Converting a matrix over set unions to a block matrix and back to a matrix over set unions gives the original matrix. -/
lemma toMatrixSumSum_toMatrixUnionUnion (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    C.toMatrixSumSum.toMatrixUnionUnion = C := by
  ext
  simp_all [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toSum_toUnion]

variable {T S : Set α}

/-- Convert a block matrix to a matrix over set unions named as single indexing sets. -/
def Matrix.toMatrixElemElem (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    Matrix T S β :=
  hT ▸ hS ▸ C.toMatrixUnionUnion

/-- Direct characterization of what entries `Matrix.toMatrixElemElem` has. -/
lemma Matrix.toMatrixElemElem_apply (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) (i : T) (j : S) :
    C.toMatrixElemElem hT hS i j = C (hT ▸ i).toSum (hS ▸ j).toSum := by
  subst hT hS
  rfl

/-- Convert a matrix over set unions named as single indexing sets to a block matrix. -/
def Matrix.fromMatrixElemElem (C : Matrix T S β) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β :=
  (hT ▸ hS ▸ C).toMatrixSumSum

lemma toMatrixElemElem_fromMatrixElemElem (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) (hTT : T₁ ⫗ T₂) (hSS : S₁ ⫗ S₂)
    (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) :
    (C.toMatrixElemElem hT hS).fromMatrixElemElem hT hS = C := by
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.toMatrixElemElem, Matrix.fromMatrixElemElem, toMatrixUnionUnion_toMatrixSumSum] <;> sorry

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions. -/
lemma Matrix.TU.toMatrixUnionUnion {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) ℤ} (hC : C.TU) :
    C.toMatrixUnionUnion.TU := by
  rw [Matrix.TU_iff] at hC ⊢
  intros
  apply hC

/-- A totally unimodular matrix over set unions stays totally unimodular after converting to a block matrix. -/
lemma Matrix.TU.toMatrixSumSum {C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem ℤ} (hC : C.TU) :
    C.toMatrixSumSum.TU := by
  rw [Matrix.TU_iff] at hC ⊢
  intros
  apply hC

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions named as
single indexing sets. -/
lemma Matrix.TU.toMatrixElemElem {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) ℤ} (hC : C.TU) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    (C.toMatrixElemElem hT hS).TU :=
  hT ▸ hS ▸ hC.toMatrixUnionUnion

/-- A totally unimodular matrix over set unions named as single indexing sets stays totally unimodular after converting to
a block matrix. -/
lemma Matrix.TU.fromMatrixElemElem {C : Matrix T S ℤ} (hC : C.TU) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    (C.fromMatrixElemElem hT hS).TU := by
  sorry
