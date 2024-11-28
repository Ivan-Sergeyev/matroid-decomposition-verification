import Seymour.Mathlib.Sets
import Seymour.ForMathlib.MatrixTU


/-- The finite field on two elements; write `Z2` for "value" type but `Fin 2` for "indexing" type. -/
abbrev Z2 : Type := ZMod 2

/-- Roughly speaking `a ᕃ A = A ∪ {a}`. -/
infixr:66 " ᕃ " => Insert.insert -- TODO (low priority) use `syntax` and write a custom delaborator

/-- Writing `X ⫗ Y` is slightly more general than writing `X ∩ Y = ∅`. -/
infix:61 " ⫗ " => Disjoint


variable {α : Type*}

def HasSubset.Subset.elem {X Y : Set α} (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

def Subtype.toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) : X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

variable {T₁ T₂ S₁ S₂ : Set α} {β : Type*}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

def Matrix.toMatrixUnionUnion (C : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  ((C ∘ Subtype.toSum) · ∘ Subtype.toSum)

variable {T S : Set α}

def Matrix.toMatrixElemElem (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    Matrix T S β :=
  hT ▸ hS ▸ C.toMatrixUnionUnion

lemma Matrix.toMatrixElemElem_eq (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    C.toMatrixElemElem hT hS = Matrix.of (fun i j => C (hT ▸ i).toSum (hS ▸ j).toSum) := by
  subst hT hS
  rfl

lemma Matrix.TU.toMatrixUnionUnion {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) ℤ} (hC : C.TU) :
    C.toMatrixUnionUnion.TU := by
  rw [Matrix.TU_iff] at hC ⊢
  intros
  apply hC

lemma Matrix.TU.toMatrixElemElem {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) ℤ} (hC : C.TU) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    (C.toMatrixElemElem hT hS).TU :=
  hT ▸ hS ▸ hC.toMatrixUnionUnion
