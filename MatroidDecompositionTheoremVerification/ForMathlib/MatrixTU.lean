import Mathlib

open scoped Matrix

variable {X Y : Type}

/-- Is the matrix `A` totally unimodular? -/
def Matrix.TU (A : Matrix X Y ℚ) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective →
    (A.submatrix f g).det = 0 ∨
    (A.submatrix f g).det = 1 ∨
    (A.submatrix f g).det = -1

lemma Matrix.TU_iff (A : Matrix X Y ℚ) : A.TU ↔
    ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y,
      (A.submatrix f g).det = 0 ∨
      (A.submatrix f g).det = 1 ∨
      (A.submatrix f g).det = -1
    := by
  constructor <;> intro hA
  · intro k f g
    if hf : f.Injective then
      if hg : g.Injective then
        exact hA k f g hf hg
      else
        left
        unfold Function.Injective at hg
        push_neg at hg
        obtain ⟨i, j, hqij, hij⟩ := hg
        apply Matrix.det_zero_of_column_eq
        · exact hij
        intro
        simp [hqij]
    else
      left
      unfold Function.Injective at hf
      push_neg at hf
      obtain ⟨i, j, hpij, hij⟩ := hf
      apply Matrix.det_zero_of_row_eq
      · exact hij
      show (A (f i)) ∘ (g ·) = (A (f j)) ∘ (g ·)
      rw [hpij]
  · intros _ _ _ _ _
    apply hA

lemma Matrix.mapEquiv_TU {X' Y' : Type} [DecidableEq X'] [DecidableEq Y']
    (A : Matrix X Y ℚ) (eX : X' ≃ X) (eY : Y' ≃ Y) :
    Matrix.TU ((A · ∘ eY) ∘ eX) ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · simpa [Matrix.submatrix] using hA k (eX.symm ∘ f) (eY.symm ∘ g)
  · simpa [Matrix.submatrix] using hA k (eX ∘ f) (eY ∘ g)

lemma Matrix.submatrix_TU {A : Matrix X Y ℚ} (hA : A.TU) (k : ℕ) (f : Fin k → X) (g : Fin k → Y) :
    (A.submatrix f g).TU := by
  intro _ _ _ _ _
  rw [Matrix.submatrix_submatrix]
  rw [Matrix.TU_iff] at hA
  apply hA

lemma Matrix.transpose_TU {A : Matrix X Y ℚ} (hA : A.TU) : Aᵀ.TU := by
  intro _ _ _ _ _
  simp only [←Matrix.transpose_submatrix, Matrix.det_transpose]
  apply hA <;> assumption

lemma Matrix.TU_glue_iff [DecidableEq X] (A : Matrix X Y ℚ) : (Matrix.fromColumns (1 : Matrix X X ℚ) A).TU ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · exact hA k f (Sum.inr ∘ g)
  · sorry

variable {X₁ X₂ Y₁ Y₂ : Type}

lemma Matrix.submatrix_fromBlocks {α : Type*} {ι ρ : Type} (f : ι → X₁ ⊕ X₂) (g : ρ → Y₁ ⊕ Y₂)
    (A₁₁ : Matrix X₁ Y₁ α) (A₁₂ : Matrix X₁ Y₂ α) (A₂₁ : Matrix X₂ Y₁ α) (A₂₂ : Matrix X₂ Y₂ α) :
    (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).submatrix f g =
    (fun (i : ι) (j : ρ) =>
      match f i with
      | .inl i₁ =>
        match g j with
        | .inl j₁ => A₁₁ i₁ j₁
        | .inr j₂ => A₁₂ i₁ j₂
      | .inr i₂ =>
        match g j with
        | .inl j₁ => A₂₁ i₂ j₁
        | .inr j₂ => A₂₂ i₂ j₂
    ) := by
  aesop

lemma todo {α β₁ β₂ : Type} (f : α → β₁ ⊕ β₂) :
    ∃ α₁ α₂ : Type, ∃ e : α ≃ α₁ ⊕ α₂, ∃ f₁ : α₁ → β₁, ∃ f₂ : α₂ → β₂,
      ∀ i : α, f i = (Sum.elim (Sum.inl ∘ f₁) (Sum.inr ∘ f₂)) (e i) := by
  classical
  use { a : α // ∃ b₁ : β₁, f a = Sum.inl b₁ }
  use { a : α // ∃ b₂ : β₂, f a = Sum.inr b₂ }
  let e' : α → { a : α // ∃ b₁ : β₁, f a = Sum.inl b₁ } ⊕ { a : α // ∃ b₂ : β₂, f a = Sum.inr b₂ } :=
    fun a : α =>
      if hb₁ : ∃ b₁ : β₁, f a = Sum.inl b₁ then sorry else sorry
  sorry

lemma Matrix.fromBlocks_TU {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ} (hA₁ : A₁.TU) (hA₂ : A₂.TU) :
    (Matrix.fromBlocks A₁ 0 0 A₂).TU := by
  intro k f g hf hg
  obtain ⟨ι₁, ι₂, eι, f₁, f₂, hf⟩ := todo f
  obtain ⟨ρ₁, ρ₂, eρ, g₁, g₂, hg⟩ := todo g
  have todo_extract :
    (Matrix.fromBlocks A₁ 0 0 A₂).submatrix f g =
    ((Matrix.fromBlocks
      (A₁.submatrix f₁ g₁) 0
      0 (A₂.submatrix f₂ g₂)
    ) · ∘ eρ) ∘ eι
  · ext i j
    cases hi : eι i <;> cases hj : eρ j <;> simp [hi, hj] <;> aesop
  rw [todo_extract]
  --rw [Matrix.det_fromBlocks_zero₂₁]
  sorry
