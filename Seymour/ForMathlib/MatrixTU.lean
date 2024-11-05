import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic

open scoped Matrix

variable {X Y : Type*}

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
        apply Matrix.det_zero_of_column_eq hij
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
  · intro _ _ _ _ _
    apply hA

lemma Matrix.TU.apply {A : Matrix X Y ℚ} (hA : A.TU) (i : X) (j : Y) :
    A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
  let f : Fin 1 → X := (fun _ => i)
  let g : Fin 1 → Y := (fun _ => j)
  convert hA 1 f g (Function.injective_of_subsingleton f) (Function.injective_of_subsingleton g) <;>
  exact (det_fin_one (A.submatrix f g)).symm

lemma Matrix.TU.submatrix {A : Matrix X Y ℚ} (hA : A.TU) (k : ℕ) (f : Fin k → X) (g : Fin k → Y) :
    (A.submatrix f g).TU := by
  intro _ _ _ _ _
  rw [Matrix.submatrix_submatrix]
  rw [Matrix.TU_iff] at hA
  apply hA

lemma Matrix.TU.transpose {A : Matrix X Y ℚ} (hA : A.TU) : Aᵀ.TU := by
  intro _ _ _ _ _
  simp only [←Matrix.transpose_submatrix, Matrix.det_transpose]
  apply hA <;> assumption

lemma Matrix.TU_iff_transpose (A : Matrix X Y ℚ) : A.TU ↔ Aᵀ.TU := by
  constructor <;> apply Matrix.TU.transpose

lemma Matrix.mapEquiv_rows_TU {X' : Type*} [DecidableEq X']
    (A : Matrix X Y ℚ) (eX : X' ≃ X) :
    Matrix.TU (A ∘ eX) ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · simpa [Matrix.submatrix] using hA k (eX.symm ∘ f) g
  · simpa [Matrix.submatrix] using hA k (eX ∘ f) g

lemma Matrix.mapEquiv_cols_TU {Y' : Type*} [DecidableEq Y']
    (A : Matrix X Y ℚ) (eY : Y' ≃ Y) :
    Matrix.TU (A · ∘ eY) ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · simpa [Matrix.submatrix] using hA k f (eY.symm ∘ g)
  · simpa [Matrix.submatrix] using hA k f (eY ∘ g)

lemma Matrix.mapEquiv_both_TU {X' Y' : Type*} [DecidableEq X'] [DecidableEq Y']
    (A : Matrix X Y ℚ) (eX : X' ≃ X) (eY : Y' ≃ Y) :
    Matrix.TU ((A · ∘ eY) ∘ eX) ↔ A.TU := by
  rw [Matrix.mapEquiv_rows_TU, Matrix.mapEquiv_cols_TU]

lemma Matrix.TU_adjoin_row0s_iff (A : Matrix X Y ℚ) {X' : Type*} :
    (Matrix.fromRows A (Matrix.row X' 0)).TU ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · exact hA k (Sum.inl ∘ f) g
  · if zerow : ∃ i, ∃ x', f i = Sum.inr x' then
      obtain ⟨i, _, _⟩ := zerow
      left
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro
      simp_all
    else
      obtain ⟨_, rfl⟩ : ∃ f₀ : Fin k → X, f = Sum.inl ∘ f₀
      · have hi (i : Fin k) : ∃ x, f i = Sum.inl x :=
          match hfi : f i with
          | .inl x => ⟨x, rfl⟩
          | .inr x => (zerow ⟨i, x, hfi⟩).elim
        choose f₀ hf₀ using hi
        use f₀
        ext
        apply hf₀
      apply hA

lemma Matrix.TU_adjoin_rowUnit_iff (A : Matrix X Y ℚ) (j' : Y) [DecidableEq Y] :
    (Matrix.fromRows A (Matrix.row Unit (fun j : Y => if j = j' then 1 else 0))).TU ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · exact hA k (Sum.inl ∘ f) g
  · if used_row : ∃ i, ∃ x', f i = Sum.inr x' then
      obtain ⟨i, x', hix'⟩ := used_row
      if hits_one : ∃ j, g j = j' then
        -- TODO Laplacian expansion
        sorry
      else
        left
        apply Matrix.det_eq_zero_of_row_eq_zero i
        intro
        simp_all
    else
      obtain ⟨_, rfl⟩ : ∃ f₀ : Fin k → X, f = Sum.inl ∘ f₀
      · have hi (i : Fin k) : ∃ x, f i = Sum.inl x :=
          match hfi : f i with
          | .inl x => ⟨x, rfl⟩
          | .inr x => (used_row ⟨i, x, hfi⟩).elim
        choose f₀ hf₀ using hi
        use f₀
        ext
        apply hf₀
      apply hA

lemma Matrix.TU_adjoin_id_below_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y ℚ) :
    (Matrix.fromRows A (1 : Matrix Y Y ℚ)).TU ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · exact hA k (Sum.inl ∘ f) g
  · sorry -- TODO inductively apply `Matrix.TU_adjoin_rowUnit_iff`

lemma Matrix.TU_adjoin_id_above_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y ℚ) :
    (Matrix.fromRows (1 : Matrix Y Y ℚ) A).TU ↔ A.TU := by
  rw [←Matrix.mapEquiv_rows_TU (Matrix.fromRows (1 : Matrix Y Y ℚ) A) (Equiv.sumComm X Y)]
  convert Matrix.TU_adjoin_id_below_iff A
  aesop

lemma Matrix.TU_adjoin_id_left_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y ℚ) :
    (Matrix.fromColumns (1 : Matrix X X ℚ) A).TU ↔ A.TU := by
  rw [Matrix.TU_iff_transpose, Matrix.transpose_fromColumns, Matrix.transpose_one, Matrix.TU_iff_transpose A]
  exact Matrix.TU_adjoin_id_above_iff Aᵀ

lemma Matrix.TU_adjoin_id_right_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y ℚ) :
    (Matrix.fromColumns A (1 : Matrix X X ℚ)).TU ↔ A.TU := by
  rw [←Matrix.mapEquiv_cols_TU (Matrix.fromColumns A (1 : Matrix X X ℚ)) (Equiv.sumComm X Y)]
  convert Matrix.TU_adjoin_id_left_iff A
  aesop

variable {X₁ X₂ Y₁ Y₂ : Type}

lemma Matrix.submatrix_fromBlocks {α ι γ : Type*} (f : ι → X₁ ⊕ X₂) (g : γ → Y₁ ⊕ Y₂)
    (A₁₁ : Matrix X₁ Y₁ α) (A₁₂ : Matrix X₁ Y₂ α) (A₂₁ : Matrix X₂ Y₁ α) (A₂₂ : Matrix X₂ Y₂ α) :
    (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).submatrix f g =
    (fun (i : ι) (j : γ) =>
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
  obtain ⟨γ₁, γ₂, eγ, g₁, g₂, hg⟩ := todo g
  have todo_extract :
    (Matrix.fromBlocks A₁ 0 0 A₂).submatrix f g =
    ((Matrix.fromBlocks
      (A₁.submatrix f₁ g₁) 0
      0 (A₂.submatrix f₂ g₂)
    ) · ∘ eγ) ∘ eι
  · ext i j
    cases hi : eι i <;> cases hj : eγ j <;> simp [hi, hj] <;> aesop
  rw [todo_extract]
  sorry
