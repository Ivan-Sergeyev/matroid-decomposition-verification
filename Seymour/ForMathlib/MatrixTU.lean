import Mathlib.Data.Matrix.ColumnRowPartitioned
import Seymour.ForMathlib.Basic

variable {X Y R : Type*} [CommRing R]

open scoped Matrix

/-- Is the matrix `A` totally unimodular? -/
def Matrix.TU (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective →
    (A.submatrix f g).det = 0 ∨
    (A.submatrix f g).det = 1 ∨
    (A.submatrix f g).det = -1

lemma Matrix.TU_iff (A : Matrix X Y R) : A.TU ↔
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
        rw [g.not_injective_iff] at hg
        obtain ⟨i, j, hqij, hij⟩ := hg
        apply Matrix.det_zero_of_column_eq hij
        intro
        simp [hqij]
    else
      left
      rw [f.not_injective_iff] at hf
      obtain ⟨i, j, hpij, hij⟩ := hf
      apply Matrix.det_zero_of_row_eq
      · exact hij
      show (A (f i)) ∘ (g ·) = (A (f j)) ∘ (g ·)
      rw [hpij]
  · intro _ _ _ _ _
    apply hA

lemma Matrix.TU.apply {A : Matrix X Y R} (hA : A.TU) (i : X) (j : Y) :
    A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
  rw [Matrix.TU_iff] at hA
  convert hA 1 (fun _ => i) (fun _ => j) <;> simp

lemma Matrix.TU.submatrix {A : Matrix X Y R} (hA : A.TU) (k : ℕ) (f : Fin k → X) (g : Fin k → Y) :
    (A.submatrix f g).TU := by
  intro _ _ _ _ _
  rw [Matrix.submatrix_submatrix]
  rw [Matrix.TU_iff] at hA
  apply hA

lemma Matrix.TU.transpose {A : Matrix X Y R} (hA : A.TU) : Aᵀ.TU := by
  intro _ _ _ _ _
  simp only [←Matrix.transpose_submatrix, Matrix.det_transpose]
  apply hA <;> assumption

lemma Matrix.TU_iff_transpose (A : Matrix X Y R) : A.TU ↔ Aᵀ.TU := by
  constructor <;> apply Matrix.TU.transpose

lemma Matrix.mapEquiv_rows_TU {X' : Type*} [DecidableEq X']
    (A : Matrix X Y R) (eX : X' ≃ X) :
    Matrix.TU (A ∘ eX) ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · simpa [Matrix.submatrix] using hA k (eX.symm ∘ f) g
  · simpa [Matrix.submatrix] using hA k (eX ∘ f) g

lemma Matrix.TU.comp_rows {X' : Type*} {A : Matrix X Y R}
    (hA : A.TU) (e : X' → X) :
    Matrix.TU (A ∘ e) := by
  rw [Matrix.TU_iff] at hA ⊢
  intro k f g
  exact hA k (e ∘ f) g

lemma Matrix.mapEquiv_cols_TU {Y' : Type*} [DecidableEq Y']
    (A : Matrix X Y R) (eY : Y' ≃ Y) :
    Matrix.TU (A · ∘ eY) ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · simpa [Matrix.submatrix] using hA k f (eY.symm ∘ g)
  · simpa [Matrix.submatrix] using hA k f (eY ∘ g)

lemma Matrix.TU.comp_cols {Y' : Type*} {A : Matrix X Y R}
    (hA : A.TU) (e : Y' → Y) :
    Matrix.TU (A · ∘ e) := by
  rw [Matrix.TU_iff] at hA ⊢
  intro k f g
  exact hA k f (e ∘ g)

lemma Matrix.mapEquiv_both_TU {X' Y' : Type*} [DecidableEq X'] [DecidableEq Y']
    (A : Matrix X Y R) (eX : X' ≃ X) (eY : Y' ≃ Y) :
    Matrix.TU ((A · ∘ eY) ∘ eX) ↔ A.TU := by
  rw [Matrix.mapEquiv_rows_TU, Matrix.mapEquiv_cols_TU]

lemma Matrix.TU_adjoin_row0s_iff (A : Matrix X Y R) {X' : Type*} :
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

lemma Matrix.TU_adjoin_rowUnit_aux (A : Matrix X Y R) (j' : Y) [DecidableEq Y] :
    (Matrix.fromRows A (Matrix.row Unit (fun j : Y => if j = j' then 1 else 0))).TU ↔
    (Matrix.fromRows A (Matrix.row Unit 0)).TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · if used_row : ∃ i, ∃ u, f i = Sum.inr u then
      obtain ⟨i, u, hiu⟩ := used_row -- here `u = ()`
      left
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro
      simp_all
    else
      obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Fin k → X, f = Sum.inl ∘ f₀
      · have hi (i : Fin k) : ∃ x, f i = Sum.inl x :=
          match hfi : f i with
          | .inl x => ⟨x, rfl⟩
          | .inr x => (used_row ⟨i, x, hfi⟩).elim
        choose f₀ hf₀ using hi
        use f₀
        ext
        apply hf₀
      specialize hA k f g
      rwa [hf₀] at hA ⊢
  · if used_row : ∃ i, ∃ u, f i = Sum.inr u then
      obtain ⟨i, u, hiu⟩ := used_row -- here `u = ()`
      if hits_one : ∃ j, g j = j' then
        -- TODO Laplacian expansion
        sorry
      else -- copypaste all below
        left
        apply Matrix.det_eq_zero_of_row_eq_zero i
        intro
        simp_all
    else
      obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Fin k → X, f = Sum.inl ∘ f₀
      · have hi (i : Fin k) : ∃ x, f i = Sum.inl x :=
          match hfi : f i with
          | .inl x => ⟨x, rfl⟩
          | .inr x => (used_row ⟨i, x, hfi⟩).elim
        choose f₀ hf₀ using hi
        use f₀
        ext
        apply hf₀
      specialize hA k f g
      rwa [hf₀] at hA ⊢

lemma Matrix.TU_adjoin_rowUnit_iff (A : Matrix X Y R) (j' : Y) [DecidableEq Y] :
    (Matrix.fromRows A (Matrix.row Unit (fun j : Y => if j = j' then 1 else 0))).TU ↔ A.TU := by
  rw [Matrix.TU_adjoin_rowUnit_aux, Matrix.TU_adjoin_row0s_iff]

lemma Matrix.TU_adjoin_id_below_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y R) :
    (Matrix.fromRows A (1 : Matrix Y Y R)).TU ↔ A.TU := by
  rw [Matrix.TU_iff, Matrix.TU_iff]
  constructor <;> intro hA k f g
  · exact hA k (Sum.inl ∘ f) g
  · sorry -- TODO inductively apply `Matrix.TU_adjoin_rowUnit_iff`

lemma Matrix.TU_adjoin_id_above_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y R) :
    (Matrix.fromRows (1 : Matrix Y Y R) A).TU ↔ A.TU := by
  rw [←Matrix.mapEquiv_rows_TU (Matrix.fromRows (1 : Matrix Y Y R) A) (Equiv.sumComm X Y)]
  convert Matrix.TU_adjoin_id_below_iff A
  aesop

lemma Matrix.TU_adjoin_id_left_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y R) :
    (Matrix.fromColumns (1 : Matrix X X R) A).TU ↔ A.TU := by
  rw [Matrix.TU_iff_transpose, Matrix.transpose_fromColumns, Matrix.transpose_one, Matrix.TU_iff_transpose A]
  exact Matrix.TU_adjoin_id_above_iff Aᵀ

lemma Matrix.TU_adjoin_id_right_iff [DecidableEq X] [DecidableEq Y] (A : Matrix X Y R) :
    (Matrix.fromColumns A (1 : Matrix X X R)).TU ↔ A.TU := by
  rw [←Matrix.mapEquiv_cols_TU (Matrix.fromColumns A (1 : Matrix X X R)) (Equiv.sumComm X Y)]
  convert Matrix.TU_adjoin_id_left_iff A
  aesop

omit X Y
variable {X₁ X₂ Y₁ Y₂ : Type*}

lemma Matrix.fromBlocks_submatrix_apply {β ι γ : Type*} (f : ι → X₁ ⊕ X₂) (g : γ → Y₁ ⊕ Y₂)
    (A₁₁ : Matrix X₁ Y₁ β) (A₁₂ : Matrix X₁ Y₂ β) (A₂₁ : Matrix X₂ Y₁ β) (A₂₂ : Matrix X₂ Y₂ β) (i : ι) (j : γ) :
    (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).submatrix f g i j =
    match f i with
    | .inl i₁ =>
      match g j with
      | .inl j₁ => A₁₁ i₁ j₁
      | .inr j₂ => A₁₂ i₁ j₂
    | .inr i₂ =>
      match g j with
      | .inl j₁ => A₂₁ i₂ j₁
      | .inr j₂ => A₂₂ i₂ j₂
    := by
  aesop

-- This is probably not the way to go:
lemma Matrix.fromBlocks_TU {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R} (hA₁ : A₁.TU) (hA₂ : A₂.TU) :
    (Matrix.fromBlocks A₁ 0 0 A₂).TU := by
  intro k f g hf hg
  rw [Matrix.TU_iff] at hA₁ hA₂
  obtain ⟨ι₁, ι₂, eιk, f₁, f₂, hfff⟩ := todo f
  obtain ⟨γ₁, γ₂, eγk, g₁, g₂, hggg⟩ := todo g
  have hι : Fintype (ι₁ ⊕ ι₂) := Fintype.ofEquiv _ eιk
  have hι₁ : Fintype ι₁ := hι.sumLeft
  have hι₂ : Fintype ι₂ := hι.sumRight
  have hγ : Fintype (γ₁ ⊕ γ₂) := Fintype.ofEquiv _ eγk
  have hγ₁ : Fintype γ₁ := hγ.sumLeft
  have hγ₂ : Fintype γ₂ := hγ.sumRight
  clear hι hγ
  if hιγ : Fintype.card ι₁ = Fintype.card γ₁ ∧ Fintype.card ι₂ = Fintype.card γ₂ then
    obtain ⟨hιγ₁, hιγ₂⟩ := hιγ
    let eι₁ : Fin (Fintype.card ι₁) ≃ ι₁ := (Fintype.equivFin ι₁).symm
    let eι₂ : Fin (Fintype.card ι₂) ≃ ι₂ := (Fintype.equivFin ι₂).symm
    let eγ₁ : Fin (Fintype.card ι₁) ≃ γ₁ := (hιγ₁ ▸ Fintype.equivFin γ₁).symm
    let eγ₂ : Fin (Fintype.card ι₂) ≃ γ₂ := (hιγ₂ ▸ Fintype.equivFin γ₂).symm
    rw
      [show
        ((Matrix.fromBlocks A₁ 0 0 A₂).submatrix f g).det =
        (A₁.submatrix (f₁ ∘ eι₁) (g₁ ∘ eγ₁)).det * (A₂.submatrix (f₂ ∘ eι₂) (g₂ ∘ eγ₂)).det
      by
        rw [←Matrix.det_fromBlocks_zero₂₁ _ 0, hfff, hggg]
        sorry]
    apply zom_mul_zom
    · apply hA₁
    · apply hA₂
  else
    have hιγ' : Fintype.card ι₁ ≠ Fintype.card γ₁ ∧ Fintype.card ι₂ ≠ Fintype.card γ₂
    · rw [not_and_or] at hιγ
      have hkι : k = Fintype.card (ι₁ ⊕ ι₂) := Fintype.card_fin k ▸ Fintype.card_congr eιk
      have hkγ : k = Fintype.card (γ₁ ⊕ γ₂) := Fintype.card_fin k ▸ Fintype.card_congr eγk
      rw [Fintype.card_sum] at hkι hkγ
      cases hιγ <;> omega
    left
    -- here we have a singular submatrix
    rw [hfff, hggg]
    simp [Matrix.submatrix, Matrix.fromBlocks]
    sorry

lemma Matrix.fromBlocks_TU_ {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R} (hA₁ : A₁.TU) (hA₂ : A₂.TU) :
    (Matrix.fromBlocks A₁ 0 0 A₂).TU := by
  intro k f g hf hg
  rw [Matrix.TU_iff] at hA₁ hA₂
  rw [f.toSumElimComp, g.toSumElimComp]
  dsimp only [Matrix.submatrix, Matrix.fromBlocks]
  show
    (Matrix.of (fun i : Fin k => fun j : Fin k =>
      Matrix.of (Sum.elim (fun x₁ => Sum.elim (A₁ x₁) 0) (fun x₂ => Sum.elim 0 (A₂ x₂)))
        (Sum.elim
          (Sum.inl ∘ ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁))
          (Sum.inr ∘ ((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂))
        (match hfa : f i with
          | Sum.inl b₁ => Sum.inl (Subtype.mk (i, b₁) hfa)
          | Sum.inr b₂ => Sum.inr (Subtype.mk (i, b₂) hfa)
        ))
        (Sum.elim
          (Sum.inl ∘ ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁))
          (Sum.inr ∘ ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂))
        (match hfa : g j with
          | Sum.inl b₁ => Sum.inl (Subtype.mk (j, b₁) hfa)
          | Sum.inr b₂ => Sum.inr (Subtype.mk (j, b₂) hfa)
        ))
      )).det = 0
      ∨
        _
      ∨
        _
  have bla :
    Matrix.of (fun i : Fin k => fun j : Fin k =>
      Matrix.of (Sum.elim (fun x₁ => Sum.elim (A₁ x₁) 0) (fun x₂ => Sum.elim 0 (A₂ x₂)))
        (Sum.elim
          (Sum.inl ∘ ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁))
          (Sum.inr ∘ ((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂))
        (match hfa : f i with
          | Sum.inl b₁ => Sum.inl (Subtype.mk (i, b₁) hfa)
          | Sum.inr b₂ => Sum.inr (Subtype.mk (i, b₂) hfa)
        ))
        (Sum.elim
          (Sum.inl ∘ ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁))
          (Sum.inr ∘ ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂))
        (match hfa : g j with
          | Sum.inl b₁ => Sum.inl (Subtype.mk (j, b₁) hfa)
          | Sum.inr b₂ => Sum.inr (Subtype.mk (j, b₂) hfa)
        ))
      ) =
    Matrix.of (fun i : Fin k => fun j : Fin k =>
        (Sum.elim
          (fun x₁ => Sum.elim (A₁ x₁ : Y₁ → R) (0 : Y₂ → R))
          (fun x₂ => Sum.elim (0 : Y₁ → R) (A₂ x₂ : Y₂ → R))
        )
        (Sum.elim
          (Sum.inl ∘ ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁))
          (Sum.inr ∘ ((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂))
        (match hfa : f i with
          | Sum.inl b₁ => Sum.inl (Subtype.mk (i, b₁) hfa)
          | Sum.inr b₂ => Sum.inr (Subtype.mk (i, b₂) hfa)
        ))
        (Sum.elim
          (Sum.inl ∘ ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁))
          (Sum.inr ∘ ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂))
        (match hfa : g j with
          | Sum.inl b₁ => Sum.inl (Subtype.mk (j, b₁) hfa)
          | Sum.inr b₂ => Sum.inr (Subtype.mk (j, b₂) hfa)
        ))
      )
  · simp
  rw [bla]
  sorry
