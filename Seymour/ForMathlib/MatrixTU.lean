import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.ForMathlib.FunctionDecompose


variable {X₁ X₂ Y₁ Y₂ R : Type*}

lemma Matrix.fromBlocks_submatrix [Zero R] (A₁ : Matrix X₁ Y₁ R) (A₂ : Matrix X₂ Y₂ R)
    {α : Type*} (f : α → X₁ ⊕ X₂) (g : α → Y₁ ⊕ Y₂) :
    (fromBlocks A₁ 0 0 A₂).submatrix f g =
    (fromBlocks
      (A₁.submatrix
        ((·.val.snd) : { x₁ : α × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
        ((·.val.snd) : { y₁ : α × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
      ) 0 0
      (A₂.submatrix
        ((·.val.snd) : { x₂ : α × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂)
        ((·.val.snd) : { y₂ : α × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
      )
     ).submatrix f.decomposeSum g.decomposeSum := by
  rw [
    f.eq_comp_decomposeSum,
    g.eq_comp_decomposeSum,
    ←Matrix.submatrix_submatrix]
  aesop

lemma in_set_range_singType_cast_mul_in_set_range_singType_cast [LinearOrderedRing R] {a b : R}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  sorry

lemma in_set_range_singType_cast_iff_abs [LinearOrderedCommRing R] (a : R) :
    a ∈ Set.range SignType.cast ↔ |a| ∈ Set.range SignType.cast := by
  sorry

attribute [-simp] Fintype.card_ofIsEmpty Fintype.card_ofSubsingleton -- major performance issue

lemma Matrix.fromBlocks_isTotallyUnimodular [LinearOrderedCommRing R]
    [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
    {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R} (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  -- different proof strategy attempted: https://github.com/madvorak/matrix-tu-experimental/blob/main/MatrixTuExperimental.lean
  intro k f g hf hg
  rw [isTotallyUnimodular_iff] at hA₁ hA₂
  rw [fromBlocks_submatrix]
  -- look at sizes of submatrices in blocks
  if hxy : Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd }
         = Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }
         ∧ Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }
         = Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
  then -- square case
    obtain ⟨cardi₁, cardi₂⟩ := hxy
    -- equivalences between canonical indexing types of given cardinality and current indexing types
    -- (domains of parts of indexing functions)
    let eX₁ :
      Fin (Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd }) ≃ { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } :=
        (Fintype.equivFin { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd }).symm
    let eX₂ :
      Fin (Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }) ≃ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } :=
        (Fintype.equivFin { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }).symm
    let eY₁ :
      Fin (Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd }) ≃ { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } :=
        (cardi₁ ▸ Fintype.equivFin { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }).symm
    let eY₂ :
      Fin (Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }) ≃ { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } :=
        (cardi₂ ▸ Fintype.equivFin { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }).symm
    -- relating submatrices in blocks to submatrices of `A₁` and `A₂`
    have hAfg :
      (fromBlocks
        (A₁.submatrix
          ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
          ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
        ) 0 0
        (A₂.submatrix
          ((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂)
          ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
        )).submatrix
          f.decomposeSum
          g.decomposeSum
      =
      (fromBlocks
        (A₁.submatrix
          (((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁) ∘ eX₁)
          (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ eY₁)
        ) 0 0
        (A₂.submatrix
          (((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂) ∘ eX₂)
          (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ eY₂)
        )).submatrix
          (f.decomposeSum.trans (Equiv.sumCongr eX₁.symm eX₂.symm))
          (g.decomposeSum.trans (Equiv.sumCongr eY₁.symm eY₂.symm))
    · ext
      simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
        Matrix.submatrix, Matrix.of_apply]
      split
      · split
        · simp
        · rfl
      · split
        · rfl
        · simp
    -- absolute value of determinant was preserved by previous mappings,
    -- and we now express it as a product of determinants of submatrices in blocks
    rw [hAfg, in_set_range_singType_cast_iff_abs, abs_det_submatrix_equiv_equiv, Matrix.det_fromBlocks_zero₁₂,
      ←in_set_range_singType_cast_iff_abs]
    -- determinants of submatrices in blocks are `0` or `±1` by TUness of `A₁` and `A₂`
    apply in_set_range_singType_cast_mul_in_set_range_singType_cast
    · apply hA₁
    · apply hA₂
  else -- the submatrix of `A₁` or the submatrix of `A₂` is non-square
    -- actually both submatrices are non-square
    obtain ⟨cardine₁, cardine₂⟩ :
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ≠
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } ∧
        Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } ≠
        Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
    · rw [not_and_or] at hxy
      have hk₁ := Fintype.card_fin k ▸ Fintype.card_congr f.decomposeSum
      have hk₂ := Fintype.card_fin k ▸ Fintype.card_congr g.decomposeSum
      rw [Fintype.card_sum] at hk₁ hk₂
      cases hxy <;> omega
    clear hxy
    -- goal: prove that `det` is `0`
    if hxy₁ :
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } <
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } then
      sorry -- the bottom half of our submatrix is singular
    else
      sorry -- the top half of our submatrix is singular
