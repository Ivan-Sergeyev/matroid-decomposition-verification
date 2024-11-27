import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Sign
import Seymour.ForMathlib.Basic

/-!
# Totally unimodular matrices

This file defines totally unimodular matrices and provides basic API for them.

## Main definitions

 - `Matrix.IsTotallyUnimodular`: a matrix is totally unimodular iff every square submatrix
    (not necessarily contiguous) has determinant `0` or `1` or `-1`.

## Main results

 - `Matrix.isTotallyUnimodular_iff`: a matrix is totally unimodular iff every square submatrix
    (possibly with repeated rows and/or repeated columns) has determinant `0` or `1` or `-1`.
 - `Matrix.IsTotallyUnimodular.apply`: entry in a totally unimodular matrix is `0` or `1` or `-1`.

-/

namespace Matrix

variable {m m' n n' R : Type*} [CommRing R]

/-- `A.IsTotallyUnimodular` means that every square submatrix of `A` (not necessarily contiguous)
has determinant `0` or `1` or `-1`; that is, the determinant is in the range of `SignType.cast`. -/
def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast

lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← det_transpose, transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro _ _ _ _ _
    apply hA

lemma isTotallyUnimodular_iff_fintype_injective.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι], ∀ f : ι → m, ∀ g : ι → n, f.Injective → g.Injective →
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  constructor
  · intro hA ι _ _ f g hf hg
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
      (by rwa [Equiv.injective_comp]) (by rwa [Equiv.injective_comp])
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g hf hg
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
      (by rwa [Equiv.injective_comp]) (by rwa [Equiv.injective_comp])
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA

lemma isTotallyUnimodular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι], ∀ f : ι → m, ∀ g : ι → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA

lemma IsTotallyUnimodular.apply_finset [DecidableEq m] [DecidableEq n]
    {A : Matrix m n R} (hA : A.IsTotallyUnimodular) {M : Finset m} {N : Finset n} (hMN : M.card = N.card) :
    (A.submatrix Subtype.val (Subtype.val ∘ Finset.equivOfCardEq hMN) : Matrix M M R).det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff_fintype] at hA
  exact hA M Subtype.val (Subtype.val ∘ Finset.equivOfCardEq hMN)

abbrev _root_.HasSubset.Subset.elem' {X Y : Finset m} (hXY : X ⊆ Y) (x : X) : Y :=
  ⟨x.val, hXY x.property⟩

abbrev submatrix_subset {X X' : Finset m} {Y Y' : Finset n}
    (A : Matrix X Y R) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) :
    (Matrix X' Y' R) :=
  A.submatrix hX'.elem' hY'.elem'

noncomputable abbrev submatrix_subset_square {X X' : Finset m} {Y Y' : Finset n}
    (A : Matrix X Y R) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (hX'Y' : X'.card = Y'.card) :
    (Matrix Y' Y' R) :=
  A.submatrix (hX'.elem' ∘ Finset.equivOfCardEq hX'Y'.symm) hY'.elem'

lemma IsTotallyUnimodular.apply_submatrix_subset [DecidableEq m] [DecidableEq n]
    {M M' : Finset m} {N N' : Finset n} {A : Matrix M N R} (hA : A.IsTotallyUnimodular)
    (hM' : M' ⊆ M) (hN' : N' ⊆ N) (hM'N' : M'.card = N'.card) :
    (A.submatrix_subset_square hM' hN' hM'N').det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff_fintype] at hA
  exact hA { x // x ∈ N' } (hM'.elem' ∘ ⇑(Finset.equivOfCardEq (submatrix_subset_square.proof_1 hM'N')))
      hN'.elem' --todo: golf

lemma isTotallyUnimodular_iff_subset [DecidableEq m] [DecidableEq n]
    {M : Finset m} {N : Finset n} (A : Matrix M N R) : A.IsTotallyUnimodular ↔
    ∀ M' : Finset m, ∀ N' : Finset n, ∀ (hM' : M' ⊆ M), ∀ (hN' : N' ⊆ N), ∀ (hM'N' : M'.card = N'.card),
    (A.submatrix_subset_square hM' hN' hM'N').det ∈ Set.range SignType.cast := by
  sorry

lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n) :
    A i j ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)

lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (f : m' → m) (g : n' → n)
    (hA : A.IsTotallyUnimodular) :
    (A.submatrix f g).IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

lemma transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply IsTotallyUnimodular.transpose

lemma IsTotallyUnimodular.reindex {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    (Matrix.reindex em en A).IsTotallyUnimodular :=
  hA.submatrix _ _

lemma reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (Matrix.reindex em en A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩

/-- If `A` is totally unimodular and each row of `B` is all zeros except for at most a single `1`,
then `fromRows A B` is totally unimodular. -/
lemma IsTotallyUnimodular.fromRows_one_aux [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : ∀ i : m', B i = 0 ∨ ∃ j, B i = Function.update (0 : n → R) j 1)
    (hA : A.IsTotallyUnimodular) :
    (fromRows A B).IsTotallyUnimodular := by
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    by_cases hfr : ∃ i : Fin (k + 1), (f i).isRight
    · simp only [Sum.isRight_iff] at hfr
      obtain ⟨i, j, hfi⟩ := hfr
      have hAB := det_succ_row ((fromRows A B).submatrix f g) i
      simp only [submatrix_apply, hfi, fromRows_apply_inr] at hAB
      obtain (hj | ⟨j', hj'⟩) := hB j
      · use 0
        simpa [hj] using hAB.symm
      · simp only [hj', Function.update_apply] at hAB
        by_cases hj'' : ∃ x, g x = j'
        · obtain ⟨x, rfl⟩ := hj''
          have hAB' :
            ((fromRows A B).submatrix f g).det =
            (-1) ^ (i.val + x.val) *
              ((fromRows A B).submatrix (f ∘ i.succAbove) (g ∘ x.succAbove)).det := by
            simpa [hg.eq_iff] using hAB
          rw [hAB']
          apply neg_one_pow_mem_signType_range
          exact ih _ _
            (hf.comp Fin.succAbove_right_injective)
            (hg.comp Fin.succAbove_right_injective)
        · rw [not_exists] at hj''
          use 0
          simpa [hj''] using hAB.symm
    · simp only [not_exists, Bool.not_eq_true, Sum.isRight_eq_false, Sum.isLeft_iff] at hfr
      choose f' hf' using hfr
      rw [isTotallyUnimodular_iff] at hA
      rw [funext hf']
      apply hA

/-- If `A` is totally unimodular and each row of `B` is all zeros except for at most a single `1`,
then `fromRows A B` is totally unimodular. -/
lemma fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : ∀ i : m', B i = 0 ∨ ∃ j, B i = Function.update (0 : n → R) j 1) :
    (fromRows A B).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨.submatrix Sum.inl id, .fromRows_one_aux hB⟩

lemma fromRows_one_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows A (1 : Matrix n n R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  fromRows_isTotallyUnimodular_iff_rows <| fun i ↦ Or.inr
    ⟨i, funext fun j ↦ by simp [one_apply, Function.update_apply, eq_comm]⟩

lemma one_fromRows_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows (1 : Matrix n n R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  have hA :
    fromRows (1 : Matrix n n R) A =
      Matrix.reindex (Equiv.sumComm m n) (Equiv.refl n) (fromRows A (1 : Matrix n n R)) := by
    aesop
  rw [hA, reindex_isTotallyUnimodular]
  exact fromRows_one_isTotallyUnimodular_iff A

lemma fromColumns_one_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromColumns A (1 : Matrix m m R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [←transpose_isTotallyUnimodular_iff, transpose_fromColumns, transpose_one,
    fromRows_one_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

lemma one_fromColumns_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromColumns (1 : Matrix m m R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [←transpose_isTotallyUnimodular_iff, transpose_fromColumns, transpose_one,
    one_fromRows_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromRows⟩ := one_fromRows_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.fromColumns_one⟩ := fromColumns_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromColumns⟩ := one_fromColumns_isTotallyUnimodular_iff

lemma fromRows_row0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromRows A (row m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  classical
  apply fromRows_isTotallyUnimodular_iff_rows
  aesop

lemma fromColumns_col0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromColumns A (col n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromColumns, transpose_col,
    fromRows_row0_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

end Matrix
