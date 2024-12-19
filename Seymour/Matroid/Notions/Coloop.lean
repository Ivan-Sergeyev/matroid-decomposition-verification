import Mathlib.Data.Matroid.Dual
import Seymour.Matroid.Notions.Loop


/-- Coloop is a loop in the dual matroid. -/
def Matroid.Coloop {α : Type*} (M : Matroid α) (a : α) : Prop :=
  M.dual.Loop a

/-- An element is a coloop iff it belongs to no circuit. -/
lemma Matroid.Coloop.IffInNoCircuit {α : Type*} (M : Matroid α) {a : α} :
    M.Coloop a ↔ a ∈ M.E ∧ ∀ C, M.Circuit C → a ∉ C := by
  constructor
  · intro ha
    obtain ⟨haE, hanIndep⟩ := ha
    unfold Matroid.dual Matroid.dualIndepMatroid at hanIndep
    simp at haE
    simp at hanIndep
    constructor
    · exact haE
    · intro C hC
      apply hanIndep at haE
      by_contra haC
      have hCmaIndep : M.Indep (C \ {a}) := Matroid.Circuit.DelSingleIndep hC haC
      apply Matroid.Indep.exists_base_superset at hCmaIndep
      obtain ⟨B, hBbase, hCmaB⟩ := hCmaIndep
      specialize haE B hBbase

      rw [←Set.singleton_subset_iff] at haE
      rw [←Set.singleton_subset_iff] at haC
      apply Set.union_subset_union_left {a} at hCmaB
      rw [Set.diff_union_of_subset haC, Set.union_eq_self_of_subset_right haE] at hCmaB

      apply Matroid.Indep.subset (Base.indep hBbase) at hCmaB
      apply Matroid.Circuit.NotIndep M at hC
      tauto
  · intro ha
    obtain ⟨haE, haC⟩ := ha
    unfold Coloop Matroid.dual Matroid.dualIndepMatroid Loop
    simp
    constructor
    · exact haE
    · intro haE' B hB
      by_contra haB
      have hBIndep : M.Indep B := Base.indep hB
      have hBinsanIndep : ¬M.Indep (insert a B) := by
        have hBins : B ⊂ insert a B := Set.ssubset_insert haB
        apply Matroid.Base.dep_of_ssubset hB at hBins
        unfold Dep at hBins
        tauto
      have hBanIndep : ¬M.Indep (B ∪ {a}) := Eq.mpr_not (congrArg M.Indep Set.union_singleton) hBinsanIndep
      have hC : ∃ C, a ∈ C ∧ C ⊆ B ∪ {a} ∧ M.Circuit C := Matroid.Circuit.IndepExtDepHasCircuit hBIndep haE hBanIndep
      obtain ⟨C, hCBa, _hCIndep, hCCirc⟩ := hC
      specialize haC C hCCirc
      tauto
