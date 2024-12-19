import Mathlib.Data.Matroid.Sum


lemma disjointSum_comm {α : Type*} {M N : Matroid α} (hMN : Disjoint M.E N.E) :
    M.disjointSum N hMN = N.disjointSum M hMN.symm := by
  ext
  · simp [Set.union_comm]
  repeat simpa [Set.union_comm] using ⟨fun ⟨m, n, h⟩ ↦ ⟨n, m, M.E.union_comm N.E ▸ h⟩,
    fun ⟨n, m, h⟩ ↦ ⟨m, n, M.E.union_comm N.E ▸ h⟩⟩
