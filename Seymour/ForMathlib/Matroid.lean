import Mathlib.Data.Matroid.Sum


lemma Matroid.disjointSum_comm {α : Type*} {M N : Matroid α} (hMN : Disjoint M.E N.E) :
    Matroid.disjointSum M N hMN = Matroid.disjointSum N M hMN.symm := by
  sorry
