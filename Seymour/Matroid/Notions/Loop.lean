import Mathlib.Data.Matroid.Basic
import Seymour.Matroid.Notions.Circuit


/-- Loop is an element of the ground set that is not independent when viewed as a singleton set. -/
def Matroid.Loop {α : Type*} (M : Matroid α) (a : α) : Prop :=
  a ∈ M.E ∧ ¬M.Indep {a}

/-- An element is a loop iff its singleton set is a circuit. -/
lemma Matroid.Loop.IffCircuit {α : Type*} (M : Matroid α) {a : α} :
    M.Loop a ↔ M.Circuit {a} := by
  constructor
  · intro ha
    exact ⟨
      Set.singleton_subset_iff.mpr ha.1,
      ha.2,
      by
        intro C' hC'
        rw [Set.ssubset_singleton_iff.mp hC']
        exact M.empty_indep
    ⟩
  · intro ha
    exact ⟨ha.1 rfl, Circuit.NotIndep M ha⟩
