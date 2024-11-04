import Mathlib

variable {α : Type*} {X Y : Set α}

lemma disjoint_left_setminus (hXY : Disjoint X Y) (Z : Set α) : Disjoint (X \ Z) Y :=
  Set.disjoint_of_subset Set.diff_subset (by rfl) hXY

lemma disjoint_right_setminus (hXY : Disjoint X Y) (Z : Set α) : Disjoint X (Y \ Z) :=
  Set.disjoint_of_subset (by rfl) Set.diff_subset hXY

lemma disjoint_of_singleton_intersection_left_wo {a : α} (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) Y := by
  rw [Set.disjoint_iff_forall_ne]
  intro u huXa v hvY huv
  have hua : u ≠ a
  · aesop
  have huX : u ∈ X
  · aesop
  have huXY := Set.mem_inter huX (huv ▸ hvY)
  rw [hXY, Set.mem_singleton_iff] at huXY
  exact hua huXY

lemma disjoint_of_singleton_intersection_right_wo {a : α} (hXY : X ∩ Y = {a}) : Disjoint X (Y \ {a}) := by
  rw [disjoint_comm]
  rw [Set.inter_comm] at hXY
  exact disjoint_of_singleton_intersection_left_wo hXY

lemma disjoint_of_singleton_intersection_both_wo {a : α} (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) (Y \ {a}) :=
  disjoint_left_setminus (disjoint_of_singleton_intersection_right_wo hXY) {a}
