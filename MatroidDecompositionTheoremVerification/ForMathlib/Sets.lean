import Mathlib

variable {α : Type*} {X Y : Set α}

lemma disjoint_left_wo (hXY : Disjoint X Y) (x : α) : Disjoint (X \ {x}) Y := by
  sorry

lemma disjoint_right_wo (hXY : Disjoint X Y) (y : α) : Disjoint X (Y \ {y}) := by
  sorry

lemma disjoint_of_singleton_intersection_left_wo {a : α} (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) Y := by
  sorry

lemma disjoint_of_singleton_intersection_right_wo {a : α} (hXY : X ∩ Y = {a}) : Disjoint X (Y \ {a}) := by
  sorry

lemma disjoint_of_singleton_intersection_both_wo {a : α} (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) (Y \ {a}) :=
  disjoint_left_wo (disjoint_of_singleton_intersection_right_wo hXY) a
