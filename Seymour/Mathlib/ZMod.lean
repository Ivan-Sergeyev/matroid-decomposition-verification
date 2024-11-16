import Mathlib.Data.ZMod.Defs

private lemma Fin2_eq_1_of_ne_0 {a : Fin 2} (ha : a ≠ 0) : a = 1 := by
  omega

lemma Z2_eq_1_of_ne_0 {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  Fin2_eq_1_of_ne_0 ha
