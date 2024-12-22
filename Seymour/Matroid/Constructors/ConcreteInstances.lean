import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Classes.IsRegular

-- TODO: specific instances of matroids
def MatroidR10 : BinaryMatroid (Fin 10) where
  X := {1, 2, 3, 4, 5}
  Y := {6, 7, 8, 9, 10}
  decmemX := sorry
  decmemY := sorry
  hXY := sorry
  -- B10 = [
  --   1 0 0 1 1
  --   1 1 0 0 1
  --   0 1 1 0 1
  --   0 0 1 1 1
  --   1 1 1 1 1
  -- ]
  B := sorry

-- todo: lemma MatroidR10.IsRegular
