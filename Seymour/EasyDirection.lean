import Mathlib.Data.Matroid.Map

import Seymour.Matroid.Classes.IsRegular
import Seymour.Matroid.Classes.IsGraphic
import Seymour.Matroid.Classes.IsCographic
import Seymour.Matroid.Constructors.ConcreteInstances
import Seymour.Matroid.Operations.SumDelta

/-!
This file states the "easy" (composition) direction of the Seymour decomposition theorem.
-/

theorem easySeymour.Sum1 {α : Type*} [DecidableEq α] {M₁ M₂ M : BinaryMatroid α}
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (hM₁M₂ : Disjoint M₁.E M₂.E)
    (hM : M.matroid = Matroid.disjointSum M₁.matroid M₂.matroid hM₁M₂) : M.IsRegular := by
  sorry

theorem easySeymour.Sum2 {α : Type*} [DecidableEq α] {M₁ M₂ M : BinaryMatroid α} {p : α}
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p)
    (hM : M.matroid = Matroid.TwoSum.matroid Assumptions) : M.IsRegular := by
  sorry

theorem easySeymour.Sum3 {α : Type*} [DecidableEq α] {M₁ M₂ M : BinaryMatroid α}
    (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (Assumptions : DeltaSum.ThreeSumAssumptions M₁ M₂)
    (hM : M.matroid = DeltaSum.matroid M₁ M₂) : M.IsRegular := by
  sorry
