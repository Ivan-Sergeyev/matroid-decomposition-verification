import Mathlib.Tactic

lemma todo {α β₁ β₂ : Type*} (f : α → β₁ ⊕ β₂) :
    ∃ α₁ α₂ : Type, ∃ e : α ≃ α₁ ⊕ α₂, ∃ f₁ : α₁ → β₁, ∃ f₂ : α₂ → β₂,
      f = (fun i => (Sum.elim (Sum.inl ∘ f₁) (Sum.inr ∘ f₂)) (e i)) := by
  sorry

lemma zom_mul_zom {R : Type*} [Ring R] {x y : R}
    (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1) :
    x*y = 0 ∨ x*y = 1 ∨ x*y = -1 := by
  aesop
