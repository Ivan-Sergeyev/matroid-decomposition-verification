import Mathlib.Tactic

-- Probably will be thrown away:
lemma todo {α β₁ β₂ : Type*} (f : α → β₁ ⊕ β₂) :
    ∃ α₁ α₂ : Type, ∃ e : α ≃ α₁ ⊕ α₂, ∃ f₁ : α₁ → β₁, ∃ f₂ : α₂ → β₂,
      f = (fun i => (Sum.elim (Sum.inl ∘ f₁) (Sum.inr ∘ f₂)) (e i)) := by
  sorry

lemma Function.toSumElimComp {α β₁ β₂ : Type*} (f : α → β₁ ⊕ β₂) :
    f =
    (fun a : α =>
      Sum.elim
        (Sum.inl ∘ ((·.val.snd) : { x₁ : α × β₁ // f x₁.fst = Sum.inl x₁.snd } → β₁))
        (Sum.inr ∘ ((·.val.snd) : { x₂ : α × β₂ // f x₂.fst = Sum.inr x₂.snd } → β₂))
      (match hfa : f a with
        | .inl b₁ => Sum.inl ⟨(a, b₁), hfa⟩
        | .inr b₂ => Sum.inr ⟨(a, b₂), hfa⟩
      )
    ) := by
  aesop

lemma zom_mul_zom {R : Type*} [Ring R] {x y : R}
    (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1) :
    x*y = 0 ∨ x*y = 1 ∨ x*y = -1 := by
  aesop
