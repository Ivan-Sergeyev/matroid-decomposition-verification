import Mathlib.Data.Matroid.Dual
import Seymour.SetTheory
import Seymour.MatroidCircuit
import Seymour.ForMathlib.CircuitMatroid
import Seymour.MatroidConnectivity


section MatroidTwoSum

/-- todo: desc -/
structure Matroid.TwoSum.Assumptions {α : Type*} (M₁ M₂ : Matroid α) (p : α) where
  /-- `M₁` and `M₂` are finite -/
  hM₁fin : M₁.Finite
  hM₂fin : M₂.Finite
  /-- `M₁` and `M₂` contain at least 2 elements -/
  hM₁card : M₁.E.encard ≥ 2
  hM₂card : M₂.E.encard ≥ 2
  /-- `M₁` and `M₂` have exactly `a` in common -/
  hp : M₁.E ∩ M₂.E = {p}
  -- /-- `M₁` and `M₂`  -/
  hpM₁ : ¬M₁.Separator {p}
  hpM₂ : ¬M₂.Separator {p}

/-- todo: desc -/
def Matroid.TwoSum.Assumptions_symm {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) :
    Matroid.TwoSum.Assumptions M₂ M₁ p :=
  ⟨
    Assumptions.hM₂fin,
    Assumptions.hM₁fin,
    Assumptions.hM₂card,
    Assumptions.hM₁card,
    by
      have hp := Assumptions.hp
      rw [Set.inter_comm] at hp
      exact hp,
    Assumptions.hpM₂,
    Assumptions.hpM₁
  ⟩

/-- todo: desc -/
def Matroid.TwoSum.E {α : Type*} (M₁ M₂ : Matroid α) (p : α) :=
  (M₁.E ∪ M₂.E) \ {p}

/-- todo: desc -/
lemma Matroid.TwoSum.pnotinE {α : Type*}
    (M₁ M₂ : Matroid α) (p : α) : p ∉ Matroid.TwoSum.E M₁ M₂ p :=
  Set.not_mem_diff_of_mem rfl

/-- todo: desc -/
lemma Matroid.TwoSum.DisjM₁M₂Emp {α : Type*} (M₁ M₂ : Matroid α) (p : α)
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : Disjoint (M₁.E \ {p}) (M₂.E \ {p}) :=
  disjoint_of_singleton_intersection_both_wo Assumptions.hp

/-- todo: desc -/
lemma Matroid.TwoSum.pinM₁ {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : p ∈ M₁.E :=
  Set.mem_of_mem_inter_left (Eq.subset Assumptions.hp.symm rfl)

/-- todo: desc -/
lemma Matroid.TwoSum.pinM₂ {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : p ∈ M₂.E :=
  Set.mem_of_mem_inter_right (Eq.subset Assumptions.hp.symm rfl)

/-- todo: desc -/
lemma Matroid.TwoSum.pNotLoopOrColoopM₁ {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : ¬M₁.Loop p ∧ ¬M₁.Coloop p := by
  have hp : ¬(p ∈ M₁.E ∧ M₁.Separator {p}) := not_and.mpr fun _ => Assumptions.hpM₁
  rw [Matroid.Separator.SingletonIff p] at hp
  exact not_or.mp hp

/-- todo: desc -/
lemma Matroid.TwoSum.pNotLoopOrColoopM₂ {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : ¬M₂.Loop p ∧ ¬M₂.Coloop p := by
  have hp : ¬(p ∈ M₂.E ∧ M₂.Separator {p}) := not_and.mpr fun _ => Assumptions.hpM₂
  rw [Matroid.Separator.SingletonIff p] at hp
  exact not_or.mp hp

/-- todo: desc -/
def Matroid.TwoSum.CircuitPred {α : Type*} (M₁ M₂ : Matroid α) (p : α) : Set α → Prop :=
  fun C =>
  -- C(M₁ - p)
  (p ∉ C ∧ M₁.Circuit C) ∨
  -- C(M₂ - p)
  (p ∉ C ∧ M₂.Circuit C) ∨
  -- {(C₁ ∪ C₂) - p : p ∈ C₁ ∈ C(M₁), p ∈ C₂ ∈ C(M₂)}
  (C ⊆ (M₁.E ∪ M₂.E) \ {p} ∧ M₁.Circuit ((C ∩ M₁.E) ∪ {p}) ∧ M₂.Circuit ((C ∩ M₂.E) ∪ {p}))

/-- todo: desc -/
lemma Matroid.TwoSum.NotCircuitEmpty {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : ¬(Matroid.TwoSum.CircuitPred M₁ M₂ p) ∅ := by
  unfold Matroid.TwoSum.CircuitPred
  simp
  constructor
  · exact Matroid.Circuit.NotCircuitEmpty M₁
  · constructor
    · exact Matroid.Circuit.NotCircuitEmpty M₂
    · by_contra hpM₁M₂
      push_neg at hpM₁M₂
      obtain ⟨hpM₁, hpM₂⟩ := hpM₁M₂
      rw [←Loop.IffCircuit M₁] at hpM₁
      apply Separator.Loop at hpM₁
      have hpM₁' := Assumptions.hpM₁
      tauto

/-- todo: desc -/
lemma Matroid.TwoSum.disjoint_CircuitM₁mp_CircuitM₂mp {α : Type*} {M₁ M₂ : Matroid α} {p : α} {C₁ C₂ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) (hC₁ : p ∉ C₁ ∧ M₁.Circuit C₁) (hC₂ : p ∉ C₂ ∧ M₂.Circuit C₂) :
    Disjoint C₁ C₂ := by
  have hC₁M₁mp : C₁ ⊆ M₁.E \ {p} := Set.subset_diff_singleton hC₁.2.1 hC₁.1
  have hC₂M₂mp : C₂ ⊆ M₂.E \ {p} := Set.subset_diff_singleton hC₂.2.1 hC₂.1
  have hM₁M₂ : Disjoint (M₁.E \ {p}) (M₂.E \ {p}) := DisjM₁M₂Emp M₁ M₂ p Assumptions
  exact Set.disjoint_of_subset hC₁M₁mp hC₂M₂mp hM₁M₂

/-- todo: desc -/
lemma Matroid.TwoSum.CircuitM₁mp_inter_M₂_empty {α : Type*} {M₁ M₂ : Matroid α} {p : α} {C₁ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) (hC₁ : p ∉ C₁ ∧ M₁.Circuit C₁) : C₁ ∩ M₂.E = ∅ := by
  have hM₁M₂ : Disjoint (M₁.E \ {p}) (M₂.E \ {p}) := DisjM₁M₂Emp M₁ M₂ p Assumptions
  have hC₁M₁mp : C₁ ⊆ M₁.E \ {p} := Set.subset_diff_singleton hC₁.2.1 hC₁.1
  have hC₁p : Disjoint C₁ {p} := Set.disjoint_singleton_right.mpr hC₁.1
  have hC₁M₂mp : Disjoint C₁ (M₂.E \ {p}) := Set.disjoint_of_subset hC₁M₁mp (fun ⦃a⦄ a => a) hM₁M₂
  have hC₁M₂ : Disjoint C₁ ((M₂.E \ {p}) ∪ {p}) := Disjoint.union_right hC₁M₂mp hC₁p
  rw [Set.diff_union_of_subset] at hC₁M₂
  exact Disjoint.inter_eq hC₁M₂
  exact Set.singleton_subset_iff.mpr (pinM₂ Assumptions)

/-- todo: desc -/
lemma Matroid.TwoSum.CircuitM₂mp_inter_M₁_empty {α : Type*} {M₁ M₂ : Matroid α} {p : α} {C₂ : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) (hC₂ : p ∉ C₂ ∧ M₂.Circuit C₂) : C₂ ∩ M₁.E = ∅ := by
  have hM₂M₁ : Disjoint (M₁.E \ {p}) (M₂.E \ {p}) := DisjM₁M₂Emp M₁ M₂ p Assumptions
  have hC₂M₂mp : C₂ ⊆ M₂.E \ {p} := Set.subset_diff_singleton hC₂.2.1 hC₂.1
  have hC₂p : Disjoint C₂ {p} := Set.disjoint_singleton_right.mpr hC₂.1
  have hC₂M₁mp : Disjoint C₂ (M₁.E \ {p}) := Set.disjoint_of_subset hC₂M₂mp (fun ⦃a⦄ a => a) hM₂M₁.symm
  have hC₂M₁ : Disjoint C₂ ((M₁.E \ {p}) ∪ {p}) := Disjoint.union_right hC₂M₁mp hC₂p
  rw [Set.diff_union_of_subset] at hC₂M₁
  exact Disjoint.inter_eq hC₂M₁
  exact Set.singleton_subset_iff.mpr (pinM₁ Assumptions)

/-- todo: desc -/
lemma Matroid.TwoSum.CircuitType3_inter_M₁_Nonempty {α : Type*} {M₁ M₂ : Matroid α} {p : α} {C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p)
    (hC : C ⊆ (M₁.E ∪ M₂.E) \ {p} ∧ M₁.Circuit (C ∩ M₁.E ∪ {p}) ∧ M₂.Circuit (C ∩ M₂.E ∪ {p})) : (C ∩ M₁.E).Nonempty := by
  by_contra hCM₁empty
  push_neg at hCM₁empty
  have hCM₁circ := hC.2.1
  rw [hCM₁empty, Set.empty_union, ←Matroid.Loop.IffCircuit] at hCM₁circ
  have hpM₁ := Matroid.TwoSum.pNotLoopOrColoopM₁ Assumptions
  tauto

/-- todo: desc -/
lemma Matroid.TwoSum.CircuitType3_inter_M₂_Nonempty {α : Type*} {M₁ M₂ : Matroid α} {p : α} {C : Set α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p)
    (hC : C ⊆ (M₁.E ∪ M₂.E) \ {p} ∧ M₁.Circuit (C ∩ M₁.E ∪ {p}) ∧ M₂.Circuit (C ∩ M₂.E ∪ {p})) : (C ∩ M₂.E).Nonempty := by
  by_contra hCM₂empty
  push_neg at hCM₂empty
  have hCM₁circ := hC.2.2
  rw [hCM₂empty, Set.empty_union, ←Matroid.Loop.IffCircuit] at hCM₁circ
  have hpM₁ := Matroid.TwoSum.pNotLoopOrColoopM₂ Assumptions
  tauto

/-- todo: desc -/
lemma Matroid.TwoSum.CircuitNotSubsetCircuit {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) :
    ∀ ⦃C₁ C₂ : Set α⦄, CircuitPred M₁ M₂ p C₁ → CircuitPred M₁ M₂ p C₂ → ¬C₂ ⊂ C₁ := by
  intro C₁ C₂ hC₁ hC₂
  unfold CircuitPred at hC₁ hC₂
  cases hC₂ with
  | inl hC₂ => cases hC₁ with
    | inl hC₁ => exact Circuit.CircuitNotSsubsetCircuit hC₁.2 hC₂.2
    | inr hC₁ => cases hC₁ with
      | inl hC₁ =>
        have hC₁C₂ : Disjoint C₁ C₂ := (disjoint_CircuitM₁mp_CircuitM₂mp Assumptions hC₂ hC₁).symm
        have hC₂ne : C₂.Nonempty := Circuit.Nonempty M₁ hC₂.2
        exact disjoint_nonempty_not_ssubset (Disjoint.symm hC₁C₂) hC₂ne
      | inr hC₁ =>
        by_contra hC₂C₁
        obtain ⟨hC₂C₁, _hnC₁C₂⟩ := hC₂C₁
        apply Matroid.Circuit.CircuitNotSsubsetCircuit hC₁.2.1 hC₂.2

        have hC₂inter : C₂ ⊆ C₁ ∩ M₁.E := Set.subset_inter hC₂C₁ hC₂.2.1
        have hC₂p : C₂ ∪ {p} ⊆ C₁ ∩ M₁.E ∪ {p} := Set.union_subset_union_left {p} hC₂inter
        have hC₂ssubC₂p : C₂ ⊂ C₂ ∪ {p} := ssubset_union_self_elem_notin hC₂.1
        exact Set.ssubset_of_ssubset_of_subset hC₂ssubC₂p hC₂p
  | inr hC₂ => cases hC₂ with
    | inl hC₂ => cases hC₁ with
      | inl hC₁ =>
          have hC₁C₂ : Disjoint C₁ C₂ := disjoint_CircuitM₁mp_CircuitM₂mp Assumptions hC₁ hC₂
          have hC₂ne : C₂.Nonempty := Circuit.Nonempty M₂ hC₂.2
          exact disjoint_nonempty_not_ssubset (id (Disjoint.symm hC₁C₂)) hC₂ne
      | inr hC₁ => cases hC₁ with
        | inl hC₁ => exact Circuit.CircuitNotSsubsetCircuit hC₁.2 hC₂.2
        | inr hC₁ =>
          by_contra hC₂C₁
          obtain ⟨hC₂C₁, _hnC₁C₂⟩ := hC₂C₁
          apply Matroid.Circuit.CircuitNotSsubsetCircuit hC₁.2.2 hC₂.2

          have hC₂inter : C₂ ⊆ C₁ ∩ M₂.E := Set.subset_inter hC₂C₁ hC₂.2.1
          have hC₂p : C₂ ∪ {p} ⊆ C₁ ∩ M₂.E ∪ {p} := Set.union_subset_union_left {p} hC₂inter
          have hC₂ssubC₂p : C₂ ⊂ C₂ ∪ {p} := ssubset_union_self_elem_notin hC₂.1
          exact Set.ssubset_of_ssubset_of_subset hC₂ssubC₂p hC₂p
    | inr hC₂ =>
      cases hC₁ with
      | inl hC₁ =>
        have hC₂M₂nempty : (C₂ ∩ M₂.E).Nonempty := CircuitType3_inter_M₂_Nonempty Assumptions hC₂
        have hC₁M₂empty : C₁ ∩ M₂.E = ∅ := CircuitM₁mp_inter_M₂_empty Assumptions hC₁
        exact disjoint_inter_nonempty_inter_empty hC₂M₂nempty hC₁M₂empty
      | inr hC₁ => cases hC₁ with
        | inl hC₁ =>
          have hC₂M₂nempty : (C₂ ∩ M₁.E).Nonempty := CircuitType3_inter_M₁_Nonempty Assumptions hC₂
          have hC₁M₁empty : C₁ ∩ M₁.E = ∅ := CircuitM₂mp_inter_M₁_empty Assumptions hC₁
          exact disjoint_inter_nonempty_inter_empty hC₂M₂nempty hC₁M₁empty
        | inr hC₁ =>
            have hpC₁ : p ∉ C₁ := fun a => (elem_notin_set_minus_singleton p (M₁.E ∪ M₂.E)) (hC₁.1 a)
            have hpC₁M₁ : p ∉ C₁ ∩ M₁.E := by
              by_contra hp
              exact hpC₁ (Set.mem_of_mem_inter_left hp)
            have hpC₁M₂ : p ∉ C₁ ∩ M₂.E := by
              by_contra hp
              exact hpC₁ (Set.mem_of_mem_inter_left hp)

            have hpC₂ : p ∉ C₂ := fun a => (elem_notin_set_minus_singleton p (M₁.E ∪ M₂.E)) (hC₂.1 a)
            have hpC₂M₁ : p ∉ C₂ ∩ M₁.E := by
              by_contra hp
              exact hpC₂ (Set.mem_of_mem_inter_left hp)
            have hpC₂M₂ : p ∉ C₂ ∩ M₂.E := by
              by_contra hp
              exact hpC₂ (Set.mem_of_mem_inter_left hp)

            have hnC₂C₁M₁ := Circuit.CircuitNotSsubsetCircuit hC₁.2.1 hC₂.2.1
            have hnC₂C₁M₂ := Circuit.CircuitNotSsubsetCircuit hC₁.2.2 hC₂.2.2

            rw [union_ssubset_union_iff hpC₂M₁ hpC₁M₁] at hnC₂C₁M₁
            rw [union_ssubset_union_iff hpC₂M₂ hpC₁M₂] at hnC₂C₁M₂

            by_contra hC₂C₁
            obtain ⟨hC₂C₁, hnC₁C₂⟩ := hC₂C₁

            have hC₂C₁M₁ : C₂ ∩ M₁.E ⊆ C₁ ∩ M₁.E := Set.inter_subset_inter hC₂C₁ fun ⦃a⦄ a => a
            rw [Set.ssubset_def] at hnC₂C₁M₁
            push_neg at hnC₂C₁M₁
            specialize hnC₂C₁M₁ hC₂C₁M₁
            have hC₂C₁M₁eq : C₂ ∩ M₁.E = C₁ ∩ M₁.E := Set.Subset.antisymm hC₂C₁M₁ hnC₂C₁M₁

            have hC₂C₁M₂ : C₂ ∩ M₂.E ⊆ C₁ ∩ M₂.E := Set.inter_subset_inter hC₂C₁ fun ⦃a⦄ a => a
            rw [Set.ssubset_def] at hnC₂C₁M₂
            push_neg at hnC₂C₁M₂
            specialize hnC₂C₁M₂ hC₂C₁M₂
            have hC₂C₁M₂eq : C₂ ∩ M₂.E = C₁ ∩ M₂.E := Set.Subset.antisymm hC₂C₁M₂ hnC₂C₁M₂

            simp_all

            have hC₁sub : C₁ ⊆ M₁.E ∪ M₂.E := sub_union_diff_sub_union hC₁
            have hC₁eq : C₁ = (C₁ ∩ M₁.E) ∪ (C₁ ∩ M₂.E) := Eq.symm (sub_parts_eq hC₁sub)
            have hC₂sub : C₂ ⊆ M₁.E ∪ M₂.E := sub_union_diff_sub_union hC₂.1
            have hC₂eq : C₂ = (C₂ ∩ M₁.E) ∪ (C₂ ∩ M₂.E) := Eq.symm (sub_parts_eq hC₂sub)
            rw [hC₂C₁M₁eq, hC₂C₁M₂eq, ←hC₁eq] at hC₂eq

            have hC₁C₂ : C₁ ⊆ C₂ := Eq.subset hC₂eq.symm
            tauto


/-- todo: desc -/
lemma Matroid.TwoSum.CircuitGround {α : Type*} (M₁ M₂ : Matroid α) (p : α) :
    ∀ (C : Set α), CircuitPred M₁ M₂ p C → C ⊆ E M₁ M₂ p := by
  intro C hC
  unfold CircuitPred at hC
  unfold E
  cases hC with
  | inl hC =>
      obtain ⟨hpC, ⟨hCE, _⟩⟩ := hC
      rw [Set.union_diff_distrib]
      exact Set.subset_union_of_subset_left (Set.subset_diff_singleton hCE hpC) (M₂.E \ {p})
  | inr hC => cases hC with
    | inl hC =>
        obtain ⟨hpC, ⟨hCE, _⟩⟩ := hC
        rw [Set.union_diff_distrib]
        exact Set.subset_union_of_subset_right (Set.subset_diff_singleton hCE hpC) (M₁.E \ {p})
    | inr hC => exact hC.1

def Matroid.TwoSum.CircuitMatroid {α : Type*} {M₁ M₂ : Matroid α} {p : α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁ M₂ p) : CircuitMatroid α :=
  ⟨
    Matroid.TwoSum.E M₁ M₂ p,
    Matroid.TwoSum.CircuitPred M₁ M₂ p,
    Matroid.TwoSum.NotCircuitEmpty Assumptions,
    Matroid.TwoSum.CircuitNotSubsetCircuit Assumptions,
    sorry, -- todo: should simplify in finite case
    sorry, -- todo: should simplify in finite case
    Matroid.TwoSum.CircuitGround M₁ M₂ p
  ⟩

-- todo: different definitions of 2-sum are equivalent
