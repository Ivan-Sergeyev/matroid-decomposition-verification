import Mathlib.Data.Matroid.Basic


/-- Independence predicate, defines which sets are circuits. -/
abbrev IndepPredicate (α : Type*) := Set α → Prop


section IndepAxioms

/-- Axiom (I1): empty set is independent. -/
def IndepPredicate.indep_empty {α : Type*} (P : IndepPredicate α) : Prop := P ∅
alias IndepPredicate.axiom_i1 := IndepPredicate.indep_empty

/-- Axiom (I2): subset of independent set is independent. -/
def IndepPredicate.indep_subset {α : Type*} (P : IndepPredicate α) : Prop := ∀ I J, P J → I ⊆ J → P I
alias IndepPredicate.axiom_i2 := IndepPredicate.indep_subset

/-- Axiom (I3): augmentation property. -/
def IndepPredicate.indep_aug {α : Type*} (P : IndepPredicate α) : Prop :=
  ∀ I B, P I → ¬Maximal P I → Maximal P B → ∃ x ∈ B \ I, P (insert x I)
alias IndepPredicate.axiom_i3 := IndepPredicate.indep_aug

/-- Axiom (IM): set of all independent sets has the maximal subset property. -/
def IndepPredicate.indep_maximal {α : Type*} (P : IndepPredicate α) (E : Set α) : Prop :=
  ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty P X
alias IndepPredicate.axiom_im := IndepPredicate.indep_maximal

/-- Every independent set is a subset of the ground set. -/
def IndepPredicate.subset_ground {α : Type*} (P : IndepPredicate α) (E : Set α) : Prop := ∀ C, P C → C ⊆ E
alias IndepPredicate.axiom_ce := IndepPredicate.subset_ground


section MatroidIndepAxioms

/-- Independence predicate of matroid satisfies (I1): empty set is independent. -/
lemma Matroid.indep_empty {α : Type*} (M : Matroid α) :
    IndepPredicate.indep_empty M.Indep :=
  M.empty_indep

/-- Independence predicate of matroid satisfies (I2): subset of independent set is independent. -/
lemma Matroid.indep_subset {α : Type*} (M : Matroid α) :
    IndepPredicate.indep_subset M.Indep :=
  fun _ _ => Matroid.Indep.subset

/-- Independence predicate of matroid satisfies (I3): augmentation property. -/
lemma Matroid.indep_aug {α : Type*} (M : Matroid α) :
    IndepPredicate.indep_aug M.Indep :=
  fun _ _ hI hInmax hI'max => Indep.exists_insert_of_not_maximal M hI hInmax hI'max

lemma subset_diff_empty_eq {α : Type*} {A B : Set α} (hAB : A ⊆ B) (hBdiffA : B \ A = ∅) : A = B :=
  Set.union_empty A ▸ hBdiffA ▸ Set.union_diff_cancel hAB

/-- (Alternative proof.) Independence predicate of matroid satisfies (I3): augmentation property. -/
lemma Matroid.indep_aug_alt {α : Type*} (M : Matroid α) :
    IndepPredicate.indep_aug M.Indep := by
  -- Follows part of proof from Theorem 4.1 (i) from Bruhn et al.
  intro I I' hI hInmax hI'max
  let ⟨B, hIB, hBmax⟩ := M.maximality M.E Set.Subset.rfl I hI (Matroid.Indep.subset_ground hI)
  if hBdiffI: (B \ I).Nonempty then
    obtain ⟨x, hx⟩ := hBdiffI
    if hxI' : x ∈ I' then
      use x
      exact ⟨
        Set.mem_diff_of_mem hxI' (Set.not_mem_of_mem_diff hx),
        Matroid.Indep.subset hBmax.1.1 (Set.insert_subset (Set.mem_of_mem_diff hx) hIB),
      ⟩
    else
      let hB : Maximal M.Indep B := ⟨hBmax.1.1, fun C hC hBC => hBmax.2 ⟨hC, Matroid.Indep.subset_ground hC⟩ hBC⟩
      rw [←Matroid.base_iff_maximal_indep] at hI'max hB
      obtain ⟨y, hy, hybase⟩ := M.base_exchange B I' hB hI'max x (Set.mem_diff_of_mem (Set.mem_of_mem_diff hx) hxI')
      use y
      exact ⟨
        Set.mem_diff_of_mem (Set.mem_of_mem_diff hy) (fun a => (Set.not_mem_of_mem_diff hy) (hIB a)),
        Matroid.Indep.subset (Matroid.Base.indep hybase)
          (Set.insert_subset_insert (Set.subset_diff_singleton hIB (Set.not_mem_of_mem_diff hx))),
      ⟩
  else
    let hIeqB : I = B := Set.union_empty I ▸ (Set.not_nonempty_iff_eq_empty.mp hBdiffI) ▸ Set.union_diff_cancel hIB
    let hBmax : Maximal M.Indep B := ⟨hBmax.1.1, fun _ hC hBC => hBmax.2 ⟨hC, Matroid.Indep.subset_ground hC⟩ hBC⟩
    exact False.elim (hInmax (hIeqB ▸ hBmax))

/-- Independence predicate of matroid satisfies (IM): set of all independent sets has the maximal subset property. -/
lemma Matroid.indep_maximal {α : Type*} (M : Matroid α) :
    IndepPredicate.indep_maximal M.Indep M.E :=
  M.maximality

/-- Every independent set is a subset of the ground set. -/
lemma Matroid.indep_subset_ground {α : Type*} (M : Matroid α) :
    IndepPredicate.subset_ground M.Indep M.E :=
  fun _ => Matroid.Indep.subset_ground
