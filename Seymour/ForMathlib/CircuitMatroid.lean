import Mathlib.Data.Matroid.IndepAxioms
import Seymour.Basic

variable {α : Type*}

section CircuitMatroid

/-- Independence predicate derived from circuit predicate `P`. -/
def CircPredToIndep (P : Set α → Prop) (E I : Set α) : Prop :=
  I ⊆ E ∧ ∀ C : Set α, P C → ¬(C ⊆ I) -- independent sets are all non-circuits

/-- Family of circuits satisfying assumptions of circuit condition (C3) from Bruhn et al. -/
structure ValidXFamily (P : Set α → Prop) (C X : Set α) where
  F : X.Elem → Set α
  hPF : ∀ x : X.Elem, P (F x)
  hF : ∀ x ∈ X, ∀ y : X.Elem, x ∈ F y ↔ x = y.val

-- todo: lemma: ∀ x : X, (x : α) ∈ F.F x
-- todo: lemma: ∀ z ∈ C \ F.union, z ∉ X

/-- Shorthand for union of sets in `CircPred.ValidXFamily` -/
def ValidXFamily.union {P : Set α → Prop} {C X : Set α}
    (F : ValidXFamily P C X) : Set α :=
  Set.iUnion F.F

/-- A matroid defined by circuit conditions. -/
structure CircuitMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The circuit predicate -/
  (CircuitPred : Set α → Prop)
  /-- Empty set is not a circuit -/
  (not_circuit_empty : ¬(CircuitPred ∅))
  /-- No circuit is a subset of another circuit -/
  (circuit_not_subset : ∀ ⦃C C' : Set α⦄, CircuitPred C → CircuitPred C' → ¬(C' ⊂ C))
  /-- Condition (C3) from Bruhn et al. -/
  (circuit_c3 : ∀ ⦃X C : Set α⦄, ∀ F : ValidXFamily CircuitPred C X,
      ∀ z ∈ C \ F.union, ∃ C' : Set α, CircuitPred C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.union) \ X)
  /-- Corresponding family of independent sets satisfies has the maximal subset property -/
  (circuit_maximal : ∀ X : Set α, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (CircPredToIndep CircuitPred E) X)
  /-- Every circuit is a subset of the ground set -/
  (subset_ground : ∀ C : Set α, CircuitPred C → C ⊆ E)

/-- Independence predicate in circuit matroid construction. -/
def CircuitMatroid.isIndep (M : CircuitMatroid α) : Set α → Prop :=
  CircPredToIndep M.CircuitPred M.E

/-- Empty set is independent in circuit matroid construction. -/
theorem CircuitMatroid.isIndep_empty (M : CircuitMatroid α) : M.isIndep ∅ :=
  ⟨M.E.empty_subset, fun _ hM hC => M.not_circuit_empty (Set.subset_eq_empty hC rfl ▸ hM)⟩

/-- Subset of independent set is independent in circuit matroid construction. -/
theorem CircuitMatroid.isIndep_subset {I J : Set α} (M : CircuitMatroid α) (hI : M.isIndep I) (hJI : J ⊆ I) :
    M.isIndep J :=
  ⟨hJI.trans hI.left, fun C hMC hCJ => hI.right C hMC (hCJ.trans hJI)⟩

lemma CircuitMatroid.Maximal_iff (M : CircuitMatroid α) (B : Set α) :
    Maximal (fun K : Set α => M.isIndep K ∧ K ⊆ M.E) B ↔ Maximal M.isIndep B :=
  ⟨fun hB => ⟨hB.left.left, fun _ hA hBA => hB.right ⟨hA, hA.left⟩ hBA⟩,
   fun hB => ⟨⟨hB.left, hB.left.left⟩, fun _ hA => hB.right hA.left⟩⟩

-- TODO move
lemma nmem_insert {z x : α} {I : Set α} (hz : z ≠ x) (hI : z ∉ I) : z ∉ x ᕃ I := by
  simp_all [Set.insert]

theorem CircuitMatroid.isIndep_aug {I I' : Set α}
    (M : CircuitMatroid α) (hI : M.isIndep I) (hMI : ¬Maximal M.isIndep I) (hMI' : Maximal M.isIndep I') :
    ∃ x ∈ I' \ I, M.isIndep (x ᕃ I) := by
  -- Proof adapted from Bruhn et al., Theorem 4.2 (ii), backward direction
  have hB := hI
  apply M.circuit_maximal at hB
  specialize hB hI.1
  obtain ⟨B, hIB, hBmax⟩ := hB
  simp only [Maximal, Set.le_eq_subset, and_imp] at hBmax
  obtain ⟨⟨hBindep, hBground⟩, hBmax⟩ := hBmax

  have hIBstrict : I ⊂ B
  · rw [Set.ssubset_def]
    by_contra! hBI
    have hIBeq : I = B := hIB.antisymm (hBI hIB)
    unfold Maximal at hMI
    push_neg at hMI
    obtain ⟨J, hJindep, hIJ, hnJI⟩ := hMI hI
    have hIJneq : I ≠ J := (ne_of_not_le hnJI).symm
    have hBJ : B ⊆ J := (hBI hIB).trans hIJ
    have hBJeq : B = J := hBJ.antisymm (hBmax hJindep hJindep.1 hBJ)
    rw [hIBeq, hBJeq] at hIJneq
    tauto

  obtain ⟨z, hzB, hzI⟩ := Set.exists_of_ssubset hIBstrict

  if hzI' : z ∈ I' then
    exact ⟨z, Set.mem_diff_of_mem hzI' hzI, isIndep_subset M hBindep (Set.insert_subset hzB hIB)⟩
  else
    let J' := z ᕃ I'
    have hJ'ground : J' ⊆ M.E := Set.insert_subset (hBground hzB) hMI'.1.1
    have hJ' : ¬M.isIndep J'
    · intro hJ'indep
      obtain ⟨hI'indep, hI'max⟩ := hMI'
      specialize hI'max hJ'indep (Set.subset_insert z I')
      have : J' ≠ I' := Set.insert_ne_self.mpr hzI'
      tauto

    unfold CircuitMatroid.isIndep CircPredToIndep at hJ'
    push_neg at hJ'
    specialize hJ' hJ'ground
    obtain ⟨C, ⟨hCcirc, hCJ'⟩⟩ := hJ'

    let X := C \ B
    have hXJ' : X ⊆ J' := fun _ x => hCJ' (Set.diff_subset x)
    have hzX : z ∉ X := Set.not_mem_diff_of_mem hzB
    have hXI' : X ⊆ I' := (Set.subset_insert_iff_of_not_mem hzX).mp hXJ'
    have hBX : B ∩ X = ∅ := Set.inter_diff_self B C
    have tmp : I ∩ X ⊆ B ∩ X := Set.inter_subset_inter hIB Set.Subset.rfl
    have hIX : I ∩ X = ∅ := Set.subset_eq_empty tmp hBX
    have hIXsubnone : I ∩ X ⊆ ∅ := Set.subset_empty_iff.mpr hIX
    have hIXdisj : Disjoint I X := Set.disjoint_iff.mpr hIXsubnone
    have hXII' : X ⊆ I' \ I := Set.subset_diff.mpr ⟨hXI', hIXdisj.symm⟩

    by_contra hx
    unfold CircuitMatroid.isIndep CircPredToIndep at hx
    push_neg at hx

    have hIxground : ∀ x ∈ M.E, x ᕃ I ⊆ M.E := fun x a => Set.insert_subset a (fun _ hxI => hBground (hIB hxI))
    have hI'mIground : I' \ I ⊆ M.E := fun _ hII' => hMI'.1.1 (Set.diff_subset hII')
    have hI'mIxground : ∀ x ∈ I' \ I, x ᕃ I ⊆ M.E := fun x a => hIxground x (hI'mIground a)

    have hz : ∀ x ∈ X, z ∉ x ᕃ I
    · intro x hxx
      have hxI'mI : x ∈ I' \ I := (hXII' hxx)
      have hxIground : x ᕃ I ⊆ M.E := hIxground x (hJ'ground (hXJ' hxx))
      obtain ⟨Cx, ⟨hCx, hCxI⟩⟩ := hx x hxI'mI hxIground
      have hzx : z ≠ x := (ne_of_mem_of_not_mem (hXI' hxx) hzI').symm
      exact nmem_insert hzx hzI

    -- for every `x ∈ X`, take corresponding `C` from `hx` and put it into `F`
    let F : ValidXFamily M.CircuitPred C X := sorry -- todo: construction
    have hzxF : ∀ x, F.F x ⊆ (x : α) ᕃ I := sorry -- holds by constructoin
    have hzF : z ∈ C \ F.union := sorry -- holds by construction
    apply M.circuit_c3 at hzF
    obtain ⟨C', ⟨hC', hzC', hC'CFX⟩⟩ := hzF

    have hCxI : ∀ x, F.F x \ X ⊆ I := sorry -- follows from `hzxF`
    have hCxB : ∀ x, F.F x \ X ⊆ B := fun x _ hFFxX => hIB (hCxI x hFFxX)
    have hCalt : C' ⊆ (C \ X) ∪ Set.iUnion (F.F · \ X) := sorry -- holds by construction of `C'`
    have hUB : Set.iUnion (F.F · \ X) ⊆ B := Set.iUnion_subset hCxB
    have hCXB : C \ X ⊆ B := Set.diff_subset_comm.mp (fun _ => id)
    have hC'exprB : (C \ X) ∪ Set.iUnion (F.F · \ X) ⊆ B := Set.union_subset hCXB hUB
    have hC'B : C' ⊆ B := hCalt.trans hC'exprB

    -- contradiction: `C'` is a cycle and a subset of an independent set
    obtain ⟨hC'ground, hC'nosubcircuit⟩ := M.isIndep_subset hBindep hC'B
    tauto

  rfl

/-- `IndepMatroid` corresponding to circuit matroid. -/
def CircuitMatroid.IndepMatroid (M : CircuitMatroid α) : IndepMatroid α where
  E := M.E
  Indep := M.isIndep
  indep_empty := M.isIndep_empty
  indep_subset _ _ := M.isIndep_subset
  indep_aug _ _ := M.isIndep_aug
  indep_maximal := M.circuit_maximal
  subset_ground _ := And.left

/-- Circuit matroid converted to `Matroid`. -/
def CircuitMatroid.matroid (M : CircuitMatroid α) : Matroid α := M.IndepMatroid.matroid
