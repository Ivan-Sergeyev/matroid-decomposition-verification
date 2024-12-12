import Mathlib.Data.Matroid.IndepAxioms
import Seymour.Basic


section CircuitMatroid

/-- Independence predicate derived from circuit predicate. -/
def CircPred.Indep {α : Type*} (Circuit : Set α → Prop) (E : Set α) : Set α → Prop :=
  fun I => I ⊆ E ∧ ∀ C, Circuit C → ¬C ⊆ I -- independent sets are all maximal non-circuits

/-- Family of circuits satisfying assumptions of circuit axiom (C3) from Bruhn et al. -/
structure CircPred.ValidXFamily {α : Type*} (Circuit : Set α → Prop) (C X : Set α) where
  F : X → Set α
  hF : ∀ x, Circuit (F x)
  Valid : ∀ x ∈ X, ∀ y : X, x ∈ (F y) ↔ x = (y : α)

-- todo: lemma: ∀ x : X, (x : α) ∈ F.F x
-- todo: lemma: ∀ z ∈ C \ F.Union, z ∉ X

/-- Shorthand for union of sets in `CircPred.ValidXFamily` -/
def CircPred.ValidXFamily.Union {α : Type*} {Circuit : Set α → Prop} {C X : Set α}
    (F : CircPred.ValidXFamily Circuit C X) : Set α :=
  Set.iUnion F.F

/-- A matroid defined by circuit axioms. -/
structure CircuitMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The circuit predicate -/
  (Circuit : Set α → Prop)
  /-- Empty set is not a circuit -/
  (not_circuit_empty : ¬Circuit ∅)
  /-- No circuit is a subset of another circuit -/
  (circuit_not_subset : ∀ ⦃C C'⦄, Circuit C → C' ⊆ C → C' = C)
  /-- Axiom (C3) from Bruhn et al. -/
  (circuit_c3 : ∀ ⦃X C⦄, ∀ F : CircPred.ValidXFamily Circuit C X,
    ∀ z ∈ C \ F.Union, ∃ C', Circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.Union) \ X)
  /-- Corresponding family of independent sets satisfies has the maximal subset property -/
  (circuit_maximal : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (CircPred.Indep Circuit E) X)
  /-- Every circuit is a subset of the ground set -/
  (subset_ground : ∀ C, Circuit C → C ⊆ E)

/-- Independence predicate in circuit matroid construction. -/
def CircuitMatroid.Indep {α : Type*} (M : CircuitMatroid α) : Set α → Prop :=
  CircPred.Indep M.Circuit M.E

/-- Empty set is independent in circuit matroid construction. -/
lemma CircuitMatroid.Indep_empty {α : Type*} (M : CircuitMatroid α) : M.Indep ∅ := by
  unfold CircuitMatroid.Indep CircPred.Indep
  constructor
  · exact Set.empty_subset M.E
  · intro C hC nC
    have hC0 : C = ∅ := Set.subset_eq_empty nC rfl
    rw [hC0] at hC
    apply M.not_circuit_empty at hC
    exact hC
  -- todo: simplify

/-- Subset of independent set is independent in circuit matroid construction. -/
lemma CircuitMatroid.Indep_subset {α : Type*} {I J : Set α}
    (M : CircuitMatroid α) (hI : M.Indep I) (hJI : J ⊆ I) : M.Indep J := by
  unfold CircuitMatroid.Indep CircPred.Indep
  unfold CircuitMatroid.Indep CircPred.Indep at hI
  constructor
  · exact Set.Subset.trans hJI hI.1
  · intro C hC
    intro nC
    obtain ⟨_, hI2⟩ := hI
    specialize hI2 C
    apply Set.Subset.trans nC at hJI
    exact hI2 hC hJI
  -- todo: simplify

-- lemma CircuitMatroid.Indep_and_subset_iff {α : Type*} (M : CircuitMatroid α) (I : Set α) :
--     M.Indep I ∧ I ⊆ M.E ↔ M.Indep I := by
--   constructor
--   · intro hI
--     exact hI.1
--   · intro hI
--     exact ⟨hI, hI.1⟩

lemma CircuitMatroid.Maximal_fun_simp {α : Type*} (M : CircuitMatroid α) (B : Set α) :
    Maximal (fun K => M.Indep K ∧ K ⊆ M.E) B ↔ Maximal M.Indep B := by
  constructor
  · intro hB
    unfold Maximal at hB ⊢
    obtain ⟨⟨hBindep, _hBground⟩, hBmax⟩ := hB
    simp at hBmax
    constructor
    · exact hBindep
    · intro A hA hBA
      specialize hBmax hA hA.1 hBA
      exact hBmax
  · intro hBmax
    unfold Maximal at hBmax ⊢
    obtain ⟨hBindep, hBmax⟩ := hBmax
    constructor
    · exact ⟨hBindep, hBindep.1⟩
    · intro A hA hBA
      obtain ⟨hAindep, _hAground⟩ := hA
      specialize hBmax hAindep hBA
      exact hBmax

lemma ne_not_ins {α : Type*} {z x : α} {I : Set α}
    (hz : z ≠ x) (hI : z ∉ I) : z ∉ x ᕃ I := by
  sorry -- todo: set theory

lemma CircuitMatroid.Indep_aug {α : Type*} {I I' : Set α}
    (M : CircuitMatroid α) (hI : M.Indep I) (hInmax : ¬Maximal M.Indep I) (hI'max : Maximal M.Indep I') :
      ∃ x ∈ I' \ I, M.Indep (x ᕃ I) := by
  -- Proof adapted from Bruhn et al., Theorem 4.2 (ii), backward direction
  have hB := hI
  apply M.circuit_maximal at hB
  specialize hB hI.1
  obtain ⟨B, hIB, hBmax⟩ := hB
  rw [←CircuitMatroid.Indep] at hBmax
  unfold Maximal at hBmax
  simp at hBmax
  obtain ⟨⟨hBindep, hBground⟩, hBmax⟩ := hBmax

  have hIBstrict : I ⊂ B := by
    have hBmax' := hBmax
    rw [@Set.ssubset_def]
    by_contra hBI
    push_neg at hBI
    have hIBeq : I = B := Set.Subset.antisymm hIB (hBI hIB)

    unfold Maximal at hInmax
    push_neg at hInmax
    specialize hInmax hI
    obtain ⟨J, hJindep, hIJ, hnJI⟩ := hInmax
    have hIJneq : I ≠ J := Ne.symm (ne_of_not_le hnJI)

    have hBJ : B ⊆ J := Set.Subset.trans (hBI hIB) hIJ
    specialize hBmax' hJindep hJindep.1 hBJ
    have hBJeq : B = J := Set.Subset.antisymm hBJ hBmax'

    rw [hIBeq, hBJeq] at hIJneq
    tauto

  apply Set.exists_of_ssubset at hIBstrict
  obtain ⟨z, hzB, hzI⟩ := hIBstrict

  if hzI' : z ∈ I' then
    use z
    constructor
    · exact Set.mem_diff_of_mem hzI' hzI
    · exact Indep_subset M hBindep (Set.insert_subset hzB hIB)
  else
    let J' := z ᕃ I'
    have hJ'ground : J' ⊆ M.E := by exact Set.insert_subset (hBground hzB) hI'max.1.1
    have hJ' : ¬M.Indep J' := by
      by_contra hJ'indep
      unfold Maximal at hI'max
      obtain ⟨hI'indep, hI'max⟩ := hI'max
      specialize hI'max hJ'indep (Set.subset_insert z I')
      have tmp : J' ≠ I' := Set.insert_ne_self.mpr hzI'
      tauto

    unfold CircuitMatroid.Indep CircPred.Indep at hJ'
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
    have hXII' : X ⊆ I' \ I := Set.subset_diff.mpr ⟨hXI', Disjoint.symm hIXdisj⟩

    convert_to ¬(∀ x ∈ I' \ I, ¬M.Indep (x ᕃ I))
    constructor
    · intro hx
      push_neg
      tauto
    · intro hx
      push_neg at hx
      tauto

    by_contra hx
    unfold CircuitMatroid.Indep CircPred.Indep at hx
    push_neg at hx

    have hIxground : ∀ x ∈ M.E, x ᕃ I ⊆ M.E := fun x a => Set.insert_subset a fun ⦃a⦄ a_1 => hBground (hIB a_1)
    have hI'mIground : I' \ I ⊆ M.E := fun ⦃a⦄ a_1 => hI'max.1.1 (Set.diff_subset a_1)
    have hI'mIxground : ∀ x ∈ I' \ I, x ᕃ I ⊆ M.E := fun x a => hIxground x (hI'mIground a)

    have hz : ∀ x ∈ X, z ∉ x ᕃ I := by
      intro x hxx
      have hxI'mI : x ∈ I' \ I := (hXII' hxx)
      have hxIground : x ᕃ I ⊆ M.E := hIxground x (hJ'ground (hXJ' hxx))
      specialize hx x hxI'mI hxIground
      obtain ⟨Cx, ⟨hCx, hCxI⟩⟩ := hx
      have hzx : z ≠ x := Ne.symm (ne_of_mem_of_not_mem (hXI' hxx) hzI')
      have hzI : z ∉ I := hzI
      exact ne_not_ins hzx hzI

    -- for every x ∈ X, take corresponding C from hx and put it into F
    let F : CircPred.ValidXFamily M.Circuit C X := sorry -- todo: construction
    have hzxF : ∀ x, F.F x ⊆ (x : α) ᕃ I := sorry -- todo: holds by constructoin
    have hzF : z ∈ C \ F.Union := sorry -- todo: holds by construction
    apply M.circuit_c3 at hzF
    obtain ⟨C', ⟨hC', hzC', hC'CFX⟩⟩ := hzF

    have hCxI : ∀ x, F.F x \ X ⊆ I := sorry -- follows from hzxF
    have hCxB : ∀ x, F.F x \ X ⊆ B := fun x ⦃a⦄ a_1 => hIB (hCxI x a_1)
    have hCalt : C' ⊆ (C \ X) ∪ Set.iUnion (fun x => F.F x \ X) := sorry -- todo: holds by construction of C'
    have hUB : Set.iUnion (fun x => F.F x \ X) ⊆ B := Set.iUnion_subset hCxB
    have hCXB : C \ X ⊆ B := Set.diff_subset_comm.mp fun ⦃a⦄ a => a
    have hC'exprB : (C \ X) ∪ Set.iUnion (fun x => F.F x \ X) ⊆ B := Set.union_subset hCXB hUB
    have hC'B : C' ⊆ B := Set.Subset.trans hCalt hC'exprB

    -- contradiction: C' is a cycle and a subset of an independent set
    have hC'indep : M.Indep C' := M.Indep_subset hBindep hC'B
    unfold CircuitMatroid.Indep CircPred.Indep at hC'indep
    obtain ⟨hC'ground, hC'nosubcircuit⟩ := hC'indep
    specialize hC'nosubcircuit C' hC'
    tauto

  exact fun ⦃a⦄ a => a

/-- `IndepMatroid` corresponding to circuit matroid. -/
def CircuitMatroid.IndepMatroid {α : Type*} (M : CircuitMatroid α) : IndepMatroid α where
  E := M.E
  Indep := M.Indep
  indep_empty := M.Indep_empty
  indep_subset := by
    intro I J
    exact M.Indep_subset
  indep_aug := by
    intro I B hI hInmax hBmax
    exact Indep_aug M hI hInmax hBmax
  indep_maximal := M.circuit_maximal
  subset_ground I hI := hI.1

/-- Circuit matroid converted to `Matroid`. -/
def CircuitMatroid.matroid {α : Type*} (M : CircuitMatroid α) : Matroid α := M.IndepMatroid.matroid
