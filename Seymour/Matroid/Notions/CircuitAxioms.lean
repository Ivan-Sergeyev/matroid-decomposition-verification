import Mathlib.Order.RelClasses
import Mathlib.Data.Matroid.Basic

import Seymour.Basic
import Seymour.Matroid.Notions.IndepAxioms


/-- Circuit predicate, defines which sets are circuits. -/
abbrev CircuitPredicate (α : Type*) := Set α → Prop


section ValidXFamily

/-- Family of circuits satisfying assumptions of circuit axiom (C3) from Bruhn et al. -/
structure ValidXFamily {α : Type*} (P : CircuitPredicate α) (C X : Set α) where
  F : X.Elem → Set α
  hPF : ∀ x : X.Elem, P (F x)
  hF : ∀ x ∈ X, ∀ y : X, x ∈ F y ↔ x = y

/-- Shorthand for union of sets in `ValidXFamily` -/
@[simp]
def ValidXFamily.union {α : Type*} {P : CircuitPredicate α} {C X : Set α} (F : ValidXFamily P C X) : Set α :=
  Set.iUnion F.F

-- question: unused API?
lemma ValidXFamily.mem_of_elem {α : Type*} {P : CircuitPredicate α} {C X : Set α} (F : ValidXFamily P C X) (x : X.Elem) :
    x.val ∈ F.F x := by
  rw [F.hF]
  exact x.property

-- question: unused API?
lemma ValidXFamily.outside {α : Type*} {P : CircuitPredicate α} {C X : Set α} {F : ValidXFamily P C X} {z : α}
    (hzCF : z ∈ C \ F.union) : z ∉ X := by
  intro hz
  have := F.hF z hz ⟨z, hz⟩
  simp_all [ValidXFamily.union]


section CircuitAxioms

/-- Circuit predicate `P` defines independence predicate: independent sets are all non-circuits. -/
def CircuitPredicate.ToIndepPredicate {α : Type*} (P : CircuitPredicate α) (E : Set α) : IndepPredicate α :=
  fun I => I ⊆ E ∧ ∀ C, C ⊆ I → ¬P C

/-- Axiom (C1): empty set is not a circuit. -/
def CircuitPredicate.not_circuit_empty {α : Type*} (P : CircuitPredicate α) : Prop :=
  ¬P ∅
alias CircuitPredicate.axiom_c1 := CircuitPredicate.not_circuit_empty

/-- Axiom (C2): no circuit is a subset of another circuit. -/
def CircuitPredicate.circuit_not_ssubset {α : Type*} (P : CircuitPredicate α) : Prop :=
  ∀ C C', P C → P C' → ¬(C' ⊂ C)
alias CircuitPredicate.axiom_c2 := CircuitPredicate.circuit_not_ssubset

/-- Axiom (C3) from Bruhn et al. -/
def CircuitPredicate.axiom_c3 {α : Type*} (P : CircuitPredicate α) : Prop :=
  ∀ X C, ∀ F : ValidXFamily P C X, ∀ z ∈ C \ F.union, ∃ C', P C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.union) \ X

/-- Axiom (CM) from Bruhn et al.: set of all independent sets has the maximal subset property. -/
def CircuitPredicate.circuit_maximal {α : Type*} (P : CircuitPredicate α) (E : Set α) : Prop :=
  ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (CircuitPredicate.ToIndepPredicate P E) X
alias CircuitPredicate.axiom_cm := CircuitPredicate.circuit_maximal

/-- Every circuit is a subset of the ground set. -/
def CircuitPredicate.subset_ground {α : Type*} (P : CircuitPredicate α) (E : Set α) : Prop :=
  ∀ C, P C → C ⊆ E
alias CircuitPredicate.axiom_ce := CircuitPredicate.subset_ground

/-- Strong circuit elimination axiom: if `C₁` and `C₂` are circuits with `e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`,
    then there is circuit `C₃` such that `f ∈ C₃ ⊆ C₁ ∪ C₂ \ {e}. -/
def CircuitPredicate.strong_circuit_elim {α : Type*} (P : CircuitPredicate α) : Prop :=
  ∀ C₁ C₂, ∀ e f, P C₁ ∧ P C₂ ∧ e ∈ C₁ ∩ C₂ ∧ f ∈ C₁ \ C₂ → ∃ C₃, P C₃ ∧ f ∈ C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e}

/-- Weak circuit elimination axiom: if `C₁` and `C₂` are distinct circuits and `e ∈ C₁ ∩ C₂`,
    then there is circuit `C₃` such that `C₃ ⊆ C₁ ∪ C₂ \ {e}`. -/
def CircuitPredicate.weak_circuit_elim {α : Type*} (P : CircuitPredicate α) : Prop :=
  ∀ C₁ C₂, C₁ ≠ C₂ → P C₁ → P C₂ → ∀ e ∈ C₁ ∩ C₂, ∃ C₃, P C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e}


section CircuitAxiomRelations

/-- Alternative formulation of axiom (C2). -/
lemma CircuitPredicate.circuit_not_ssubset_iff {α : Type*} (P : CircuitPredicate α) :
    P.circuit_not_ssubset ↔ ∀ C C', P C → P C' → C' ⊆ C → C ⊆ C' := by
  constructor
  · intro hP C C' hC hC' hC'C
    apply hP C C' hC at hC'
    rw [ssubset_iff_subset_ne] at hC'
    push_neg at hC'
    exact (hC' hC'C).symm.subset
  · intro hP C C' hC hC' hC'C
    apply hP C C' hC at hC'
    rw [ssubset_iff_subset_ne] at hC'C
    exact hC'C.2.symm (Set.Subset.antisymm (hC' hC'C.1) hC'C.1)

/-- Axiom (C3) implies strong circuit elimination. -/
lemma CircuitPredicate.C3_strong_circuit_elim {α : Type*} (P : CircuitPredicate α) :
    P.axiom_c3 → P.strong_circuit_elim := by
  intro hPC3 C₁ C₂ x z hxz
  obtain ⟨_hC₁, hC₂, hx, hz⟩ := hxz
  let F : ValidXFamily P C₁ {x} :=
  ⟨
    (fun _ => C₂),
    (fun _ => hC₂),
    (by
      simp only [Set.mem_singleton_iff, Subtype.forall, forall_eq, iff_true]
      exact Set.mem_of_mem_inter_right hx)
  ⟩
  specialize hPC3 {x} C₁ F
  simp only [ValidXFamily.union, Set.iUnion_coe_set, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left] at hPC3
  specialize hPC3 z hz
  exact hPC3

/-- Strong circuit elimination implies weak circuit elimination. -/
lemma CircuitPredicate.strong_circuit_elim_weak_circuit_elim {α : Type*} (P : CircuitPredicate α) :
    P.strong_circuit_elim → P.weak_circuit_elim := by
  intro hP C₁ C₂ hC₁C₂ hC₁ hC₂ e he
  if hf : ∃ f, f ∈ C₁ \ C₂ then
    obtain ⟨f, hf⟩ := hf
    specialize hP C₁ C₂ e f (And.intro hC₁ (And.intro hC₂ (And.intro he hf)))
    obtain ⟨C₃, ⟨hC₃, ⟨_hfC₃, hC₃C₁C₂e⟩⟩⟩ := hP
    use C₃
  else
    push_neg at hf
    simp only [Set.mem_diff, not_and, not_not] at hf
    let hC₁sC₂ : C₁ ⊆ C₂ := hf
    let hC₂dC₁ : (C₂ \ C₁).Nonempty := by
      rw [Set.diff_nonempty]
      by_contra hC₂sC₁
      apply Set.Subset.antisymm hC₂sC₁ at hC₁sC₂
      tauto
    obtain ⟨f, hff⟩ := hC₂dC₁
    specialize hP C₂ C₁ e f (And.intro hC₂ (And.intro hC₁ (And.intro he.symm hff)))
    obtain ⟨C₃, ⟨hC₃, ⟨_hfC₃, hC₃C₁C₂e⟩⟩⟩ := hP
    rw [Set.union_comm] at hC₃C₁C₂e
    use C₃

/-- todo: desc -/
def CircuitPredicate.support {α : Type*} (P : CircuitPredicate α) : Set α :=
  {C : Set α | P C}.sUnion

/-- todo: desc -/
lemma CircuitPredicate.support_eq {α : Type*} (P : CircuitPredicate α) :
    Minimal (fun S => ∀ C, P C → C ⊆ S) P.support := by
  sorry

/-- Condition for circuit predicate to have finite support. -/
lemma CircuitPredicate.finite_support_iff {α : Type*} (P : CircuitPredicate α) :
    P.support.Finite ↔ ∃ S, S.Finite ∧ ∀ C, P C → C ⊆ S := by
  sorry

/-- If `P` is finitely supported and `P` satisfies weak circuit elimination, then `P` satisfies (C3). -/
lemma CircuitPredicate.FinSup_weak_circuit_elim_C3 {α : Type*} {P : CircuitPredicate α} (hP_fin : P.support.Finite) :
    P.weak_circuit_elim → P.axiom_c3 := by
  sorry


section PredicateRelations

/-- Independence predicate defines following circuit predicate: circuits are minimal dependent sets. -/
def IndepPredicate.ToCircuitPredicate {α : Type*} (P : IndepPredicate α) (E : Set α) : CircuitPredicate α :=
  fun C => Minimal (fun D => ¬P D ∧ D ⊆ E) C

/-- Converting circuit predicate to independence predicate and then to circuit predicate
    yields original independence predicate.-/
lemma CircuitPredicate.ToIndep_ToCircuit {α : Type*} (P : CircuitPredicate α) (E C : Set α) :
    (P.ToIndepPredicate E).ToCircuitPredicate E C → C ⊆ E ∧ P C := by
  intro ⟨⟨hCdep, hCE⟩, hCmin⟩
  constructor
  · exact hCE
  · unfold ToIndepPredicate at hCdep hCmin
    push_neg at hCdep
    obtain ⟨D, hDC, hD⟩ := hCdep hCE
    let hDok : (fun K => ¬(K ⊆ E ∧ ∀ C ⊆ K, ¬P C) ∧ K ⊆ E) D := ⟨
      (by
        push_neg
        intro _hDE
        use D),
      hDC.trans hCE,
    ⟩
    specialize hCmin hDok hDC
    exact (Set.eq_of_subset_of_subset hCmin hDC) ▸ hD

/-- todo: desc-/
lemma CircuitPredicate.ToIndep_ToCircuit_iff {α : Type*} {P : CircuitPredicate α} (hP : P.circuit_not_ssubset) (E C : Set α) :
    (P.ToIndepPredicate E).ToCircuitPredicate E C ↔ C ⊆ E ∧ P C := by
  constructor
  · exact CircuitPredicate.ToIndep_ToCircuit P E C
  · intro ⟨hCE, hC⟩
    constructor
    · exact ⟨fun ⟨_, hCsub⟩ => (hCsub C Set.Subset.rfl) hC, hCE⟩
    · intro D ⟨hDnindep, hDE⟩ hDC
      unfold ToIndepPredicate at hDnindep
      push_neg at hDnindep
      obtain ⟨D', ⟨hD'D, hD'⟩⟩ := hDnindep hDE
      rw [CircuitPredicate.circuit_not_ssubset_iff] at hP
      exact (hP C D' hC hD' (hD'D.trans hDC)).trans hD'D

/-- Converting independence predicate to circuit predicate and then to independence predicate
    yields original independence predicate.-/
lemma IndepPredicate.ToCircuit_ToIndep_iff {α : Type*} (P : IndepPredicate α) (E I : Set α) :
    (P.ToCircuitPredicate E).ToIndepPredicate E I ↔ P I ∧ I ⊆ E := by
  constructor
  · intro ⟨hIE, hI⟩
    constructor
    · sorry
    · exact hIE
  · intro ⟨hPI, hIE⟩
    constructor
    · exact hIE
    · sorry

/-- Converting independence predicate of matroid to circuit predicate and then to independence predicate
    yields original independence predicate. -/
lemma IndepPredicate.Matroid_ToCircuit_ToIndep_iff {α : Type*} (M : Matroid α) (I : Set α) :
    (M.IndepPredicate.ToCircuitPredicate M.E).ToIndepPredicate M.E I ↔ I ⊆ M.E ∧ M.Indep I := by
  constructor
  · intro ⟨hIE, hI⟩
    constructor
    · exact hIE
    · -- hI : I contains no circuit
      let hIE' := hIE
      apply M.maximality at hIE
      unfold Matroid.ExistsMaximalSubsetProperty at hIE
      specialize hIE ∅ M.empty_indep I.empty_subset
      obtain ⟨J, _hJ0, ⟨hJindep, hJI⟩, hJ⟩ := hIE
      simp at hJ
      let hJeqI : J = I := by
        by_contra hJneqI
        let haIJ : ∃ a, a ∈ I \ J := Set.nonempty_of_ssubset (HasSubset.Subset.ssubset_of_ne hJI hJneqI)
        obtain ⟨a, ha⟩ := haIJ
        let hJanindep : ¬M.Indep (J ∪ {a}) := sorry
        let hC : ∃ C, C ⊆ J ∪ {a} ∧ ¬M.Indep C ∧ ∀ C' ⊂ C, M.Indep C' := by sorry
        obtain ⟨C, hCJa, hCnindep, hCsindep⟩ := hC
        let hJE : J ⊆ M.E := fun ⦃a⦄ a_1 => hIE (hJI a_1)
        let haE : {a} ⊆ M.E := Set.singleton_subset_iff.mpr (hIE (Set.mem_of_mem_diff ha))
        let hCE : C ⊆ M.E := fun _ a_1 => (Set.union_subset hJE haE) (hCJa a_1)
        let haI : {a} ⊆ I := (Set.singleton_subset_iff.mpr (Set.mem_of_mem_diff ha))
        let hJaI : J ∪ {a} ⊆ I := Set.union_subset hJI haI
        let hCI : C ⊆ I := hCJa.trans hJaI
        unfold IndepPredicate.ToCircuitPredicate Minimal at hI
        push_neg at hI
        specialize hI C hCI ⟨hCnindep, hCE⟩
        obtain ⟨D, ⟨hDdep, hDE⟩, ⟨hDC, hnCD⟩⟩ := hI
        sorry -- todo: finish
      exact hJeqI ▸ hJindep
  · intro ⟨hIE, hIindep⟩
    constructor
    · exact hIE
    · intro C hCI ⟨⟨hCdep, hCE⟩, hCmin⟩
      exact hCdep (Matroid.Indep.subset hIindep hCI)


section CircuitToIndepAxioms

/-- Independence predicate constructed from circuit predicate satisfies (I1): empty set is independent. -/
lemma CircuitPredicate.ToIndepPredicate.indep_empty {α : Type*} {P : CircuitPredicate α}
    (hP : P.not_circuit_empty) (E : Set α) : (P.ToIndepPredicate E).indep_empty :=
  ⟨E.empty_subset, fun _ hCempty hC => hP (Set.subset_eq_empty hCempty rfl ▸ hC)⟩

/-- Independence predicate constructed from circuit predicate satisfies (I2): subsets of independent sets are independent. -/
lemma CircuitPredicate.ToIndepPredicate.indep_subset {α : Type*} (P : CircuitPredicate α) (E : Set α) :
    (P.ToIndepPredicate E).indep_subset := by
  unfold IndepPredicate.indep_subset
  exact fun I J hJ hIJ => ⟨hIJ.trans hJ.1, fun C hCI hPC => hJ.2 C (hCI.trans hIJ) hPC⟩

/-- Independence predicate constructed from circuit predicate satisfies (I3): independent sets have augmentation property. -/
lemma CircuitPredicate.ToIndepPredicate.indep_aug {α : Type*} {P : CircuitPredicate α} {E : Set α}
    (hPCM : P.circuit_maximal E) (hPC3 : P.axiom_c3) : (P.ToIndepPredicate E).indep_aug := by
  -- Proof adapted from Bruhn et al., Theorem 4.2 (ii), backward direction
  intro I B hI hInmax hBmax
  sorry -- todo : fix

    -- (hI : P.ToIndepPredicate E I)
    -- (hPI : ¬Maximal (P.ToIndepPredicate E) I)
    -- (hPI' : Maximal (P.ToIndepPredicate E) I')

  -- have hB := hI
  -- apply hPCM at hB
  -- specialize hB hI.1
  -- obtain ⟨B, hIB, hBmax⟩ := hB
  -- simp only [Maximal, Set.le_eq_subset, and_imp] at hBmax
  -- obtain ⟨⟨hBindep, hBground⟩, hBmax⟩ := hBmax

  -- have hIBstrict : I ⊂ B
  -- · rw [Set.ssubset_def]
  --   by_contra! hBI
  --   unfold Maximal at hInmax
  --   push_neg at hInmax
  --   obtain ⟨J, hJindep, hIJ, hnJI⟩ := hInmax hI
  --   have hIJneq : I ≠ J := (ne_of_not_le hnJI).symm
  --   have hBJ : B ⊆ J := (hBI hIB).trans hIJ
  --   rw [hIB.antisymm (hBI hIB), hBJ.antisymm (hBmax hJindep hJindep.1 hBJ)] at hIJneq
  --   exact hIJneq rfl

  -- obtain ⟨z, hzB, hzI⟩ := Set.exists_of_ssubset hIBstrict

  -- if hzI' : z ∈ I' then
  --   exact ⟨z, Set.mem_diff_of_mem hzI' hzI, indep_subset hBindep (Set.insert_subset hzB hIB)⟩
  -- else
  --   let J' := z ᕃ I'
  --   have hJ'ground : J' ⊆ E := Set.insert_subset (hBground hzB) hPI'.1.1
  --   have hJ' : ¬P.ToIndepPredicate E J'
  --   · intro hJ'indep
  --     obtain ⟨hI'indep, hI'max⟩ := hPI'
  --     exact hzI' (hI'max hJ'indep (Set.subset_insert z I') (Or.inl rfl))

  --   unfold CircuitPredicate.ToIndepPredicate at hJ'
  --   push_neg at hJ'
  --   specialize hJ' hJ'ground
  --   obtain ⟨C, ⟨hCcirc, hCJ'⟩⟩ := hJ'

  --   let X := C \ B
  --   have hXJ' : X ⊆ J' := fun _ x => hCJ' (Set.diff_subset x)
  --   have hzX : z ∉ X := Set.not_mem_diff_of_mem hzB
  --   have hXI' : X ⊆ I' := (Set.subset_insert_iff_of_not_mem hzX).mp hXJ'
  --   have hBX : B ∩ X = ∅ := Set.inter_diff_self B C
  --   have tmp : I ∩ X ⊆ B ∩ X := Set.inter_subset_inter hIB Set.Subset.rfl
  --   have hIX : I ∩ X = ∅ := Set.subset_eq_empty tmp hBX
  --   have hIXsubnone : I ∩ X ⊆ ∅ := Set.subset_empty_iff.mpr hIX
  --   have hIXdisj : Disjoint I X := Set.disjoint_iff.mpr hIXsubnone
  --   have hXII' : X ⊆ I' \ I := Set.subset_diff.mpr ⟨hXI', hIXdisj.symm⟩

  --   by_contra hx
  --   unfold CircuitPredicate.ToIndepPredicate at hx
  --   push_neg at hx

  --   have hIxground : ∀ x ∈ E, x ᕃ I ⊆ E := fun x a => Set.insert_subset a (fun _ hxI => hBground (hIB hxI))
  --   have hI'mIground : I' \ I ⊆ E := fun _ hII' => hPI'.1.1 (Set.diff_subset hII')
  --   have hI'mIxground : ∀ x ∈ I' \ I, x ᕃ I ⊆ E := fun x a => hIxground x (hI'mIground a)

  --   have hz : ∀ x ∈ X, z ∉ x ᕃ I
  --   · intro x hxx
  --     have hxI'mI : x ∈ I' \ I := hXII' hxx
  --     have hxIground : x ᕃ I ⊆ E := hIxground x (hJ'ground (hXJ' hxx))
  --     obtain ⟨Cx, ⟨hCx, hCxI⟩⟩ := hx x hxI'mI hxIground
  --     have hzx : z ≠ x := (ne_of_mem_of_not_mem (hXI' hxx) hzI').symm
  --     exact nmem_insert hzx hzI

  --   -- for every `x ∈ X`, take corresponding `C` from `hx` and put it into `F`
  --   let F : ValidXFamily P C X := sorry -- todo: construction
  --   have hzxF : ∀ x, F.F x ⊆ (x : α) ᕃ I := sorry -- holds by constructoin
  --   have hzF : z ∈ C \ F.union := sorry -- holds by construction
  --   apply hPC3 at hzF
  --   obtain ⟨C', hC', hzC', hC'CFX⟩ := hzF

  --   have hCxI : ∀ x, F.F x \ X ⊆ I := sorry -- follows from `hzxF`
  --   have hCxB : ∀ x, F.F x \ X ⊆ B := fun x _ hFFxX => hIB (hCxI x hFFxX)
  --   have hCalt : C' ⊆ (C \ X) ∪ Set.iUnion (F.F · \ X) := sorry -- holds by construction of `C'`
  --   have hUB : Set.iUnion (F.F · \ X) ⊆ B := Set.iUnion_subset hCxB
  --   have hCXB : C \ X ⊆ B := Set.diff_subset_comm.mp (fun _ => id)
  --   have hC'exprB : (C \ X) ∪ Set.iUnion (F.F · \ X) ⊆ B := Set.union_subset hCXB hUB
  --   have hC'B : C' ⊆ B := hCalt.trans hC'exprB

  --   -- contradiction: `C'` is a cycle and a subset of an independent set
  --   obtain ⟨hC'ground, hC'nosubcircuit⟩ := indep_subset hBindep hC'B
  --   exact hC'nosubcircuit C' hC' (fun _ => id)

  -- rfl

/-- Independence predicate constructed from circuit predicate satisfies (IM): independent sets have maximal property. -/
lemma CircuitPredicate.ToIndepPredicate.indep_maximal {α : Type*} (P : CircuitPredicate α) (E : Set α) :
    (P.ToIndepPredicate E).indep_maximal E :=
  sorry

/-- Independence predicate constructed from circuit predicate satisfies (IE): independent sets are subsets of ground set. -/
lemma CircuitPredicate.ToIndepPredicate.subset_ground {α : Type*} (P : CircuitPredicate α) (E : Set α) :
    (P.ToIndepPredicate E).subset_ground E :=
  fun _ hI => hI.1

/-- Independence predicate constructed from circuit predicate satisfies augmentation property
    if weak circuit elimination axiom holds in finite case. -/
lemma CircuitPredicate.ToIndepPredicate.finite_weak_circuit_elim_indep_aug {α : Type*} {P : CircuitPredicate α} {E I J : Set α}
    -- todo: add hP: necessary assumptions on circuit predicate
    (hE : E.Finite) (hI : P.ToIndepPredicate E I) (hJ : P.ToIndepPredicate E J) (hIJ : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ P.ToIndepPredicate E (e ᕃ I) := by
  unfold ToIndepPredicate at hI hJ
  by_contra heJ
  push_neg at heJ

  let hKmin : ∃ K, P.ToIndepPredicate E K ∧ K ⊆ I ∪ J ∧ I.ncard < K.ncard ∧
      (∀ K', (P.ToIndepPredicate E K' ∧ K' ⊆ I ∪ J ∧ I.ncard < K'.ncard) → (I \ K).ncard ≤ (I \ K').ncard) := by
    sorry
  obtain ⟨K, hK⟩ := hKmin
  let hImKnonempty : (I \ K).Nonempty := sorry
  obtain ⟨e, he⟩ := hImKnonempty
  sorry
-- todo: formalize proof below (taken from Oxley)
-- To prove (I3), suppose that I1 and I2 are members of I and |I1| < |I2|.
-- Assume that (I3) fails for the pair (I1, I2). Now I has a member that is a subset
-- of I1 ∪ I2 and has more elements than I1. Choose such a subset I3 for which
-- |I1 − I3| is minimal. As (I3) fails, I1 − I3 is non-empty, so we can choose an
-- element e from this set. Now, for each element f of I3 −I1, let Tf be (I3 ∪e)−f.
-- Then Tf ⊆ I1 ∪ I2 and |I1 − Tf| < |I1 − I3|. Therefore Tf /∈ I, so Tf contains
-- a member Cf of C. Hence Cf ⊆ (I3 ∪ e) − f, so f /∈ Cf. Moreover, e ∈ Cf,
-- otherwise Cf ⊆ I3 contradicting the fact that I3 ∈ I.
-- Suppose g ∈ I3 − I1. If Cg ∩ (I3 − I1) = ∅, then Cg ⊆ ((I1 ∩ I3) ∪ e) − g ⊆ I1;
-- a contradiction. Thus there is an element h in Cg ∩ (I3 − I1), and Ch ̸= Cg since
-- h ̸∈ Ch. Now e ∈ Cg ∩ Ch, so (C3) implies that C contains a member C such
-- that C ⊆ (Cg ∪ Ch) − e. But, both Cg and Ch are subsets of I3 ∪ e, so C ⊆ I3; a
-- contradiction. We conclude that (I3) holds. Thus (E, I) is a matroid M.


section CircuitsSatisfyCircuitAxioms

-- todo: Matroid.Circuit's satisfy circuit axioms
