import Seymour.Matroid.Notions.Circuit


section DisjointCircuitFamily

/-- Family of disjoint circuits of matroid `M`. -/
structure DisjointCircuitFamily {α : Type*} (M : Matroid α) (Idx : Set α) where
  /-- Set family indexed by `Idx` -/
  -- question: upgrade from indexing by Set β to indexing by Sort v (see Set.iUnion in Mathlib.Order.SetNotation)?
  -- note: if we know that `C` is a disjoint union of circuits of `M`,
  -- then wlog we can choose `Idx` to be set of representatives of those circuits
  F : Idx → Set α
  /-- All sets in family are circuits in `M` -/
  hCircuit : ∀ x, M.Circuit (F x)
  /-- All sets in family are disjoint -/
  hDisjoint : ∀ x y, x ≠ y → Disjoint (F x) (F y)

/-- Shorthand for union of sets in `DisjointCircuitFamily`. -/
def DisjointCircuitFamily.union {α : Type*} {M : Matroid α} {Idx : Set α} (F : DisjointCircuitFamily M Idx) : Set α :=
  Set.iUnion F.F

/-- Every element in `DisjointCircuitFamily` is subset of ground set. -/
lemma DisjointCircuitFamily.mem_subset_ground {α : Type*} {M : Matroid α} {Idx : Set α} (F : DisjointCircuitFamily M Idx)
    (x : Idx) : F.F x ⊆ M.E := (F.hCircuit x).subset_ground

/-- Union of sets in `DisjointCircuitFamily` is subset of ground set. -/
lemma DisjointCircuitFamily.union_subset_ground {α : Type*} {M : Matroid α} {Idx : Set α} (F : DisjointCircuitFamily M Idx) :
    F.union ⊆ M.E := by
  simp only [union, Set.iUnion_coe_set, Set.iUnion_subset_iff]
  exact fun i i_1 => mem_subset_ground F (Subtype.mk i i_1)

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma DisjointCircuitFamily.union_indep_empty {α : Type*} {M : Matroid α} {Idx : Set α} {F : DisjointCircuitFamily M Idx} :
    M.Indep F.union → F.union = ∅ := by
  intro hFindep
  by_contra hFnempty
  let hx : ∃ x, (F.F x).Nonempty := by
    by_contra h
    push_neg at h
    unfold union at hFnempty
    simp_all only [Set.iUnion_coe_set, Set.iUnion_empty, not_true_eq_false]
  obtain ⟨x, hx⟩ := hx
  let hFxdep := Matroid.Dep.not_indep (F.hCircuit x).1
  let hFxsubF : F.F x ⊆ F.union := Set.subset_iUnion_of_subset x Set.Subset.rfl
  let hFxindep := Matroid.Indep.subset hFindep hFxsubF
  exact hFxdep hFxindep

/-- Nonempty union of disjoint circuits is dependent. -/
lemma DisjointCircuitFamily.union_nonempty_dep {α : Type*} {M : Matroid α} {Idx : Set α} {F : DisjointCircuitFamily M Idx} :
    F.union.Nonempty → M.Dep F.union := by
  intro hF
  by_contra h
  exact Set.not_nonempty_empty (DisjointCircuitFamily.union_indep_empty (Matroid.indep_of_not_dep h F.union_subset_ground) ▸ hF)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma DisjointCircuitFamily.dep_or_empty {α : Type*} {M : Matroid α} {Idx : Set α} (F : DisjointCircuitFamily M Idx) :
    M.Dep F.union ∨ F.union = ∅ := by
  if h: M.Indep F.union then
    exact Or.inr (DisjointCircuitFamily.union_indep_empty h)
  else
    exact Or.inl ⟨h, F.union_subset_ground⟩

/-- Empty family of disjoint circuits. -/
def DisjointCircuitFamily.Empty {α : Type*} (M : Matroid α) :
    DisjointCircuitFamily M ∅ where
  F := fun _ => ∅
  hCircuit := fun x => False.elim x.2
  hDisjoint := fun x => False.elim x.2

/-- Union of sets in empty family is empty. -/
lemma DisjointCircuitFamily.Empty_union {α : Type*} {M : Matroid α} :
    (DisjointCircuitFamily.Empty M).union = ∅ := Set.iUnion_empty

/-- Family of one circuit, indexed by one element --- that circuit. -/
def DisjointCircuitFamily.One {α : Type*} {M : Matroid α} {C : Set α} (p : α) (hC : M.Circuit C) :
    DisjointCircuitFamily M {p} where
  F := fun _ => C
  hCircuit := fun _ => hC
  hDisjoint := fun x y hxy => False.elim ((x.2 ▸ y.2 ▸ (Subtype.coe_ne_coe.mpr hxy)) rfl)

/-- Union of sets in family of one circuit is that circuit. -/
lemma DisjointCircuitFamily.One_union {α : Type*} {M : Matroid α} {C : Set α} (p : α) (hC : M.Circuit C) :
    (DisjointCircuitFamily.One p hC).union = C := by
  simp only [One, union, Set.iUnion_coe_set, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]


section UnionDisjointCircuits

/-- Set `C` can be represented as disjoint union of circuits of `M`. -/
def Matroid.UnionDisjointCircuits {α : Type*} (M : Matroid α) (C : Set α) : Prop :=
  ∃ Idx, ∃ F : DisjointCircuitFamily M Idx, C = F.union

/-- Empty set is disjoint union of circuits. -/
lemma Matroid.UnionDisjointCircuits.empty {α : Type*} (M : Matroid α) :
    M.UnionDisjointCircuits ∅ := by
  use ∅
  use DisjointCircuitFamily.Empty M
  exact DisjointCircuitFamily.Empty_union.symm

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.UnionDisjointCircuits.indep_empty {α : Type*} {M : Matroid α} {X : Set α} :
    M.UnionDisjointCircuits X → M.Indep X → X = ∅ :=
  fun ⟨_, _, hXF⟩ hXindep => DisjointCircuitFamily.union_indep_empty (hXF ▸ hXindep) ▸ hXF

/-- Nonempty union of disjoint circuits is dependent. -/
lemma Matroid.UnionDisjointCircuits.nonempty_dep {α : Type*} {M : Matroid α} {X : Set α} :
    M.UnionDisjointCircuits X → X.Nonempty → M.Dep X := by
  exact fun ⟨_, _, hXF⟩ hXnempty => hXF ▸ DisjointCircuitFamily.union_nonempty_dep (hXF ▸ hXnempty)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma Matroid.UnionDisjointCircuits.dep_or_empty {α : Type*} {M : Matroid α} {X : Set α} :
    M.UnionDisjointCircuits X → (M.Dep X ∨ X = ∅) :=
  fun ⟨_, F, hXF⟩ => hXF ▸ F.dep_or_empty

/-- One circuit is disjoint union of circuits. -/
lemma Matroid.UnionDisjointCircuits.circuit {α : Type*} {M : Matroid α} {C : Set α} (hC : M.Circuit C) :
    M.UnionDisjointCircuits C := by
  obtain ⟨x, _hxC⟩ := Matroid.Circuit.nonempty hC
  use {x}
  use DisjointCircuitFamily.One x hC
  exact (DisjointCircuitFamily.One_union x hC).symm

/-- Union of disjoint circuits is subset of ground set. -/
lemma Matroid.UnionDisjointCircuits.subset_ground {α : Type*} {M : Matroid α} {X : Set α} :
    M.UnionDisjointCircuits X → X ⊆ M.E :=
  fun ⟨_, F, hXF⟩ => hXF ▸ F.union_subset_ground
