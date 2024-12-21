import Mathlib.Data.Matroid.IndepAxioms

import Seymour.Basic
import Seymour.Matroid.Notions.IndepAxioms
import Seymour.Matroid.Notions.CircuitAxioms
import Seymour.Matroid.Notions.Circuit


section CircuitMatroid

/-- Matroid defined by circuit axioms. -/
structure CircuitMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The circuit predicate -/
  (CircuitPred : CircuitPredicate α)
  /-- Empty set is not a circuit -/
  (not_circuit_empty : CircuitPred.not_circuit_empty)
  /-- No circuit is a subset of another circuit -/
  (circuit_not_subset : CircuitPred.circuit_not_subset)
  /-- Condition (C3) from Bruhn et al. -/
  (circuit_c3 : CircuitPred.axiom_c3)
  /-- Corresponding family of independent sets satisfies has the maximal subset property -/
  (circuit_maximal : CircuitPred.circuit_maximal E)
  /-- Every circuit is a subset of the ground set -/
  (subset_ground : CircuitPred.subset_ground E) -- question: unused?

/-- Corresponding independence predicate of circuit matroid. -/
def CircuitMatroid.IndepPred {α : Type*} (M : CircuitMatroid α) :
    IndepPredicate α :=
  M.CircuitPred.ToIndepPredicate M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I1): empty set is independent. -/
lemma CircuitMatroid.indep_empty {α : Type*} (M : CircuitMatroid α) :
    M.IndepPred.indep_empty :=
  CircuitPredicate.ToIndepPredicate.indep_empty M.not_circuit_empty M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I2): subsets of independent sets are independent. -/
lemma CircuitMatroid.indep_subset {α : Type*} (M : CircuitMatroid α) :
    M.IndepPred.indep_subset :=
  CircuitPredicate.ToIndepPredicate.indep_subset M.CircuitPred M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I3): independent sets have augmentation property. -/
lemma CircuitMatroid.indep_aug {α : Type*} (M : CircuitMatroid α) :
    M.IndepPred.indep_aug :=
  CircuitPredicate.ToIndepPredicate.indep_aug M.circuit_maximal M.circuit_c3

/-- Corresponding independence predicate of circuit matroid satisfies (IM): independent sets have maximal property. -/
lemma CircuitMatroid.indep_maximal {α : Type*} (M : CircuitMatroid α) :
    M.IndepPred.indep_maximal M.E :=
  CircuitPredicate.ToIndepPredicate.indep_maximal M.CircuitPred M.E

/-- Corresponding independence predicate of circuit matroid satisfies (IE): independent sets are subsets of ground set. -/
def CircuitMatroid.indep_subset_ground {α : Type*} (M : CircuitMatroid α) :
    M.IndepPred.subset_ground M.E :=
  CircuitPredicate.ToIndepPredicate.subset_ground M.CircuitPred M.E

/-- `IndepMatroid` corresponding to circuit matroid. -/
def CircuitMatroid.IndepMatroid {α : Type*} (M : CircuitMatroid α) : IndepMatroid α where
  E := M.E
  Indep := M.IndepPred
  indep_empty := M.indep_empty
  indep_subset := M.indep_subset
  indep_aug := M.indep_aug
  indep_maximal := M.indep_maximal
  subset_ground := M.indep_subset_ground

/-- Circuit matroid converted to `Matroid`. -/
def CircuitMatroid.matroid {α : Type*} (M : CircuitMatroid α) : Matroid α := M.IndepMatroid.matroid

-- question: unused API?
lemma CircuitMatroid.Maximal_iff {α : Type*} (M : CircuitMatroid α) (B : Set α) :
    Maximal (fun K : Set α => M.IndepPred K ∧ K ⊆ M.E) B ↔ Maximal M.IndepPred B :=
  ⟨fun hB => ⟨hB.left.left, fun _ hA hBA => hB.right ⟨hA, hA.left⟩ hBA⟩,
   fun hB => ⟨⟨hB.left, hB.left.left⟩, fun _ hA => hB.right hA.left⟩⟩

@[simp] lemma CircuitMatroid.E_eq {α : Type*} (M : CircuitMatroid α) : M.matroid.E = M.E := rfl

@[simp] lemma CircuitMatroid.indep_eq {α : Type*} (M : CircuitMatroid α) : M.matroid.Indep = M.IndepPred := rfl

@[simp] lemma CircuitMatroid.circuit_iff {α : Type*} (M : CircuitMatroid α) {C : Set α} :
    M.matroid.Circuit C ↔ M.CircuitPred C := by
  constructor
  · intro hC
    sorry
  · intro hC
    sorry

/-- Registered conversion from `CircuitMatroid` to `Matroid`. -/
instance {α : Type*} : Coe (CircuitMatroid α) (Matroid α) where
  coe := CircuitMatroid.matroid
