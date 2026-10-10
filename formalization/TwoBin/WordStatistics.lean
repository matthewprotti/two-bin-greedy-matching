import TwoBin.TailExpansion
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange

namespace TwoBin

def PositiveWord (word : List Degree) : Prop := ∀ d ∈ word, d ≠ .zero

theorem activeTrials_append (ranking : Bool) (xs ys : List Degree) :
    activeTrials ranking (xs++ys) = activeTrials ranking xs + activeTrials ranking ys := by
  induction xs with
  | nil => simp [activeTrials]
  | cons d xs ih => cases d <;> cases ranking <;> simp [activeTrials,ih] <;> omega

theorem forcedChoices_append (ranking priority : Bool) (xs ys : List Degree) :
    forcedChoices ranking priority (xs++ys) = forcedChoices ranking priority xs + forcedChoices ranking priority ys := by
  induction xs with
  | nil => simp [forcedChoices]
  | cons d xs ih =>
    cases d <;> cases ranking <;> cases priority <;> simp [forcedChoices,ih]
    all_goals ring

theorem forcedChoices_nonnegative (ranking priority : Bool) (word : List Degree) :
    0 ≤ forcedChoices ranking priority word := by
  induction word with
  | nil => simp [forcedChoices]
  | cons d ds ih => cases d <;> cases ranking <;> cases priority <;> simp [forcedChoices] <;> omega

theorem activeTrials_positive (word : List Degree) (hp : PositiveWord word) :
    activeTrials false word = word.length := by
  induction word with
  | nil => rfl
  | cons d ds ih =>
    have hd := hp d (by simp)
    have ht : PositiveWord ds := by intro x hx; exact hp x (by simp [hx])
    cases d <;> simp [activeTrials,ih ht] at *

theorem activeTrials_le_length (ranking : Bool) (word : List Degree) :
    activeTrials ranking word ≤ word.length := by
  induction word with
  | nil => rfl
  | cons d ds ih => cases d <;> cases ranking <;> simp [activeTrials] <;> omega

theorem positiveWord_append (xs ys : List Degree) :
    PositiveWord (xs++ys) ↔ PositiveWord xs ∧ PositiveWord ys := by
  simp only [PositiveWord,List.mem_append,or_imp,forall_and]

theorem positiveWord_take (word : List Degree) (hp : PositiveWord word) (n : ℕ) :
    PositiveWord (word.take n) := by
  intro d hd
  exact hp d (List.mem_of_mem_take hd)

theorem positiveWord_drop (word : List Degree) (hp : PositiveWord word) (n : ℕ) :
    PositiveWord (word.drop n) := by
  intro d hd
  exact hp d (List.mem_of_mem_drop hd)

theorem insertEverywhere_eq_permutationsAux (d : Degree) (word : List Degree) :
    insertEverywhere d word = List.permutations'Aux d word := by
  induction word with
  | nil => rfl
  | cons x xs ih => simp [insertEverywhere,List.permutations'Aux,ih]

/-- Exact equality with the standard permutation enumerator, including multiplicities. -/
theorem arrivalOrders_eq_permutations (word : List Degree) :
    arrivalOrders word = word.permutations' := by
  induction word with
  | nil => rfl
  | cons d ds ih =>
    have hf : insertEverywhere d = List.permutations'Aux d := funext (insertEverywhere_eq_permutationsAux d)
    simp only [arrivalOrders,List.permutations',ih,hf]

/-- Relabeling distinct job IDs by their degrees preserves every permutation entry. -/
theorem arrivalOrders_labeled {α : Type*} (labels : List α) (degree : α → Degree) :
    arrivalOrders (labels.map degree) = (labels.permutations').map (List.map degree) := by
  rw [arrivalOrders_eq_permutations]
  exact (List.map_permutations' degree labels).symm

/-- The source arrival list is the degree image of all permutations of distinct job IDs. -/
theorem arrivalOrders_labeled_indices (word : List Degree) :
    arrivalOrders word = ((List.finRange word.length).permutations').map (List.map word.get) := by
  have h := arrivalOrders_labeled (List.finRange word.length) word.get
  rw [List.finRange_map_get] at h
  exact h

theorem labeled_arrival_orders_nodup (n : ℕ) : ((List.finRange n).permutations').Nodup := by
  have h := List.nodup_permutations (List.finRange n) (List.nodup_finRange n)
  exact (List.permutations_perm_permutations' (List.finRange n)).nodup_iff.mp h

end TwoBin
