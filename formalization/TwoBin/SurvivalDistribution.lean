import TwoBin.ChoiceDistribution
import Mathlib.Algebra.BigOperators.Field

namespace TwoBin

theorem freeStep_total (ranking priority : Bool) (loads : Loads) (d : Degree) (coin : Bool) :
    (freeStep ranking priority loads d coin).1 + (freeStep ranking priority loads d coin).2 =
      loads.1+loads.2+activeTrials false [d] := by
  cases d <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [freeStep, addAt, activeTrials] <;> omega

theorem runFree_total (ranking priority : Bool) (word : List Degree) (cs : List Bool)
    (loads : Loads) (hlen : cs.length = word.length) :
    (runFree ranking priority (word.zip cs) loads).1 +
      (runFree ranking priority (word.zip cs) loads).2 = loads.1+loads.2+activeTrials false word := by
  induction word generalizing cs loads with
  | nil => simp [runFree, activeTrials]
  | cons d ds ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      simp only [List.length_cons] at hlen
      change (runFree ranking priority (ds.zip cs) (freeStep ranking priority loads d c)).1 +
        (runFree ranking priority (ds.zip cs) (freeStep ranking priority loads d c)).2 = _
      rw [ih cs _ (by omega)]
      have hs := freeStep_total ranking priority loads d c
      cases d <;> simp only [activeTrials, Bool.false_eq_true, if_false] at * <;> omega

theorem activeTrials_single_le_positive (word : List Degree) :
    activeTrials true word ≤ activeTrials false word := by
  induction word with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [activeTrials] <;> omega

theorem window_indicator (lo x : ℤ) (len : ℕ) :
    (∑ i ∈ Finset.range len, if x = lo+(i : ℤ) then (1 : ℚ) else 0) =
      if lo ≤ x ∧ x < lo+(len : ℤ) then 1 else 0 := by
  by_cases hx : lo ≤ x ∧ x < lo+(len : ℤ)
  · rw [if_pos hx]
    let k := (x-lo).toNat
    have hk : k ∈ Finset.range len := by apply Finset.mem_range.mpr; dsimp [k]; omega
    have he : x = lo+(k : ℤ) := by dsimp [k]; omega
    rw [Finset.sum_eq_single k]
    · simp [he]
    · intro j hj hjk
      have hj' := Finset.mem_range.mp hj
      have hne : x ≠ lo+(j : ℤ) := by omega
      simp [hne]
    · intro hn
      exact False.elim (hn hk)
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : x ≠ lo+(i : ℤ) := by omega
    simp [he]

theorem coinAverage_sum_range (n len : ℕ) (f : List Bool → ℕ → ℚ) :
    coinAverage n (fun cs => ∑ i ∈ Finset.range len, f cs i) =
      ∑ i ∈ Finset.range len, coinAverage n (fun cs => f cs i) := by
  induction len with
  | zero => simp [coinAverage_const]
  | succ len ih => simp only [Finset.sum_range_succ]; rw [coinAverage_add,ih]

theorem free_interval_probability (ranking priority : Bool) (word : List Degree) (lo : ℤ) (len : ℕ) :
    coinAverage word.length (fun cs => if lo ≤ firstSum ranking priority (word.zip cs) ∧
      firstSum ranking priority (word.zip cs) < lo+(len : ℤ) then 1 else 0) =
    binomialWindow (activeTrials ranking word) (lo-forcedChoices ranking priority word) len /
      2^(activeTrials ranking word) := by
  have he := coinAverage_congr word.length _ _ (fun cs _ =>
    (window_indicator lo (firstSum ranking priority (word.zip cs)) len).symm)
  rw [he,coinAverage_sum_range]
  change (∑ i ∈ Finset.range len, freeFirstMass ranking priority word (lo+(i : ℤ))) = _
  simp_rw [freeFirstMass_binomial]
  rw [← Finset.sum_div, binomialWindow_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem unsaturated_free_interval (r q : ℕ) (ranking priority : Bool)
    (word : List Degree) (cs : List Bool) (hlen : cs.length = word.length) :
    Unsaturated (r+1) (q+1) (runFree ranking priority (word.zip cs) (0,0)) ↔
      (activeTrials false word : ℤ)-(q : ℤ) ≤ firstSum ranking priority (word.zip cs) ∧
      firstSum ranking priority (word.zip cs) < (activeTrials false word : ℤ)-(q : ℤ) +
        ((r+q+1-activeTrials false word : ℕ) : ℤ) := by
  have hf := runFree_first ranking priority (word.zip cs) (0,0)
  have ht := runFree_total ranking priority word cs (0,0) hlen
  simp only [Nat.zero_add, Nat.cast_zero, zero_add] at hf ht
  unfold Unsaturated
  omega

def survivalProbability (a b : ℕ) (ranking priority : Bool) (word : List Degree) : ℚ :=
  (sourceSurvivalCount a b ranking priority word : ℚ) / 2^word.length

theorem survivalProbability_average (a b : ℕ) (ranking priority : Bool) (word : List Degree) :
    survivalProbability a b ranking priority word =
      coinAverage word.length (fun cs => if Unsaturated a b
        (runActual a b ranking priority (word.zip cs) (0,0)) then 1 else 0) := by
  unfold survivalProbability sourceSurvivalCount coinAverage
  rw [← sum_indicator_eq_filter_length]
  simp

/-- Universal source-to-binomial bridge, including unused coins and zero-degree jobs. -/
theorem survivalProbability_binomial (r q : ℕ) (ranking priority : Bool) (word : List Degree) :
    survivalProbability (r+1) (q+1) ranking priority word =
      binomialWindow (activeTrials ranking word)
        ((activeTrials false word : ℤ)-(q : ℤ)-forcedChoices ranking priority word)
        (r+q+1-activeTrials false word) / 2^(activeTrials ranking word) := by
  rw [survivalProbability_average]
  simp only [run_unsaturated_iff]
  rw [← free_interval_probability]
  apply coinAverage_congr
  intro cs hc
  simp only [unsaturated_free_interval r q ranking priority word cs (coinWords_mem_length _ cs hc)]

theorem rv_survival_formula (r q : ℕ) (word : List Degree) :
    survivalProbability (r+1) (q+1) false false word =
      rvSurvivalFormula r q (activeTrials false word) := by
  rw [survivalProbability_binomial, forcedChoices_rv]
  simp [rvSurvivalFormula]

theorem ranking_survival_formula (r q : ℕ) (word : List Degree) :
    (survivalProbability (r+1) (q+1) true false word +
      survivalProbability (r+1) (q+1) true true word)/2 =
      rankingSurvivalFormula r q (activeTrials false word) (activeTrials true word) := by
  rw [survivalProbability_binomial, survivalProbability_binomial, forcedChoices_rank1]
  have ht := activeTrials_split word
  by_cases htN : activeTrials false word ≤ r+q
  · have he : (activeTrials true word : ℤ) -
        ((activeTrials false word : ℤ)-(q : ℤ)-forcedChoices true false word) -
        ((r+q+1-activeTrials false word : ℕ) : ℤ)+1 =
        (activeTrials false word : ℤ)-(r : ℤ) := by omega
    rw [binomialWindow_reflection (activeTrials true word) _
      ((activeTrials false word : ℤ)-(q : ℤ)-forcedChoices true false word), he]
    unfold rankingSurvivalFormula
    simp only [sub_zero]
    ring
  · have hz : r+q+1-activeTrials false word = 0 := by omega
    simp [rankingSurvivalFormula, hz, binomialWindow]

/-- Actual source first-saturation comparison, not an assumed survival law. -/
theorem source_survival_dominance (r q : ℕ) (hrq : r ≤ q) (hregion : QuadraticRegion r q)
    (word : List Degree) :
    (survivalProbability (r+1) (q+1) true false word +
      survivalProbability (r+1) (q+1) true true word)/2 ≤
      survivalProbability (r+1) (q+1) false false word := by
  rw [ranking_survival_formula, rv_survival_formula]
  by_cases ht : activeTrials false word ≤ r+q
  · exact survivalFormula_dominance r q _ _ hrq hregion ht (activeTrials_single_le_positive word)
  · have hz : r+q+1-activeTrials false word = 0 := by omega
    simp [rankingSurvivalFormula, rvSurvivalFormula, hz, binomialWindow]

end TwoBin
