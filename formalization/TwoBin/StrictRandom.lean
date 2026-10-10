import TwoBin.StrictRV

namespace TwoBin

theorem survivalProbability_one_of_short (a b : ℕ) (ranking priority : Bool) (word : List Degree)
    (ha : activeTrials false word<a) (hb : activeTrials false word<b) :
    survivalProbability a b ranking priority word=1 := by
  rw [survivalProbability_average]
  simp only [run_unsaturated_iff]
  calc
    _ = coinAverage word.length (fun _ => 1) := by
      apply coinAverage_congr
      intro cs hc
      have ht := runFree_total ranking priority word cs (0,0) (coinWords_mem_length _ cs hc)
      have hu : Unsaturated a b (runFree ranking priority (word.zip cs) (0,0)) := by
        unfold Unsaturated
        simp only [Nat.zero_add] at ht
        omega
      exact if_pos hu
    _ = 1 := coinAverage_const _ _

theorem sourceSurvivalGap_short (a b : ℕ) (word : List Degree)
    (ha : activeTrials false word<a) (hb : activeTrials false word<b) : sourceSurvivalGap a b word=0 := by
  unfold sourceSurvivalGap
  rw [survivalProbability_one_of_short a b false false word ha hb,
    survivalProbability_one_of_short a b true false word ha hb,
    survivalProbability_one_of_short a b true true word ha hb]
  norm_num

theorem prefixGap_all_flexes (a b K : ℕ) (pre : List Degree) (n : ℕ) :
    prefixGap a b K pre (List.replicate n Degree.flexible)=0 := by
  have h := prefixGap_leading_flexibles a b K pre [] n
  simpa [prefixGap_nil] using h

theorem insertAt_singleton_flexes (n i : ℕ) (hi : i ≤ n) :
    insertAt Degree.singleton i (List.replicate n Degree.flexible) =
      List.replicate i Degree.flexible ++ Degree.singleton::List.replicate (n-i) Degree.flexible := by
  induction n generalizing i with
  | zero =>
    have hz : i=0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => simp [insertAt]
    | succ i => simp [List.replicate_succ,insertAt,ih i (by omega)]

theorem matchingGap_singleton_position (a b : ℕ) (_ha : 1 ≤ a) (hab : a ≤ b) (i : ℕ) (hi : i ≤ a) :
    matchingGap a b (a+1) (insertAt .singleton i (List.replicate a .flexible)) =
      if i=a then matchingGap a b (a+1) (strictRVWitness a) else 0 := by
  rw [insertAt_singleton_flexes a i hi]
  by_cases he : i=a
  · subst i
    simp [strictRVWitness]
  · rw [if_neg he,matchingGap_prefix,prefixGap_leading_flexibles]
    simp only [List.nil_append]
    rw [prefixGap_cons,prefixGap_all_flexes,
      sourceSurvivalGap_short a b (List.replicate i Degree.flexible)
        (by simp [activeTrials_flexes]; omega) (by simp [activeTrials_flexes]; omega)]
    ring

theorem arrivalOrders_one_sum (d x : Degree) (n : ℕ) (f : List Degree → ℚ) :
    ((arrivalOrders (d::List.replicate n x)).map f).sum =
      (n.factorial : ℚ)*∑ i ∈ Finset.range (n+1), f (insertAt d i (List.replicate n x)) := by
  rw [arrivalOrders,list_sum_map_flatMap,arrivalOrders_replicate_sum,insertEverywhere_sum,List.length_replicate]

/-- The average strict example loses only the 1/(a+1) weight of the singleton-last order. -/
theorem strictRV_random_gap (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    randomMatchingGap a b (a+1) (.singleton::List.replicate a .flexible) =
      (a.factorial : ℚ)*matchingGap a b (a+1) (strictRVWitness a) := by
  unfold randomMatchingGap
  rw [arrivalOrders_one_sum]
  congr 1
  calc
    _ = ∑ i ∈ Finset.range (a+1), if i=a then matchingGap a b (a+1) (strictRVWitness a) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact matchingGap_singleton_position a b ha hab i (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by simp

theorem not_random_reverse_of_two_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ¬ RandomReverseDominance a b := by
  intro h
  have hpos : 0 < randomMatchingGap a b (a+1) (.singleton::List.replicate a .flexible) := by
    rw [strictRV_random_gap a b (by omega) hab]
    exact mul_pos (by positivity) (strictRVWitness_positive a b ha hab)
  have hneg := randomMatchingGap_nonpositive_of_reverse a b h (a+1) (.singleton::List.replicate a .flexible)
  linarith

end TwoBin
