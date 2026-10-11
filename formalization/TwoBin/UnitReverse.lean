import TwoBin.UniformWitness

namespace TwoBin

def FixedReverseDominance (a b : ℕ) : Prop :=
  ∀ word : List Degree, ∀ K : ℕ, 2*rvCount a b word K ≤ rkCount a b word K

def RandomReverseDominance (a b : ℕ) : Prop :=
  ∀ word : List Degree, ∀ K : ℕ,
    2*((arrivalOrders word).map (fun w => rvCount a b w K)).sum ≤
      ((arrivalOrders word).map (fun w => rkCount a b w K)).sum

def FixedEquality (a b : ℕ) : Prop :=
  ∀ word : List Degree, ∀ K : ℕ, rkCount a b word K = 2*rvCount a b word K

def RandomEquality (a b : ℕ) : Prop :=
  ∀ word : List Degree, ∀ K : ℕ,
    ((arrivalOrders word).map (fun w => rkCount a b w K)).sum =
      2*((arrivalOrders word).map (fun w => rvCount a b w K)).sum

theorem binomialZ_zero (n : ℕ) : binomialZ n 0=1 := by simp [binomialZ]

theorem survivalProbability_unit_mass (q : ℕ) (ranking priority : Bool) (word : List Degree)
    (ht : activeTrials false word ≤ q) :
    survivalProbability 1 (q+1) ranking priority word = freeFirstMass ranking priority word 0 := by
  rw [survivalProbability_average]
  simp only [run_unsaturated_iff]
  unfold freeFirstMass
  apply coinAverage_congr
  intro cs hc
  have hf := runFree_first ranking priority (word.zip cs) (0,0)
  have hh := runFree_total ranking priority word cs (0,0) (coinWords_mem_length _ cs hc)
  have he : Unsaturated 1 (q+1) (runFree ranking priority (word.zip cs) (0,0)) ↔
      firstSum ranking priority (word.zip cs)=0 := by
    unfold Unsaturated
    simp only [Nat.zero_add,Nat.cast_zero,zero_add] at hf hh
    omega
  simp only [he]

theorem survivalProbability_zero_of_too_long (r q : ℕ) (ranking priority : Bool)
    (word : List Degree) (ht : r+q < activeTrials false word) :
    survivalProbability (r+1) (q+1) ranking priority word=0 := by
  rw [survivalProbability_binomial]
  have hz : r+q+1-activeTrials false word=0 := by omega
  simp [hz,binomialWindow]

theorem unit_survival_reverse (q : ℕ) (word : List Degree) :
    survivalProbability 1 (q+1) false false word ≤
      (survivalProbability 1 (q+1) true false word + survivalProbability 1 (q+1) true true word)/2 := by
  by_cases ht : activeTrials false word ≤ q
  · rw [survivalProbability_unit_mass q false false word ht,
      survivalProbability_unit_mass q true false word ht,
      survivalProbability_unit_mass q true true word ht]
    simp only [freeFirstMass_binomial,forcedChoices_rv,forcedChoices_rank1,sub_zero,binomialZ_zero,zero_sub]
    have hs := activeTrials_split word
    have hf := forcedChoices_nonnegative true false word
    by_cases hz : forcedChoices true false word=0
    · rw [hz,neg_zero,binomialZ_zero]
      have he : activeTrials false word=activeTrials true word := by omega
      rw [he]
      apply le_of_eq
      ring
    · rw [binomialZ_negative _ _ (by omega)]
      have hi : activeTrials true word+1 ≤ activeTrials false word := by omega
      have hp : (2 : ℚ)^(activeTrials true word+1) ≤ 2^(activeTrials false word) := by
        gcongr; norm_num
      calc
        (1 : ℚ)/2^(activeTrials false word) ≤ 1/2^(activeTrials true word+1) :=
          one_div_le_one_div_of_le (by positivity) hp
        _ = _ := by rw [pow_succ]; ring
  · have hn : 0+q < activeTrials false word := by omega
    rw [survivalProbability_zero_of_too_long 0 q false false word hn,
      survivalProbability_zero_of_too_long 0 q true false word hn,
      survivalProbability_zero_of_too_long 0 q true true word hn]
    norm_num

theorem prefixExpansion_unit_reverse (q K : ℕ) (pre word : List Degree) :
    prefixExpansion 1 (q+1) K false false pre word ≤
      (prefixExpansion 1 (q+1) K true false pre word + prefixExpansion 1 (q+1) K true true pre word)/2 := by
  induction word generalizing pre with
  | nil => simp [prefixExpansion]
  | cons d ds ih =>
    have hs := unit_survival_reverse q pre
    have hg := continuationGain_nonnegative (1+(q+1)) K d ds (activeTrials false pre)
    have hm := mul_le_mul_of_nonneg_right hs hg
    have hh := ih (pre++[d])
    simp only [prefixExpansion]
    nlinarith

theorem fixed_reverse_unit (q : ℕ) : FixedReverseDominance 1 (q+1) := by
  intro word K
  have h := prefixExpansion_unit_reverse q K [] word
  have hk : tailKernel 1 (q+1) false false K word (0,0) ≤
      (tailKernel 1 (q+1) true false K word (0,0) + tailKernel 1 (q+1) true true K word (0,0))/2 := by
    rw [source_tail_expansion,source_tail_expansion,source_tail_expansion]
    linarith
  rw [tailKernel_rvCount,tailKernel_rkCount] at hk
  have hp : (0 : ℚ) < 2^word.length := by positivity
  have hc := (div_le_div_iff₀ hp (show (0 : ℚ) < 2^(word.length+1) by positivity)).mp hk
  rw [pow_succ] at hc
  have hn : 2*(rvCount 1 (q+1) word K : ℚ) ≤ (rkCount 1 (q+1) word K : ℚ) := by
    apply (mul_le_mul_right hp).mp
    nlinarith
  exact_mod_cast hn

theorem fixed_reverse_implies_random_reverse (a b : ℕ) (h : FixedReverseDominance a b) :
    RandomReverseDominance a b := by
  intro word K
  have hs : ∀ orders : List (List Degree),
      2*(orders.map (fun w => rvCount a b w K)).sum ≤
        (orders.map (fun w => rkCount a b w K)).sum := by
    intro orders
    induction orders with
    | nil => simp
    | cons w ws ih =>
      simpa only [List.map_cons,List.sum_cons,Nat.mul_add] using add_le_add (h w K) ih
  exact hs (arrivalOrders word)

theorem matchingGap_nonpositive_of_reverse (a b : ℕ) (h : FixedReverseDominance a b)
    (K : ℕ) (word : List Degree) : matchingGap a b K word ≤ 0 := by
  rw [matchingGap_counts]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have hc : 2*(rvCount a b word K : ℚ) ≤ (rkCount a b word K : ℚ) := by exact_mod_cast h word K
  linarith

theorem randomMatchingGap_nonpositive_of_reverse (a b : ℕ) (h : RandomReverseDominance a b)
    (K : ℕ) (word : List Degree) : randomMatchingGap a b K word ≤ 0 := by
  unfold randomMatchingGap
  rw [sum_matchingGap_counts a b K word.length _ (by intro w hw; exact arrivalOrders_mem_length word w hw)]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have hc : 2*(((arrivalOrders word).map (fun w => rvCount a b w K)).sum : ℚ) ≤
      (((arrivalOrders word).map (fun w => rkCount a b w K)).sum : ℚ) := by exact_mod_cast h word K
  linarith

end TwoBin
