import TwoBin.UnitReverse

namespace TwoBin

theorem activeTrials_flexes (ranking : Bool) (n : ℕ) :
    activeTrials ranking (List.replicate n Degree.flexible) = if ranking then 0 else n := by
  induction n with
  | zero => cases ranking <;> rfl
  | succ n ih => cases ranking <;> simp [List.replicate_succ,activeTrials,ih]

theorem forcedChoices_flexes (n : ℕ) :
    forcedChoices true false (List.replicate n Degree.flexible) = (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,forcedChoices,ih]; omega

theorem binomialWindow_zero_trials (lo : ℤ) (len : ℕ) :
    binomialWindow 0 lo len = if lo ≤ 0 ∧ 0 < lo+(len : ℤ) then 1 else 0 := by
  rw [binomialWindow_sum]
  simp only [binomialZ_zero_trials]
  simpa only [eq_comm] using window_indicator lo 0 len

theorem survivalProbability_general (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ranking priority : Bool) (word : List Degree) :
    survivalProbability a b ranking priority word =
      binomialWindow (activeTrials ranking word)
        ((activeTrials false word : ℤ)-((b-1 : ℕ) : ℤ)-forcedChoices ranking priority word)
        ((a-1)+(b-1)+1-activeTrials false word)/2^(activeTrials ranking word) := by
  have ha' : a-1+1=a := by omega
  have hb' : b-1+1=b := by omega
  simpa only [ha',hb'] using survivalProbability_binomial (a-1) (b-1) ranking priority word

theorem ranking_flexes_first (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    survivalProbability a b true false (List.replicate a Degree.flexible)=0 := by
  rw [survivalProbability_general a b ha (by omega),activeTrials_flexes,activeTrials_flexes,forcedChoices_flexes]
  simp only [Bool.false_eq_true,if_false,if_true,pow_zero,div_one]
  have hl : (a-1)+(b-1)+1-a=b-1 := by omega
  rw [hl,binomialWindow_zero_trials]
  have hn : ¬ (0 : ℤ) < (a : ℤ)-((b-1 : ℕ) : ℤ)-(a : ℤ)+((b-1 : ℕ) : ℤ) := by omega
  simp [hn]

theorem ranking_flexes_second (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    survivalProbability a b true true (List.replicate a Degree.flexible) = if a<b then 1 else 0 := by
  rw [survivalProbability_general a b ha (by omega),activeTrials_flexes,activeTrials_flexes,forcedChoices_rank1]
  simp only [Bool.false_eq_true,if_false,if_true,pow_zero,div_one,sub_zero]
  have hl : (a-1)+(b-1)+1-a=b-1 := by omega
  rw [hl,binomialWindow_zero_trials]
  have he : (a : ℤ)-((b-1 : ℕ) : ℤ) ≤ 0 ∧
      0 < (a : ℤ)-((b-1 : ℕ) : ℤ)+((b-1 : ℕ) : ℤ) ↔ a<b := by omega
  simp only [he]

theorem rv_flexes_survival (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    survivalProbability a b false false (List.replicate a Degree.flexible) =
      if a=b then 1-2/2^a else 1-1/2^a := by
  have hm0 : freeFirstMass false false (List.replicate a Degree.flexible) 0 = 1/2^a := by
    simp [freeFirstMass_binomial,activeTrials_flexes,binomialZ]
  have hma : freeFirstMass false false (List.replicate a Degree.flexible) (a : ℤ) = 1/2^a := by
    simp [freeFirstMass_binomial,activeTrials_flexes,binomialZ]
  rw [survivalProbability_average]
  simp only [run_unsaturated_iff]
  by_cases he : a=b
  · rw [if_pos he]
    have hav := coinAverage_congr (List.replicate a Degree.flexible).length _ _
      (fun cs hc => show (if Unsaturated a b (runFree false false ((List.replicate a Degree.flexible).zip cs) (0,0)) then (1 : ℚ) else 0) =
        1-(if firstSum false false ((List.replicate a Degree.flexible).zip cs)=(a : ℤ) then 1 else 0)-
          (if firstSum false false ((List.replicate a Degree.flexible).zip cs)=0 then 1 else 0) from by
        have hf := runFree_first false false ((List.replicate a Degree.flexible).zip cs) (0,0)
        have ht := runFree_total false false (List.replicate a Degree.flexible) cs (0,0) (coinWords_mem_length _ cs hc)
        simp only [activeTrials_flexes,Bool.false_eq_true,if_false,Nat.zero_add,Nat.cast_zero,zero_add] at hf ht
        simp only [Unsaturated]
        split_ifs <;> norm_num at * <;> omega)
    rw [hav,coinAverage_sub,coinAverage_sub,coinAverage_const]
    change 1-freeFirstMass false false (List.replicate a Degree.flexible) (a : ℤ)-
      freeFirstMass false false (List.replicate a Degree.flexible) 0 = _
    rw [hma,hm0]
    ring
  · rw [if_neg he]
    have hav := coinAverage_congr (List.replicate a Degree.flexible).length _ _
      (fun cs hc => show (if Unsaturated a b (runFree false false ((List.replicate a Degree.flexible).zip cs) (0,0)) then (1 : ℚ) else 0) =
        1-(if firstSum false false ((List.replicate a Degree.flexible).zip cs)=(a : ℤ) then 1 else 0) from by
        have hf := runFree_first false false ((List.replicate a Degree.flexible).zip cs) (0,0)
        have ht := runFree_total false false (List.replicate a Degree.flexible) cs (0,0) (coinWords_mem_length _ cs hc)
        simp only [activeTrials_flexes,Bool.false_eq_true,if_false,Nat.zero_add,Nat.cast_zero,zero_add] at hf ht
        simp only [Unsaturated]
        split_ifs <;> norm_num at * <;> omega)
    rw [hav,coinAverage_sub,coinAverage_const]
    exact congrArg (fun x : ℚ => 1-x) hma

theorem sourceSurvivalGap_flexes_positive (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    0 < sourceSurvivalGap a b (List.replicate a Degree.flexible) := by
  unfold sourceSurvivalGap
  rw [rv_flexes_survival a b (by omega) hab,ranking_flexes_first a b (by omega) hab,
    ranking_flexes_second a b (by omega) hab]
  have hp : (4 : ℚ) ≤ 2^a := by
    calc
      (4 : ℚ) = 2^2 := by norm_num
      _ ≤ 2^a := by gcongr; norm_num
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 4) hp
  have hdiv : (2 : ℚ)/2^a = 2*(1/2^a) := by ring
  by_cases he : a=b
  · rw [if_pos he,if_neg (by omega),hdiv]
    nlinarith
  · rw [if_neg he,if_pos (by omega)]
    nlinarith

theorem prefixGap_leading_flexibles (a b K : ℕ) (pre tail : List Degree) (n : ℕ) :
    prefixGap a b K pre (List.replicate n Degree.flexible ++ tail) =
      prefixGap a b K (pre++List.replicate n Degree.flexible) tail := by
  induction n generalizing pre with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,prefixGap_flexible,ih]
    simp [List.replicate_succ,List.append_assoc]

def strictRVWitness (a : ℕ) : List Degree := List.replicate a .flexible ++ [.singleton]

theorem strictRVWitness_gap (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    matchingGap a b (a+1) (strictRVWitness a) = sourceSurvivalGap a b (List.replicate a Degree.flexible)/2 := by
  rw [matchingGap_prefix]
  unfold strictRVWitness
  rw [prefixGap_leading_flexibles]
  simp only [List.nil_append]
  rw [prefixGap_cons,prefixGap_nil]
  simp only [activeTrials_flexes,Bool.false_eq_true,if_false,add_zero]
  have hg := continuationGain_all_matched (a+b) (a+1) [] a (by simp [PositiveWord]) (by simp) (by omega)
  simp only [activeTrials,zero_add] at hg
  rw [hg]
  ring

theorem strictRVWitness_positive (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    0 < matchingGap a b (a+1) (strictRVWitness a) := by
  rw [strictRVWitness_gap a b (by omega) hab]
  exact div_pos (sourceSurvivalGap_flexes_positive a b ha hab) (by norm_num)

theorem not_fixed_reverse_of_two_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ¬ FixedReverseDominance a b := by
  intro h
  have hpos := strictRVWitness_positive a b ha hab
  have hneg := matchingGap_nonpositive_of_reverse a b h (a+1) (strictRVWitness a)
  linarith

end TwoBin
