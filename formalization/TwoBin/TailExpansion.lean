import TwoBin.Continuation

namespace TwoBin

theorem runActual_valid (a b : ℕ) (ranking priority : Bool) (events : List (Degree × Bool))
    (loads : Loads) (hv : ValidLoads a b loads) :
    ValidLoads a b (runActual a b ranking priority events loads) := by
  induction events generalizing loads with
  | nil => exact hv
  | cons dc ds ih => exact ih _ (step_valid a b ranking priority loads dc.1 dc.2 hv)

theorem unsaturated_actual_total (a b : ℕ) (ranking priority : Bool) (word : List Degree)
    (cs : List Bool) (hc : cs.length=word.length)
    (hu : Unsaturated a b (runActual a b ranking priority (word.zip cs) (0,0))) :
    (runActual a b ranking priority (word.zip cs) (0,0)).1 +
      (runActual a b ranking priority (word.zip cs) (0,0)).2 = activeTrials false word := by
  rw [run_eq_free_of_unsaturated a b ranking priority (word.zip cs) (0,0) hu]
  simpa using runFree_total ranking priority word cs (0,0) hc

theorem zip_snoc (word : List Degree) (cs : List Bool) (hc : cs.length=word.length) (d : Degree) (c : Bool) :
    (word++[d]).zip (cs++[c]) = word.zip cs ++ [(d,c)] := by
  induction word generalizing cs with
  | nil => have he : cs=[] := List.length_eq_zero_iff.mp hc; subst cs; rfl
  | cons x xs ih =>
    cases cs with
    | nil => simp at hc
    | cons y ys => simpa using ih ys (by simpa using hc)

theorem runActual_snoc (a b : ℕ) (ranking priority : Bool) (word : List Degree) (cs : List Bool)
    (hc : cs.length=word.length) (d : Degree) (c : Bool) (loads : Loads) :
    runActual a b ranking priority ((word++[d]).zip (cs++[c])) loads =
      step a b ranking priority (runActual a b ranking priority (word.zip cs) loads) d c := by
  rw [zip_snoc word cs hc d c]
  simp [runActual, List.foldl_append]

theorem coinAverage_next_state (a b : ℕ) (ranking priority : Bool) (pre : List Degree)
    (d : Degree) (f : Loads → ℚ) :
    coinAverage pre.length (fun cs =>
      (f (step a b ranking priority (runActual a b ranking priority (pre.zip cs) (0,0)) d false) +
       f (step a b ranking priority (runActual a b ranking priority (pre.zip cs) (0,0)) d true))/2) =
    coinAverage (pre++[d]).length (fun cs => f (runActual a b ranking priority ((pre++[d]).zip cs) (0,0))) := by
  rw [coinAverage_div,coinAverage_add]
  simp only [List.length_append,List.length_singleton]
  rw [coinAverage_snoc]
  congr 1
  apply congrArg₂ (fun x y : ℚ => x+y)
  · apply coinAverage_congr
    intro cs hc
    rw [runActual_snoc a b ranking priority pre cs (coinWords_mem_length _ cs hc)]
  · apply coinAverage_congr
    intro cs hc
    rw [runActual_snoc a b ranking priority pre cs (coinWords_mem_length _ cs hc)]

def rewardKernel (a b K : ℕ) (ranking priority : Bool) : List Degree → Loads → ℚ
  | [], _ => 0
  | d::ds, loads =>
    (if Unsaturated a b loads then continuationGain (a+b) K d ds (loads.1+loads.2) else 0) +
      (rewardKernel a b K ranking priority ds (step a b ranking priority loads d false) +
       rewardKernel a b K ranking priority ds (step a b ranking priority loads d true))/2

theorem tailKernel_reward_decomposition (a b K : ℕ) (ranking priority : Bool)
    (word : List Degree) (loads : Loads) (hv : ValidLoads a b loads) :
    tailKernel a b ranking priority K word loads =
      continuationKernel (a+b) K word (loads.1+loads.2) + rewardKernel a b K ranking priority word loads := by
  induction word generalizing loads with
  | nil =>
    have hm : loads.1+loads.2 ≤ a+b := add_le_add hv.1 hv.2
    simp [tailKernel,continuationKernel,rewardKernel,min_eq_right hm]
  | cons d ds ih =>
    rw [tailKernel, ih _ (step_valid a b ranking priority loads d false hv),
      ih _ (step_valid a b ranking priority loads d true hv)]
    simp only [rewardKernel]
    by_cases hu : Unsaturated a b loads
    · rw [if_pos hu, step_total_unsaturated a b ranking priority loads d false hu,
        step_total_unsaturated a b ranking priority loads d true hu]
      unfold continuationGain
      ring
    · rw [if_neg hu]
      have he := saturated_continuation_step a b K ranking priority d ds loads hv hu
      linarith

def prefixExpansion (a b K : ℕ) (ranking priority : Bool) (pre : List Degree) : List Degree → ℚ
  | [] => 0
  | d::ds => survivalProbability a b ranking priority pre *
      continuationGain (a+b) K d ds (activeTrials false pre) +
      prefixExpansion a b K ranking priority (pre++[d]) ds

theorem average_prefix_gain (a b K : ℕ) (ranking priority : Bool) (pre : List Degree)
    (d : Degree) (ds : List Degree) :
    coinAverage pre.length (fun cs =>
      let loads := runActual a b ranking priority (pre.zip cs) (0,0)
      if Unsaturated a b loads then continuationGain (a+b) K d ds (loads.1+loads.2) else 0) =
      survivalProbability a b ranking priority pre * continuationGain (a+b) K d ds (activeTrials false pre) := by
  rw [survivalProbability_average, ← coinAverage_mul_const]
  apply coinAverage_congr
  intro cs hc
  by_cases hu : Unsaturated a b (runActual a b ranking priority (pre.zip cs) (0,0))
  · simp only [hu,if_true,one_mul]
    rw [unsaturated_actual_total a b ranking priority pre cs (coinWords_mem_length _ cs hc) hu]
  · simp only [hu,if_false,zero_mul]

theorem rewardKernel_prefix_expansion (a b K : ℕ) (ranking priority : Bool)
    (pre word : List Degree) :
    coinAverage pre.length (fun cs =>
      rewardKernel a b K ranking priority word (runActual a b ranking priority (pre.zip cs) (0,0))) =
      prefixExpansion a b K ranking priority pre word := by
  induction word generalizing pre with
  | nil => simp [rewardKernel,prefixExpansion,coinAverage_const]
  | cons d ds ih =>
    simp only [rewardKernel,prefixExpansion]
    rw [coinAverage_add,average_prefix_gain,coinAverage_next_state,ih]

/-- Exact source tail expansion; no probability-identity hypothesis is required. -/
theorem source_tail_expansion (a b K : ℕ) (ranking priority : Bool) (word : List Degree) :
    tailKernel a b ranking priority K word (0,0) =
      continuationKernel (a+b) K word 0 + prefixExpansion a b K ranking priority [] word := by
  rw [tailKernel_reward_decomposition a b K ranking priority word (0,0) (by constructor <;> omega)]
  have he := rewardKernel_prefix_expansion a b K ranking priority [] word
  simp only [List.length_nil,coinAverage_zero,List.zip_nil_right,runActual,List.foldl_nil] at he
  simpa only [Nat.zero_add] using congrArg (fun x => continuationKernel (a+b) K word 0+x) he

theorem prefixExpansion_dominance (r q K : ℕ) (hrq : r ≤ q) (hregion : QuadraticRegion r q)
    (pre word : List Degree) :
    (prefixExpansion (r+1) (q+1) K true false pre word +
     prefixExpansion (r+1) (q+1) K true true pre word)/2 ≤
      prefixExpansion (r+1) (q+1) K false false pre word := by
  induction word generalizing pre with
  | nil => simp [prefixExpansion]
  | cons d ds ih =>
    have hs := source_survival_dominance r q hrq hregion pre
    have hg := continuationGain_nonnegative ((r+1)+(q+1)) K d ds (activeTrials false pre)
    have hm := mul_le_mul_of_nonneg_right hs hg
    have ht := ih (pre++[d])
    simp only [prefixExpansion]
    nlinarith

theorem fixed_sufficiency (r q : ℕ) (hrq : r ≤ q) (hregion : QuadraticRegion r q) :
    FixedDominance (r+1) (q+1) := by
  intro word K
  have h := prefixExpansion_dominance r q K hrq hregion [] word
  have hk : (tailKernel (r+1) (q+1) true false K word (0,0) +
      tailKernel (r+1) (q+1) true true K word (0,0))/2 ≤
      tailKernel (r+1) (q+1) false false K word (0,0) := by
    rw [source_tail_expansion,source_tail_expansion,source_tail_expansion]
    linarith
  rw [tailKernel_rkCount,tailKernel_rvCount] at hk
  have hp : (0 : ℚ) < 2^word.length := by positivity
  have hc := (div_le_div_iff₀ (show (0 : ℚ) < 2^(word.length+1) by positivity) hp).mp hk
  rw [pow_succ] at hc
  have hn : (rkCount (r+1) (q+1) word K : ℚ) ≤ 2*(rvCount (r+1) (q+1) word K : ℚ) := by
    apply (mul_le_mul_right hp).mp
    nlinarith
  exact_mod_cast hn

theorem capacityRegion_succ (r q : ℕ) :
    CapacityRegion (r+1) (q+1) ↔ QuadraticRegion r q := by
  unfold CapacityRegion QuadraticRegion
  push_cast
  constructor <;> intro h <;> nlinarith

theorem capacityRegion_implies_fixed (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (h : CapacityRegion a b) : FixedDominance a b := by
  cases a with
  | zero => omega
  | succ r =>
    cases b with
    | zero => omega
    | succ q => exact fixed_sufficiency r q (by omega) ((capacityRegion_succ r q).mp h)

end TwoBin
