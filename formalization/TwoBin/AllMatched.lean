import TwoBin.WordStatistics

namespace TwoBin

theorem continuationKernel_too_few (S K : ℕ) (word : List Degree) (m : ℕ)
    (h : m+word.length < K) : continuationKernel S K word m = 0 := by
  induction word generalizing m with
  | nil => simp only [List.length_nil,Nat.add_zero] at h; simp [continuationKernel,show ¬ K ≤ min S m by omega]
  | cons d ds ih =>
    have h1 := ih m (by simp only [List.length_cons] at h; omega)
    have h2 := ih (min S (m+1)) (by simp only [List.length_cons] at h; omega)
    cases d <;> simp [continuationKernel,h1,h2]

theorem continuationKernel_all_matched (S K : ℕ) (word : List Degree) (m : ℕ)
    (hp : PositiveWord word) (hs : m+word.length=K) (hk : K ≤ S) :
    continuationKernel S K word m = 1/2^(activeTrials true word) := by
  induction word generalizing m with
  | nil => simp only [List.length_nil,Nat.add_zero] at hs; subst K; simp [continuationKernel,min_eq_right hk,activeTrials]
  | cons d ds ih =>
    have hd := hp d (by simp)
    have hds : PositiveWord ds := by intro x hx; exact hp x (by simp [hx])
    have hm : m+1 ≤ S := by simp only [List.length_cons] at hs; omega
    have hnext := ih (m+1) hds (by simp only [List.length_cons] at hs; omega)
    have hmiss := continuationKernel_too_few S K ds m (by simp only [List.length_cons] at hs; omega)
    cases d with
    | zero => exact False.elim (hd rfl)
    | flexible => simpa [continuationKernel,activeTrials,min_eq_right hm] using hnext
    | singleton =>
      simp only [continuationKernel,min_eq_right hm,hnext,hmiss,activeTrials,pow_succ]
      ring

theorem continuationGain_zero (S K : ℕ) (ds : List Degree) (m : ℕ) :
    continuationGain S K .zero ds m = 0 := by simp [continuationGain,continuationKernel,activeTrials]

theorem continuationGain_flexible (S K : ℕ) (ds : List Degree) (m : ℕ) :
    continuationGain S K .flexible ds m = 0 := by
  simp [continuationGain,continuationKernel,activeTrials,continuationKernel_clamp]

theorem continuationGain_all_matched (S K : ℕ) (ds : List Degree) (m : ℕ)
    (hp : PositiveWord ds) (hs : m+ds.length+1=K) (hk : K ≤ S) :
    continuationGain S K .singleton ds m = 1/2^(activeTrials true ds+1) := by
  have hm : m+1 ≤ S := by omega
  have hnext := continuationKernel_all_matched S K ds (m+1) hp (by omega) hk
  have hmiss := continuationKernel_too_few S K ds m (by omega)
  simp only [continuationGain,continuationKernel,activeTrials,min_eq_right hm,hnext,hmiss,pow_succ]
  ring

def sourceSurvivalGap (a b : ℕ) (word : List Degree) : ℚ :=
  survivalProbability a b false false word -
    (survivalProbability a b true false word + survivalProbability a b true true word)/2

def matchingGap (a b K : ℕ) (word : List Degree) : ℚ :=
  tailKernel a b false false K word (0,0) -
    (tailKernel a b true false K word (0,0) + tailKernel a b true true K word (0,0))/2

def prefixGap (a b K : ℕ) (pre word : List Degree) : ℚ :=
  prefixExpansion a b K false false pre word -
    (prefixExpansion a b K true false pre word + prefixExpansion a b K true true pre word)/2

theorem matchingGap_prefix (a b K : ℕ) (word : List Degree) : matchingGap a b K word = prefixGap a b K [] word := by
  unfold matchingGap prefixGap
  rw [source_tail_expansion,source_tail_expansion,source_tail_expansion]
  ring

theorem prefixGap_nil (a b K : ℕ) (pre : List Degree) : prefixGap a b K pre [] = 0 := by
  simp [prefixGap,prefixExpansion]

theorem prefixGap_cons (a b K : ℕ) (pre : List Degree) (d : Degree) (ds : List Degree) :
    prefixGap a b K pre (d::ds) = sourceSurvivalGap a b pre *
      continuationGain (a+b) K d ds (activeTrials false pre) + prefixGap a b K (pre++[d]) ds := by
  unfold prefixGap sourceSurvivalGap
  simp only [prefixExpansion]
  ring

theorem matchingGap_counts (a b K : ℕ) (word : List Degree) :
    matchingGap a b K word =
      (2*(rvCount a b word K : ℚ)-(rkCount a b word K : ℚ))/(2*2^word.length) := by
  unfold matchingGap
  rw [tailKernel_rvCount,tailKernel_rkCount,pow_succ]
  ring

theorem matchingGap_nonnegative_of_fixed (a b : ℕ) (h : FixedDominance a b) (K : ℕ) (word : List Degree) :
    0 ≤ matchingGap a b K word := by
  rw [matchingGap_counts]
  apply div_nonneg _ (by positivity)
  have hc : (rkCount a b word K : ℚ) ≤ 2*(rvCount a b word K : ℚ) := by exact_mod_cast h word K
  linarith

end TwoBin
