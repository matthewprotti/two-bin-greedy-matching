import TwoBin.AllMatched

namespace TwoBin

def twoFlexCoefficient (r q t : ℕ) : ℚ :=
  binomialZ (t-2) ((r : ℤ)-1) + binomialZ (t-2) ((q : ℤ)-1) -
    binomialZ (t-2) (r : ℤ) - binomialZ (t-2) (q : ℤ)

theorem ranking_last_step (r q t : ℕ) (ht : t ≤ r+q) (ht1 : 1 ≤ t) :
    rankingSurvivalFormula r q t t = rankingSurvivalFormula r q t (t-1) := by
  have hs := rankingSurvivalFormula_step r q t (t-1) ht
  have hn : t-1+1=t := by omega
  have e1 : ((t-1 : ℕ) : ℤ)-((t : ℤ)-(q : ℤ)-1) = (q : ℤ) := by omega
  have e2 : ((t-1 : ℕ) : ℤ)-((t : ℤ)-(r : ℤ)-1) = (r : ℤ) := by omega
  have hb1 := binomialZ_reflection (t-1) ((t : ℤ)-(q : ℤ)-1)
  have hb2 := binomialZ_reflection (t-1) ((t : ℤ)-(r : ℤ)-1)
  rw [e1] at hb1
  rw [e2] at hb2
  rw [hn,hb1,hb2] at hs
  have he : binomialZ (t-1) (q : ℤ)+binomialZ (t-1) (r : ℤ)-
      binomialZ (t-1) (r : ℤ)-binomialZ (t-1) (q : ℤ) = 0 := by ring
  rw [he,zero_div] at hs
  linarith

theorem sourceSurvivalGap_zero (r q : ℕ) (word : List Degree)
    (hf : forcedChoices true false word ≤ 1) : sourceSurvivalGap (r+1) (q+1) word = 0 := by
  unfold sourceSurvivalGap
  rw [rv_survival_formula,ranking_survival_formula]
  have hsplit := activeTrials_split word
  have hf0 := forcedChoices_nonnegative true false word
  by_cases ht : activeTrials false word ≤ r+q
  · rw [← pure_singleton_endpoint r q _ ht]
    by_cases hz : forcedChoices true false word = 0
    · have he : activeTrials false word=activeTrials true word := by omega
      rw [he]
      ring
    · have he : activeTrials true word=activeTrials false word-1 := by omega
      have ht1 : 1 ≤ activeTrials false word := by omega
      rw [he,ranking_last_step r q _ ht ht1]
      ring
  · have hz : r+q+1-activeTrials false word=0 := by omega
    simp [rvSurvivalFormula,rankingSurvivalFormula,hz,binomialWindow]

/-- Actual survival gap with exactly two flexible jobs, paper equation (19). -/
theorem sourceSurvivalGap_two (r q : ℕ) (word : List Degree)
    (hf : forcedChoices true false word = 2) (ht : activeTrials false word ≤ r+q) :
    sourceSurvivalGap (r+1) (q+1) word =
      twoFlexCoefficient r q (activeTrials false word) / 2^(activeTrials false word) := by
  have hsplit := activeTrials_split word
  have ht2 : 2 ≤ activeTrials false word := by omega
  have hsingle : activeTrials true word = activeTrials false word-2 := by omega
  unfold sourceSurvivalGap
  rw [rv_survival_formula,ranking_survival_formula,← pure_singleton_endpoint r q _ ht,
    ranking_last_step r q _ ht (by omega),hsingle]
  have hs := rankingSurvivalFormula_step r q (activeTrials false word) (activeTrials false word-2) ht
  have hn : activeTrials false word-2+1=activeTrials false word-1 := by omega
  have e1 : ((activeTrials false word-2 : ℕ) : ℤ)-
      ((activeTrials false word : ℤ)-(q : ℤ)-1) = (q : ℤ)-1 := by omega
  have e2 : ((activeTrials false word-2 : ℕ) : ℤ)-
      ((activeTrials false word : ℤ)-(r : ℤ)-1) = (r : ℤ)-1 := by omega
  have hb1 := binomialZ_reflection (activeTrials false word-2) ((activeTrials false word : ℤ)-(q : ℤ)-1)
  have hb2 := binomialZ_reflection (activeTrials false word-2) ((activeTrials false word : ℤ)-(r : ℤ)-1)
  rw [e1] at hb1
  rw [e2] at hb2
  have hp : (4 : ℚ)*2^(activeTrials false word-2) = 2^(activeTrials false word) := by
    calc
      _ = (2 : ℚ)^((activeTrials false word-2)+2) := by rw [pow_add]; norm_num; ring
      _ = _ := by congr 1; omega
  rw [hn,hb1,hb2,hp] at hs
  rw [hs]
  unfold twoFlexCoefficient
  ring

theorem excluded_total_ge_two (r q : ℕ) (h : ¬ QuadraticRegion r q) : 2 ≤ r+q := by
  by_contra hn
  have hr : r=0 ∨ r=1 := by omega
  have hq : q=0 ∨ q=1 := by omega
  rcases hr with rfl | rfl <;> rcases hq with rfl | rfl <;>
    norm_num [QuadraticRegion] at *

theorem twoFlexCoefficient_boundary_negative (r q : ℕ) (h : ¬ QuadraticRegion r q) :
    twoFlexCoefficient r q (r+q) < 0 := by
  have hN := excluded_total_ge_two r q h
  have h1 := binomial_factorial_bridge r q 1 1 (r+q-2) (by omega)
  have h2 := binomial_factorial_bridge q r 1 1 (r+q-2) (by omega)
  have h3 := binomial_factorial_bridge r q 0 2 (r+q-2) (by omega)
  have h4 := binomial_factorial_bridge q r 0 2 (r+q-2) (by omega)
  simp only [Nat.cast_one,Nat.cast_zero,sub_zero] at h1 h2 h3 h4
  unfold twoFlexCoefficient
  rw [h1,h2,h3,h4]
  simp only [fallingRat]
  have hp : (0 : ℚ) < ((r+q-2).factorial : ℚ)/((r.factorial : ℚ)*(q.factorial : ℚ)) := by positivity
  have hn : (r : ℚ)+(q : ℚ)-((q : ℚ)-(r : ℚ))^2 < 0 := by
    unfold QuadraticRegion at h
    have hz : (r : ℤ)+(q : ℤ) < ((q : ℤ)-(r : ℤ))^2 := lt_of_not_ge h
    have hq' : (r : ℚ)+(q : ℚ) < ((q : ℚ)-(r : ℚ))^2 := by exact_mod_cast hz
    linarith
  have hneg := mul_neg_of_neg_of_pos hn hp
  convert hneg using 1
  ring

end TwoBin
