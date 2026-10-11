import TwoBin.GapFormula

namespace TwoBin

theorem activeTrials_singletons (ranking : Bool) (n : ℕ) :
    activeTrials ranking (List.replicate n Degree.singleton) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,activeTrials,ih]

theorem forcedChoices_singletons (ranking priority : Bool) (n : ℕ) :
    forcedChoices ranking priority (List.replicate n Degree.singleton) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,forcedChoices,ih]

theorem prefixGap_leading_singletons (r q K : ℕ) (pre tail : List Degree) (n : ℕ)
    (hf : forcedChoices true false pre ≤ 1) :
    prefixGap (r+1) (q+1) K pre (List.replicate n Degree.singleton ++ tail) =
      prefixGap (r+1) (q+1) K (pre++List.replicate n Degree.singleton) tail := by
  induction n generalizing pre with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,prefixGap_cons,sourceSurvivalGap_zero r q pre hf,
      zero_mul,zero_add]
    have hf' : forcedChoices true false (pre++[Degree.singleton]) ≤ 1 := by
      simpa [forcedChoices_append,forcedChoices] using hf
    simpa [List.replicate_succ,List.append_assoc] using ih (pre++[Degree.singleton]) hf'

theorem prefixGap_flexible (a b K : ℕ) (pre tail : List Degree) :
    prefixGap a b K pre (.flexible::tail) = prefixGap a b K (pre++[.flexible]) tail := by
  rw [prefixGap_cons,continuationGain_flexible]
  ring

def fixedWitness (r q : ℕ) : List Degree :=
  List.replicate (r+q-2) .singleton ++ [.flexible,.flexible,.singleton]

/-- Actual all-matched probability difference for the fixed-order witness. -/
theorem fixedWitness_gap (r q : ℕ) (hN : 2 ≤ r+q) :
    matchingGap (r+1) (q+1) (r+q+1) (fixedWitness r q) =
      twoFlexCoefficient r q (r+q) / 2^(r+q+1) := by
  rw [matchingGap_prefix]
  unfold fixedWitness
  rw [prefixGap_leading_singletons r q (r+q+1) [] _ _ (by simp [forcedChoices])]
  simp only [List.nil_append]
  rw [prefixGap_flexible,prefixGap_flexible,prefixGap_cons,prefixGap_nil,add_zero]
  have hp : activeTrials false
      ((List.replicate (r+q-2) Degree.singleton ++ [.flexible]) ++ [.flexible]) = r+q := by
    simp only [activeTrials_append,activeTrials_singletons,activeTrials,Bool.false_eq_true,if_false]
    omega
  have hf : forcedChoices true false
      ((List.replicate (r+q-2) Degree.singleton ++ [.flexible]) ++ [.flexible]) = 2 := by
    simp [forcedChoices_append,forcedChoices_singletons,forcedChoices]
  rw [sourceSurvivalGap_two r q _ hf (by rw [hp]),hp]
  have hg := continuationGain_all_matched ((r+1)+(q+1)) (r+q+1) [] (r+q)
    (by simp [PositiveWord]) (by simp) (by omega)
  simp only [activeTrials,zero_add] at hg
  rw [hg,pow_succ]
  ring

theorem fixedWitness_gap_negative (r q : ℕ) (h : ¬ QuadraticRegion r q) :
    matchingGap (r+1) (q+1) (r+q+1) (fixedWitness r q) < 0 := by
  rw [fixedWitness_gap r q (excluded_total_ge_two r q h)]
  exact div_neg_of_neg_of_pos (twoFlexCoefficient_boundary_negative r q h) (by positivity)

theorem fixed_implies_quadratic (r q : ℕ) (h : FixedDominance (r+1) (q+1)) : QuadraticRegion r q := by
  by_contra hn
  have hneg := fixedWitness_gap_negative r q hn
  have hpos := matchingGap_nonnegative_of_fixed (r+1) (q+1) h (r+q+1) (fixedWitness r q)
  linarith

/-- Complete fixed-order classification for the unchanged literal source model. -/
theorem fixed_classification (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    CapacityRegion a b ↔ FixedDominance a b := by
  constructor
  · exact capacityRegion_implies_fixed a b ha hab
  · intro h
    cases a with
    | zero => omega
    | succ r =>
      cases b with
      | zero => omega
      | succ q => exact (capacityRegion_succ r q).mpr (fixed_implies_quadratic r q h)

end TwoBin
