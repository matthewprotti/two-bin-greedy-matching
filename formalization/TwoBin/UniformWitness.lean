import TwoBin.Insertion
import TwoBin.UniformAlgebra

namespace TwoBin

def randomMatchingGap (a b K : ℕ) (word : List Degree) : ℚ :=
  ((arrivalOrders word).map (matchingGap a b K)).sum

theorem sum_matchingGap_counts (a b K n : ℕ) (orders : List (List Degree))
    (hlen : ∀ w ∈ orders, w.length=n) :
    (orders.map (matchingGap a b K)).sum =
      (2*((orders.map (fun w => rvCount a b w K)).sum : ℚ) -
        ((orders.map (fun w => rkCount a b w K)).sum : ℚ))/(2*2^n) := by
  induction orders with
  | nil => simp
  | cons w ws ih =>
    have hw := hlen w (by simp)
    have ht : ∀ x ∈ ws, x.length=n := by intro x hx; exact hlen x (by simp [hx])
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,matchingGap_counts,hw,ih ht]
    ring

theorem randomMatchingGap_nonnegative (a b : ℕ) (h : RandomOrderDominance a b) (K : ℕ) (word : List Degree) :
    0 ≤ randomMatchingGap a b K word := by
  unfold randomMatchingGap
  rw [sum_matchingGap_counts a b K word.length _ (by intro w hw; exact arrivalOrders_mem_length word w hw)]
  apply div_nonneg _ (by positivity)
  have hc : (((arrivalOrders word).map (fun w => rkCount a b w K)).sum : ℚ) ≤
      2*(((arrivalOrders word).map (fun w => rvCount a b w K)).sum : ℚ) := by exact_mod_cast h word K
  linarith

theorem sum_range_lt_const (n k : ℕ) (c : ℚ) :
    (∑ i ∈ Finset.range n, if i<k then c else 0) = ((min n k : ℕ) : ℚ)*c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hn : n<k
    · rw [if_pos hn,min_eq_left (by omega : n ≤ k),min_eq_left (by omega : n+1 ≤ k)]
      push_cast
      ring
    · rw [if_neg hn,min_eq_right (by omega : k ≤ n),min_eq_right (by omega : k ≤ n+1)]
      ring

theorem sum_insertion_indicator (s t : ℕ) (ht : t<s+2) (c : ℚ) :
    (∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+2), if i<t-1 ∧ j<t then c else 0) =
      2*(t.choose 2 : ℚ)*c := by
  have hi (i : ℕ) :
      (∑ j ∈ Finset.range (s+2), if i<t-1 ∧ j<t then c else 0) =
        if i<t-1 then (t : ℚ)*c else 0 := by
    by_cases h : i<t-1
    · simp only [h,true_and,if_true]
      rw [sum_range_lt_const,min_eq_right (by omega : t ≤ s+2)]
    · simp [h]
  simp_rw [hi]
  rw [sum_range_lt_const,min_eq_right (by omega : t-1 ≤ s+1)]
  cases t with
  | zero => norm_num
  | succ t =>
    rw [Nat.cast_choose_two ℚ]
    push_cast
    ring

def uniformWitness (r q : ℕ) : List Degree :=
  .flexible::.flexible::List.replicate (r+q-1) .singleton

/-- Exact sum of actual matching gaps over every labeled arrival order. -/
theorem uniformWitness_gap (r q : ℕ) (hN : 2 ≤ r+q) :
    randomMatchingGap (r+1) (q+1) (r+q+1) (uniformWitness r q) =
      (2*((r+q-1).factorial : ℚ))*weightedCoefficientSum r q / 2^(r+q+1) := by
  let s := r+q-1
  have hs1 : s+1=r+q := by dsimp [s]; omega
  have hs2 : s+2=r+q+1 := by omega
  have hterm (i j : ℕ) (hi : i ∈ Finset.range (s+1)) (hj : j ∈ Finset.range (s+2)) :
      matchingGap (r+1) (q+1) (r+q+1) (twiceInserted s i j) =
        (∑ t ∈ Finset.range (r+q+1), if i<t-1 ∧ j<t then twoFlexCoefficient r q t else 0)/2^(r+q+1) := by
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [matchingGap_two_profile r q _ (twiceInserted_positive s i j)
      (twiceInserted_flexible_count s i j hi' hj')
      (by rw [twiceInserted_length s i j hi' hj',hs2])]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    simp only [twiceInserted_prefix_two s i j t hi' hj']
  have hsum : (∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+2),
      ∑ t ∈ Finset.range (r+q+1), if i<t-1 ∧ j<t then twoFlexCoefficient r q t else 0) =
      2*weightedCoefficientSum r q := by
    calc
      _ = ∑ i ∈ Finset.range (s+1), ∑ t ∈ Finset.range (r+q+1),
          ∑ j ∈ Finset.range (s+2), if i<t-1 ∧ j<t then twoFlexCoefficient r q t else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ t ∈ Finset.range (r+q+1), ∑ i ∈ Finset.range (s+1),
          ∑ j ∈ Finset.range (s+2), if i<t-1 ∧ j<t then twoFlexCoefficient r q t else 0 := by rw [Finset.sum_comm]
      _ = ∑ t ∈ Finset.range (r+q+1), 2*(t.choose 2 : ℚ)*twoFlexCoefficient r q t := by
        apply Finset.sum_congr rfl
        intro t ht
        exact sum_insertion_indicator s t (by have := Finset.mem_range.mp ht; omega) _
      _ = _ := by unfold weightedCoefficientSum; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht; ring
  unfold randomMatchingGap uniformWitness
  rw [arrivalOrders_two_flexible_sum]
  change (s.factorial : ℚ)*(∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+2),
    matchingGap (r+1) (q+1) (r+q+1) (twiceInserted s i j)) = _
  have hterms : (∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+2),
      matchingGap (r+1) (q+1) (r+q+1) (twiceInserted s i j)) =
      (∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+2),
        ∑ t ∈ Finset.range (r+q+1), if i<t-1 ∧ j<t then twoFlexCoefficient r q t else 0)/2^(r+q+1) := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Finset.sum_div] using hterm i j hi hj
  rw [hterms,hsum]
  dsimp [s]
  ring

theorem uniformWitness_gap_negative (r q : ℕ) (h : ¬ QuadraticRegion r q) :
    randomMatchingGap (r+1) (q+1) (r+q+1) (uniformWitness r q) < 0 := by
  rw [uniformWitness_gap r q (excluded_total_ge_two r q h)]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by positivity) (weightedCoefficientSum_negative r q h)) (by positivity)

theorem random_implies_quadratic (r q : ℕ) (h : RandomOrderDominance (r+1) (q+1)) : QuadraticRegion r q := by
  by_contra hn
  have hneg := uniformWitness_gap_negative r q hn
  have hpos := randomMatchingGap_nonnegative (r+1) (q+1) h (r+q+1) (uniformWitness r q)
  linarith

/-- The full fixed-order and uniform-random-order classification, for the original source counts. -/
theorem full_classification : FullClassificationTarget := by
  intro a b ha hab
  constructor
  · exact fixed_classification a b ha hab
  · constructor
    · intro h
      exact fixedDominance_implies_randomOrderDominance a b (capacityRegion_implies_fixed a b ha hab h)
    · intro h
      cases a with
      | zero => omega
      | succ r =>
        cases b with
        | zero => omega
        | succ q => exact (capacityRegion_succ r q).mpr (random_implies_quadratic r q h)

end TwoBin
