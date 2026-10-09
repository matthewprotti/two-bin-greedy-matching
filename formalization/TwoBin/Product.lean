import TwoBin.Falling

/-! The cross-multiplied product bound and the integer endpoint bounds. -/
namespace TwoBin

theorem gap_lower_bound (r d : ℕ) (hd : 2 ≤ d)
    (h : (d : ℤ) * ((d : ℤ) - 1) ≤ 2 * (r : ℤ)) :
    (d : ℤ) - 1 ≤ (r : ℤ) := by
  have hd' : (2 : ℤ) ≤ d := by exact_mod_cast hd
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 2 by omega)
    (show (0 : ℤ) ≤ d - 1 by omega)]

theorem gap_interior_lower_bound (r d : ℕ) (hd : 2 ≤ d)
    (h : (d : ℤ) * ((d : ℤ) - 1) ≤ 2 * (r : ℤ)) :
    2 * (d : ℤ) - 3 ≤ (r : ℤ) := by
  by_cases htwo : d = 2
  · subst d
    norm_num at h ⊢
    omega
  · have hd' : (3 : ℤ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 2 by omega)
      (show (0 : ℤ) ≤ d - 3 by omega)]

theorem interior_endpoint (r d u v : ℕ) (hd : 2 ≤ d)
    (h : (d : ℤ) * ((d : ℤ) - 1) ≤ 2 * (r : ℤ))
    (hu : u < d) (hv : v < d) :
    (v : ℤ) - 1 ≤ (r : ℤ) - (u : ℤ) := by
  have := gap_interior_lower_bound r d hd h
  omega

/-- Paper equation (3), without division. -/
theorem product_ratio_bound (r d : ℕ) (hd : 2 ≤ d)
    (h : (d : ℤ) * ((d : ℤ) - 1) ≤ 2 * (r : ℤ))
    (u : ℕ) (hu : u < d) :
    ((d : ℤ) - (u : ℤ)) * falling ((r + d : ℕ) : ℤ) u ≤
      ((d : ℤ) + (u : ℤ)) * falling (r : ℤ) u := by
  induction u with
  | zero => simp [falling]
  | succ j ih =>
    have hjd : j < d := by omega
    have ih' := ih hjd
    have hr := gap_lower_bound r d hd h
    have hrj : (0 : ℤ) ≤ (r : ℤ) - (j : ℤ) := by omega
    have hdp : (0 : ℤ) < (d : ℤ) + (j : ℤ) := by omega
    have hdp1 : (0 : ℤ) ≤ (d : ℤ) + (j : ℤ) + 1 := by omega
    have hf := falling_nat_nonnegative j (r + d)
    have hs := product_step_nonnegative r d j h
    have hm1 := mul_le_mul_of_nonneg_right ih' (mul_nonneg hrj hdp1)
    have hm2 := mul_nonneg hs hf
    apply (mul_le_mul_left hdp).mp
    simp only [falling, Nat.cast_add, Nat.cast_succ]
    simp only [Nat.cast_add] at hm1 hm2
    nlinarith

/-- The beyond-support case is explicitly zero; otherwise compare the split factor. -/
theorem falling_add_le_mul (a b u v : ℕ) (h : a ≤ b + u) :
    falling (a : ℤ) (u + v) ≤ falling (a : ℤ) u * falling (b : ℤ) v := by
  by_cases hu : u ≤ a
  · rw [falling_add]
    have hc : ((a - u : ℕ) : ℤ) = (a : ℤ) - (u : ℤ) := by omega
    rw [← hc]
    exact mul_le_mul_of_nonneg_left
      (falling_nat_monotone v (a-u) b (by omega)) (falling_nat_nonnegative u a)
  · rw [falling_zero_of_lt u a (by omega), falling_zero_of_lt (u+v) a (by omega)]
    simp

theorem paired_large_left (r q u v : ℕ) (hrq : r ≤ q) (hu : q ≤ r + u) :
    falling (r : ℤ) (u + v) + falling (q : ℤ) (u + v) ≤
    falling (r : ℤ) u * falling (q : ℤ) v +
    falling (q : ℤ) u * falling (r : ℤ) v := by
  exact add_le_add (falling_add_le_mul r q u v (by omega))
    (falling_add_le_mul q r u v hu)

end TwoBin
