import TwoBin.Paired
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-! Integer-index binomial coefficients and the full zero-support factorial bridge. -/
namespace TwoBin

/-- Binomial coefficient with integer lower index, zero outside its support. -/
def binomialZ (n : ℕ) (k : ℤ) : ℚ :=
  if 0 ≤ k then (n.choose k.toNat : ℚ) else 0

theorem binomialZ_negative (n : ℕ) (k : ℤ) (hk : k < 0) :
    binomialZ n k = 0 := by simp [binomialZ, show ¬ 0 ≤ k by omega]

theorem binomialZ_above (n : ℕ) (k : ℤ) (hk : (n : ℤ) < k) :
    binomialZ n k = 0 := by
  have hk0 : 0 ≤ k := by omega
  have hkn : n < k.toNat := by omega
  simp [binomialZ, hk0, Nat.choose_eq_zero_of_lt hkn]

theorem falling_nat_eq_descFactorial (n k : ℕ) :
    falling (n : ℤ) k = (n.descFactorial k : ℤ) := by
  induction k with
  | zero => simp [falling]
  | succ k ih =>
    rw [falling, Nat.descFactorial_succ, Nat.cast_mul, ← ih]
    by_cases hk : k ≤ n
    · rw [Nat.cast_sub hk]
      ring
    · rw [falling_zero_of_lt k n (by omega)]
      simp

theorem fallingRat_factorial (n k : ℕ) (hk : k ≤ n) :
    fallingRat (n : ℚ) k = (n.factorial : ℚ) / ((n-k).factorial : ℚ) := by
  rw [fallingRat_nat, falling_nat_eq_descFactorial, Int.cast_natCast]
  have h := congrArg (fun x : ℕ => (x : ℚ)) (Nat.factorial_mul_descFactorial hk)
  simp only [Nat.cast_mul] at h
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (n-k))).mpr
  simpa [mul_comm] using h

theorem fallingRat_zero_of_lt (n k : ℕ) (hk : n < k) :
    fallingRat (n : ℚ) k = 0 := by
  rw [fallingRat_nat, falling_zero_of_lt k n hk]
  norm_num

/-- Exact factorial-to-binomial identity, including both ways support can vanish. -/
theorem binomial_factorial_bridge (r q u v s : ℕ) (hs : s+u+v = r+q) :
    binomialZ s ((r : ℤ)-(u : ℤ)) =
      fallingRat (r : ℚ) u * fallingRat (q : ℚ) v *
        ((s.factorial : ℚ) / ((r.factorial : ℚ)*(q.factorial : ℚ))) := by
  by_cases hu : u ≤ r
  · by_cases hv : v ≤ q
    · have hru : 0 ≤ (r : ℤ)-(u : ℤ) := by omega
      have he : ((r : ℤ)-(u : ℤ)).toNat = r-u := by omega
      have hk : r-u ≤ s := by omega
      have hsub : s-(r-u) = q-v := by omega
      rw [binomialZ, if_pos hru, he, Nat.cast_choose ℚ hk, hsub,
        fallingRat_factorial r u hu, fallingRat_factorial q v hv]
      have hr0 : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
      have hq0 : (q.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
      have hru0 : ((r-u).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r-u)
      have hqv0 : ((q-v).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (q-v)
      field_simp
      ring
    · rw [binomialZ_above s _ (by omega), fallingRat_zero_of_lt q v (by omega)]
      simp
  · rw [binomialZ_negative s _ (by omega), fallingRat_zero_of_lt r u (by omega)]
    simp

/-- Paper Corollary 4, with integer lower indices and all vanishing cases. -/
theorem paired_binomial_shift (r q u v s : ℕ) (hrq : r ≤ q)
    (hregion : QuadraticRegion r q) (hs : s+u+v = r+q) :
    binomialZ s (r : ℤ) + binomialZ s (q : ℤ) ≤
      binomialZ s ((r : ℤ)-(u : ℤ)) + binomialZ s ((q : ℤ)-(u : ℤ)) := by
  have hp := quadratic_implies_paired r q hrq hregion u v
  have hp' : fallingRat (r : ℚ) (u+v) + fallingRat (q : ℚ) (u+v) ≤
      fallingRat (r : ℚ) u * fallingRat (q : ℚ) v +
      fallingRat (q : ℚ) u * fallingRat (r : ℚ) v := by
    simp only [fallingRat_nat]
    exact_mod_cast hp
  have hc : 0 ≤ (s.factorial : ℚ) / ((r.factorial : ℚ)*(q.factorial : ℚ)) := by positivity
  have hm := mul_le_mul_of_nonneg_right hp' hc
  have h1 := binomial_factorial_bridge r q 0 (u+v) s (by omega)
  have h2 := binomial_factorial_bridge q r 0 (u+v) s (by omega)
  simp only [Nat.cast_zero, sub_zero, fallingRat, one_mul] at h1 h2
  rw [h1,h2,binomial_factorial_bridge r q u v s hs,
    binomial_factorial_bridge q r u v s (by omega)]
  simpa only [mul_add, add_mul, mul_comm, add_comm] using hm

end TwoBin
