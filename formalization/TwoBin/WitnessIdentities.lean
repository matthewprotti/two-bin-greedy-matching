import TwoBin.UniformWitness

namespace TwoBin

theorem factorial_pred_rat (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℚ) = (n : ℚ)*((n-1).factorial : ℚ) := by
  cases n with
  | zero => omega
  | succ n => simp [Nat.factorial_succ]

theorem twoFlexCoefficient_boundary_factorial (r q : ℕ) (hN : 2 ≤ r+q) :
    twoFlexCoefficient r q (r+q) =
      ((r : ℚ)+(q : ℚ)-((q : ℚ)-(r : ℚ))^2) *
        ((r+q-2).factorial : ℚ)/((r.factorial : ℚ)*(q.factorial : ℚ)) := by
  have h1 := binomial_factorial_bridge r q 1 1 (r+q-2) (by omega)
  have h2 := binomial_factorial_bridge q r 1 1 (r+q-2) (by omega)
  have h3 := binomial_factorial_bridge r q 0 2 (r+q-2) (by omega)
  have h4 := binomial_factorial_bridge q r 0 2 (r+q-2) (by omega)
  simp only [Nat.cast_one,Nat.cast_zero,sub_zero] at h1 h2 h3 h4
  unfold twoFlexCoefficient
  rw [h1,h2,h3,h4]
  simp only [fallingRat]
  ring

/-- Paper equation (17), as an identity for the actual matching probabilities. -/
theorem fixedWitness_closed_formula (r q : ℕ) (hN : 2 ≤ r+q) :
    matchingGap (r+1) (q+1) (r+q+1) (fixedWitness r q) =
      (((r+q).choose r : ℚ)/2^(r+q)) *
        (((r : ℚ)+(q : ℚ)-((q : ℚ)-(r : ℚ))^2) /
          (2*((r : ℚ)+(q : ℚ))*((r : ℚ)+(q : ℚ)-1))) := by
  rw [fixedWitness_gap r q hN,twoFlexCoefficient_boundary_factorial r q hN,
    Nat.cast_choose ℚ (show r ≤ r+q by omega)]
  have he : r+q-r=q := by omega
  rw [he,factorial_pred_rat (r+q) (by omega),factorial_pred_rat (r+q-1) (by omega)]
  have hsub : ((r+q-1 : ℕ) : ℚ)=(r : ℚ)+(q : ℚ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ r+q by omega),Nat.cast_add,Nat.cast_one]
  rw [hsub]
  rw [pow_succ (2 : ℚ) (r+q)]
  simp only [Nat.sub_sub,Nat.cast_add]
  have hr : (r.factorial : ℚ) ≠ 0 := by positivity
  have hq : (q.factorial : ℚ) ≠ 0 := by positivity
  have hp : (2 : ℚ)^(r+q) ≠ 0 := by positivity
  have hN' : (2 : ℚ) ≤ (r : ℚ)+(q : ℚ) := by exact_mod_cast hN
  have hn0 : (r : ℚ)+(q : ℚ) ≠ 0 := by linarith
  have hn1 : (r : ℚ)+(q : ℚ)-1 ≠ 0 := by linarith
  field_simp
  ring

/-- Paper equation (23), averaged over the original labeled-arrival sample space. -/
theorem uniformWitness_closed_formula (r q : ℕ) (hN : 2 ≤ r+q) :
    randomMatchingGap (r+1) (q+1) (r+q+1) (uniformWitness r q) /
      ((arrivalOrders (uniformWitness r q)).length : ℚ) =
      (((r+q).choose r : ℚ)/2^(r+q)) *
        (2*((r : ℚ)+(q : ℚ)+2)*witnessPolynomial ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2)) /
        (((r : ℚ)+(q : ℚ))*witnessDenominator ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2)) := by
  have hl : (uniformWitness r q).length=r+q+1 := by simp only [uniformWitness,List.length_cons,List.length_replicate]; omega
  rw [uniformWitness_gap r q hN,weightedCoefficientSum_closed,arrivalOrders_length,hl,
    Nat.factorial_succ,Nat.cast_mul,factorial_pred_rat (r+q) (by omega)]
  rw [pow_succ (2 : ℚ) (r+q)]
  simp only [Nat.cast_add,Nat.cast_one]
  have hr : (0 : ℚ) ≤ r := by positivity
  have hq : (0 : ℚ) ≤ q := by positivity
  have hu : ((q : ℚ)-(r : ℚ))^2 ≤ ((r : ℚ)+(q : ℚ))^2 := by nlinarith [mul_nonneg hr hq]
  have hd := witness_denominator_positive ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2) (by positivity) hu
  have hN' : (2 : ℚ) ≤ (r : ℚ)+(q : ℚ) := by exact_mod_cast hN
  have hn0 : (r : ℚ)+(q : ℚ) ≠ 0 := by linarith
  have hn1 : (r : ℚ)+(q : ℚ)+1 ≠ 0 := by positivity
  have hf : ((r+q-1).factorial : ℚ) ≠ 0 := by positivity
  have hp : (2 : ℚ)^(r+q) ≠ 0 := by positivity
  field_simp [ne_of_gt hd]
  ring

end TwoBin
