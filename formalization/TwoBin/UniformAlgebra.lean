import TwoBin.GapFormula
import TwoBin.Witness
import Mathlib.Algebra.Ring.Int.Parity

namespace TwoBin

theorem hockey_range (n k : ℕ) :
    (∑ t ∈ Finset.range n, t.choose k) = n.choose (k+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ']; omega

theorem choose_two_product (t k : ℕ) :
    t.choose 2 * (t-2).choose k = (k+2).choose 2 * t.choose (k+2) := by
  by_cases ht : t < 2
  · rw [Nat.choose_eq_zero_of_lt ht, Nat.choose_eq_zero_of_lt (show t < k+2 by omega)]
    simp
  by_cases hk : k+2 ≤ t
  · have h := Nat.choose_mul (n:=t) (k:=k+2) (s:=2) hk (by omega)
    simpa [Nat.mul_comm] using h.symm
  · rw [Nat.choose_eq_zero_of_lt (show t-2 < k by omega),
      Nat.choose_eq_zero_of_lt (show t < k+2 by omega)]
    simp

theorem binomialZ_nat (n k : ℕ) : binomialZ n (k : ℤ) = (n.choose k : ℚ) := by
  simp [binomialZ]

theorem weighted_hockey (n r : ℕ) :
    (∑ t ∈ Finset.range n, (t.choose 2 : ℚ)*binomialZ (t-2) ((r : ℤ)-1)) =
      ((r+1).choose 2 : ℚ)*(n.choose (r+2) : ℚ) := by
  cases r with
  | zero => simp [binomialZ]
  | succ k =>
    have he : ((k+1 : ℕ) : ℤ)-1 = (k : ℤ) := by omega
    simp only [Nat.succ_eq_add_one,he,binomialZ_nat]
    have hp (t : ℕ) : (t.choose 2 : ℚ)*((t-2).choose k : ℚ) =
        ((k+2).choose 2 : ℚ)*(t.choose (k+2) : ℚ) := by exact_mod_cast choose_two_product t k
    simp_rw [hp]
    rw [← Finset.mul_sum]
    congr 1
    exact_mod_cast hockey_range n (k+2)

def weightedCoefficientSum (r q : ℕ) : ℚ :=
  ∑ t ∈ Finset.range (r+q+1), (t.choose 2 : ℚ)*twoFlexCoefficient r q t

theorem weightedCoefficientSum_expansion (r q : ℕ) :
    weightedCoefficientSum r q =
      ((r+1).choose 2 : ℚ)*((r+q+1).choose (r+2) : ℚ) -
      ((r+2).choose 2 : ℚ)*((r+q+1).choose (r+3) : ℚ) +
      ((q+1).choose 2 : ℚ)*((r+q+1).choose (q+2) : ℚ) -
      ((q+2).choose 2 : ℚ)*((r+q+1).choose (q+3) : ℚ) := by
  have h1 := weighted_hockey (r+q+1) r
  have h2 := weighted_hockey (r+q+1) q
  have h3 := weighted_hockey (r+q+1) (r+1)
  have h4 := weighted_hockey (r+q+1) (q+1)
  have e1 : ((r+1 : ℕ) : ℤ)-1=(r : ℤ) := by omega
  have e2 : ((q+1 : ℕ) : ℤ)-1=(q : ℤ) := by omega
  rw [e1] at h3
  rw [e2] at h4
  unfold weightedCoefficientSum twoFlexCoefficient
  simp_rw [mul_sub,mul_add]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib,h1,h2,h3,h4]
  ring

theorem choose_raise_one (r q : ℕ) :
    ((r+q+1).choose (r+1) : ℚ) =
      ((r : ℚ)+(q : ℚ)+1)*((r+q).choose r : ℚ)/((r : ℚ)+1) := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.succ_mul_choose_eq (r+q) r)
  push_cast at h
  apply (eq_div_iff (by positivity : (r : ℚ)+1 ≠ 0)).mpr
  exact h.symm

theorem choose_raise_two (r q : ℕ) :
    ((r+q+1).choose (r+2) : ℚ) =
      (q : ℚ)*((r+q+1).choose (r+1) : ℚ)/((r : ℚ)+2) := by
  have h := Nat.choose_succ_right_eq (r+q+1) (r+1)
  have he : r+q+1-(r+1)=q := by omega
  rw [he] at h
  have h' := congrArg (fun n : ℕ => (n : ℚ)) h
  push_cast at h'
  apply (eq_div_iff (by positivity : (r : ℚ)+2 ≠ 0)).mpr
  nlinarith

theorem choose_raise_three (r q : ℕ) :
    ((r+q+1).choose (r+3) : ℚ) =
      ((q : ℚ)-1)*((r+q+1).choose (r+2) : ℚ)/((r : ℚ)+3) := by
  by_cases hq : q=0
  · subst q
    rw [Nat.choose_eq_zero_of_lt (show r+0+1 < r+3 by omega),
      Nat.choose_eq_zero_of_lt (show r+0+1 < r+2 by omega)]
    simp
  · have h := Nat.choose_succ_right_eq (r+q+1) (r+2)
    have he : r+q+1-(r+2)=q-1 := by omega
    rw [he] at h
    have h' := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at h'
    rw [Nat.cast_sub (show 1 ≤ q by omega),Nat.cast_one] at h'
    apply (eq_div_iff (by positivity : (r : ℚ)+3 ≠ 0)).mpr
    nlinarith

theorem weighted_first_term (r q : ℕ) :
    ((r+1).choose 2 : ℚ)*((r+q+1).choose (r+2) : ℚ) =
      ((r+q).choose r : ℚ)*((r : ℚ)+(q : ℚ)+1)*(r : ℚ)*(q : ℚ)/(2*((r : ℚ)+2)) := by
  rw [Nat.cast_choose_two ℚ,choose_raise_two,choose_raise_one]
  push_cast
  have h1 : (r : ℚ)+1 ≠ 0 := by positivity
  have h2 : (r : ℚ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem weighted_second_term (r q : ℕ) :
    ((r+2).choose 2 : ℚ)*((r+q+1).choose (r+3) : ℚ) =
      ((r+q).choose r : ℚ)*((r : ℚ)+(q : ℚ)+1)*(q : ℚ)*((q : ℚ)-1)/(2*((r : ℚ)+3)) := by
  rw [Nat.cast_choose_two ℚ,choose_raise_three,choose_raise_two,choose_raise_one]
  push_cast
  have h1 : (r : ℚ)+1 ≠ 0 := by positivity
  have h2 : (r : ℚ)+2 ≠ 0 := by positivity
  have h3 : (r : ℚ)+3 ≠ 0 := by positivity
  field_simp
  ring

def witnessBracket (r q : ℚ) : ℚ :=
  r*q/(r+2)+r*q/(q+2)-q*(q-1)/(r+3)-r*(r-1)/(q+3)

theorem witnessBracket_formula (r q : ℕ) :
    witnessBracket (r : ℚ) (q : ℚ) =
      4*((r : ℚ)+(q : ℚ)+2)*witnessPolynomial ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2) /
        witnessDenominator ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2) := by
  have hr : (0 : ℚ) ≤ r := by positivity
  have hq : (0 : ℚ) ≤ q := by positivity
  have hz : ((q : ℚ)-(r : ℚ))^2 ≤ ((r : ℚ)+(q : ℚ))^2 := by nlinarith [mul_nonneg hr hq]
  have hD1 : 0 < ((r : ℚ)+(q : ℚ)+4)^2-((q : ℚ)-(r : ℚ))^2 := by nlinarith
  have hD2 : 0 < ((r : ℚ)+(q : ℚ)+6)^2-((q : ℚ)-(r : ℚ))^2 := by nlinarith
  have hr2 : (r : ℚ)+2 ≠ 0 := by positivity
  have hr3 : (r : ℚ)+3 ≠ 0 := by positivity
  have hq2 : (q : ℚ)+2 ≠ 0 := by positivity
  have hq3 : (q : ℚ)+3 ≠ 0 := by positivity
  unfold witnessBracket witnessPolynomial witnessDenominator
  field_simp [ne_of_gt hD1,ne_of_gt hD2]
  ring

theorem weightedCoefficientSum_closed (r q : ℕ) :
    weightedCoefficientSum r q = ((r+q).choose r : ℚ)*((r : ℚ)+(q : ℚ)+1)*
      (2*((r : ℚ)+(q : ℚ)+2)*witnessPolynomial ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2)) /
        witnessDenominator ((r : ℚ)+(q : ℚ)) (((q : ℚ)-(r : ℚ))^2) := by
  have hc : ((r+q).choose q : ℚ)=((r+q).choose r : ℚ) := by
    exact_mod_cast (Nat.choose_symm_add (a:=r) (b:=q)).symm
  have hq1 := weighted_first_term q r
  have hq2 := weighted_second_term q r
  simp only [Nat.add_comm q r,hc] at hq1 hq2
  calc
    weightedCoefficientSum r q = ((r+q).choose r : ℚ)*((r : ℚ)+(q : ℚ)+1)/2*witnessBracket r q := by
      rw [weightedCoefficientSum_expansion,weighted_first_term r q,weighted_second_term r q,hq1,hq2]
      unfold witnessBracket
      have hr2 : (r : ℚ)+2 ≠ 0 := by positivity
      have hr3 : (r : ℚ)+3 ≠ 0 := by positivity
      have hq2 : (q : ℚ)+2 ≠ 0 := by positivity
      have hq3 : (q : ℚ)+3 ≠ 0 := by positivity
      field_simp
      ring
    _ = _ := by rw [witnessBracket_formula]; ring

theorem excluded_parity_gap (r q : ℕ) (h : ¬ QuadraticRegion r q) :
    (r : ℤ)+(q : ℤ)+2 ≤ ((q : ℤ)-(r : ℤ))^2 := by
  obtain ⟨x,hx⟩ := Int.even_mul_pred_self (r : ℤ)
  obtain ⟨y,hy⟩ := Int.even_mul_pred_self (q : ℤ)
  have he : ((q : ℤ)-(r : ℤ))^2-((r : ℤ)+(q : ℤ)) = 2*(x+y-(r : ℤ)*(q : ℤ)) := by nlinarith
  unfold QuadraticRegion at h
  omega

theorem weightedCoefficientSum_negative (r q : ℕ) (h : ¬ QuadraticRegion r q) :
    weightedCoefficientSum r q < 0 := by
  rw [weightedCoefficientSum_closed]
  have hN := excluded_total_ge_two r q h
  have hN' : (2 : ℚ) ≤ (r : ℚ)+(q : ℚ) := by exact_mod_cast hN
  have hl : (r : ℚ)+(q : ℚ)+2 ≤ ((q : ℚ)-(r : ℚ))^2 := by exact_mod_cast excluded_parity_gap r q h
  have hr : (0 : ℚ) ≤ r := by positivity
  have hq : (0 : ℚ) ≤ q := by positivity
  have hu : ((q : ℚ)-(r : ℚ))^2 ≤ ((r : ℚ)+(q : ℚ))^2 := by nlinarith [mul_nonneg hr hq]
  have hp := witness_polynomial_negative _ _ hN' hl hu
  have hd := witness_denominator_positive _ _ (by positivity) hu
  have hc : (0 : ℚ) < ((r+q).choose r : ℚ) := by
    rw [Nat.cast_choose ℚ (show r ≤ r+q by omega)]
    positivity
  apply div_neg_of_neg_of_pos _ hd
  exact mul_neg_of_pos_of_neg (mul_pos hc (by positivity))
    (mul_neg_of_pos_of_neg (by positivity) hp)

end TwoBin
