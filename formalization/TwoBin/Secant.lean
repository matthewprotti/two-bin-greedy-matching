import TwoBin.Falling

/-! Generic odd-coefficient and combination helpers. The complete falling-factorial
    secant bound is proved by the exact even/odd recurrence in Symmetric.lean;
    Paired.lean assembles the unconditional paired-factorial criterion. -/
namespace TwoBin
open Finset

/-- Normalized odd part of a polynomial, as used in the symmetric secant argument. -/
def oddSlope (coeff : ℕ → ℚ) (degree : ℕ) (h : ℚ) : ℚ :=
  ∑ k ∈ range (degree + 1), if Odd k then coeff k * h ^ (k - 1) else 0

theorem oddSlope_monotone (coeff : ℕ → ℚ) (degree : ℕ)
    (hc : ∀ k ≤ degree, 0 ≤ coeff k) (h H : ℚ)
    (hh : 0 ≤ h) (hH : h ≤ H) :
    oddSlope coeff degree h ≤ oddSlope coeff degree H := by
  unfold oddSlope
  apply Finset.sum_le_sum
  intro k hk
  have hkdeg : k ≤ degree := by
    have := Finset.mem_range.mp hk
    omega
  by_cases ho : Odd k
  · simp only [if_pos ho]
    have hk0 := hc k hkdeg
    gcongr
  · simp only [if_neg ho]
    exact le_rfl

/-- Clearing the two positive denominators combines the product and secant bounds.
    The two input bounds are genuine hypotheses here and must be proved at use sites. -/
theorem combine_product_secant (A B L R C D : ℚ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hD : 0 < D)
    (hprod : B*C ≤ A*D) (hsec : L*D ≤ R*C) :
    B*L ≤ A*R := by
  apply (mul_le_mul_right hD).mp
  have hp := mul_le_mul_of_nonneg_right hprod hR
  have hs := mul_le_mul_of_nonneg_left hsec hB
  nlinarith

end TwoBin
