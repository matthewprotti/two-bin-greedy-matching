import TwoBin.Definitions

/-! CHECKED SUPPORTING SOURCE. Sign lemmas do not identify these expressions with
    actual matching probabilities; that finite-sample-space bridge is still open. -/
namespace TwoBin

def witnessPolynomial (N z : ℚ) : ℚ :=
  z^2 - (N^2 + 9*N + 26)*z + N^3 + 10*N^2 + 24*N

def witnessDenominator (N z : ℚ) : ℚ :=
  ((N+4)^2-z)*((N+6)^2-z)

theorem witness_factorization (N z : ℚ) :
    witnessPolynomial N z = (z-N-2)*(z-N^2)-8*(N+3)*(z-N) := by
  unfold witnessPolynomial
  ring

theorem witness_polynomial_negative (N z : ℚ)
    (hN : 2 ≤ N) (hl : N+2 ≤ z) (hu : z ≤ N^2) :
    witnessPolynomial N z < 0 := by
  rw [witness_factorization]
  have hleft : 0 ≤ z-N-2 := by linarith
  have hright : z-N^2 ≤ 0 := by linarith
  have hp : (z-N-2)*(z-N^2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hleft hright
  have hzn : 0 < z-N := by linarith
  have hnp : 0 < N+3 := by linarith
  have hn : 0 < 8*(N+3)*(z-N) :=
    mul_pos (mul_pos (by norm_num) hnp) hzn
  linarith

theorem witness_denominator_positive (N z : ℚ)
    (hN : 0 ≤ N) (hz : z ≤ N^2) : 0 < witnessDenominator N z := by
  unfold witnessDenominator
  apply mul_pos <;> nlinarith

/-- Closed algebraic sign, conditional on the stated probability prefactor. -/
theorem random_witness_expression_negative (N z p : ℚ)
    (hN : 2 ≤ N) (hl : N+2 ≤ z) (hu : z ≤ N^2) (hp : 0 < p) :
    p * (2*(N+2)*witnessPolynomial N z) /
      (N*witnessDenominator N z) < 0 := by
  have hpoly := witness_polynomial_negative N z hN hl hu
  have hden := witness_denominator_positive N z (by linarith) hu
  have hfactor : 0 < 2*(N+2) := by linarith
  have hnum : p * (2*(N+2)*witnessPolynomial N z) < 0 :=
    mul_neg_of_pos_of_neg hp (mul_neg_of_pos_of_neg hfactor hpoly)
  exact div_neg_of_neg_of_pos hnum (mul_pos (by linarith) hden)

end TwoBin
