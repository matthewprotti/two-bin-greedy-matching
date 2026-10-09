import TwoBin.Definitions

/-! CHECKED SUPPORTING SOURCE: compiled and audited; the full classification remains open. -/
namespace TwoBin

@[simp] theorem falling_zero (x : ℤ) : falling x 0 = 1 := rfl
@[simp] theorem falling_one (x : ℤ) : falling x 1 = x := by simp [falling]
@[simp] theorem falling_two (x : ℤ) : falling x 2 = x * (x - 1) := by
  simp [falling]

theorem falling_add (x : ℤ) (u v : ℕ) :
    falling x (u + v) = falling x u * falling (x - (u : ℤ)) v := by
  induction v with
  | zero => simp [falling]
  | succ v ih =>
    change falling x (u + v) * (x - ((u + v : ℕ) : ℤ)) =
      falling x u * (falling (x - (u : ℤ)) v * (x - (u : ℤ) - (v : ℤ)))
    rw [ih, Nat.cast_add]
    ring

theorem falling_zero_of_lt : ∀ n x : ℕ, x < n → falling (x : ℤ) n = 0 := by
  intro n
  induction n with
  | zero => intro x h; omega
  | succ n ih =>
    intro x h
    rw [falling]
    by_cases hx : x < n
    · rw [ih x hx]; ring
    · have heq : x = n := by omega
      subst x
      simp

theorem falling_nat_nonnegative : ∀ n x : ℕ, 0 ≤ falling (x : ℤ) n := by
  intro n
  induction n with
  | zero => intro x; simp [falling]
  | succ n ih =>
    intro x
    by_cases hx : n ≤ x
    · rw [falling]
      apply mul_nonneg (ih x)
      exact sub_nonneg.mpr (by exact_mod_cast hx)
    · have hz := falling_zero_of_lt n x (by omega)
      rw [falling, hz]
      simp

theorem falling_nat_monotone : ∀ n a b : ℕ, a ≤ b →
    falling (a : ℤ) n ≤ falling (b : ℤ) n := by
  intro n
  induction n with
  | zero => intro a b h; simp [falling]
  | succ n ih =>
    intro a b hab
    by_cases hn : n + 1 ≤ a
    · rw [falling, falling]
      apply mul_le_mul (ih a b hab)
      · exact sub_le_sub_right (by exact_mod_cast hab) _
      · have hna : (n : ℤ) ≤ (a : ℤ) := by exact_mod_cast (show n ≤ a by omega)
        linarith
      · exact falling_nat_nonnegative n b
    · have ha : a < n + 1 := by omega
      rw [falling_zero_of_lt (n + 1) a ha]
      exact falling_nat_nonnegative (n + 1) b

theorem paired_axis (r q : ℕ) (v : ℕ) :
    falling (r : ℤ) (0 + v) + falling (q : ℤ) (0 + v) =
    falling (r : ℤ) 0 * falling (q : ℤ) v +
    falling (q : ℤ) 0 * falling (r : ℤ) v := by
  simp [falling, add_comm]

/-- Necessity is the (u,v)=(1,1) specialization, not the full lemma. -/
theorem paired_implies_quadratic (r q : ℕ) (h : PairedBound r q) :
    QuadraticRegion r q := by
  have h11 := h 1 1
  simp only [show (1 : ℕ) + 1 = 2 by rfl, falling_one, falling_two] at h11
  unfold QuadraticRegion
  nlinarith

theorem gap_form (r d : ℕ) :
    QuadraticRegion r (r + d) ↔ (d : ℤ) * ((d : ℤ) - 1) ≤ 2 * (r : ℤ) := by
  unfold QuadraticRegion
  push_cast
  constructor <;> intro h <;> nlinarith

theorem product_step_identity (r d j : ℤ) :
    (r-j)*(d+j+1)*(d-j) - (r+d-j)*(d-j-1)*(d+j) =
    d*(2*r-d*(d-1)+j*(j-1)) := by ring

theorem adjacent_nat_product_nonnegative (j : ℕ) :
    0 ≤ (j : ℤ) * ((j : ℤ) - 1) := by
  cases j with
  | zero => norm_num
  | succ k =>
    push_cast
    have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
    nlinarith

theorem product_step_nonnegative (r d j : ℕ)
    (h : (d : ℤ) * ((d : ℤ) - 1) ≤ 2 * (r : ℤ)) :
    0 ≤ ((r : ℤ)-(j : ℤ))*((d : ℤ)+(j : ℤ)+1)*((d : ℤ)-(j : ℤ)) -
      ((r : ℤ)+(d : ℤ)-(j : ℤ))*((d : ℤ)-(j : ℤ)-1)*((d : ℤ)+(j : ℤ)) := by
  rw [product_step_identity]
  apply mul_nonneg (by positivity)
  have hj := adjacent_nat_product_nonnegative j
  linarith

end TwoBin
