import TwoBin.Secant

/-! An exact even/odd product recurrence proves the symmetric-secant comparison.
This is the coefficient argument written recursively: multiplying E(y²)+y O(y²)
by c+y sends (E,O) to (cE+y²O, E+cO). For c≥0 both parts have
nonnegative coefficients and are nondecreasing in y≥0. -/
namespace TwoBin

def fallingRat (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => fallingRat x n * (x - (n : ℚ))

def midpointParts (μ h : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | n+1 =>
    let p := midpointParts μ h n
    ((μ - (n : ℚ)) * p.1 + h^2 * p.2,
     p.1 + (μ - (n : ℚ)) * p.2)

theorem fallingRat_int (x : ℤ) (n : ℕ) :
    fallingRat (x : ℚ) n = (falling x n : ℚ) := by
  induction n with
  | zero => simp [fallingRat, falling]
  | succ n ih => simp [fallingRat, falling, ih]

theorem fallingRat_nat (x n : ℕ) :
    fallingRat (x : ℚ) n = (falling (x : ℤ) n : ℚ) := by
  exact_mod_cast fallingRat_int (x : ℤ) n

theorem midpointParts_identity (μ h : ℚ) (n : ℕ) :
    fallingRat (μ+h) n = (midpointParts μ h n).1 + h*(midpointParts μ h n).2 ∧
    fallingRat (μ-h) n = (midpointParts μ h n).1 - h*(midpointParts μ h n).2 := by
  induction n with
  | zero => simp [fallingRat, midpointParts]
  | succ n ih =>
    simp only [fallingRat, midpointParts]
    rw [ih.1, ih.2]
    constructor <;> ring

theorem midpointParts_nonnegative (μ h : ℚ) (n : ℕ)
    (hμ : (n : ℚ) ≤ μ+1) :
    0 ≤ (midpointParts μ h n).1 ∧ 0 ≤ (midpointParts μ h n).2 := by
  induction n with
  | zero => norm_num [midpointParts]
  | succ n ih =>
    have hn : (n : ℚ) ≤ μ := by push_cast at hμ; linarith
    have hi := ih (by linarith)
    have hc : 0 ≤ μ - (n : ℚ) := by linarith
    simp only [midpointParts]
    exact ⟨add_nonneg (mul_nonneg hc hi.1) (mul_nonneg (sq_nonneg h) hi.2),
      add_nonneg hi.1 (mul_nonneg hc hi.2)⟩

theorem midpointParts_monotone (μ h H : ℚ) (n : ℕ)
    (hμ : (n : ℚ) ≤ μ+1) (hh : 0 ≤ h) (hhH : h ≤ H) :
    (midpointParts μ h n).1 ≤ (midpointParts μ H n).1 ∧
    (midpointParts μ h n).2 ≤ (midpointParts μ H n).2 := by
  induction n with
  | zero => simp [midpointParts]
  | succ n ih =>
    have hn : (n : ℚ) ≤ μ := by push_cast at hμ; linarith
    have hi := ih (by linarith)
    have hc : 0 ≤ μ - (n : ℚ) := by linarith
    have hp := midpointParts_nonnegative μ h n (by linarith)
    have hsq : h^2 ≤ H^2 := by nlinarith
    simp only [midpointParts]
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left hi.1 hc)
        (mul_le_mul hsq hi.2 hp.2 (sq_nonneg H)),
      add_le_add hi.1 (mul_le_mul_of_nonneg_left hi.2 hc)⟩

/-- The actual falling-factorial secants, with denominators cleared. -/
theorem symmetric_secant_rat (r d u : ℚ) (v : ℕ)
    (hu : 0 ≤ u) (hud : u ≤ d) (hend : (v : ℚ)-1 ≤ r-u) :
    (d+u) * (fallingRat (r+d-u) v - fallingRat r v) ≤
      (d-u) * (fallingRat (r+d) v - fallingRat (r-u) v) := by
  let μ := (2*r+d-u)/2
  let h := (d-u)/2
  let H := (d+u)/2
  have hμ : (v : ℚ) ≤ μ+1 := by dsimp [μ]; linarith
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hhH : h ≤ H := by dsimp [h,H]; linarith
  have hm := (midpointParts_monotone μ h H v hμ hh hhH).2
  have he := midpointParts_identity μ h v
  have hE := midpointParts_identity μ H v
  have e1 : μ+h = r+d-u := by dsimp [μ,h]; ring
  have e2 : μ-h = r := by dsimp [μ,h]; ring
  have e3 : μ+H = r+d := by dsimp [μ,H]; ring
  have e4 : μ-H = r-u := by dsimp [μ,H]; ring
  rw [e1,e2] at he
  rw [e3,e4] at hE
  rw [he.1,he.2,hE.1,hE.2]
  have hp : 0 ≤ (d+u)*(d-u) := mul_nonneg (by linarith) (by linarith)
  have hm' := mul_le_mul_of_nonneg_left hm hp
  dsimp [h,H] at *
  nlinarith

theorem symmetric_secant_int (r d u v : ℕ)
    (hud : u ≤ d) (hend : (v : ℤ)-1 ≤ (r : ℤ)-(u : ℤ)) :
    ((d : ℤ)+(u : ℤ)) *
      (falling ((r : ℤ)+(d : ℤ)-(u : ℤ)) v - falling (r : ℤ) v) ≤
    ((d : ℤ)-(u : ℤ)) *
      (falling ((r : ℤ)+(d : ℤ)) v - falling ((r : ℤ)-(u : ℤ)) v) := by
  have hrat := symmetric_secant_rat (r : ℚ) (d : ℚ) (u : ℚ) v
    (by positivity) (by exact_mod_cast hud) (by exact_mod_cast hend)
  have e1 : (r : ℚ)+(d : ℚ)-(u : ℚ) = (((r : ℤ)+(d : ℤ)-(u : ℤ) : ℤ) : ℚ) := by push_cast; rfl
  have e2 : (r : ℚ)+(d : ℚ) = (((r : ℤ)+(d : ℤ) : ℤ) : ℚ) := by push_cast; rfl
  have e3 : (r : ℚ)-(u : ℚ) = (((r : ℤ)-(u : ℤ) : ℤ) : ℚ) := by push_cast; rfl
  rw [e1,e2,e3,fallingRat_int,fallingRat_int,fallingRat_int,fallingRat_nat] at hrat
  exact_mod_cast hrat

end TwoBin
