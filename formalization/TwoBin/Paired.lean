import TwoBin.Product
import TwoBin.Symmetric

/-! Complete paired falling-factorial classification (paper Lemma 3).
The definitions in Definitions.lean are unchanged. No secant, ratio, or
classification premise is assumed by the release theorem. -/
namespace TwoBin

theorem paired_interior (r d u v : ℕ) (hd : 2 ≤ d)
    (hgap : (d : ℤ) * ((d : ℤ)-1) ≤ 2*(r : ℤ))
    (hu : u < d) (hv : v < d) :
    falling (r : ℤ) (u+v) + falling ((r+d : ℕ) : ℤ) (u+v) ≤
    falling (r : ℤ) u * falling ((r+d : ℕ) : ℤ) v +
    falling ((r+d : ℕ) : ℤ) u * falling (r : ℤ) v := by
  have hr := gap_lower_bound r d hd hgap
  have hur : u ≤ r := by omega
  have hcast : ((r-u : ℕ) : ℤ) = (r : ℤ)-(u : ℤ) := by omega
  have hR : 0 ≤ falling ((r+d : ℕ) : ℤ) v - falling ((r : ℤ)-(u : ℤ)) v := by
    rw [← hcast]
    exact sub_nonneg.mpr (falling_nat_monotone v (r-u) (r+d) (by omega))
  have hB := falling_nat_nonnegative u (r+d)
  have hD : 0 < (d : ℤ)+(u : ℤ) := by omega
  have hp := product_ratio_bound r d hd hgap u hu
  have hs := symmetric_secant_int r d u v (by omega)
    (interior_endpoint r d u v hd hgap hu hv)
  simp only [← Nat.cast_add] at hs
  have hc : falling ((r+d : ℕ) : ℤ) u *
      (falling (((r+d : ℕ) : ℤ)-(u : ℤ)) v - falling (r : ℤ) v) ≤
    falling (r : ℤ) u *
      (falling ((r+d : ℕ) : ℤ) v - falling ((r : ℤ)-(u : ℤ)) v) := by
    apply (mul_le_mul_right hD).mp
    have hp' := mul_le_mul_of_nonneg_right hp hR
    have hs' := mul_le_mul_of_nonneg_left hs hB
    simp only [Nat.cast_add] at hp' hs' ⊢
    nlinarith
  rw [falling_add, falling_add]
  nlinarith

/-- Sufficiency, with axes, large indices, and all zero-support cases included. -/
theorem quadratic_implies_paired (r q : ℕ) (hrq : r ≤ q)
    (h : QuadraticRegion r q) : PairedBound r q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrq
  have hgap := (gap_form r d).mp h
  intro u v
  by_cases hu0 : u = 0
  · subst u
    simp [add_comm]
  by_cases hv0 : v = 0
  · subst v
    simp
  by_cases hu : d ≤ u
  · exact paired_large_left r (r+d) u v (by omega) (by omega)
  by_cases hv : d ≤ v
  · simpa only [Nat.add_comm v u, mul_comm, add_comm] using
      paired_large_left r (r+d) v u (by omega) (by omega)
  exact paired_interior r d u v (by omega) hgap (by omega) (by omega)

/-- Algebraic release theorem. This proves Lemma 3, not the matching classification. -/
theorem paired_classification : PairedClassificationTarget := by
  intro r q hrq
  exact ⟨quadratic_implies_paired r q hrq, paired_implies_quadratic r q⟩

end TwoBin
