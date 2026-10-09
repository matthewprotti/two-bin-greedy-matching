import TwoBin.Definitions

/-! CHECKED SUPPORTING SOURCE. Explicitly conditional algebraic bridge:
    the actual stochastic identity has not been proved in Lean. -/
namespace TwoBin
open Finset

def tailExpansion (n : ℕ) (delta h : ℕ → ℚ) : ℚ :=
  ∑ t ∈ range n, delta t * (h (t+1) - h t)

theorem tailExpansion_nonnegative (n : ℕ) (delta h : ℕ → ℚ)
    (hd : ∀ t < n, 0 ≤ delta t)
    (hh : ∀ t < n, h t ≤ h (t+1)) :
    0 ≤ tailExpansion n delta h := by
  unfold tailExpansion
  apply Finset.sum_nonneg
  intro t ht
  have htn := Finset.mem_range.mp ht
  exact mul_nonneg (hd t htn) (sub_nonneg.mpr (hh t htn))

/-- Do not count this conditional lemma as the stochastic theorem. -/
theorem tail_comparison_from_identity (n : ℕ) (delta h : ℕ → ℚ) (rv rk : ℚ)
    (hid : rv-rk = tailExpansion n delta h)
    (hd : ∀ t < n, 0 ≤ delta t)
    (hh : ∀ t < n, h t ≤ h (t+1)) : rk ≤ rv := by
  have hpos := tailExpansion_nonnegative n delta h hd hh
  rw [← hid] at hpos
  linarith

theorem clipped_continuation_step (S t rest y : ℚ) (hy : y ≤ 1) :
    min S (t+rest+y) ≤ min S (t+1+rest) := by
  apply min_le_min_left
  linarith

theorem mixture_le {ι : Type*} [Fintype ι] (w f g : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hfg : ∀ i, f i ≤ g i) :
    (∑ i, w i * f i) ≤ ∑ i, w i * g i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hfg i) (hw i)

end TwoBin
