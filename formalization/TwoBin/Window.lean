import TwoBin.Binomial
import Mathlib.Algebra.BigOperators.Intervals

/-! Binomial-window identities. These are formulas, not a definition of the
matching process's survival law. Their identification with SourceModel is open. -/
namespace TwoBin

theorem binomialZ_pascal (n : ℕ) (k : ℤ) :
    binomialZ (n+1) k = binomialZ n (k-1) + binomialZ n k := by
  by_cases hk : k < 0
  · rw [binomialZ_negative _ _ hk, binomialZ_negative _ _ (by omega),
      binomialZ_negative _ _ hk]
    norm_num
  by_cases hk0 : k = 0
  · subst k
    norm_num [binomialZ]
  have hkp : 1 ≤ k := by omega
  have hnat : k.toNat = (k-1).toNat + 1 := by omega
  simp only [binomialZ, if_pos (show 0 ≤ k by omega),
    if_pos (show 0 ≤ k-1 by omega)]
  rw [hnat, Nat.choose_succ_succ']
  push_cast
  rfl

theorem binomialZ_reflection (n : ℕ) (k : ℤ) :
    binomialZ n k = binomialZ n ((n : ℤ)-k) := by
  by_cases hk : k < 0
  · rw [binomialZ_negative _ _ hk, binomialZ_above _ _ (by omega)]
  by_cases hn : (n : ℤ) < k
  · rw [binomialZ_above _ _ hn, binomialZ_negative _ _ (by omega)]
  have hk0 : 0 ≤ k := by omega
  have hnk : 0 ≤ (n : ℤ)-k := by omega
  have hkn : k.toNat ≤ n := by omega
  have he : ((n : ℤ)-k).toNat = n-k.toNat := by omega
  simp only [binomialZ, if_pos hk0, if_pos hnk, he, Nat.choose_symm hkn]

def binomialWindow (n : ℕ) (lo : ℤ) : ℕ → ℚ
  | 0 => 0
  | len+1 => binomialWindow n lo len + binomialZ n (lo+(len : ℤ))

theorem binomialWindow_sum (n len : ℕ) (lo : ℤ) :
    binomialWindow n lo len = ∑ i ∈ Finset.range len, binomialZ n (lo+(i : ℤ)) := by
  induction len with
  | zero => simp [binomialWindow]
  | succ len ih => simp [binomialWindow, Finset.sum_range_succ, ih]

theorem binomialWindow_shift (n len : ℕ) (lo : ℤ) :
    binomialWindow n (lo-1) len - binomialWindow n lo len =
      binomialZ n (lo-1) - binomialZ n (lo+(len : ℤ)-1) := by
  induction len with
  | zero => simp [binomialWindow]
  | succ len ih =>
    simp only [binomialWindow, Nat.cast_succ]
    have he1 : lo-1+(len : ℤ) = lo+(len : ℤ)-1 := by ring
    have he2 : lo+((len : ℤ)+1)-1 = lo+(len : ℤ) := by ring
    rw [he1,he2]
    linarith

theorem binomialWindow_pascal (n len : ℕ) (lo : ℤ) :
    binomialWindow (n+1) lo len =
      binomialWindow n (lo-1) len + binomialWindow n lo len := by
  induction len with
  | zero => simp [binomialWindow]
  | succ len ih =>
    simp only [binomialWindow, binomialZ_pascal, ih]
    have he : lo+(len : ℤ)-1 = lo-1+(len : ℤ) := by ring
    rw [he]
    ring

theorem binomialWindow_reflection (n len : ℕ) (lo : ℤ) :
    binomialWindow n lo len = binomialWindow n ((n : ℤ)-lo-(len : ℤ)+1) len := by
  rw [binomialWindow_sum, binomialWindow_sum,
    ← Finset.sum_range_reflect (fun i => binomialZ n (lo+(i : ℤ))) len]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [binomialZ_reflection]
  congr 1
  omega

/-- The paper's expression R_t(s), before any identification with source counts. -/
def rankingSurvivalFormula (r q t s : ℕ) : ℚ :=
  (binomialWindow s ((t : ℤ)-(q : ℤ)) (r+q+1-t) +
    binomialWindow s ((t : ℤ)-(r : ℤ)) (r+q+1-t)) / (2*2^s)

def rvSurvivalFormula (r q t : ℕ) : ℚ :=
  binomialWindow t ((t : ℤ)-(q : ℤ)) (r+q+1-t) / 2^t

/-- Pascal's window difference, paper equation (11), with the fair-coin denominator. -/
theorem rankingSurvivalFormula_step (r q t s : ℕ) (ht : t ≤ r+q) :
    rankingSurvivalFormula r q t (s+1) - rankingSurvivalFormula r q t s =
    (binomialZ s ((t : ℤ)-(q : ℤ)-1) + binomialZ s ((t : ℤ)-(r : ℤ)-1) -
      binomialZ s (r : ℤ) - binomialZ s (q : ℤ)) / (4*2^s) := by
  have h1 := binomialWindow_shift s (r+q+1-t) ((t : ℤ)-(q : ℤ))
  have h2 := binomialWindow_shift s (r+q+1-t) ((t : ℤ)-(r : ℤ))
  have e1 : (t : ℤ)-(q : ℤ)+((r+q+1-t : ℕ) : ℤ)-1 = (r : ℤ) := by omega
  have e2 : (t : ℤ)-(r : ℤ)+((r+q+1-t : ℕ) : ℤ)-1 = (q : ℤ) := by omega
  rw [e1] at h1
  rw [e2] at h2
  have hp1 := binomialWindow_pascal s (r+q+1-t) ((t : ℤ)-(q : ℤ))
  have hp2 := binomialWindow_pascal s (r+q+1-t) ((t : ℤ)-(r : ℤ))
  have hsum : binomialWindow (s+1) ((t : ℤ)-(q : ℤ)) (r+q+1-t) +
      binomialWindow (s+1) ((t : ℤ)-(r : ℤ)) (r+q+1-t) =
      2 * (binomialWindow s ((t : ℤ)-(q : ℤ)) (r+q+1-t) +
        binomialWindow s ((t : ℤ)-(r : ℤ)) (r+q+1-t)) +
      binomialZ s ((t : ℤ)-(q : ℤ)-1) + binomialZ s ((t : ℤ)-(r : ℤ)-1) -
      binomialZ s (r : ℤ) - binomialZ s (q : ℤ) := by linarith
  unfold rankingSurvivalFormula
  rw [pow_succ, hsum]
  have hpow : (2 : ℚ)^s ≠ 0 := by positivity
  field_simp
  ring

theorem rankingSurvivalFormula_le_succ (r q t s : ℕ) (hrq : r ≤ q)
    (hregion : QuadraticRegion r q) (ht : t ≤ r+q) (hst : s < t) :
    rankingSurvivalFormula r q t s ≤ rankingSurvivalFormula r q t (s+1) := by
  have hb := paired_binomial_shift r q (r+q-t+1) (t-s-1) s hrq hregion (by omega)
  have e1 : (r : ℤ)-((r+q-t+1 : ℕ) : ℤ) = (t : ℤ)-(q : ℤ)-1 := by omega
  have e2 : (q : ℤ)-((r+q-t+1 : ℕ) : ℤ) = (t : ℤ)-(r : ℤ)-1 := by omega
  rw [e1,e2] at hb
  apply sub_nonneg.mp
  rw [rankingSurvivalFormula_step r q t s ht]
  exact div_nonneg (by linarith) (by positivity)

theorem rankingSurvivalFormula_monotone (r q t s S : ℕ) (hrq : r ≤ q)
    (hregion : QuadraticRegion r q) (ht : t ≤ r+q) (hsS : s ≤ S) (hSt : S ≤ t) :
    rankingSurvivalFormula r q t s ≤ rankingSurvivalFormula r q t S := by
  induction S with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact le_rfl
  | succ S ih =>
    by_cases hs : s = S+1
    · subst s
      exact le_rfl
    · exact le_trans (ih (by omega) (by omega))
        (rankingSurvivalFormula_le_succ r q t S hrq hregion ht (by omega))

theorem pure_singleton_endpoint (r q t : ℕ) (ht : t ≤ r+q) :
    rankingSurvivalFormula r q t t = rvSurvivalFormula r q t := by
  have hw := binomialWindow_reflection t (r+q+1-t) ((t : ℤ)-(r : ℤ))
  have he : (t : ℤ)-((t : ℤ)-(r : ℤ))-((r+q+1-t : ℕ) : ℤ)+1 =
      (t : ℤ)-(q : ℤ) := by omega
  rw [he] at hw
  unfold rankingSurvivalFormula rvSurvivalFormula
  rw [hw]
  ring

theorem survivalFormula_dominance (r q t s : ℕ) (hrq : r ≤ q)
    (hregion : QuadraticRegion r q) (ht : t ≤ r+q) (hst : s ≤ t) :
    rankingSurvivalFormula r q t s ≤ rvSurvivalFormula r q t := by
  rw [← pure_singleton_endpoint r q t ht]
  exact rankingSurvivalFormula_monotone r q t s t hrq hregion ht hst le_rfl

end TwoBin
