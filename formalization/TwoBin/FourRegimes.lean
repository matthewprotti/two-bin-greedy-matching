import TwoBin.Regimes
import TwoBin.WitnessIdentities

namespace TwoBin

def FixedStrictRV (a b : ℕ) : Prop := ∃ word : List Degree, ∃ K : ℕ, rkCount a b word K < 2*rvCount a b word K

def FixedStrictRK (a b : ℕ) : Prop := ∃ word : List Degree, ∃ K : ℕ, 2*rvCount a b word K < rkCount a b word K

def RandomStrictRV (a b : ℕ) : Prop := ∃ word : List Degree, ∃ K : ℕ,
  ((arrivalOrders word).map (fun w => rkCount a b w K)).sum <
    2*((arrivalOrders word).map (fun w => rvCount a b w K)).sum

def RandomStrictRK (a b : ℕ) : Prop := ∃ word : List Degree, ∃ K : ℕ,
  2*((arrivalOrders word).map (fun w => rvCount a b w K)).sum <
    ((arrivalOrders word).map (fun w => rkCount a b w K)).sum

theorem fixed_strict_rv_of_two_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) : FixedStrictRV a b := by
  have h := not_fixed_reverse_of_two_le a b ha hab
  unfold FixedReverseDominance at h
  push_neg at h
  exact h

theorem random_strict_rv_of_two_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) : RandomStrictRV a b := by
  have h := not_random_reverse_of_two_le a b ha hab
  unfold RandomReverseDominance at h
  push_neg at h
  exact h

theorem fixed_strict_rk_outside (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hr : ¬ CapacityRegion a b) :
    FixedStrictRK a b := by
  have h : ¬ FixedDominance a b := fun h => hr ((fixed_classification a b ha hab).mpr h)
  unfold FixedDominance at h
  push_neg at h
  exact h

theorem random_strict_rk_outside (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hr : ¬ CapacityRegion a b) :
    RandomStrictRK a b := by
  have h : ¬ RandomOrderDominance a b := fun h => hr ((full_classification a b ha hab).2.mpr h)
  unfold RandomOrderDominance at h
  push_neg at h
  exact h

/-- Literal four-row regime statement, including strict examples in both arrival models. -/
def FourRegimeTarget : Prop := ∀ a b : ℕ, 1 ≤ a → a ≤ b →
  ((a=1 ∧ b ≤ 2) → FixedEquality a b ∧ RandomEquality a b) ∧
  ((a=1 ∧ 3 ≤ b) → FixedReverseDominance a b ∧ RandomReverseDominance a b ∧
    FixedStrictRK a b ∧ RandomStrictRK a b) ∧
  ((2 ≤ a ∧ CapacityRegion a b) → FixedDominance a b ∧ RandomOrderDominance a b ∧
    FixedStrictRV a b ∧ RandomStrictRV a b) ∧
  ((2 ≤ a ∧ ¬ CapacityRegion a b) →
    (¬ FixedDominance a b ∧ ¬ FixedReverseDominance a b ∧
      ¬ RandomOrderDominance a b ∧ ¬ RandomReverseDominance a b) ∧
    FixedStrictRV a b ∧ FixedStrictRK a b ∧ RandomStrictRV a b ∧ RandomStrictRK a b)

/-- Paper Theorem 2, including the equality boundaries and strict witnesses. -/
theorem four_regimes : FourRegimeTarget := by
  intro a b ha hab
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    exact ⟨(fixed_equality_classification a b ha hab).mpr h,
      (random_equality_classification a b ha hab).mpr h⟩
  · rintro ⟨h1,hb⟩
    have hr : ¬ CapacityRegion a b := by
      subst a
      rw [unit_region_iff b (by omega)]
      omega
    exact ⟨(fixed_reverse_classification a b ha hab).mpr h1,
      (random_reverse_classification a b ha hab).mpr h1,
      fixed_strict_rk_outside a b ha hab hr,random_strict_rk_outside a b ha hab hr⟩
  · rintro ⟨ha2,hr⟩
    exact ⟨(full_classification a b ha hab).1.mp hr,(full_classification a b ha hab).2.mp hr,
      fixed_strict_rv_of_two_le a b ha2 hab,random_strict_rv_of_two_le a b ha2 hab⟩
  · rintro ⟨ha2,hr⟩
    exact ⟨no_universal_order_outside a b ha2 hab hr,fixed_strict_rv_of_two_le a b ha2 hab,
      fixed_strict_rk_outside a b ha hab hr,random_strict_rv_of_two_le a b ha2 hab,
      random_strict_rk_outside a b ha hab hr⟩

end TwoBin
