import TwoBin.StrictRandom

namespace TwoBin

theorem fixed_reverse_classification (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    FixedReverseDominance a b ↔ a=1 := by
  constructor
  · intro h
    by_contra hn
    exact not_fixed_reverse_of_two_le a b (by omega) hab h
  · intro h
    subst a
    cases b with
    | zero => omega
    | succ q => exact fixed_reverse_unit q

theorem random_reverse_classification (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    RandomReverseDominance a b ↔ a=1 := by
  constructor
  · intro h
    by_contra hn
    exact not_random_reverse_of_two_le a b (by omega) hab h
  · intro h
    exact fixed_reverse_implies_random_reverse a b ((fixed_reverse_classification a b ha hab).mpr h)

theorem unit_region_iff (b : ℕ) (hb : 1 ≤ b) : CapacityRegion 1 b ↔ b ≤ 2 := by
  unfold CapacityRegion
  norm_num
  constructor
  · intro h
    by_contra hn
    have hb3 : (3 : ℤ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
    nlinarith [sq_nonneg ((b : ℤ)-2)]
  · intro h
    have hc : b=1 ∨ b=2 := by omega
    rcases hc with rfl | rfl <;> norm_num

theorem fixed_equality_classification (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    FixedEquality a b ↔ a=1 ∧ b ≤ 2 := by
  constructor
  · intro h
    have hf : FixedDominance a b := by intro w K; exact le_of_eq (h w K)
    have hr : FixedReverseDominance a b := by intro w K; exact le_of_eq (h w K).symm
    have h1 := (fixed_reverse_classification a b ha hab).mp hr
    refine ⟨h1,?_⟩
    subst a
    exact (unit_region_iff b hab).mp ((fixed_classification 1 b ha hab).mpr hf)
  · rintro ⟨h1,hb⟩
    have hr := (fixed_reverse_classification a b ha hab).mpr h1
    have hreg : CapacityRegion a b := by subst a; exact (unit_region_iff b hab).mpr hb
    have hf := capacityRegion_implies_fixed a b ha hab hreg
    intro w K
    exact le_antisymm (hf w K) (hr w K)

theorem random_equality_classification (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    RandomEquality a b ↔ a=1 ∧ b ≤ 2 := by
  constructor
  · intro h
    have hf : RandomOrderDominance a b := by intro w K; exact le_of_eq (h w K)
    have hr : RandomReverseDominance a b := by intro w K; exact le_of_eq (h w K).symm
    have h1 := (random_reverse_classification a b ha hab).mp hr
    refine ⟨h1,?_⟩
    subst a
    exact (unit_region_iff b hab).mp ((full_classification 1 b ha hab).2.mpr hf)
  · rintro ⟨h1,hb⟩
    have hr := (random_reverse_classification a b ha hab).mpr h1
    have hreg : CapacityRegion a b := by subst a; exact (unit_region_iff b hab).mpr hb
    have hf := (full_classification a b ha hab).2.mp hreg
    intro w K
    exact le_antisymm (hf w K) (hr w K)

theorem no_universal_order_outside (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hregion : ¬ CapacityRegion a b) :
    ¬ FixedDominance a b ∧ ¬ FixedReverseDominance a b ∧
    ¬ RandomOrderDominance a b ∧ ¬ RandomReverseDominance a b := by
  exact ⟨fun h => hregion ((full_classification a b (by omega) hab).1.mpr h),
    not_fixed_reverse_of_two_le a b ha hab,
    fun h => hregion ((full_classification a b (by omega) hab).2.mpr h),
    not_random_reverse_of_two_le a b ha hab⟩

/-- Theorem 2's equality and reverse-order regimes, together with Theorem 1's RV criterion. -/
theorem full_regime_classification (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (CapacityRegion a b ↔ FixedDominance a b) ∧
    (CapacityRegion a b ↔ RandomOrderDominance a b) ∧
    (FixedReverseDominance a b ↔ a=1) ∧
    (RandomReverseDominance a b ↔ a=1) ∧
    (FixedEquality a b ↔ a=1 ∧ b ≤ 2) ∧
    (RandomEquality a b ↔ a=1 ∧ b ≤ 2) := by
  exact ⟨(full_classification a b ha hab).1,(full_classification a b ha hab).2,
    fixed_reverse_classification a b ha hab,random_reverse_classification a b ha hab,
    fixed_equality_classification a b ha hab,random_equality_classification a b ha hab⟩

end TwoBin
