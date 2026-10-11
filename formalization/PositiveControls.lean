import TwoBin
example : TwoBin.rvCount 1 3 [.flexible, .flexible, .singleton] 3 = 5 := by decide
example : ¬ TwoBin.CapacityRegion 1 3 := by norm_num [TwoBin.CapacityRegion]
example : TwoBin.rkCount 1 3 [.flexible, .flexible, .singleton] 3 = 12 := by decide
example : ¬ TwoBin.PairedBound 0 2 := by
  intro h
  have hc := TwoBin.paired_implies_quadratic 0 2 h
  norm_num [TwoBin.QuadraticRegion] at hc
example : TwoBin.FixedDominance 2 3 := (TwoBin.full_classification 2 3 (by decide) (by decide)).1.mp (by norm_num [TwoBin.CapacityRegion])
example : TwoBin.RandomOrderDominance 2 3 := (TwoBin.full_classification 2 3 (by decide) (by decide)).2.mp (by norm_num [TwoBin.CapacityRegion])
example : TwoBin.FixedReverseDominance 1 3 := (TwoBin.fixed_reverse_classification 1 3 (by decide) (by decide)).mpr rfl
example : TwoBin.FixedEquality 1 2 := (TwoBin.fixed_equality_classification 1 2 (by decide) (by decide)).mpr ⟨rfl,by decide⟩
