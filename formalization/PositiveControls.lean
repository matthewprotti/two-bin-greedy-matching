import TwoBin
example : TwoBin.rvCount 1 3 [.flexible, .flexible, .singleton] 3 = 5 := by decide
example : ¬ TwoBin.CapacityRegion 1 3 := by norm_num [TwoBin.CapacityRegion]
example : TwoBin.rkCount 1 3 [.flexible, .flexible, .singleton] 3 = 12 := by decide
example : ¬ TwoBin.PairedBound 0 2 := by
  intro h
  have hc := TwoBin.paired_implies_quadratic 0 2 h
  norm_num [TwoBin.QuadraticRegion] at hc
