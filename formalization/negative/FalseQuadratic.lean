import TwoBin
-- Capacities (1,3) lie outside the admissible region. This MUST fail.
example : TwoBin.CapacityRegion 1 3 := by norm_num [TwoBin.CapacityRegion]
