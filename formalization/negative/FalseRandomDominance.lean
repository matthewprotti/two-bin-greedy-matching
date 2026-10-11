import TwoBin
-- The independent uniform-arrival necessity theorem must reject this claim.
example : TwoBin.RandomOrderDominance 1 3 := (TwoBin.full_classification 1 3 (by decide) (by decide)).2.mp (by norm_num [TwoBin.CapacityRegion])
