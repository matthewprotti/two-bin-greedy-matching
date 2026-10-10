import TwoBin
-- This excluded capacity pair must not acquire universal RV dominance.
example : TwoBin.FixedDominance 1 3 := (TwoBin.full_classification 1 3 (by decide) (by decide)).1.mp (by norm_num [TwoBin.CapacityRegion])
