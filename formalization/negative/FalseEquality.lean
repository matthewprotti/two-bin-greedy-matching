import TwoBin
-- Equal capacities do not mean equal distributions when capacity is at least two.
example : TwoBin.FixedEquality 2 2 := (TwoBin.fixed_equality_classification 2 2 (by decide) (by decide)).mpr (by norm_num)
