import TwoBin
-- Applying the classification outside its quadratic region must fail.
example : TwoBin.PairedBound 0 2 := (TwoBin.paired_classification 0 2 (by decide)).mp (by norm_num [TwoBin.QuadraticRegion])
