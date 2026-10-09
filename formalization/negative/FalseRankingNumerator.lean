import TwoBin
-- A false probability numerator MUST be rejected; positive imports must build first.
example : TwoBin.rkCount 1 3 [.flexible, .flexible, .singleton] 3 = 10 := by decide
