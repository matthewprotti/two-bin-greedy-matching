import TwoBin
-- This file MUST fail kernel checking; it is excluded from the positive library.
example : TwoBin.rvCount 1 3 [.flexible, .flexible, .singleton] 3 = 6 := by decide
