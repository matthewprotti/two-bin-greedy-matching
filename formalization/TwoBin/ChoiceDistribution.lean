import TwoBin.FiniteProbability

namespace TwoBin

def firstIncrement (ranking priority : Bool) (d : Degree) (coin : Bool) : ℤ :=
  match d with
  | .zero => 0
  | .singleton => if coin then 0 else 1
  | .flexible => if (if ranking then priority else coin) then 0 else 1

def firstSum (ranking priority : Bool) (events : List (Degree × Bool)) : ℤ :=
  (events.map (fun dc => firstIncrement ranking priority dc.1 dc.2)).sum

def activeTrials (ranking : Bool) : List Degree → ℕ
  | [] => 0
  | .zero::ds => activeTrials ranking ds
  | .singleton::ds => activeTrials ranking ds + 1
  | .flexible::ds => if ranking then activeTrials ranking ds else activeTrials ranking ds + 1

def forcedChoices (ranking priority : Bool) : List Degree → ℤ
  | [] => 0
  | .zero::ds => forcedChoices ranking priority ds
  | .singleton::ds => forcedChoices ranking priority ds
  | .flexible::ds => if ranking && !priority then 1 + forcedChoices ranking priority ds else forcedChoices ranking priority ds

@[simp] theorem forcedChoices_rv (priority : Bool) (word : List Degree) : forcedChoices false priority word = 0 := by
  induction word with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [forcedChoices, ih]

@[simp] theorem forcedChoices_rank1 (word : List Degree) : forcedChoices true true word = 0 := by
  induction word with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [forcedChoices, ih]

theorem activeTrials_split (word : List Degree) :
    (activeTrials false word : ℤ) = (activeTrials true word : ℤ) + forcedChoices true false word := by
  induction word with
  | nil => simp [activeTrials, forcedChoices]
  | cons d ds ih => cases d <;> simp [activeTrials, forcedChoices, ih] <;> ring

theorem freeStep_first (ranking priority : Bool) (loads : Loads) (d : Degree) (coin : Bool) :
    ((freeStep ranking priority loads d coin).1 : ℤ) = (loads.1 : ℤ) + firstIncrement ranking priority d coin := by
  cases d <;> cases ranking <;> cases priority <;> cases coin <;> simp [freeStep, addAt, firstIncrement]

theorem runFree_first (ranking priority : Bool) (events : List (Degree × Bool)) (loads : Loads) :
    ((runFree ranking priority events loads).1 : ℤ) = (loads.1 : ℤ) + firstSum ranking priority events := by
  induction events generalizing loads with
  | nil => simp [runFree, firstSum]
  | cons dc ds ih =>
    change ((runFree ranking priority ds (freeStep ranking priority loads dc.1 dc.2)).1 : ℤ) = _
    rw [ih, freeStep_first]
    simp only [firstSum, List.map_cons, List.sum_cons]
    ring

def freeFirstMass (ranking priority : Bool) (word : List Degree) (k : ℤ) : ℚ :=
  coinAverage word.length (fun cs => if firstSum ranking priority (word.zip cs) = k then 1 else 0)

theorem freeFirstMass_nil (ranking priority : Bool) (k : ℤ) :
    freeFirstMass ranking priority [] k = if k = 0 then 1 else 0 := by
  simp [freeFirstMass, coinAverage_zero, firstSum, eq_comm]

theorem freeFirstMass_cons (ranking priority : Bool) (d : Degree) (ds : List Degree) (k : ℤ) :
    freeFirstMass ranking priority (d::ds) k =
      (freeFirstMass ranking priority ds (k-firstIncrement ranking priority d false) +
       freeFirstMass ranking priority ds (k-firstIncrement ranking priority d true))/2 := by
  have he (a b c : ℤ) : a+b=c ↔ b=c-a := by omega
  simp only [freeFirstMass, List.length_cons, coinAverage_succ, List.zip_cons_cons,
    firstSum, List.map_cons, List.sum_cons, he]

theorem binomialMass_pascal (n : ℕ) (k j : ℤ) :
    binomialZ (n+1) (k-j) / 2^(n+1) =
      (binomialZ n (k-1-j) / 2^n + binomialZ n (k-j) / 2^n) / 2 := by
  rw [binomialZ_pascal, pow_succ]
  have he : k-j-1 = k-1-j := by ring
  rw [he]
  ring

theorem binomialZ_zero_trials (k : ℤ) : binomialZ 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k < 0
  · rw [binomialZ_negative _ _ hk, if_neg (by omega)]
  by_cases hz : k = 0
  · subst k
    norm_num [binomialZ]
  · rw [binomialZ_above _ _ (by omega), if_neg hz]

/-- Complete first-bin assignment law from the literal fair-coin sample space. -/
theorem freeFirstMass_binomial (ranking priority : Bool) (word : List Degree) (k : ℤ) :
    freeFirstMass ranking priority word k =
      binomialZ (activeTrials ranking word) (k-forcedChoices ranking priority word) /
        2^(activeTrials ranking word) := by
  induction word generalizing k with
  | nil => simp [freeFirstMass_nil, activeTrials, forcedChoices, binomialZ_zero_trials]
  | cons d ds ih =>
    rw [freeFirstMass_cons, ih, ih]
    cases d with
    | zero =>
      simp only [firstIncrement, activeTrials, forcedChoices, sub_zero]
      ring
    | singleton =>
      simpa only [firstIncrement, activeTrials, forcedChoices, Bool.false_eq_true,
        if_false, if_true, sub_zero] using
        (binomialMass_pascal (activeTrials ranking ds) k (forcedChoices ranking priority ds)).symm
    | flexible =>
      cases ranking with
      | false =>
        simpa only [firstIncrement, activeTrials, forcedChoices, Bool.false_and,
          Bool.false_eq_true, if_false, if_true, sub_zero] using
          (binomialMass_pascal (activeTrials false ds) k (forcedChoices false priority ds)).symm
      | true =>
        cases priority with
        | true =>
          simp only [firstIncrement, activeTrials, forcedChoices, Bool.not_true,
            Bool.and_false, Bool.false_eq_true, if_false, if_true, sub_zero]
          ring
        | false =>
          simp only [firstIncrement, activeTrials, forcedChoices, Bool.not_false,
            Bool.and_true, Bool.false_eq_true, if_false, if_true, sub_sub]
          ring

end TwoBin
