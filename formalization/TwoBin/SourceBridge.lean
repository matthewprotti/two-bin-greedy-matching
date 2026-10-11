import TwoBin.SourceModel
import TwoBin.Window

/-! Structural bridges for the literal source model. No stochastic law is assumed. -/
namespace TwoBin

theorem coinWords_length (n : ℕ) : (coinWords n).length = 2^n := by
  induction n with
  | zero => simp [coinWords]
  | succ n ih => simp [coinWords, ih, pow_succ, Nat.mul_two]

theorem coinWords_mem_length (n : ℕ) (cs : List Bool) (hc : cs ∈ coinWords n) :
    cs.length = n := by
  induction n generalizing cs with
  | zero => simpa [coinWords] using hc
  | succ n ih =>
    simp only [coinWords, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨xs, hx, rfl⟩ | ⟨xs, hx, rfl⟩ <;>
      simpa only [List.length_cons] using congrArg Nat.succ (ih xs hx)

theorem insertEverywhere_length (d : Degree) (word : List Degree) :
    (insertEverywhere d word).length = word.length+1 := by
  induction word with
  | nil => simp [insertEverywhere]
  | cons x xs ih => simp [insertEverywhere, ih]

theorem insertEverywhere_mem_length (d : Degree) (word out : List Degree)
    (ho : out ∈ insertEverywhere d word) : out.length = word.length+1 := by
  induction word generalizing out with
  | nil => simp only [insertEverywhere, List.mem_singleton] at ho; subst out; rfl
  | cons x xs ih =>
    simp only [insertEverywhere, List.mem_cons, List.mem_map] at ho
    rcases ho with rfl | ⟨ys, hy, rfl⟩
    · simp
    · simpa only [List.length_cons] using congrArg Nat.succ (ih ys hy)

theorem arrivalOrders_mem_length (word out : List Degree) (ho : out ∈ arrivalOrders word) :
    out.length = word.length := by
  induction word generalizing out with
  | nil => simpa [arrivalOrders] using ho
  | cons d ds ih =>
    simp only [arrivalOrders, List.mem_flatMap] at ho
    obtain ⟨xs, hx, ho⟩ := ho
    simpa only [List.length_cons, ih xs hx] using insertEverywhere_mem_length d xs out ho

theorem flatMap_length_constant {α β : Type*} (xs : List α) (f : α → List β) (n : ℕ)
    (hf : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hf x (by simp), ih (by intro y hy; exact hf y (by simp [hy]))]
    ring

/-- Labeled permutations are counted with their multiplicities, including repeats. -/
theorem arrivalOrders_length (word : List Degree) :
    (arrivalOrders word).length = word.length.factorial := by
  induction word with
  | nil => simp [arrivalOrders]
  | cons d ds ih =>
    change ((arrivalOrders ds).flatMap (insertEverywhere d)).length = (d::ds).length.factorial
    rw [flatMap_length_constant (arrivalOrders ds) (insertEverywhere d) (ds.length+1)
      (by intro x hx; rw [insertEverywhere_length, arrivalOrders_mem_length ds x hx])]
    rw [ih]
    simp only [List.length_cons, Nat.factorial_succ]
    ring

theorem fixedDominance_implies_randomOrderDominance (a b : ℕ) (h : FixedDominance a b) :
    RandomOrderDominance a b := by
  intro word K
  have hs : ∀ orders : List (List Degree),
      (orders.map (fun w => rkCount a b w K)).sum ≤
        2*(orders.map (fun w => rvCount a b w K)).sum := by
    intro orders
    induction orders with
    | nil => simp
    | cons w ws ih =>
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using add_le_add (h w K) ih
  exact hs (arrivalOrders word)

def Unsaturated (a b : ℕ) (loads : Loads) : Prop := loads.1 < a ∧ loads.2 < b

instance (a b : ℕ) (loads : Loads) : Decidable (Unsaturated a b loads) :=
  inferInstanceAs (Decidable (loads.1 < a ∧ loads.2 < b))

def freeStep (ranking priority : Bool) (loads : Loads) (degree : Degree) (coin : Bool) : Loads :=
  match degree with
  | .zero => loads
  | .singleton => addAt loads coin
  | .flexible => addAt loads (if ranking then priority else coin)

def runActual (a b : ℕ) (ranking priority : Bool) (events : List (Degree × Bool)) (loads : Loads) : Loads :=
  events.foldl (fun l dc => step a b ranking priority l dc.1 dc.2) loads

def runFree (ranking priority : Bool) (events : List (Degree × Bool)) (loads : Loads) : Loads :=
  events.foldl (fun l dc => freeStep ranking priority l dc.1 dc.2) loads

theorem step_loads_monotone (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (degree : Degree) (coin : Bool) :
    loads.1 ≤ (step a b ranking priority loads degree coin).1 ∧
    loads.2 ≤ (step a b ranking priority loads degree coin).2 := by
  rcases loads with ⟨x,y⟩
  cases degree <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [step, available, addAt] <;> split_ifs <;> simp_all

theorem freeStep_loads_monotone (ranking priority : Bool) (loads : Loads)
    (degree : Degree) (coin : Bool) :
    loads.1 ≤ (freeStep ranking priority loads degree coin).1 ∧
    loads.2 ≤ (freeStep ranking priority loads degree coin).2 := by
  rcases loads with ⟨x,y⟩
  cases degree <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [freeStep, addAt]

theorem step_unsaturated_iff (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (degree : Degree) (coin : Bool) :
    Unsaturated a b (step a b ranking priority loads degree coin) ↔
      Unsaturated a b (freeStep ranking priority loads degree coin) := by
  rcases loads with ⟨x,y⟩
  cases degree <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [step, freeStep, available, addAt, Unsaturated] <;>
    split_ifs <;> simp_all <;> omega

theorem step_eq_free_of_unsaturated (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (degree : Degree) (coin : Bool) (h : Unsaturated a b (step a b ranking priority loads degree coin)) :
    step a b ranking priority loads degree coin = freeStep ranking priority loads degree coin := by
  rcases loads with ⟨x,y⟩
  cases degree <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [step, freeStep, available, addAt, Unsaturated] at * <;>
    split_ifs at * <;> simp_all

theorem runActual_loads_monotone (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) :
    loads.1 ≤ (runActual a b ranking priority events loads).1 ∧
    loads.2 ≤ (runActual a b ranking priority events loads).2 := by
  induction events generalizing loads with
  | nil => simp [runActual]
  | cons dc ds ih =>
    have hs := step_loads_monotone a b ranking priority loads dc.1 dc.2
    have hi := ih (step a b ranking priority loads dc.1 dc.2)
    exact ⟨hs.1.trans hi.1, hs.2.trans hi.2⟩

theorem runFree_loads_monotone (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) :
    loads.1 ≤ (runFree ranking priority events loads).1 ∧
    loads.2 ≤ (runFree ranking priority events loads).2 := by
  induction events generalizing loads with
  | nil => simp [runFree]
  | cons dc ds ih =>
    have hs := freeStep_loads_monotone ranking priority loads dc.1 dc.2
    have hi := ih (freeStep ranking priority loads dc.1 dc.2)
    exact ⟨hs.1.trans hi.1, hs.2.trans hi.2⟩

/-- The actual and unconstrained processes have exactly the same no-saturation event. -/
theorem run_unsaturated_iff (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) :
    Unsaturated a b (runActual a b ranking priority events loads) ↔
      Unsaturated a b (runFree ranking priority events loads) := by
  induction events generalizing loads with
  | nil => rfl
  | cons dc ds ih =>
    change Unsaturated a b (runActual a b ranking priority ds (step a b ranking priority loads dc.1 dc.2)) ↔
      Unsaturated a b (runFree ranking priority ds (freeStep ranking priority loads dc.1 dc.2))
    by_cases h : Unsaturated a b (step a b ranking priority loads dc.1 dc.2)
    · rw [step_eq_free_of_unsaturated a b ranking priority loads dc.1 dc.2 h]
      exact ih _
    · have hf : ¬ Unsaturated a b (freeStep ranking priority loads dc.1 dc.2) := by
        rwa [← step_unsaturated_iff]
      have hleft : ¬ Unsaturated a b (runActual a b ranking priority ds (step a b ranking priority loads dc.1 dc.2)) := by
        intro hc
        have hm := runActual_loads_monotone a b ranking priority ds (step a b ranking priority loads dc.1 dc.2)
        exact h ⟨lt_of_le_of_lt hm.1 hc.1, lt_of_le_of_lt hm.2 hc.2⟩
      have hright : ¬ Unsaturated a b (runFree ranking priority ds (freeStep ranking priority loads dc.1 dc.2)) := by
        intro hc
        have hm := runFree_loads_monotone ranking priority ds (freeStep ranking priority loads dc.1 dc.2)
        exact hf ⟨lt_of_le_of_lt hm.1 hc.1, lt_of_le_of_lt hm.2 hc.2⟩
      simp only [hleft, hright]

theorem run_eq_free_of_unsaturated (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads)
    (h : Unsaturated a b (runActual a b ranking priority events loads)) :
    runActual a b ranking priority events loads = runFree ranking priority events loads := by
  induction events generalizing loads with
  | nil => rfl
  | cons dc ds ih =>
    have hm := runActual_loads_monotone a b ranking priority ds (step a b ranking priority loads dc.1 dc.2)
    have hstep : Unsaturated a b (step a b ranking priority loads dc.1 dc.2) :=
      ⟨lt_of_le_of_lt hm.1 h.1, lt_of_le_of_lt hm.2 h.2⟩
    change runActual a b ranking priority ds (step a b ranking priority loads dc.1 dc.2) =
      runFree ranking priority ds (freeStep ranking priority loads dc.1 dc.2)
    rw [ih _ h]
    change runFree ranking priority ds (step a b ranking priority loads dc.1 dc.2) =
      runFree ranking priority ds (freeStep ranking priority loads dc.1 dc.2)
    rw [step_eq_free_of_unsaturated a b ranking priority loads dc.1 dc.2 hstep]

/-- One-based arrival index of first saturation; `none` means it never occurs.
Zero-degree arrivals are retained, as in the literal source model. -/
def firstSaturationIndex (a b : ℕ) (ranking priority : Bool) :
    List (Degree × Bool) → Loads → Option ℕ
  | [], _ => none
  | dc::ds, loads =>
    let next := step a b ranking priority loads dc.1 dc.2
    if Unsaturated a b next then
      (firstSaturationIndex a b ranking priority ds next).map (fun t => t+1)
    else some 1

def truncatedFirstSaturation (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) : ℕ :=
  (firstSaturationIndex a b ranking priority events loads).getD events.length

theorem firstSaturationIndex_none_iff (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) (hstart : Unsaturated a b loads) :
    firstSaturationIndex a b ranking priority events loads = none ↔
      Unsaturated a b (runActual a b ranking priority events loads) := by
  induction events generalizing loads with
  | nil => simp [firstSaturationIndex, runActual, hstart]
  | cons dc ds ih =>
    by_cases hs : Unsaturated a b (step a b ranking priority loads dc.1 dc.2)
    · simpa only [firstSaturationIndex, if_pos hs, Option.map_eq_none_iff,
        runActual, List.foldl_cons] using ih _ hs
    · have hn : ¬ Unsaturated a b
          (runActual a b ranking priority ds (step a b ranking priority loads dc.1 dc.2)) := by
        intro hc
        have hm := runActual_loads_monotone a b ranking priority ds (step a b ranking priority loads dc.1 dc.2)
        exact hs ⟨lt_of_le_of_lt hm.1 hc.1, lt_of_le_of_lt hm.2 hc.2⟩
      simpa only [firstSaturationIndex, if_neg hs, Option.some_ne_none, false_iff,
        runActual, List.foldl_cons] using hn

theorem firstSaturationIndex_bounds (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) (t : ℕ)
    (ht : firstSaturationIndex a b ranking priority events loads = some t) :
    1 ≤ t ∧ t ≤ events.length := by
  induction events generalizing loads t with
  | nil => simp [firstSaturationIndex] at ht
  | cons dc ds ih =>
    simp only [firstSaturationIndex] at ht
    split_ifs at ht with hs
    · cases he : firstSaturationIndex a b ranking priority ds
          (step a b ranking priority loads dc.1 dc.2) with
      | none => simp [he] at ht
      | some k =>
        simp only [he, Option.map_some, Option.some.injEq] at ht
        have ht' : k+1 = t := Option.some.inj ht
        have hb := ih _ k he
        simp only [List.length_cons]
        omega
    · simp only [Option.some.injEq] at ht
      simp only [List.length_cons]
      omega

theorem truncatedFirstSaturation_le_length (a b : ℕ) (ranking priority : Bool)
    (events : List (Degree × Bool)) (loads : Loads) :
    truncatedFirstSaturation a b ranking priority events loads ≤ events.length := by
  unfold truncatedFirstSaturation
  cases he : firstSaturationIndex a b ranking priority events loads with
  | none => simp
  | some t => exact (firstSaturationIndex_bounds a b ranking priority events loads t he).2

/-- Count the literal source coin words on which neither bin has yet saturated. -/
def sourceSurvivalCount (a b : ℕ) (ranking priority : Bool) (word : List Degree) : ℕ :=
  ((coinWords word.length).filter (fun cs => decide
    (Unsaturated a b (runActual a b ranking priority (word.zip cs) (0,0))))).length

theorem sourceSurvivalCount_eq_free (a b : ℕ) (ranking priority : Bool) (word : List Degree) :
    sourceSurvivalCount a b ranking priority word =
    ((coinWords word.length).filter (fun cs => decide
      (Unsaturated a b (runFree ranking priority (word.zip cs) (0,0))))).length := by
  simp only [sourceSurvivalCount, run_unsaturated_iff]

/-- The computed no-saturation count is exactly the event that the stopping index is absent. -/
theorem sourceSurvivalCount_eq_no_saturation (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ranking priority : Bool) (word : List Degree) :
    sourceSurvivalCount a b ranking priority word =
      ((coinWords word.length).filter (fun cs => decide
        (firstSaturationIndex a b ranking priority (word.zip cs) (0,0) = none))).length := by
  have hstart : Unsaturated a b (0,0) := by constructor <;> omega
  have heq : (fun cs => decide (Unsaturated a b
      (runActual a b ranking priority (word.zip cs) (0,0)))) =
      (fun cs => decide (firstSaturationIndex a b ranking priority (word.zip cs) (0,0) = none)) := by
    funext cs
    simp only [firstSaturationIndex_none_iff a b ranking priority (word.zip cs) (0,0) hstart]
  unfold sourceSurvivalCount
  rw [heq]

end TwoBin
