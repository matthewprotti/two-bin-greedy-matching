import TwoBin.SurvivalDistribution

namespace TwoBin

def ValidLoads (a b : ℕ) (loads : Loads) : Prop := loads.1 ≤ a ∧ loads.2 ≤ b

def continuationKernel (S K : ℕ) : List Degree → ℕ → ℚ
  | [], m => if K ≤ min S m then 1 else 0
  | .zero::ds, m => continuationKernel S K ds m
  | .singleton::ds, m =>
    (continuationKernel S K ds m + continuationKernel S K ds (min S (m+1)))/2
  | .flexible::ds, m => continuationKernel S K ds (min S (m+1))

theorem continuationKernel_clamp (S K : ℕ) (word : List Degree) (m : ℕ) :
    continuationKernel S K word (min S m) = continuationKernel S K word m := by
  induction word generalizing m with
  | nil => simp [continuationKernel, min_assoc]
  | cons d ds ih =>
    have he : min S (min S m + 1) = min S (m+1) := by omega
    cases d <;> simp only [continuationKernel, he, ih]

theorem continuationKernel_mono (S K : ℕ) (word : List Degree) (m M : ℕ) (hm : m ≤ M) :
    continuationKernel S K word m ≤ continuationKernel S K word M := by
  induction word generalizing m M with
  | nil =>
    have hh := min_le_min_left S hm
    by_cases hk : K ≤ min S m
    · have hk' : K ≤ min S M := hk.trans hh
      simp [continuationKernel, hk, hk']
    · simp only [continuationKernel, if_neg hk]
      split_ifs <;> norm_num
  | cons d ds ih =>
    have h1 := ih m M hm
    have h2 := ih (min S (m+1)) (min S (M+1)) (by omega)
    cases d <;> simp only [continuationKernel] <;> linarith

theorem step_valid (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (d : Degree) (coin : Bool) (h : ValidLoads a b loads) :
    ValidLoads a b (step a b ranking priority loads d coin) := by
  rcases loads with ⟨x,y⟩
  cases d <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [step, available, addAt, ValidLoads] at * <;> (try split_ifs) <;> simp_all <;> omega

theorem step_not_unsaturated (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (d : Degree) (coin : Bool) (h : ¬ Unsaturated a b loads) :
    ¬ Unsaturated a b (step a b ranking priority loads d coin) := by
  intro hh
  have hm := step_loads_monotone a b ranking priority loads d coin
  exact h ⟨lt_of_le_of_lt hm.1 hh.1, lt_of_le_of_lt hm.2 hh.2⟩

theorem step_total_unsaturated (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (d : Degree) (coin : Bool) (h : Unsaturated a b loads) :
    (step a b ranking priority loads d coin).1 + (step a b ranking priority loads d coin).2 =
      loads.1+loads.2+activeTrials false [d] := by
  rcases loads with ⟨x,y⟩
  cases d <;> cases ranking <;> cases priority <;> cases coin <;>
    simp [step, available, addAt, activeTrials, h.1, h.2] <;> omega

theorem step_total_flexible (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (coin : Bool) (h : ValidLoads a b loads) :
    (step a b ranking priority loads .flexible coin).1 +
      (step a b ranking priority loads .flexible coin).2 = min (a+b) (loads.1+loads.2+1) := by
  rcases loads with ⟨x,y⟩
  cases ranking <;> cases priority <;> cases coin <;>
    simp [step, available, addAt, ValidLoads] at * <;> (try split_ifs) <;> simp_all <;> omega

theorem singleton_totals_first_full (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (h : ValidLoads a b loads) (hx : loads.1 = a) :
    ((step a b ranking priority loads .singleton false).1 +
      (step a b ranking priority loads .singleton false).2 = loads.1+loads.2) ∧
    ((step a b ranking priority loads .singleton true).1 +
      (step a b ranking priority loads .singleton true).2 = min (a+b) (loads.1+loads.2+1)) := by
  rcases loads with ⟨x,y⟩
  simp only at hx
  subst x
  simp [step, available, addAt, ValidLoads] at *
  split_ifs <;> simp_all <;> omega

theorem singleton_totals_second_full (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (h : ValidLoads a b loads) (hy : loads.2 = b) :
    ((step a b ranking priority loads .singleton true).1 +
      (step a b ranking priority loads .singleton true).2 = loads.1+loads.2) ∧
    ((step a b ranking priority loads .singleton false).1 +
      (step a b ranking priority loads .singleton false).2 = min (a+b) (loads.1+loads.2+1)) := by
  rcases loads with ⟨x,y⟩
  simp only at hy
  subst y
  simp [step, available, addAt, ValidLoads] at *
  split_ifs <;> simp_all <;> omega

theorem saturated_continuation_step (a b K : ℕ) (ranking priority : Bool)
    (d : Degree) (ds : List Degree) (loads : Loads)
    (hv : ValidLoads a b loads) (hu : ¬ Unsaturated a b loads) :
    (continuationKernel (a+b) K ds ((step a b ranking priority loads d false).1 +
      (step a b ranking priority loads d false).2) +
     continuationKernel (a+b) K ds ((step a b ranking priority loads d true).1 +
      (step a b ranking priority loads d true).2))/2 =
      continuationKernel (a+b) K (d::ds) (loads.1+loads.2) := by
  cases d with
  | zero => simp only [step, continuationKernel]; ring
  | flexible =>
    rw [step_total_flexible a b ranking priority loads false hv,
      step_total_flexible a b ranking priority loads true hv]
    simp only [continuationKernel]
    ring
  | singleton =>
    have hf : loads.1=a ∨ loads.2=b := by unfold ValidLoads Unsaturated at *; omega
    rcases hf with hx | hy
    · have hs := singleton_totals_first_full a b ranking priority loads hv hx
      rw [hs.1,hs.2]
      rfl
    · have hs := singleton_totals_second_full a b ranking priority loads hv hy
      rw [hs.1,hs.2]
      simp only [continuationKernel]
      ring

/-- The actual source process has one common continuation law after saturation. -/
theorem tailKernel_saturated (a b K : ℕ) (ranking priority : Bool) (word : List Degree)
    (loads : Loads) (hv : ValidLoads a b loads) (hu : ¬ Unsaturated a b loads) :
    tailKernel a b ranking priority K word loads =
      continuationKernel (a+b) K word (loads.1+loads.2) := by
  induction word generalizing loads with
  | nil =>
    have hm : loads.1+loads.2 ≤ a+b := by exact add_le_add hv.1 hv.2
    simp [tailKernel, continuationKernel, min_eq_right hm]
  | cons d ds ih =>
    rw [tailKernel, ih _ (step_valid a b ranking priority loads d false hv)
      (step_not_unsaturated a b ranking priority loads d false hu),
      ih _ (step_valid a b ranking priority loads d true hv)
      (step_not_unsaturated a b ranking priority loads d true hu)]
    exact saturated_continuation_step a b K ranking priority d ds loads hv hu

def continuationGain (S K : ℕ) (d : Degree) (ds : List Degree) (m : ℕ) : ℚ :=
  continuationKernel S K ds (m+activeTrials false [d]) - continuationKernel S K (d::ds) m

theorem continuationGain_nonnegative (S K : ℕ) (d : Degree) (ds : List Degree) (m : ℕ) :
    0 ≤ continuationGain S K d ds m := by
  have hm := continuationKernel_mono S K ds m (m+1) (by omega)
  cases d with
  | zero => simp [continuationGain, continuationKernel, activeTrials]
  | flexible => simp [continuationGain, continuationKernel, activeTrials, continuationKernel_clamp]
  | singleton =>
    simp only [continuationGain, continuationKernel, activeTrials, continuationKernel_clamp]
    linarith

end TwoBin
