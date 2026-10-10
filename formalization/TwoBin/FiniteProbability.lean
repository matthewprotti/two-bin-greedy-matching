import TwoBin.SourceBridge

/-! Exact finite fair-coin expectations, tied to the unchanged literal source model. -/
namespace TwoBin

def coinAverage (n : ℕ) (f : List Bool → ℚ) : ℚ :=
  ((coinWords n).map f).sum / 2^n

theorem coinAverage_zero (f : List Bool → ℚ) : coinAverage 0 f = f [] := by
  simp [coinAverage, coinWords]

theorem coinAverage_succ (n : ℕ) (f : List Bool → ℚ) :
    coinAverage (n+1) f =
      (coinAverage n (fun cs => f (false::cs)) +
       coinAverage n (fun cs => f (true::cs))) / 2 := by
  simp only [coinAverage, coinWords, List.map_append, List.map_map, List.sum_append, pow_succ, Function.comp_def]
  ring

theorem coinAverage_congr (n : ℕ) (f g : List Bool → ℚ)
    (h : ∀ cs ∈ coinWords n, f cs = g cs) : coinAverage n f = coinAverage n g := by
  unfold coinAverage
  congr 1
  exact congrArg List.sum (List.map_congr_left h)

theorem coinAverage_add (n : ℕ) (f g : List Bool → ℚ) :
    coinAverage n (fun cs => f cs + g cs) = coinAverage n f + coinAverage n g := by
  unfold coinAverage
  rw [List.sum_map_add]
  ring

theorem coinAverage_sub (n : ℕ) (f g : List Bool → ℚ) :
    coinAverage n (fun cs => f cs - g cs) = coinAverage n f - coinAverage n g := by
  unfold coinAverage
  have hs : ∀ xs : List (List Bool),
      (xs.map (fun cs => f cs - g cs)).sum = (xs.map f).sum - (xs.map g).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hs]
  ring

theorem coinAverage_const (n : ℕ) (c : ℚ) : coinAverage n (fun _ => c) = c := by
  induction n with
  | zero => simp [coinAverage_zero]
  | succ n ih => rw [coinAverage_succ]; simp only [ih]; ring

theorem coinAverage_nonnegative (n : ℕ) (f : List Bool → ℚ)
    (hf : ∀ cs ∈ coinWords n, 0 ≤ f cs) : 0 ≤ coinAverage n f := by
  unfold coinAverage
  apply div_nonneg _ (by positivity)
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hx
  exact hf cs hcs

theorem coinAverage_mono (n : ℕ) (f g : List Bool → ℚ)
    (hfg : ∀ cs ∈ coinWords n, f cs ≤ g cs) : coinAverage n f ≤ coinAverage n g := by
  have h := coinAverage_nonnegative n (fun cs => g cs - f cs) (by intro cs hc; exact sub_nonneg.mpr (hfg cs hc))
  rw [coinAverage_sub] at h
  linarith

theorem sum_indicator_eq_filter_length {α : Type*} (xs : List α) (p : α → Bool) :
    (xs.map (fun x => if p x then (1 : ℚ) else 0)).sum = ((xs.filter p).length : ℚ) := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih, add_comm]

def tailKernel (a b : ℕ) (ranking priority : Bool) (K : ℕ) : List Degree → Loads → ℚ
  | [], loads => if K ≤ loads.1+loads.2 then 1 else 0
  | d::ds, loads =>
    (tailKernel a b ranking priority K ds (step a b ranking priority loads d false) +
     tailKernel a b ranking priority K ds (step a b ranking priority loads d true)) / 2

theorem tailKernel_source (a b : ℕ) (ranking priority : Bool) (K : ℕ)
    (word : List Degree) (loads : Loads) :
    tailKernel a b ranking priority K word loads =
      coinAverage word.length (fun cs =>
        let out := runActual a b ranking priority (word.zip cs) loads
        if K ≤ out.1+out.2 then 1 else 0) := by
  induction word generalizing loads with
  | nil => simp [tailKernel, coinAverage_zero, runActual]
  | cons d ds ih =>
    simp only [List.length_cons, coinAverage_succ, tailKernel, ih,
      List.zip_cons_cons, runActual, List.foldl_cons]

theorem tailKernel_rvCount (a b K : ℕ) (word : List Degree) :
    tailKernel a b false false K word (0,0) = (rvCount a b word K : ℚ) / 2^word.length := by
  rw [tailKernel_source]
  simp only [coinAverage, rvCount, accepted, runActual]
  rw [← sum_indicator_eq_filter_length]
  simp

theorem tailKernel_rkCount (a b K : ℕ) (word : List Degree) :
    (tailKernel a b true false K word (0,0) + tailKernel a b true true K word (0,0))/2 =
      (rkCount a b word K : ℚ) / 2^(word.length+1) := by
  rw [tailKernel_source,tailKernel_source]
  simp only [coinAverage, rkCount, accepted, runActual, Nat.cast_add, pow_succ]
  rw [← sum_indicator_eq_filter_length, ← sum_indicator_eq_filter_length]
  simp only [Bool.decide_coe, decide_eq_true_eq]
  ring

theorem coinAverage_mul_const (n : ℕ) (f : List Bool → ℚ) (c : ℚ) :
    coinAverage n (fun cs => f cs*c) = coinAverage n f*c := by
  unfold coinAverage
  have hs : ∀ xs : List (List Bool), (xs.map (fun cs => f cs*c)).sum = (xs.map f).sum*c := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hs]
  ring

theorem coinAverage_div (n : ℕ) (f : List Bool → ℚ) (c : ℚ) :
    coinAverage n (fun cs => f cs/c) = coinAverage n f/c := by
  simp only [div_eq_mul_inv]
  exact coinAverage_mul_const n f c⁻¹

theorem coinAverage_snoc (n : ℕ) (f : List Bool → ℚ) :
    coinAverage (n+1) f =
      (coinAverage n (fun cs => f (cs++[false])) +
       coinAverage n (fun cs => f (cs++[true])))/2 := by
  induction n generalizing f with
  | zero => simp [coinAverage_succ, coinAverage_zero]
  | succ n ih =>
    rw [coinAverage_succ (n+1) f, ih, ih]
    simp only [coinAverage_succ, List.cons_append]
    ring

end TwoBin
