import TwoBin.WitnessExpansion

namespace TwoBin

def insertAt (d : Degree) : ℕ → List Degree → List Degree
  | 0, word => d::word
  | _+1, [] => []
  | i+1, x::xs => x::insertAt d i xs

theorem insertAt_length (d : Degree) (i : ℕ) (word : List Degree) (hi : i ≤ word.length) :
    (insertAt d i word).length=word.length+1 := by
  induction word generalizing i with
  | nil =>
    have hz : i=0 := by simpa using hi
    subst i
    rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => simpa [insertAt] using congrArg Nat.succ (ih i (by simp at hi; omega))

theorem insertEverywhere_range (d : Degree) (word : List Degree) :
    insertEverywhere d word = (List.range (word.length+1)).map (fun i => insertAt d i word) := by
  induction word with
  | nil => rfl
  | cons x xs ih =>
    simp only [insertEverywhere,ih,List.length_cons,List.range_succ_eq_map,
      List.map_cons,List.map_map,Function.comp_def,insertAt]

theorem insertAt_mem (d : Degree) (i : ℕ) (word : List Degree) (x : Degree)
    (hx : x ∈ insertAt d i word) : x=d ∨ x ∈ word := by
  induction i generalizing word with
  | zero => simpa [insertAt] using hx
  | succ i ih =>
    cases word with
    | nil => simp [insertAt] at hx
    | cons y ys =>
      simp only [insertAt,List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (by simp)
      · rcases ih ys hx with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem positiveWord_insertAt (d : Degree) (hd : d ≠ .zero) (i : ℕ) (word : List Degree)
    (hw : PositiveWord word) : PositiveWord (insertAt d i word) := by
  intro x hx
  rcases insertAt_mem d i word x hx with rfl | h
  · exact hd
  · exact hw x h

theorem forcedChoices_cons_flex (d : Degree) (word : List Degree) :
    forcedChoices true false (d::word) =
      (if d=Degree.flexible then 1 else 0)+forcedChoices true false word := by
  cases d <;> simp [forcedChoices]

theorem forcedChoices_insertAt_take (i t : ℕ) (word : List Degree) (hi : i ≤ word.length) :
    forcedChoices true false ((insertAt .flexible i word).take t) =
      if i<t then 1+forcedChoices true false (word.take (t-1))
      else forcedChoices true false (word.take t) := by
  induction word generalizing i t with
  | nil =>
    have hz : i=0 := by simpa using hi
    subst i
    cases t <;> simp [insertAt,forcedChoices]
  | cons d ds ih =>
    cases i with
    | zero => cases t <;> simp [insertAt,forcedChoices]
    | succ i =>
      have hi' : i ≤ ds.length := by simp at hi; omega
      cases t with
      | zero => simp [forcedChoices]
      | succ t =>
        cases t with
        | zero => simp [insertAt,forcedChoices]
        | succ t =>
          have hh := ih i (t+1) hi'
          simp only [insertAt,List.take_succ_cons,forcedChoices_cons_flex,
            Nat.succ_lt_succ_iff,Nat.succ_sub_one]
          rw [hh]
          simp only [Nat.add_sub_cancel]
          split_ifs <;> ring

theorem forcedChoices_take_le (word : List Degree) (t : ℕ) :
    forcedChoices true false (word.take t) ≤ forcedChoices true false word := by
  have h := forcedChoices_append true false (word.take t) (word.drop t)
  rw [List.take_append_drop] at h
  have hp := forcedChoices_nonnegative true false (word.drop t)
  omega

theorem forcedChoices_take_zero (word : List Degree) (h : forcedChoices true false word=0) (t : ℕ) :
    forcedChoices true false (word.take t)=0 := by
  have h1 := forcedChoices_take_le word t
  have h2 := forcedChoices_nonnegative true false (word.take t)
  omega

theorem forcedChoices_insertAt (i : ℕ) (word : List Degree) (hi : i ≤ word.length) :
    forcedChoices true false (insertAt .flexible i word) = 1+forcedChoices true false word := by
  have h := forcedChoices_insertAt_take i (word.length+1) word hi
  rw [List.take_of_length_le (by rw [insertAt_length _ _ _ hi]),if_pos (by omega),
    Nat.add_sub_cancel,List.take_length] at h
  exact h

def twiceInserted (s i j : ℕ) : List Degree :=
  insertAt .flexible j (insertAt .flexible i (List.replicate s .singleton))

theorem twiceInserted_length (s i j : ℕ) (hi : i < s+1) (hj : j < s+2) :
    (twiceInserted s i j).length=s+2 := by
  unfold twiceInserted
  have h1 : (insertAt .flexible i (List.replicate s Degree.singleton)).length=s+1 := by
    simpa using insertAt_length .flexible i (List.replicate s .singleton) (by simp; omega)
  rw [insertAt_length _ _ _ (by rw [h1]; omega),h1]

theorem twiceInserted_positive (s i j : ℕ) : PositiveWord (twiceInserted s i j) := by
  apply positiveWord_insertAt _ (by decide)
  apply positiveWord_insertAt _ (by decide)
  intro d hd
  have he : d=Degree.singleton := (List.mem_replicate.mp hd).2
  subst d
  decide

theorem twiceInserted_flexible_count (s i j : ℕ) (hi : i < s+1) (hj : j < s+2) :
    forcedChoices true false (twiceInserted s i j)=2 := by
  unfold twiceInserted
  have hi' : i ≤ (List.replicate s Degree.singleton).length := by simp; omega
  rw [forcedChoices_insertAt j _ (by rw [insertAt_length _ _ _ hi',List.length_replicate]; omega),
    forcedChoices_insertAt i _ hi',forcedChoices_singletons]
  norm_num

theorem twiceInserted_prefix_two (s i j t : ℕ) (hi : i < s+1) (hj : j < s+2) :
    forcedChoices true false ((twiceInserted s i j).take t)=2 ↔ i<t-1 ∧ j<t := by
  have hi' : i ≤ (List.replicate s Degree.singleton).length := by simp; omega
  have hz (k : ℕ) : forcedChoices true false ((List.replicate s Degree.singleton).take k)=0 :=
    forcedChoices_take_zero _ (forcedChoices_singletons true false s) k
  unfold twiceInserted
  rw [forcedChoices_insertAt_take j t _ (by rw [insertAt_length _ _ _ hi',List.length_replicate]; omega)]
  rw [forcedChoices_insertAt_take i (t-1) _ hi',forcedChoices_insertAt_take i t _ hi']
  simp only [hz,add_zero]
  split_ifs <;> omega

theorem list_sum_map_flatMap {α β : Type*} (xs : List α) (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons,List.map_append,List.sum_append,ih]

theorem list_sum_map_range (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

theorem insertEverywhere_sum (d : Degree) (word : List Degree) (f : List Degree → ℚ) :
    ((insertEverywhere d word).map f).sum =
      ∑ i ∈ Finset.range (word.length+1), f (insertAt d i word) := by
  rw [insertEverywhere_range,List.map_map]
  exact list_sum_map_range _ _

theorem arrivalOrders_replicate (d : Degree) (n : ℕ) :
    arrivalOrders (List.replicate n d) = List.replicate n.factorial (List.replicate n d) := by
  apply List.eq_replicate_iff.mpr
  constructor
  · simp [arrivalOrders_length]
  · intro out ho
    rw [arrivalOrders_eq_permutations] at ho
    have hp := List.mem_permutations'.mp ho
    apply List.eq_replicate_iff.mpr
    constructor
    · simpa using hp.length_eq
    · intro x hx
      exact (List.mem_replicate.mp (hp.mem_iff.mp hx)).2

theorem arrivalOrders_replicate_sum (d : Degree) (n : ℕ) (f : List Degree → ℚ) :
    ((arrivalOrders (List.replicate n d)).map f).sum =
      (n.factorial : ℚ)*f (List.replicate n d) := by
  rw [arrivalOrders_replicate,List.map_replicate,List.sum_replicate]
  simp [nsmul_eq_mul]

/-- The two labeled flexible jobs produce every insertion pair, with s! copies. -/
theorem arrivalOrders_two_flexible_sum (s : ℕ) (f : List Degree → ℚ) :
    ((arrivalOrders (.flexible::.flexible::List.replicate s .singleton)).map f).sum =
      (s.factorial : ℚ)*∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+2), f (twiceInserted s i j) := by
  change ((((arrivalOrders (List.replicate s Degree.singleton)).flatMap (insertEverywhere .flexible)).flatMap
      (insertEverywhere .flexible)).map f).sum = _
  rw [list_sum_map_flatMap,list_sum_map_flatMap,arrivalOrders_replicate_sum,insertEverywhere_sum]
  simp only [List.length_replicate]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [insertEverywhere_sum,insertAt_length _ _ _ (by simp; have := Finset.mem_range.mp hi; omega)]
  simp only [List.length_replicate]
  rfl

end TwoBin
