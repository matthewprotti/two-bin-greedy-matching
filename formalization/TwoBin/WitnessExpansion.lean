import TwoBin.FixedWitness

namespace TwoBin

theorem two_flex_contribution (r q : ℕ) (pre : List Degree) (d : Degree) (ds : List Degree)
    (hp : PositiveWord pre) (hw : PositiveWord (d::ds))
    (hf : forcedChoices true false pre + forcedChoices true false (d::ds) = 2)
    (hn : pre.length+(d::ds).length = r+q+1) :
    sourceSurvivalGap (r+1) (q+1) pre *
      continuationGain ((r+1)+(q+1)) (r+q+1) d ds (activeTrials false pre) =
    if forcedChoices true false pre=2 then twoFlexCoefficient r q pre.length / 2^(r+q+1) else 0 := by
  have hpf := forcedChoices_nonnegative true false pre
  have hwf := forcedChoices_nonnegative true false (d::ds)
  by_cases htwo : forcedChoices true false pre=2
  · rw [if_pos htwo]
    have hrest : forcedChoices true false (d::ds)=0 := by omega
    have htail := forcedChoices_nonnegative true false ds
    have hd0 := hw d (by simp)
    have hds : PositiveWord ds := by intro x hx; exact hw x (by simp [hx])
    have hd : d=Degree.singleton := by
      cases d with
      | zero => exact False.elim (hd0 rfl)
      | singleton => rfl
      | flexible => simp [forcedChoices] at hrest; omega
    subst d
    have hfc : forcedChoices true false ds=0 := by simpa [forcedChoices] using hrest
    have hs : activeTrials true ds=ds.length := by
      have hh := activeTrials_split ds
      rw [activeTrials_positive ds hds,hfc] at hh
      omega
    have hpre : activeTrials false pre=pre.length := activeTrials_positive pre hp
    rw [sourceSurvivalGap_two r q pre htwo (by rw [hpre]; simp only [List.length_cons] at hn; omega),hpre]
    rw [continuationGain_all_matched _ _ ds pre.length hds
      (by simp only [List.length_cons] at hn; omega) (by omega),hs]
    have hn' : pre.length+(ds.length+1)=r+q+1 := by simpa only [List.length_cons] using hn
    calc
      _ = twoFlexCoefficient r q pre.length / (2^pre.length * 2^(ds.length+1)) := by ring
      _ = twoFlexCoefficient r q pre.length / 2^(pre.length+(ds.length+1)) := by rw [pow_add (2 : ℚ) pre.length (ds.length+1)]
      _ = _ := by rw [hn']
  · rw [if_neg htwo,sourceSurvivalGap_zero r q pre (by omega)]
    ring

def witnessSum (r q : ℕ) (pre : List Degree) : List Degree → ℚ
  | [] => 0
  | d::ds => (if forcedChoices true false pre=2 then twoFlexCoefficient r q pre.length else 0) +
      witnessSum r q (pre++[d]) ds

theorem prefixGap_two_profile (r q : ℕ) (pre word : List Degree)
    (hp : PositiveWord pre) (hw : PositiveWord word)
    (hf : forcedChoices true false pre + forcedChoices true false word = 2)
    (hn : pre.length+word.length = r+q+1) :
    prefixGap (r+1) (q+1) (r+q+1) pre word = witnessSum r q pre word / 2^(r+q+1) := by
  induction word generalizing pre with
  | nil => simp [prefixGap_nil,witnessSum]
  | cons d ds ih =>
    have hds : PositiveWord ds := by intro x hx; exact hw x (by simp [hx])
    have hpre : PositiveWord (pre++[d]) := by
      rw [positiveWord_append]
      exact ⟨hp,by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact hw d (by simp)⟩
    have hf' : forcedChoices true false (pre++[d]) + forcedChoices true false ds=2 := by
      rw [forcedChoices_append]
      cases d <;> simp [forcedChoices] at * <;> omega
    have hn' : (pre++[d]).length+ds.length=r+q+1 := by simp at *; omega
    rw [prefixGap_cons,two_flex_contribution r q pre d ds hp hw hf hn,ih _ hpre hds hf' hn']
    simp only [witnessSum]
    split_ifs <;> ring

theorem witnessSum_range (r q : ℕ) (pre word : List Degree) :
    witnessSum r q pre word = ∑ i ∈ Finset.range word.length,
      if forcedChoices true false (pre++word.take i)=2 then
        twoFlexCoefficient r q (pre++word.take i).length else 0 := by
  induction word generalizing pre with
  | nil => simp [witnessSum]
  | cons d ds ih =>
    rw [witnessSum,ih]
    simp only [List.length_cons,Finset.sum_range_succ',List.take_zero,List.append_nil,
      List.take_succ_cons,List.append_assoc,List.singleton_append]
    ring

/-- Actual all-matched gap as a finite weighted prefix sum for any positive two-flexible word. -/
theorem matchingGap_two_profile (r q : ℕ) (word : List Degree)
    (hw : PositiveWord word) (hf : forcedChoices true false word=2)
    (hn : word.length=r+q+1) :
    matchingGap (r+1) (q+1) (r+q+1) word =
      (∑ i ∈ Finset.range (r+q+1), if forcedChoices true false (word.take i)=2 then
        twoFlexCoefficient r q i else 0) / 2^(r+q+1) := by
  rw [matchingGap_prefix,prefixGap_two_profile r q [] word (by simp [PositiveWord]) hw
    (by simpa [forcedChoices] using hf) (by simpa using hn),witnessSum_range]
  simp only [List.nil_append,hn]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have he : (word.take i).length=i := by rw [List.length_take,hn,min_eq_left (by omega)]
  rw [he]

end TwoBin
