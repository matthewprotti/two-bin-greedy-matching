import TwoBin.Definitions

/-! CHECKED SUPPORTING SOURCE. A literal finite sample space, not an abstract
    proposition whose name stands in for the actual matching process.
    Every job has one independent fair coin; its coin is unused for RK-flexible
    jobs and for zero-degree jobs. Duplicated outcomes keep the right weights. -/
namespace TwoBin

inductive Degree where
  | zero | singleton | flexible
  deriving DecidableEq, Repr

abbrev Loads := ℕ × ℕ

def coinWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (coinWords n).map (false :: ·) ++ (coinWords n).map (true :: ·)

def addAt (loads : Loads) (bin : Bool) : Loads :=
  if bin then (loads.1, loads.2+1) else (loads.1+1, loads.2)

def available (a b : ℕ) (loads : Loads) (bin : Bool) : Bool :=
  if bin then decide (loads.2 < b) else decide (loads.1 < a)

def step (a b : ℕ) (ranking priority : Bool) (loads : Loads)
    (degree : Degree) (coin : Bool) : Loads :=
  match degree with
  | .zero => loads
  | .singleton => if available a b loads coin then addAt loads coin else loads
  | .flexible =>
    let preferred := if ranking then priority else coin
    if available a b loads preferred then addAt loads preferred
    else if available a b loads (!preferred) then addAt loads (!preferred)
    else loads

def accepted (a b : ℕ) (ranking priority : Bool) (word : List Degree)
    (coins : List Bool) : ℕ :=
  let out := (word.zip coins).foldl
    (fun loads dc => step a b ranking priority loads dc.1 dc.2) (0,0)
  out.1 + out.2

def rvCount (a b : ℕ) (word : List Degree) (K : ℕ) : ℕ :=
  ((coinWords word.length).filter
    (fun cs => decide (K ≤ accepted a b false false word cs))).length

/-- Common denominator is 2^(n+1): average the two complete fixed-priority laws. -/
def rkCount (a b : ℕ) (word : List Degree) (K : ℕ) : ℕ :=
  ((coinWords word.length).filter
    (fun cs => decide (K ≤ accepted a b true false word cs))).length +
  ((coinWords word.length).filter
    (fun cs => decide (K ≤ accepted a b true true word cs))).length

def insertEverywhere (d : Degree) : List Degree → List (List Degree)
  | [] => [[d]]
  | h::t => (d::h::t) :: (insertEverywhere d t).map (h :: ·)

/-- Multiplicities retained: labeled permutations, even when degrees repeat. -/
def arrivalOrders : List Degree → List (List Degree)
  | [] => [[]]
  | d::ds => (arrivalOrders ds).flatMap (insertEverywhere d)

def FixedDominance (a b : ℕ) : Prop :=
  ∀ word : List Degree, ∀ K : ℕ, rkCount a b word K ≤ 2 * rvCount a b word K

def RandomOrderDominance (a b : ℕ) : Prop :=
  ∀ word : List Degree, ∀ K : ℕ,
    ((arrivalOrders word).map (fun w => rkCount a b w K)).sum ≤
    2 * ((arrivalOrders word).map (fun w => rvCount a b w K)).sum

/-- Unproved, source-anchored full paper target. -/
def FullClassificationTarget : Prop := ∀ a b : ℕ, 1 ≤ a → a ≤ b →
  (CapacityRegion a b ↔ FixedDominance a b) ∧
  (CapacityRegion a b ↔ RandomOrderDominance a b)

/-- Small examples proved by kernel reduction and included in the axiom audit. -/
theorem reversal_rv_count :
    rvCount 1 3 [.flexible, .flexible, .singleton] 3 = 5 := by decide

theorem reversal_rk_count :
    rkCount 1 3 [.flexible, .flexible, .singleton] 3 = 12 := by decide

theorem adjacent_rv_count :
    rvCount 2 3 [.flexible, .flexible, .singleton] 3 = 7 := by decide

theorem adjacent_rk_count :
    rkCount 2 3 [.flexible, .flexible, .singleton] 3 = 12 := by decide

end TwoBin
