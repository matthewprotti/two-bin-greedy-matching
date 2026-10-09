import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

/-! CHECKED SUPPORTING SOURCE. See STATUS.json. Integer subtraction is intentional:
    it avoids silently truncating the capacity gap or the witness numerators. -/
namespace TwoBin

def falling (x : ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => falling x n * (x - (n : ℤ))

def QuadraticRegion (r q : ℕ) : Prop :=
  ((q : ℤ) - (r : ℤ)) ^ 2 ≤ (r : ℤ) + (q : ℤ)

def CapacityRegion (a b : ℕ) : Prop :=
  ((b : ℤ) - (a : ℤ)) ^ 2 ≤ (a : ℤ) + (b : ℤ) - 2

def PairedBound (r q : ℕ) : Prop := ∀ u v : ℕ,
  falling (r : ℤ) (u + v) + falling (q : ℤ) (u + v) ≤
  falling (r : ℤ) u * falling (q : ℤ) v +
  falling (q : ℤ) u * falling (r : ℤ) v

/-- Full algebraic target; defining a proposition is not proving it. -/
def PairedClassificationTarget : Prop := ∀ r q : ℕ, r ≤ q →
  (QuadraticRegion r q ↔ PairedBound r q)

end TwoBin
