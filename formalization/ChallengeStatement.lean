import Mathlib.Algebra.Order.Field.Rat

/-! Frozen literal statement for correspondence review. This file depends on
Mathlib alone, not on the proof library or its target aliases. It has not been
independently audited by a human specialist. -/
namespace TwoBinChallenge

def falling (x : ℤ) : ℕ → ℤ
  | 0 => 1
  | n+1 => falling x n * (x-(n : ℤ))

def PairedCriterion : Prop := ∀ r q : ℕ, r ≤ q →
  ((((q : ℤ)-(r : ℤ))^2 ≤ (r : ℤ)+(q : ℤ)) ↔
    ∀ u v : ℕ,
      falling (r : ℤ) (u+v) + falling (q : ℤ) (u+v) ≤
        falling (r : ℤ) u * falling (q : ℤ) v +
        falling (q : ℤ) u * falling (r : ℤ) v)

end TwoBinChallenge
