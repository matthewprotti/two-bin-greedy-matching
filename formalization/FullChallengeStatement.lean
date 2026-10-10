import TwoBin.SourceModel

/-! Literal release contracts over the original frozen source model.
This file imports definitions and the original four finite controls, not the
classification proof. MODEL_LOCK.json pins those definitions to publication.
Independent human correspondence review remains a separate step. -/
namespace TwoBinChallenge

def FullCriterion : Prop := ∀ a b : ℕ, 1 ≤ a → a ≤ b →
  ((((b : ℤ)-(a : ℤ))^2 ≤ (a : ℤ)+(b : ℤ)-2) ↔
    ∀ word : List TwoBin.Degree, ∀ K : ℕ,
      TwoBin.rkCount a b word K ≤ 2*TwoBin.rvCount a b word K) ∧
  ((((b : ℤ)-(a : ℤ))^2 ≤ (a : ℤ)+(b : ℤ)-2) ↔
    ∀ word : List TwoBin.Degree, ∀ K : ℕ,
      ((TwoBin.arrivalOrders word).map (fun w => TwoBin.rkCount a b w K)).sum ≤
        2*((TwoBin.arrivalOrders word).map (fun w => TwoBin.rvCount a b w K)).sum)

def RegimesCriterion : Prop := ∀ a b : ℕ, 1 ≤ a → a ≤ b →
  ((∀ word : List TwoBin.Degree, ∀ K : ℕ,
    2*TwoBin.rvCount a b word K ≤ TwoBin.rkCount a b word K) ↔ a=1) ∧
  ((∀ word : List TwoBin.Degree, ∀ K : ℕ,
    2*((TwoBin.arrivalOrders word).map (fun w => TwoBin.rvCount a b w K)).sum ≤
      ((TwoBin.arrivalOrders word).map (fun w => TwoBin.rkCount a b w K)).sum) ↔ a=1) ∧
  ((∀ word : List TwoBin.Degree, ∀ K : ℕ,
    TwoBin.rkCount a b word K = 2*TwoBin.rvCount a b word K) ↔ a=1 ∧ b ≤ 2) ∧
  ((∀ word : List TwoBin.Degree, ∀ K : ℕ,
    ((TwoBin.arrivalOrders word).map (fun w => TwoBin.rkCount a b w K)).sum =
      2*((TwoBin.arrivalOrders word).map (fun w => TwoBin.rvCount a b w K)).sum) ↔ a=1 ∧ b ≤ 2)

end TwoBinChallenge
