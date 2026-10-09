import ChallengeStatement
import TwoBin.Paired

namespace TwoBinChallenge

/-- The release theorem matches the separately written literal criterion.
The two recursive falling-factorial functions are first identified by induction. -/
theorem release_matches_literal_statement : PairedCriterion := by
  have hf (x : ℤ) (n : ℕ) : falling x n = TwoBin.falling x n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [falling, TwoBin.falling, ih]
  unfold PairedCriterion
  simp_rw [hf]
  exact TwoBin.paired_classification

end TwoBinChallenge
#print axioms TwoBinChallenge.release_matches_literal_statement
