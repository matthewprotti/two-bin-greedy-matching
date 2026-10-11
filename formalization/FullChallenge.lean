import FullChallengeStatement
import TwoBin.FourRegimes

namespace TwoBinChallenge

theorem release_matches_full_statement : FullCriterion := TwoBin.full_classification

theorem regimes_match_literal_statement : RegimesCriterion := by
  intro a b ha hab
  exact ⟨TwoBin.fixed_reverse_classification a b ha hab,
    TwoBin.random_reverse_classification a b ha hab,
    TwoBin.fixed_equality_classification a b ha hab,
    TwoBin.random_equality_classification a b ha hab⟩

end TwoBinChallenge
#print axioms TwoBin.full_classification
#print axioms TwoBin.four_regimes
#print axioms TwoBinChallenge.release_matches_full_statement
#print axioms TwoBinChallenge.regimes_match_literal_statement
