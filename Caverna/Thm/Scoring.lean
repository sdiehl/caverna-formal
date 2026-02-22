/-
  Caverna.Thm.Scoring -- Scoring system theorems
  ================================================

  Proven properties of the end-game scoring formula.
  Uses v4.28 tactics: `simp +locals` for unfolding file-local definitions,
  `grind +locals` for structural reasoning with local e-match lemmas.
-/

import Caverna.Scoring

namespace Caverna

/-- The maximum possible penalty from missing all 4 farm animal types is 8. -/
theorem max_missing_animal_penalty :
    forall (ac : AnimalCounts), penaltyMissingAnimals ac <= 8 := by
  intro ac
  simp only [penaltyMissingAnimals, AnimalCounts.missingFarmTypes]
  split <;> split <;> split <;> split <;> omega

/-- An empty home board (24 spaces) incurs exactly 24 penalty points for unused spaces.
    This is the worst-case board penalty. -/
theorem worst_case_unused_penalty :
    penaltyUnusedSpaces 24 = 24 := by
  decide

/-- Having all 4 farm animal types means zero missing-type penalty. -/
theorem no_missing_penalty_if_all_types (ac : AnimalCounts)
    (hs : ac.sheep > 0) (hd : ac.donkeys > 0)
    (hw : ac.wildBoars > 0) (hc : ac.cattle > 0) :
    penaltyMissingAnimals ac = 0 := by
  simp [penaltyMissingAnimals, AnimalCounts.missingFarmTypes]
  split <;> split <;> split <;> split <;> omega

/-- Grain scoring: 0 grain = 0 points (edge case for the rounding rule). -/
theorem grain_zero : scoreGrain 0 = 0 := by decide

/-- Grain scoring: 1 grain = 1 point (rounds up from 0.5). -/
theorem grain_one : scoreGrain 1 = 1 := by decide

/-- Grain scoring: 2 grain = 1 point. -/
theorem grain_two : scoreGrain 2 = 1 := by decide

/-- Grain scoring: 3 grain = 2 points. -/
theorem grain_three : scoreGrain 3 = 2 := by decide

/-- Grain scoring is monotonically non-decreasing. -/
theorem grain_score_monotone (a b : Nat) (h : a <= b) :
    scoreGrain a <= scoreGrain b := by
  simp only [scoreGrain]
  omega

/-- Each begging marker costs exactly 3 points, which is the single harshest
    per-item penalty in the game. This makes avoiding begging critical. -/
theorem begging_is_harsh (n : Nat) (hn : n > 0) :
    penaltyBegging n >= 3 := by
  simp only [penaltyBegging]
  omega

/-- Begging penalty scales linearly: n markers cost exactly 3n points. -/
theorem begging_penalty_linear (n : Nat) :
    penaltyBegging n = 3 * n := by
  simp only [penaltyBegging]
  omega

/-- Mine scoring: ore mines are worth 3, ruby mines worth 4.
    Ruby mines are strictly more valuable per slot. -/
theorem ruby_mine_beats_ore_mine :
    scoreMines 0 1 > scoreMines 1 0 := by decide

/-- A single pasture of each size: small gives 2, large gives 4.
    Large pastures are exactly 2x the scoring value. -/
theorem large_pasture_double_score :
    scorePastures 0 1 = 2 * scorePastures 1 0 := by decide

/-- The missing animal penalty is strictly worse than begging for
    1 marker (8 vs 3). Having no animals at all is devastating. -/
theorem all_missing_worse_than_one_beg :
    penaltyMissingAnimals { sheep := 0, donkeys := 0, wildBoars := 0, cattle := 0, dogs := 0 }
    > penaltyBegging 1 := by decide

end Caverna
