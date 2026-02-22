/-
  Caverna.Thm.Food -- Food economy theorems
  ===========================================

  Proven properties of the food conversion system.
  Key findings: donkey super-linearity, gold inefficiency,
  starting food insufficiency, and round-4 feeding discount.

  Uses v4.28 tactics: `simp +locals` for unfolding file-local definitions,
  `decide` for concrete numeric equalities, `omega` for linear arithmetic.
-/

import Caverna.Food

namespace Caverna

/-- The donkey conversion is super-linear: 2 donkeys give 3 food, not 2.
    This is a genuine mechanical quirk that rewards batching donkeys. -/
theorem donkey_pair_bonus : donkeyFoodValue 2 = 3 := by decide

/-- Single donkey gives just 1 food. -/
theorem donkey_single : donkeyFoodValue 1 = 1 := by decide

/-- Three donkeys give 4 food (1 pair = 3, plus 1 remainder = 1). -/
theorem donkey_three : donkeyFoodValue 3 = 4 := by decide

/-- Four donkeys give 6 food (2 pairs, each worth 3). -/
theorem donkey_four : donkeyFoodValue 4 = 6 := by decide

/-- The donkey super-linearity: converting 2 donkeys gives strictly more
    food than converting them individually (3 > 1 + 1).
    This is a genuine game design quirk worth exploiting. -/
theorem donkey_superlinear :
    donkeyFoodValue 2 > donkeyFoodValue 1 + donkeyFoodValue 1 := by decide

/-- Cattle is the most food-efficient single animal (3 food per unit). -/
theorem cattle_most_efficient :
    cattleFoodValue > wildBoarFoodValue /\
    cattleFoodValue > sheepFoodValue := by
  constructor <;> decide

/-- Vegetables are twice as food-efficient as grain. -/
theorem vegetable_over_grain :
    vegetableFoodValue = 2 * grainFoodValue := by decide

/-- Gold-to-food conversion is always lossy: you lose 1 gold as overhead.
    Spending 2 gold gets only 1 food. Spending 1 gold gets nothing. -/
theorem gold_food_lossy : goldToFood 2 = 1 := by decide
theorem gold_one_worthless : goldToFood 1 = 0 := by decide
theorem gold_zero_worthless : goldToFood 0 = 0 := by decide

/-- Gold-to-food has diminishing marginal loss: the overhead is always 1,
    so bigger batches are relatively more efficient.
    For n >= 2, goldToFood(n) = n - 1. -/
theorem gold_food_formula (n : Nat) (h : n >= 2) :
    goldToFood n = n - 1 := by
  simp [goldToFood]
  omega

/-- A player with 2 dwarfs needs 4 food per harvest. -/
theorem two_dwarf_feeding : feedingCost 2 0 = 4 := by decide

/-- A player with 5 dwarfs (max normal) needs 10 food per harvest. -/
theorem five_dwarf_feeding : feedingCost 5 0 = 10 := by decide

/-- Feeding cost with offspring: 5 adults + 1 newborn = 11 food. -/
theorem feeding_with_offspring : feedingCost 5 1 = 11 := by decide

/-- Round 4 special feeding is always cheaper than a normal harvest
    (1 food per dwarf vs 2 food per dwarf). -/
theorem round4_cheaper (n : Nat) (hn : n > 0) :
    round4FeedingCost n < feedingCost n 0 := by
  simp only [round4FeedingCost, feedingCost]
  omega

/-- Starting food (1 for starting player) cannot feed 2 dwarfs at harvest.
    This means the starting player MUST acquire food before round 3. -/
theorem starting_food_insufficient :
    (1 : Nat) < feedingCost 2 0 := by decide

/-- Even 3rd-player starting food (2 food) is insufficient for first harvest. -/
theorem third_player_food_insufficient :
    (2 : Nat) < feedingCost 2 0 := by decide

/-- A ruby can always be converted to at least 2 food.
    This makes rubies one of the most flexible emergency resources. -/
theorem ruby_emergency_food : rubyFoodValue >= 2 := by decide

/-- Feeding cost scales linearly: each adult dwarf adds exactly 2 food cost. -/
theorem feeding_cost_per_adult (n : Nat) :
    feedingCost (n + 1) 0 = feedingCost n 0 + 2 := by
  simp only [feedingCost]
  omega

/-- Maximum food deficit at first harvest (round 3): player starts with 1 food,
    needs 4 for 2 dwarfs. Deficit is exactly 3. -/
theorem first_harvest_deficit :
    feedingCost 2 0 - startingFoodP1 = 3 := by decide

end Caverna
