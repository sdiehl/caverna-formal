/-
  Caverna.Food -- Food conversion economy
  ========================================

  Models the food conversion rules from the rulebook (p.11).
  Caverna's food economy is rich: animals, crops, rubies, and gold
  can all be converted to food. The donkey conversion is notably
  super-linear: 2 donkeys give 3 food, not 2.
-/

import Caverna.Types

namespace Caverna

/-- Food value of a single sheep. -/
def sheepFoodValue : Nat := 1

/-- Food value of a single wild boar. -/
def wildBoarFoodValue : Nat := 2

/-- Food value of a single cattle. -/
def cattleFoodValue : Nat := 3

/-- Food value of a single grain. -/
def grainFoodValue : Nat := 1

/-- Food value of a single vegetable. -/
def vegetableFoodValue : Nat := 2

/-- Food value of a single ruby (can be exchanged for a 2-food good). -/
def rubyFoodValue : Nat := 2

/-- Food from converting donkeys. This is the quirky rule:
    1 donkey = 1 food, but 2 donkeys = 3 food (not 2!).
    For n donkeys: pairs contribute 3 each, remainder contributes 1. -/
def donkeyFoodValue (n : Nat) : Nat :=
  let pairs := n / 2
  let remainder := n % 2
  pairs * 3 + remainder * 1

/-- Food from converting gold: you pay (food_wanted + 1) gold.
    So n gold buys (n - 1) food, but only if n >= 2. -/
def goldToFood (goldSpent : Nat) : Nat :=
  if goldSpent >= 2 then goldSpent - 1 else 0

/-- Total food obtainable by converting all of a player's convertible goods.
    This represents the maximum food a player could produce in an emergency. -/
def maxFoodFromSupply (s : Supply) (ac : AnimalCounts) : Nat :=
  ac.sheep * sheepFoodValue +
  donkeyFoodValue ac.donkeys +
  ac.wildBoars * wildBoarFoodValue +
  ac.cattle * cattleFoodValue +
  s.grain * grainFoodValue +
  s.vegetables * vegetableFoodValue +
  s.rubies * rubyFoodValue +
  s.food +
  goldToFood s.gold

/-- Food required to feed dwarfs during a normal harvest. -/
def feedingCost (numAdultDwarfs numOffspring : Nat) : Nat :=
  numAdultDwarfs * 2 + numOffspring * 1

/-- Food required during the round-4 special feeding (1 per dwarf). -/
def round4FeedingCost (totalDwarfs : Nat) : Nat :=
  totalDwarfs

end Caverna
