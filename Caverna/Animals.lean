/-
  Caverna.Animals -- Animal husbandry capacity model
  ====================================================

  Models the animal housing rules from the rulebook (p.20).
  Each space type has specific capacity rules. Dogs are special:
  they watch sheep on meadows/pastures but cannot live in mines.
-/

import Caverna.Types

namespace Caverna

-- ============================================================
-- Capacity per space type
-- ============================================================

/-- Capacity of the entry-level dwelling for farm animals.
    It holds 2 farm animals of the same type. -/
def entryLevelDwellingCapacity : Nat := 2

/-- A small pasture (1 fenced meadow) holds 2 same-type farm animals. -/
def smallPastureCapacity : Nat := 2

/-- A small pasture with stable doubles capacity. -/
def smallPastureStableCapacity : Nat := 4

/-- A large pasture (2 fenced meadows) holds 4 same-type farm animals. -/
def largePastureCapacity : Nat := 4

/-- A large pasture with 1 stable holds 8 same-type. -/
def largePastureOneStableCapacity : Nat := 8

/-- A large pasture with 2 stables holds 16 same-type. -/
def largePastureTwoStableCapacity : Nat := 16

/-- A stable on a meadow (not pasture) holds 1 any farm animal. -/
def meadowStableCapacity : Nat := 1

/-- A stable on a forest (uncleared) holds exactly 1 wild boar. -/
def forestStableCapacity : Nat := 1  -- wild boar only

/-- Each ore or ruby mine holds 1 donkey. -/
def mineCapacity : Nat := 1  -- donkey only

/-- Dog-sheep watching: n dogs on a meadow/pasture watch (n+1) sheep.
    This replaces the normal capacity rules for that space. -/
def dogSheepCapacity (numDogs : Nat) : Nat :=
  numDogs + 1

-- ============================================================
-- Maximum animal capacity calculations
-- ============================================================

/-- Maximum sheep capacity using the dog-watching trick on a large
    pasture with 2 stables. With k dogs, you get k+1 sheep.
    But if you use dogs, you cannot use the stables for normal capacity.
    So the tradeoff: 16 same-type via stables, or (dogs+1) sheep via dogs.
    Dogs only make sense when you have more than 16 dogs on that pasture,
    which is absurd. The real use is on unstabled meadows/pastures. -/
def dogSheepOnMeadow (numDogs : Nat) : Nat :=
  numDogs + 1

end Caverna
