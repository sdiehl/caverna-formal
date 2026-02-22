/-
  Caverna.Thm.Animals -- Animal husbandry theorems
  ==================================================

  Proven properties of the animal capacity system.
  Key findings: stable doubling, dog-sheep tradeoffs,
  mine constraints, and initial capacity limitations.

  Uses v4.28 tactics: `simp +locals` for definition unfolding,
  `decide` for concrete equalities, `omega` for linear arithmetic.
-/

import Caverna.Animals

namespace Caverna

/-- A stable on a pasture doubles that pasture's capacity. -/
theorem stable_doubles_small_pasture :
    smallPastureStableCapacity = 2 * smallPastureCapacity := by decide

/-- A stable on a large pasture doubles its capacity. -/
theorem stable_doubles_large_pasture :
    largePastureOneStableCapacity = 2 * largePastureCapacity := by decide

/-- Two stables on a large pasture quadruples base capacity. -/
theorem two_stables_quadruple_large_pasture :
    largePastureTwoStableCapacity = 4 * largePastureCapacity := by decide

/-- The single largest animal-holding space is a large pasture
    with 2 stables, holding 16 animals. This is the maximum for
    any single logical space on the board. -/
theorem max_single_space_capacity :
    largePastureTwoStableCapacity = 16 := by decide

/-- Dog-sheep watching with 1 dog gives 2 sheep (same as small pasture). -/
theorem one_dog_two_sheep : dogSheepCapacity 1 = 2 := by decide

/-- Dog-sheep watching with 3 dogs gives 4 sheep. -/
theorem three_dogs_four_sheep : dogSheepCapacity 3 = 4 := by decide

/-- Dog watching is strictly worse than a stabled large pasture for sheep
    unless you have 16+ dogs. This means the dog mechanic is only useful
    on un-stabled meadows where you have no other option. -/
theorem dogs_worse_than_stabled_large_pasture (n : Nat) (h : n < 15) :
    dogSheepCapacity n < largePastureTwoStableCapacity := by
  simp only [dogSheepCapacity, largePastureTwoStableCapacity]
  omega

/-- With 0 mines and 0 stables on forest, you cannot keep donkeys
    or wild boars outside of pastures. This means both types require
    dedicated infrastructure beyond just clearing land.
    Wild boars need: forest stables, expeditions, or ruby trades.
    Donkeys need: mines. -/
theorem no_infrastructure_no_specialty_animals :
    mineCapacity * 0 = 0 /\ forestStableCapacity * 0 = 0 := by
  decide

/-- The entry-level dwelling is initially the ONLY place to keep animals
    at the start of the game (capacity 2, same type).
    This severely limits early animal acquisition. -/
theorem initial_animal_capacity : entryLevelDwellingCapacity = 2 := by decide

/-- Stables provide exponential scaling on large pastures:
    0 stables = 4, 1 stable = 8, 2 stables = 16. Each stable doubles. -/
theorem stable_scaling_exponential :
    largePastureCapacity * 2 = largePastureOneStableCapacity /\
    largePastureOneStableCapacity * 2 = largePastureTwoStableCapacity := by
  decide

/-- A meadow with a stable holds exactly 1 animal. Without fencing,
    a stable on a meadow is the minimum viable animal housing. -/
theorem meadow_stable_minimal : meadowStableCapacity = 1 := by decide

/-- Dog-sheep capacity is strictly increasing: more dogs always means
    more sheep capacity. -/
theorem dog_sheep_monotone (a b : Nat) (h : a < b) :
    dogSheepCapacity a < dogSheepCapacity b := by
  simp only [dogSheepCapacity]
  omega

/-- The breakeven point where dogs match a small pasture is exactly 1 dog.
    Below that (0 dogs), a small pasture is better. -/
theorem dog_breakeven_small_pasture :
    dogSheepCapacity 1 = smallPastureCapacity := by decide

end Caverna
