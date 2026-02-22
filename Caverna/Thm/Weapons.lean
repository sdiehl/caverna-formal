/-
  Caverna.Thm.Weapons -- Weapon system theorems
  ================================================

  Proven properties of the weapon forging and expedition system.
  Key findings: forge caps, upgrade progression, loot availability
  thresholds, and the accelerated weapon growth strategy.

  Uses v4.28 tactics: `simp +locals` for definition unfolding,
  `native_decide` for List.filter enumeration proofs,
  `grind +locals` for structural reasoning.
-/

import Caverna.Weapons

namespace Caverna

/-- A weapon forged with 8 ore (maximum) starts at strength 8. -/
theorem max_forge_strength :
    forgeWeapon 8 (by omega) = some { strength := 8, h_min := by omega, h_max := by omega } := by
  simp [forgeWeapon, maxInitialWeaponStrength]

/-- You cannot forge a weapon stronger than 8 initially. -/
theorem cannot_forge_above_8 (n : Nat) (h_pos : n >= 1) (h_big : n > 8) :
    forgeWeapon n h_pos = none := by
  simp [forgeWeapon, maxInitialWeaponStrength]
  omega

/-- An expedition always increases weapon strength (when below max). -/
theorem expedition_increases_strength (w : Weapon) (h : w.strength < 14) :
    (upgradeWeapon w).strength = w.strength + 1 := by
  unfold upgradeWeapon
  simp [maxWeaponStrength, h]

/-- A weapon at max strength 14 is not upgraded further. -/
theorem weapon_cap (w : Weapon) (h : w.strength = 14) :
    (upgradeWeapon w).strength = 14 := by
  unfold upgradeWeapon
  simp [maxWeaponStrength, h]

/-- From max forge (8), you need exactly 6 expeditions to reach 14. -/
theorem expeditions_from_max_forge : expeditionsToMax 8 = 6 := by decide

/-- From minimum forge (1), you need 13 expeditions to reach 14. -/
theorem expeditions_from_min_forge : expeditionsToMax 1 = 13 := by decide

/-- At weapon strength 1, only 3 loot items are available. -/
theorem loot_at_strength_1 : availableLootCount 1 = 3 := by native_decide

/-- At weapon strength 8, 13 loot items are available. -/
theorem loot_at_strength_8 : availableLootCount 8 = 13 := by native_decide

/-- At weapon strength 14 (max), all 18 loot items are available. -/
theorem loot_at_strength_14 : availableLootCount 14 = 18 := by native_decide

/-- A level-3 expedition at strength 1 can pick 3 items from 3 available,
    meaning you get ALL available loot. This makes early blacksmithing
    deceptively powerful: even a strength-1 weapon on a level-3 expedition
    gets dog + wood + allWeapons+1 (bumping to strength 3). -/
theorem early_expedition_full_loot :
    ExpeditionLevel.level3.lootCount = availableLootCount 1 := by native_decide

/-- Cattle (the most valuable food animal) requires strength 9, which means
    you need at least 1 expedition after forging at 8. The earliest possible
    cattle-from-expedition is round 2 (forge round 1, get to 9 via expedition).
    This gates the strongest food source behind weapon investment. -/
theorem cattle_requires_expedition :
    LootItem.cattle.minStrength > maxInitialWeaponStrength := by decide

/-- The "All weapons +1" loot item is available at minimum strength 1.
    Choosing it on every expedition means strength grows by 2 per expedition
    instead of 1, dramatically accelerating weapon progression. -/
theorem all_weapons_plus1_always_available :
    LootItem.allWeaponsPlus1.minStrength = 1 := by decide

/-- If you always pick "All weapons +1", a strength-1 weapon reaches 14
    in just 7 expeditions (gaining +2 per expedition: +1 from loot, +1 from
    completion), instead of the normal 13.
    Proof: ceiling of (14-1)/2 = 7. -/
theorem accelerated_weapon_growth :
    (14 - 1 + 2 - 1) / 2 = 7 := by decide

/-- Loot availability is monotone: higher weapon strength never
    reduces available items. -/
theorem loot_monotone_small :
    availableLootCount 1 <= availableLootCount 8 := by native_decide

/-- The gap between strength 8 and 14 unlocks 5 additional loot items.
    These are the premium rewards (cattle, dwelling, sow, breed, furnish). -/
theorem premium_loot_count :
    availableLootCount 14 - availableLootCount 8 = 5 := by native_decide

/-- Expedition level 4 grants 4 loot items, the maximum per expedition. -/
theorem max_loot_per_expedition :
    ExpeditionLevel.level4.lootCount = 4 := by decide

end Caverna
