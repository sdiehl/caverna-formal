/-
  Caverna.Weapons -- Weapon forging and expedition system
  ========================================================

  Models the weapon/expedition mechanics from the rulebook (pp.20-22).
  Weapons are forged from ore (max initial strength 8), grow +1 per
  expedition, and cap at 14.
-/

import Caverna.Types

namespace Caverna

/-- Maximum initial weapon strength when forging. -/
def maxInitialWeaponStrength : Nat := 8

/-- Maximum weapon strength after upgrades. -/
def maxWeaponStrength : Nat := 14

/-- Expedition levels determine how many loot items you receive. -/
inductive ExpeditionLevel where
  | level1  -- 1 loot item
  | level2  -- 2 loot items
  | level3  -- 3 loot items
  | level4  -- 4 loot items
  deriving Repr, DecidableEq, BEq

/-- Number of loot items for each expedition level. -/
def ExpeditionLevel.lootCount : ExpeditionLevel -> Nat
  | .level1 => 1
  | .level2 => 2
  | .level3 => 3
  | .level4 => 4

/-- The loot items available from expeditions, with minimum strength required. -/
inductive LootItem where
  | allWeaponsPlus1     -- min strength 1: all weapons +1
  | dog                 -- min strength 1: 1 dog
  | grain               -- min strength 2: 1 grain
  | wood                -- min strength 1: 1 wood
  | sheep               -- min strength 2: 1 sheep
  | stone               -- min strength 3: 1 stone
  | donkey              -- min strength 3: 1 donkey
  | ore                 -- min strength 4: 1 ore
  | wildBoar            -- min strength 4: 1 wild boar
  | gold2               -- min strength 6: 2 gold
  | furnishCavern       -- min strength 7: furnish a cavern
  | stableFree          -- min strength 5: build 1 stable (free)
  | buildFencesCheap    -- min strength 8: build fences (-3 wood)
  | cattle              -- min strength 9: 1 cattle
  | dwelling            -- min strength 10: furnish a dwelling
  | sow                 -- min strength 11: sow action
  | breedTwoTypes       -- min strength 12: breed up to 2 types
  | furnishCavernAgain  -- min strength 14: furnish a cavern (again)
  deriving Repr, DecidableEq, BEq

/-- Minimum weapon strength required for each loot item. -/
def LootItem.minStrength : LootItem -> Nat
  | .allWeaponsPlus1    => 1
  | .dog                => 1
  | .wood               => 1
  | .grain              => 2
  | .sheep              => 2
  | .stone              => 3
  | .donkey             => 3
  | .ore                => 4
  | .wildBoar           => 4
  | .stableFree         => 5
  | .gold2              => 6
  | .furnishCavern      => 7
  | .buildFencesCheap   => 8
  | .cattle             => 9
  | .dwelling           => 10
  | .sow                => 11
  | .breedTwoTypes      => 12
  | .furnishCavernAgain => 14

/-- Forge a new weapon from ore. Returns None if ore exceeds max initial strength. -/
def forgeWeapon (oreSpent : Nat) (h_pos : oreSpent >= 1) : Option Weapon :=
  if h : oreSpent <= maxInitialWeaponStrength then
    some { strength := oreSpent
         , h_min := h_pos
         , h_max := by simp [maxInitialWeaponStrength] at h; omega }
  else
    none

/-- Increase weapon strength by 1 after an expedition (capped at 14). -/
def upgradeWeapon (w : Weapon) : Weapon :=
  if h : w.strength < maxWeaponStrength then
    { strength := w.strength + 1
    , h_min := by omega
    , h_max := by simp [maxWeaponStrength] at h; omega }
  else
    w

/-- Check if a loot item is available given weapon strength. -/
def canLoot (weaponStr : Nat) (item : LootItem) : Bool :=
  weaponStr >= item.minStrength

/-- Count of available loot items at a given weapon strength. -/
def availableLootCount (weaponStr : Nat) : Nat :=
  let allItems := [
    LootItem.allWeaponsPlus1, .dog, .wood, .grain, .sheep,
    .stone, .donkey, .ore, .wildBoar, .stableFree, .gold2,
    .furnishCavern, .buildFencesCheap, .cattle, .dwelling,
    .sow, .breedTwoTypes, .furnishCavernAgain
  ]
  allItems.filter (canLoot weaponStr) |>.length

/-- Number of expeditions needed to go from initial strength to 14. -/
def expeditionsToMax (initialStrength : Nat) : Nat :=
  if initialStrength >= maxWeaponStrength then 0
  else maxWeaponStrength - initialStrength

end Caverna
