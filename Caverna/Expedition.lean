/-
  Caverna.Expedition -- Complete expedition loot system
  =====================================================

  Models the full expedition system: expedition levels (1-4), the complete
  loot table with minimum strength requirements, loot selection rules,
  and weapon strength progression.

  Key rules:
  - Expedition level determines number of loot items (1-4)
  - Each loot item has a minimum weapon strength requirement
  - Each item may only be chosen once per expedition
  - Weapon strength increases by 1 after each expedition (regardless of level)
  - "All weapons +1" loot item increases ALL of a player's weapon strengths by 1
  - Newly forged weapons cap at strength 8; upgrades can go to 14

  Loot items are chosen one by one in any order. The strength check uses
  the weapon strength BEFORE the expedition's +1 bonus.
-/

import Caverna.Types
import Caverna.Weapons
import Caverna.Furnishings

namespace Caverna

-- ============================================================
-- Loot item effects
-- ============================================================

/-- The concrete effect of choosing a loot item.
    This models exactly what a player receives from each loot choice. -/
inductive LootEffect where
  | allWeaponsPlus1      -- all dwarfs' weapons gain +1 strength
  | gainDog              -- +1 dog
  | gainWood             -- +1 wood
  | gainGrain            -- +1 grain
  | gainSheep            -- +1 sheep
  | gainStone            -- +1 stone
  | gainDonkey           -- +1 donkey
  | gainOre              -- +1 ore
  | gainWildBoar         -- +1 wild boar
  | gainGold2            -- +2 gold
  | furnishCavern        -- furnish a cavern (bonus action)
  | gainStable           -- build 1 stable for free
  | buildFencesCheap     -- build fences at -3 wood discount
  | gainCattle           -- +1 cattle
  | furnishDwelling      -- furnish a dwelling (bonus action)
  | sowAction            -- take a sow action
  | breedTwoTypes        -- breed up to 2 animal types
  | furnishCavernAgain   -- furnish another cavern (bonus action)
  deriving Repr, DecidableEq, BEq

/-- Map a loot item to its concrete effect. -/
def LootItem.effect : LootItem -> LootEffect
  | .allWeaponsPlus1 => .allWeaponsPlus1
  | .dog => .gainDog
  | .wood => .gainWood
  | .grain => .gainGrain
  | .sheep => .gainSheep
  | .stone => .gainStone
  | .donkey => .gainDonkey
  | .ore => .gainOre
  | .wildBoar => .gainWildBoar
  | .gold2 => .gainGold2
  | .furnishCavern => .furnishCavern
  | .stableFree => .gainStable
  | .buildFencesCheap => .buildFencesCheap
  | .cattle => .gainCattle
  | .dwelling => .furnishDwelling
  | .sow => .sowAction
  | .breedTwoTypes => .breedTwoTypes
  | .furnishCavernAgain => .furnishCavernAgain

-- ============================================================
-- Loot selection validation
-- ============================================================

/-- All loot items in the game, in order of minimum strength. -/
def allLootItems : List LootItem :=
  [ .allWeaponsPlus1, .dog, .wood, .grain, .sheep,
    .stone, .donkey, .ore, .wildBoar, .stableFree,
    .gold2, .furnishCavern, .buildFencesCheap, .cattle,
    .dwelling, .sow, .breedTwoTypes, .furnishCavernAgain ]

/-- Items available at a given weapon strength. -/
def availableLoot (weaponStr : Nat) : List LootItem :=
  allLootItems.filter (canLoot weaponStr)

/-- Is a loot selection valid for a given expedition?
    - Must have exactly `level.lootCount` items
    - All items must be distinct
    - All items must be within weapon strength range -/
def validLootSelection (level : ExpeditionLevel) (weaponStr : Nat)
    (selection : List LootItem) : Bool :=
  selection.length == level.lootCount &&
  selection.eraseDups.length == selection.length &&
  selection.all (canLoot weaponStr)

-- ============================================================
-- Expedition resolution
-- ============================================================

/-- Result of resolving an expedition: the list of effects to apply
    and the new weapon strength (after +1 from expedition completion). -/
structure ExpeditionResult where
  effects : List LootEffect
  newWeaponStrength : Nat   -- after +1 from expedition experience
  deriving Repr

/-- Resolve an expedition given the level, current weapon strength,
    and chosen loot items. Returns the effects and updated weapon strength. -/
def resolveExpedition (level : ExpeditionLevel) (weaponStr : Nat)
    (selection : List LootItem) : Option ExpeditionResult :=
  if validLootSelection level weaponStr selection then
    let effects := selection.map LootItem.effect
    -- Check if "All weapons +1" was selected
    let hasAllPlus1 := selection.any (fun i => match i with | .allWeaponsPlus1 => true | _ => false)
    -- Weapon gains +1 from expedition completion
    let newStr := min 14 (weaponStr + 1)
    -- If "All weapons +1" was taken, that's an additional +1 applied to ALL weapons
    -- (The effect is applied separately via the LootEffect)
    some { effects := effects
         , newWeaponStrength := if hasAllPlus1 then min 14 (newStr + 1) else newStr }
  else
    none

-- ============================================================
-- Action spaces that provide expeditions
-- ============================================================

/-- Which action spaces provide expeditions and at what levels?
    This determines the expedition opportunities available each round. -/
def expeditionSpaces : List (ActionSpaceId × ExpeditionLevel) :=
  [ (.blacksmithing, .level3)       -- stage 1: forge + level 3 expedition
  , (.oreMineConstruction, .level2) -- stage 1: build ore mine + level 2 expedition
  , (.rubyMineConstruction, .level2)-- stage 2: build ruby mine + level 2 expedition
  , (.adventure, .level1)           -- stage 4: forge + 2x level 1 expeditions
  ]

/-- The Adventure action space gives TWO level-1 expeditions.
    This is the only space with multiple expeditions per dwarf. -/
def adventureExpeditionCount : Nat := 2

-- ============================================================
-- Weapon strength progression analysis
-- ============================================================

/-- Fastest possible weapon progression in the 2-player game:
    Round 1: Forge 1 ore -> str 1, level 3 expedition -> str 3 (with AllWeapons+1 loot)
    Round 2: Use expedition elsewhere -> str 4
    ...continuing with 1 expedition per round. -/
def fastestProgression : List (Nat × Nat) :=  -- (round, strength)
  [ (1, 3)    -- forge 1, expedition, allWeapons+1
  , (2, 4)    -- one more expedition
  , (3, 5)    -- ore mine construction expedition
  , (4, 6)    -- (no expedition space available unless specific cards)
  , (5, 7)
  , (6, 8)
  , (7, 9)
  , (8, 10)
  , (10, 11)
  , (11, 12)  -- adventure: +2 from two level-1 expeditions
  , (12, 14)  -- cap
  ]

/-- Maximum weapon strength achievable by game end,
    starting from forge at round 1 with 1 ore. -/
def maxAchievableStrength : Nat := 14

-- ============================================================
-- Loot value estimation (for strategy comparison)
-- ============================================================

/-- Estimated "point value" of a loot item for strategic comparison.
    This is approximate, combining immediate points and resource value. -/
def lootPointEstimate : LootItem -> Nat
  | .allWeaponsPlus1 => 3    -- unlocks future loot + weapon storage bonus
  | .dog => 1                -- 1 point at scoring
  | .wood => 1               -- ~0.5 points (building material)
  | .grain => 1              -- 0.5 points at scoring
  | .sheep => 1              -- 1 point at scoring
  | .stone => 2              -- ~1 point (valuable building material)
  | .donkey => 1             -- 1 point at scoring + food value
  | .ore => 1                -- ~0.5 points (weapon/building)
  | .wildBoar => 2           -- 1 point + 2 food value
  | .stableFree => 2         -- saves 1 stone + enables capacity
  | .gold2 => 2              -- 2 gold = 2 points
  | .furnishCavern => 4      -- high-value bonus action
  | .buildFencesCheap => 2   -- saves 3 wood = ~2 points
  | .cattle => 3             -- 1 point + 3 food value
  | .dwelling => 5           -- enables family growth
  | .sow => 3               -- ~1.5 points per field sown
  | .breedTwoTypes => 2     -- ~2 extra animals
  | .furnishCavernAgain => 4 -- another furnishing action

/-- Total estimated loot value for an expedition at a given strength and level. -/
def maxLootValue (weaponStr : Nat) (level : ExpeditionLevel) : Nat :=
  let available := availableLoot weaponStr
  let sorted := available.map lootPointEstimate |>.mergeSort (· >= ·)
  sorted.take level.lootCount |>.foldl (· + ·) 0

end Caverna
