/-
  Caverna.Furnishings -- Complete furnishing tile catalog
  =======================================================

  Models all 48 furnishing tiles from the Caverna appendix (pp. A3-A6).
  Each tile has a unique ID, building cost, base point value, a category
  (dwelling, parlor, storage, chamber, or special), and an ability that
  affects gameplay or scoring.

  In the full game there are 48 distinct tile types (the ordinary Dwelling
  is unlimited in supply; all others are unique, one copy each).

  The tiles are organized in 4 blocks of 12:
    Block 1: Dwellings (6) + Special furnishing tiles (6)
    Block 2: Building material tiles (12)
    Block 3: Food tiles (6) + Food/bonus parlors (6)
    Block 4: Bonus point storages/chambers (12)

  Categories (indicated by name tag color):
  - Dwelling (red tag): provides room for 1 or 2 dwarfs
  - Parlor (yellow tag): bonus scoring based on game-end state
  - Storage (yellow tag): bonus scoring based on stored goods
  - Chamber (yellow tag): bonus scoring or special abilities
  - Special (orange tag): unique ongoing abilities

  Reference: Caverna Appendix pp. A3-A6, official rules.
-/

import Caverna.Types

namespace Caverna

-- ============================================================
-- Furnishing tile identifiers (all 48 unique types)
-- ============================================================

/-- Every distinct furnishing tile in Caverna.
    Ordinary Dwelling has unlimited copies; all others are unique (1 copy). -/
inductive FurnishingId where
  -- Block 1: Dwellings (red name tag, provide dwarf capacity)
  | dwelling                -- 4W 3S, 3pts, room for 1 dwarf (unlimited copies)
  | simpleDwelling1         -- 4W 2S, 0pts, room for 1 dwarf (cheaper by 1 stone)
  | simpleDwelling2         -- 3W 3S, 0pts, room for 1 dwarf (cheaper by 1 wood)
  | mixedDwelling            -- 5W 4S, 4pts, room for 1 dwarf + 2 animals of same type
  | coupleDwelling          -- 8W 6S, 5pts, room for 2 dwarfs (couple)
  | additionalDwelling      -- 4W 3S, 5pts, room for sixth dwarf only
  -- Block 1: Special furnishing tiles (orange tag)
  | cuddleRoom             -- 1W, 2pts, holds sheep equal to number of dwarfs
  | breakfastRoom           -- 1W, 0pts, holds up to 3 cattle
  | stubbleRoom             -- 1W 1Ore, 1pt, keep 1 animal on each empty field
  | workRoom                -- 1S, 2pts, build furnishings on tunnels/deep tunnels
  | guestRoom                -- 1W 1S, 0pts, "either...or" becomes "and/or"
  | officeRoom               -- 1S, 0pts, twin tiles can overhang board (+2 gold each)
  -- Block 2: Building material tiles (orange tag, ongoing abilities)
  | carpenter                -- 1S, 0pts, pay 1 fewer wood when furnishing or fencing
  | stoneCarver              -- 1W, 1pt, immediately get 2 stone; pay 1 fewer stone when furnishing/building stable
  | blacksmith               -- 1W 2S, 3pts, immediately get 2 ore; pay 2 fewer ore when forging
  | miner                    -- 1W 1S, 3pts, +1 ore per round per ore mine with donkey
  | builder                  -- 1S, 2pts, may replace 1W with 1Ore and/or 1S with 1Ore when furnishing
  | trader                   -- 1W, 2pts, buy 1W+1S+1Ore for 2 gold (full set only); overwrites spare part storage
  | woodSupplier             -- 1S, 2pts, place 1W on next 7 round spaces
  | stoneSupplier            -- 1W, 1pt, place 1S on next 5 round spaces
  | rubySupplier             -- 2W 2S, 2pts, place 1 ruby on next 4 round spaces
  | dogSchool                -- 0, 0pts, +1 wood per new dog placed on board
  | quarry                   -- 1W, 2pts, +1 stone per newborn donkey
  | seam                     -- 2W, 1pt, +1 ore on top of each stone you get
  -- Block 3: Food tiles (orange tag, ongoing abilities)
  | slaughteringCave         -- 2W 2S, 2pts, +1 food per animal converted to food
  | cookingCave              -- 2S, 2pts, 1 grain + 1 veg = 5 food (instead of 3)
  | workingCave              -- 1W 1S, 2pts, feed 1 dwarf with 1W or 1S or 2Ore instead of food
  | miningCave               -- 3W 2S, 2pts, reduce feeding by 1 food per donkey in a mine
  | breedingCave             -- 1Grain 1S, 2pts, +1 food per newborn; +1 extra if all 4 types breed
  | peacefulCave             -- 2W 2S, 2pts, trade weapons for food (strength:food 1:1)
  -- Block 3: Food/bonus parlors (yellow tag)
  | weavingParlor           -- 2W 1S, bonus: immediately 1 food/sheep; scoring +1 per 2 sheep
  | milkingParlor           -- 2W 2S, bonus: immediately 1 food/cattle; scoring +1 per cattle
  | stateParlor             -- 5Gold 3S, bonus: immediately 2 food per adjacent dwelling; scoring +4 per adjacent dwelling
  | huntingParlor           -- 2W, 1pt, before scoring: trade 2 boar for 2 gold + 2 food
  | beerParlor              -- 2W, 3pts, before scoring: trade 2 grain for 3 gold or 4 food
  | blacksmithingParlor     -- 3Ore, 2pts, before scoring: trade 1 ruby + 1 ore for 2 gold + 1 food
  -- Block 4: Bonus point storages/chambers (yellow tag)
  | stoneStorage            -- 3W 1Ore, bonus: +1 per stone you have
  | oreStorage              -- 1W 2S, bonus: +1 per 2 ore you have
  | sparePartStorage        -- 2W, 0pts, before scoring: trade sets of 1W+1S+1Ore for 2 gold; overwrites trader
  | mainStorage             -- 2W 1S, bonus: +2 per furnishing with yellow tag (incl itself)
  | weaponStorage           -- 3W 2S, bonus: +3 per armed dwarf
  | suppliesStorage         -- 3Food 1W, bonus: +8 if all dwarfs have weapons
  | broomChamber            -- 1W, bonus: +5 if 5 dwarfs, +10 if 6 dwarfs
  | treasureChamber         -- 1W 1S, bonus: +1 per ruby
  | foodChamber             -- 2W 2Veg, bonus: +2 per grain+veg pair
  | prayerChamber           -- 2W, bonus: +8 if no dwarfs have weapons
  | writingChamber          -- 2S, 0pts, prevent up to 7 gold points of losses
  | fodderChamber           -- 2Grain 1S, bonus: +1 per 3 farm animals
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- Furnishing tile metadata
-- ============================================================

/-- Category of a furnishing tile (determines name tag color and rules). -/
inductive FurnishingCategory where
  | dwelling     -- red tag: provides dwarf room
  | parlor       -- yellow tag: bonus scoring at end
  | storage      -- yellow tag: scoring from stored goods
  | chamber      -- yellow tag: scoring or special ability
  | special      -- orange tag: ongoing ability
  deriving Repr, DecidableEq, BEq

/-- Complete metadata for a furnishing tile.
    Building costs can be paid in wood, stone, ore, gold, grain, vegetables, or food.
    Most tiles cost only wood and/or stone, but several use other resources. -/
structure FurnishingSpec where
  id : FurnishingId
  category : FurnishingCategory
  woodCost : Nat := 0
  stoneCost : Nat := 0
  oreCost : Nat := 0
  goldCost : Nat := 0
  grainCost : Nat := 0
  vegCost : Nat := 0
  foodCost : Nat := 0
  basePoints : Nat := 0
  dwarfCapacity : Nat := 0      -- how many dwarfs it can house
  isUnlimited : Bool := false    -- only true for ordinary Dwelling
  deriving Repr

/-- Get the specification for a furnishing tile. -/
def furnishingSpec : FurnishingId -> FurnishingSpec
  -- Block 1: Dwellings
  | .dwelling => { id := .dwelling, category := .dwelling, woodCost := 4, stoneCost := 3,
                   basePoints := 3, dwarfCapacity := 1, isUnlimited := true }
  | .simpleDwelling1 => { id := .simpleDwelling1, category := .dwelling, woodCost := 4,
                           stoneCost := 2, dwarfCapacity := 1 }
  | .simpleDwelling2 => { id := .simpleDwelling2, category := .dwelling, woodCost := 3,
                           stoneCost := 3, dwarfCapacity := 1 }
  | .mixedDwelling => { id := .mixedDwelling, category := .dwelling, woodCost := 5,
                         stoneCost := 4, basePoints := 4, dwarfCapacity := 1 }
  | .coupleDwelling => { id := .coupleDwelling, category := .dwelling, woodCost := 8,
                          stoneCost := 6, basePoints := 5, dwarfCapacity := 2 }
  | .additionalDwelling => { id := .additionalDwelling, category := .dwelling, woodCost := 4,
                              stoneCost := 3, basePoints := 5, dwarfCapacity := 1 }
  -- Block 1: Special tiles
  | .cuddleRoom => { id := .cuddleRoom, category := .special, woodCost := 1, basePoints := 2 }
  | .breakfastRoom => { id := .breakfastRoom, category := .special, woodCost := 1 }
  | .stubbleRoom => { id := .stubbleRoom, category := .special, woodCost := 1, oreCost := 1,
                       basePoints := 1 }
  | .workRoom => { id := .workRoom, category := .special, stoneCost := 1, basePoints := 2 }
  | .guestRoom => { id := .guestRoom, category := .special, woodCost := 1, stoneCost := 1 }
  | .officeRoom => { id := .officeRoom, category := .special, stoneCost := 1 }
  -- Block 2: Building material tiles
  | .carpenter => { id := .carpenter, category := .special, stoneCost := 1 }
  | .stoneCarver => { id := .stoneCarver, category := .special, woodCost := 1, basePoints := 1 }
  | .blacksmith => { id := .blacksmith, category := .special, woodCost := 1, stoneCost := 2,
                      basePoints := 3 }
  | .miner => { id := .miner, category := .special, woodCost := 1, stoneCost := 1,
                 basePoints := 3 }
  | .builder => { id := .builder, category := .special, stoneCost := 1, basePoints := 2 }
  | .trader => { id := .trader, category := .special, woodCost := 1, basePoints := 2 }
  | .woodSupplier => { id := .woodSupplier, category := .special, stoneCost := 1, basePoints := 2 }
  | .stoneSupplier => { id := .stoneSupplier, category := .special, woodCost := 1, basePoints := 1 }
  | .rubySupplier => { id := .rubySupplier, category := .special, woodCost := 2, stoneCost := 2,
                        basePoints := 2 }
  | .dogSchool => { id := .dogSchool, category := .special }
  | .quarry => { id := .quarry, category := .special, woodCost := 1, basePoints := 2 }
  | .seam => { id := .seam, category := .special, woodCost := 2, basePoints := 1 }
  -- Block 3: Food tiles
  | .slaughteringCave => { id := .slaughteringCave, category := .special, woodCost := 2,
                            stoneCost := 2, basePoints := 2 }
  | .cookingCave => { id := .cookingCave, category := .special, stoneCost := 2, basePoints := 2 }
  | .workingCave => { id := .workingCave, category := .special, woodCost := 1, stoneCost := 1,
                       basePoints := 2 }
  | .miningCave => { id := .miningCave, category := .special, woodCost := 3, stoneCost := 2,
                      basePoints := 2 }
  | .breedingCave => { id := .breedingCave, category := .special, grainCost := 1, stoneCost := 1,
                        basePoints := 2 }
  | .peacefulCave => { id := .peacefulCave, category := .special, woodCost := 2, stoneCost := 2,
                        basePoints := 2 }
  -- Block 3: Food/bonus parlors
  | .weavingParlor => { id := .weavingParlor, category := .parlor, woodCost := 2, stoneCost := 1 }
  | .milkingParlor => { id := .milkingParlor, category := .parlor, woodCost := 2, stoneCost := 2 }
  | .stateParlor => { id := .stateParlor, category := .parlor, goldCost := 5, stoneCost := 3 }
  | .huntingParlor => { id := .huntingParlor, category := .parlor, woodCost := 2, basePoints := 1 }
  | .beerParlor => { id := .beerParlor, category := .parlor, woodCost := 2, basePoints := 3 }
  | .blacksmithingParlor => { id := .blacksmithingParlor, category := .parlor, oreCost := 3,
                               basePoints := 2 }
  -- Block 4: Bonus point storages/chambers
  | .stoneStorage => { id := .stoneStorage, category := .storage, woodCost := 3, oreCost := 1 }
  | .oreStorage => { id := .oreStorage, category := .storage, woodCost := 1, stoneCost := 2 }
  | .sparePartStorage => { id := .sparePartStorage, category := .storage, woodCost := 2 }
  | .mainStorage => { id := .mainStorage, category := .storage, woodCost := 2, stoneCost := 1 }
  | .weaponStorage => { id := .weaponStorage, category := .storage, woodCost := 3, stoneCost := 2 }
  | .suppliesStorage => { id := .suppliesStorage, category := .storage, foodCost := 3,
                           woodCost := 1 }
  | .broomChamber => { id := .broomChamber, category := .chamber, woodCost := 1 }
  | .treasureChamber => { id := .treasureChamber, category := .chamber, woodCost := 1,
                           stoneCost := 1 }
  | .foodChamber => { id := .foodChamber, category := .chamber, woodCost := 2, vegCost := 2 }
  | .prayerChamber => { id := .prayerChamber, category := .chamber, woodCost := 2 }
  | .writingChamber => { id := .writingChamber, category := .chamber, stoneCost := 2 }
  | .fodderChamber => { id := .fodderChamber, category := .chamber, grainCost := 2,
                         stoneCost := 1 }

-- ============================================================
-- Bonus point computation at game end
-- ============================================================

/-- Game-end state relevant for computing furnishing bonus points.
    Replaces the old positional-argument approach with named fields
    so callers are self-documenting. -/
structure BonusContext where
  stoneInSupply      : Nat := 0
  oreInSupply        : Nat := 0
  sheepCount         : Nat := 0
  cattleCount        : Nat := 0
  numAdjacentDwellings : Nat := 0  -- for State Parlor (max 4)
  numArmedDwarfs     : Nat := 0
  numDwarfs          : Nat := 0
  rubyCount          : Nat := 0
  grainCount         : Nat := 0
  vegCount           : Nat := 0
  farmAnimalCount    : Nat := 0    -- sheep + donkey + boar + cattle (no dogs)
  hasAnyWeapon       : Bool := false
  allDwarfsArmed     : Bool := false
  numYellowTagTiles  : Nat := 0    -- parlors + storages + chambers
  deriving Repr, DecidableEq, BEq

/-- Compute bonus points for a parlor/storage/chamber at game end.
    Takes the furnishing ID and a `BonusContext` capturing the relevant
    game-end state.

    Bonus formulas (from the appendix):
    - Weaving Parlor: +1 per 2 sheep (not per sheep)
    - Milking Parlor: +1 per cattle
    - State Parlor: +4 per adjacent dwelling (max 4 adjacent = 16 pts max)
    - Stone Storage: +1 per stone
    - Ore Storage: +1 per 2 ore
    - Main Storage: +2 per yellow-tag furnishing tile (parlors/storages/chambers)
    - Weapon Storage: +3 per armed dwarf (not per weapon strength)
    - Supplies Storage: +8 if ALL dwarfs have weapons
    - Broom Chamber: +5 if 5 dwarfs, +10 if 6 dwarfs
    - Treasure Chamber: +1 per ruby
    - Food Chamber: +2 per grain+veg pair
    - Prayer Chamber: +8 if no dwarfs have weapons
    - Fodder Chamber: +1 per 3 farm animals
    - Writing Chamber: prevent up to 7 points of losses (handled separately) -/
def furnishingBonusPoints (fid : FurnishingId) (ctx : BonusContext) : Nat :=
  match fid with
  | .stoneStorage => ctx.stoneInSupply
  | .oreStorage => ctx.oreInSupply / 2
  | .weavingParlor => ctx.sheepCount / 2
  | .milkingParlor => ctx.cattleCount
  | .stateParlor => ctx.numAdjacentDwellings * 4
  | .huntingParlor => 0   -- trade effect handled separately
  | .beerParlor => 0      -- trade effect handled separately
  | .blacksmithingParlor => 0  -- trade effect handled separately
  | .mainStorage => ctx.numYellowTagTiles * 2
  | .weaponStorage => ctx.numArmedDwarfs * 3
  | .suppliesStorage => if ctx.allDwarfsArmed then 8 else 0
  | .broomChamber => if ctx.numDwarfs >= 6 then 10
                     else if ctx.numDwarfs >= 5 then 5
                     else 0
  | .treasureChamber => ctx.rubyCount
  | .foodChamber => min ctx.grainCount ctx.vegCount * 2
  | .prayerChamber => if ctx.hasAnyWeapon then 0 else 8
  | .fodderChamber => ctx.farmAnimalCount / 3
  | .sparePartStorage => 0  -- trade effect handled separately
  | _ => 0  -- non-scoring furnishings

-- ============================================================
-- Pre-scoring trade abilities
-- ============================================================

/-- Gold gained from Beer Parlor ability: trade 2 grain for 3 gold.
    Can be used once per pair of grain. -/
def beerParlorGold (grainAvailable : Nat) : Nat :=
  (grainAvailable / 2) * 3

/-- Food gained from Beer Parlor ability: alternatively trade 2 grain for 4 food. -/
def beerParlorFood (grainAvailable : Nat) : Nat :=
  (grainAvailable / 2) * 4

/-- Gold gained from Blacksmithing Parlor: trade 1 ruby + 1 ore for 2 gold + 1 food.
    Returns the gold component. -/
def blacksmithingParlorGold (rubyAvailable oreAvailable : Nat) : Nat :=
  min rubyAvailable oreAvailable * 2

/-- Gold gained from Spare Part Storage: trade sets of 1W+1S+1Ore for 2 gold per set. -/
def sparePartStorageGold (woodAvailable stoneAvailable oreAvailable : Nat) : Nat :=
  min (min woodAvailable stoneAvailable) oreAvailable * 2

/-- Gold and food gained from Hunting Parlor: trade 2 wild boar for 2 gold + 2 food.
    Can be done once. Returns (gold, food). -/
def huntingParlorGold (wildBoarCount : Nat) : Nat :=
  if wildBoarCount >= 2 then 2 else 0

def huntingParlorFood (wildBoarCount : Nat) : Nat :=
  if wildBoarCount >= 2 then 2 else 0

-- ============================================================
-- Writing Chamber effect: prevent up to 7 points of losses
-- ============================================================

/-- Apply Writing Chamber: prevent up to 7 gold points of losses.
    Takes the total negative points and returns the amount prevented. -/
def writingChamberReduction (negativePoints : Nat) : Nat :=
  min negativePoints 7

-- ============================================================
-- Dwelling capacity helpers
-- ============================================================

/-- Does a furnishing tile provide dwelling capacity? -/
def FurnishingId.isDwelling : FurnishingId -> Bool
  | .dwelling | .simpleDwelling1 | .simpleDwelling2 | .mixedDwelling
  | .coupleDwelling | .additionalDwelling => true
  | _ => false

/-- Total dwarf capacity provided by a furnishing tile. -/
def FurnishingId.dwarfCapacity : FurnishingId -> Nat
  | .dwelling => 1
  | .simpleDwelling1 => 1
  | .simpleDwelling2 => 1
  | .mixedDwelling => 1
  | .coupleDwelling => 2
  | .additionalDwelling => 1
  | _ => 0

/-- Does a furnishing raise the dwarf cap beyond 5? -/
def FurnishingId.raisesMaxDwarfs : FurnishingId -> Bool
  | .additionalDwelling => true
  | _ => false

-- ============================================================
-- Building cost check
-- ============================================================

/-- Can a player afford a furnishing tile? -/
def canAffordFurnishing (fid : FurnishingId) (wood stone ore gold grain veg food : Nat) : Bool :=
  let spec := furnishingSpec fid
  wood >= spec.woodCost && stone >= spec.stoneCost && ore >= spec.oreCost &&
  gold >= spec.goldCost && grain >= spec.grainCost && veg >= spec.vegCost &&
  food >= spec.foodCost

-- ============================================================
-- Enumeration of all furnishing tiles
-- ============================================================

/-- List of all unique furnishing tile IDs (48 tiles in 4 blocks of 12). -/
def allFurnishingIds : List FurnishingId :=
  [ -- Block 1: Dwellings + Special
    .dwelling, .simpleDwelling1, .simpleDwelling2, .mixedDwelling,
    .coupleDwelling, .additionalDwelling,
    .cuddleRoom, .breakfastRoom, .stubbleRoom, .workRoom,
    .guestRoom, .officeRoom,
    -- Block 2: Building materials
    .carpenter, .stoneCarver, .blacksmith, .miner,
    .builder, .trader, .woodSupplier, .stoneSupplier,
    .rubySupplier, .dogSchool, .quarry, .seam,
    -- Block 3: Food + Food/bonus parlors
    .slaughteringCave, .cookingCave, .workingCave, .miningCave,
    .breedingCave, .peacefulCave,
    .weavingParlor, .milkingParlor, .stateParlor, .huntingParlor,
    .beerParlor, .blacksmithingParlor,
    -- Block 4: Bonus storages/chambers
    .stoneStorage, .oreStorage, .sparePartStorage, .mainStorage,
    .weaponStorage, .suppliesStorage, .broomChamber, .treasureChamber,
    .foodChamber, .prayerChamber, .writingChamber, .fodderChamber ]

/-- Total number of unique furnishing tiles. -/
def numUniqueFurnishings : Nat := allFurnishingIds.length

end Caverna
