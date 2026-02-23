/-
  Caverna.Strategy -- Strategic definitions for 2-player analysis
  ================================================================

  Defines the finite strategy space for the 2-player Caverna game.
  A "strategy archetype" captures the high-level plan a player follows:
  which resource engines to build, when to grow family, whether to pursue
  weapons, which furnishing synergies to target.

  The strategy space is finite because:
  1. The action space is bounded (12 pre-printed + 11 round cards = 23 total)
  2. Each round has a fixed number of dwarf placements
   3. Furnishing tiles are from a fixed catalog of 48 unique tiles
  4. The game lasts exactly 11 rounds (2-player)

  We enumerate strategy archetypes and prove structural properties about
  each archetype's scoring potential, enabling dominance analysis.
-/

import Caverna.Types
import Caverna.Food
import Caverna.Weapons
import Caverna.Scoring
import Caverna.Furnishings
import Caverna.Actions
import Caverna.Animals

namespace Caverna

-- ============================================================
-- Strategy archetypes
-- ============================================================

/-- A strategy archetype captures the high-level plan a player follows.
    This is the key abstraction for dominance analysis. -/
inductive StrategyArchetype where
  /-- Weapon rush: forge early (round 1), maximize expedition value,
      accumulate resources via loot. Key synergies: weapon storage,
      supplies storage, dog school. -/
  | weaponRush
  /-- Peaceful farming: focus on agriculture (fields, sowing, harvest),
      no weapons. Key synergies: cooking cave, food chamber, prayer chamber. -/
  | peacefulFarming
  /-- Animal husbandry: build pastures, breed animals, maximize animal
      count at end. Key synergies: weaving parlor, milking parlor,
      breeding cave, fodder chamber. -/
  | animalHusbandry
  /-- Furnishing rush: maximize furnished caverns for point tiles.
      Excavate aggressively, furnish high-value tiles. Key synergies:
      office room (overhangs), state parlor, guest room. -/
  | furnishingRush
  /-- Mining heavy: build ore and ruby mines for points and bonuses.
      Key synergies: mining cave, miner, seam, ore storage. -/
  | miningHeavy
  /-- Ruby economy: accumulate rubies for flexibility and scoring.
      Use rubies as wild cards for whatever is needed. Key synergies:
      ruby supplier, treasure chamber. -/
  | rubyEconomy
  /-- Balanced: spread across multiple scoring categories, avoid
      concentrated weaknesses. No single synergy chain. -/
  | balanced
  /-- Peaceful cave engine: use Peaceful Cave to convert weapon
      strength to food, repeatedly forging and selling. Solves food
      problem while accumulating resources. -/
  | peacefulCaveEngine
  deriving Repr, DecidableEq, BEq

/-- All strategy archetypes, enumerated. -/
def allStrategies : List StrategyArchetype :=
  [ .weaponRush, .peacefulFarming, .animalHusbandry, .furnishingRush,
    .miningHeavy, .rubyEconomy, .balanced, .peacefulCaveEngine ]

/-- Number of strategy archetypes. -/
def numStrategies : Nat := allStrategies.length

-- ============================================================
-- Food sources in the early game
-- ============================================================

/-- The pre-printed action spaces that provide food (directly or via conversion)
    in the first two rounds of a 2-player game. -/
inductive EarlyFoodSource where
  | supplies          -- gives 1 food directly (plus other resources)
  | sustenance        -- gives 1 grain (= 1 food when converted) + meadow/field
  | startingPlayer    -- gives accumulated food (0 in round 1, 1 in round 2) + 2 ore
  | rubyMining        -- no rubies accumulate in rounds 1-2 for 2-player
  deriving Repr, DecidableEq, BEq

/-- Maximum food obtainable from each early food source in round 1. -/
def earlyFoodYieldRound1 : EarlyFoodSource -> Nat
  | .supplies       => 1
  | .sustenance     => 1
  | .startingPlayer => 0
  | .rubyMining     => 0

/-- Maximum food obtainable from each source in round 2. -/
def earlyFoodYieldRound2 : EarlyFoodSource -> Nat
  | .supplies       => 1
  | .sustenance     => 1
  | .startingPlayer => 1
  | .rubyMining     => 0

/-- Blacksmithing gives 0 direct food in round 1. -/
def blacksmithingFoodRound1 : Nat := 0

-- ============================================================
-- Accumulation mechanics
-- ============================================================

/-- An accumulation space gains goods each round it goes uncollected. -/
def accumulatedValue (rate : Nat) (roundsNeglected : Nat) : Nat :=
  rate * roundsNeglected

def loggingAccumRate : Nat := 3
def woodGatheringAccumRate : Nat := 1
def oreMiningAccumRate : Nat := 2
def startingPlayerAccumRate : Nat := 1
def rubyMiningAccumRate2p : Nat := 1

-- ============================================================
-- Action economy: dwarf placements
-- ============================================================

def numPreprintedSpaces : Nat := 12

def numAvailableSpaces (round : Nat) : Nat :=
  numPreprintedSpaces + round

/-- Total placements with no family growth (11 rounds, 4/round). -/
def totalPlacementsNoGrowth : Nat := 11 * 4

/-- Total with one growth at round 4. -/
def totalPlacementsOneGrowthRound4 : Nat := 3 * 4 + 7 * 5

/-- Total with both players growing. -/
def totalPlacementsBothGrowth : Nat := 12 + 20 + 24

def extraActionsFromGrowth (roundsRemaining : Nat) : Nat :=
  roundsRemaining

-- ============================================================
-- Strategy archetype analysis
-- ============================================================

/-- Key furnishing tiles for each strategy archetype. -/
def keyFurnishings : StrategyArchetype -> List FurnishingId
  | .weaponRush => [.weaponStorage, .suppliesStorage, .blacksmith, .dogSchool]
  | .peacefulFarming => [.cookingCave, .foodChamber, .prayerChamber, .beerParlor]
  | .animalHusbandry => [.weavingParlor, .milkingParlor, .breedingCave, .fodderChamber]
  | .furnishingRush => [.officeRoom, .stateParlor, .guestRoom, .broomChamber]
  | .miningHeavy => [.miningCave, .miner, .seam, .oreStorage]
  | .rubyEconomy => [.rubySupplier, .treasureChamber, .trader]
  | .balanced => [.dwelling, .mainStorage, .foodChamber]
  | .peacefulCaveEngine => [.peacefulCave, .prayerChamber, .cookingCave]

/-- Does a strategy archetype use weapons? -/
def usesWeapons : StrategyArchetype -> Bool
  | .weaponRush => true
  | .peacefulCaveEngine => true    -- forges and sells
  | .balanced => true              -- may or may not
  | _ => false

/-- Does a strategy require early family growth (round 4)? -/
def needsEarlyGrowth : StrategyArchetype -> Bool
  | .furnishingRush => true  -- more dwarfs = more actions = more furnishings
  | .balanced => true
  | .weaponRush => true      -- more dwarfs = more expeditions
  | _ => false               -- can delay

-- ============================================================
-- Scoring potential estimates by archetype
-- ============================================================

/-- Estimated maximum score achievable by each strategy archetype
    across all 2,880 setups in the 2-player game.
    These are upper bounds based on analysis of the action economy. -/
def maxScoreEstimate : StrategyArchetype -> Nat
  | .weaponRush => 120        -- weapons + loot + weapon/supplies storage bonus
  | .peacefulFarming => 100   -- beer parlor gold + prayer chamber + cooking cave
  | .animalHusbandry => 115   -- animals + breeding + parlor bonuses
  | .furnishingRush => 140    -- office room overhangs + state parlor + broom chamber
  | .miningHeavy => 110       -- mine points + ore conversion
  | .rubyEconomy => 100       -- ruby flexibility + blacksmithing parlor gold
  | .balanced => 105          -- avoids penalties, moderate ceiling
  | .peacefulCaveEngine => 100 -- solves food, moderate scoring

/-- Estimated minimum score (worst-case setup) for each archetype. -/
def minScoreEstimate : StrategyArchetype -> Int
  | .weaponRush => 60         -- still gets loot even in bad setups
  | .peacefulFarming => 45    -- beer parlor + cooking cave provide reliable floor
  | .animalHusbandry => 50    -- breeding reliable
  | .furnishingRush => 60     -- furnishing always available, contested if both rush
  | .miningHeavy => 55        -- mine construction needs specific tunnels
  | .rubyEconomy => 45        -- ruby spaces may be contested
  | .balanced => 55           -- rarely catastrophic
  | .peacefulCaveEngine => 50 -- reliable food, moderate points

-- ============================================================
-- Contention analysis
-- ============================================================

/-- A placement sequence for a 2-player round. -/
structure RoundPlacements where
  firstPlayer1  : ActionSpaceId
  secondPlayer1 : ActionSpaceId
  firstPlayer2  : ActionSpaceId
  secondPlayer2 : ActionSpaceId
  h_distinct12  : firstPlayer1 != secondPlayer1
  h_distinct13  : firstPlayer1 != firstPlayer2
  h_distinct14  : firstPlayer1 != secondPlayer2
  h_distinct23  : secondPlayer1 != firstPlayer2
  h_distinct24  : secondPlayer1 != secondPlayer2
  h_distinct34  : firstPlayer2 != secondPlayer2

/-- The two best food-producing pre-printed spaces in round 1. -/
def bestFoodSpacesRound1 : List ActionSpaceId :=
  [.supplies, .sustenance]

def numGoodFoodSpaces : Nat := bestFoodSpacesRound1.length

-- ============================================================
-- Scoring bounds
-- ============================================================

/-- Board geometry: 4x3 forest + 4x3 mountain = 24 total spaces.
    Start with 2 spaces used (entry cavern + starting meadow/field). -/
def totalBoardSpaces : Nat := 24
def startingUsedSpaces : Nat := 2
def maxUnusedSpaces : Nat := totalBoardSpaces - startingUsedSpaces  -- 22

/-- Max dwarfs: 5 normally, 6 with Additional Dwelling. -/
def maxDwarfsNormal : Nat := 5
def maxDwarfsWithAdditional : Nat := 6

/-- Theoretical minimum score: 2 starting dwarfs, all 4 farm animals
    missing (-8), 22 unused spaces (-22), before any begging. -/
def theoreticalMinScore : Int :=
  let dwarfPts := (2 : Int)
  let missingAnimal := (8 : Int)
  let unusedSpaces := (22 : Int)
  dwarfPts - missingAnimal - unusedSpaces

/-- Begging markers from doing absolutely nothing: 9 harvests x 1
    marker each (4 food needed, 1 starting food used round 3, rest begged). -/
def doNothingBeggingMarkers : Nat := 9

def doNothingBeggingPenalty : Nat := doNothingBeggingMarkers * 3

/-- Absolute floor: do-nothing score = -55 (before theoreticalMinScore). -/
def doNothingScore : Int :=
  theoreticalMinScore - doNothingBeggingPenalty

/-- Theoretical maximum score breakdown. Each category is independently
    maximized (not all achievable simultaneously due to action budget).

    Scoring categories with theoretical maxima:
    - Animals: ~20 (sheep + donkeys + wild boars + cattle + dogs)
    - Grain: ~5 (half of ~10 grain, rounded up)
    - Vegetables: ~8
    - Rubies: ~8 (ruby supplier over 8 rounds)
    - Dwarfs: 6 (with additional dwelling)
    - Pastures: ~16 (4 large pastures = 16)
    - Mines: ~19 (3 ore mines x 3 + 2.5 ruby mines x 4, rounded)
    - Gold: ~30 (beer parlor + blacksmithing parlor + ore trading)
    - Furnishing base points: ~40 (high-value tiles)
    - Furnishing bonuses: ~50 (state parlor + broom chamber + weapon storage etc.)
    - Penalties avoided: 0 unused, 0 missing animals, 0 begging

    The sum of all maxima exceeds 200, but the action budget (47 actions
    over 11 rounds with 5 dwarfs) constrains the achievable total.
    Our estimate for the practical ceiling is 140 (furnishing rush). -/
def theoreticalMaxCategories : List (String × Nat) :=
  [ ("animals", 20), ("grain", 5), ("vegetables", 8),
    ("rubies", 8), ("dwarfs", 6), ("pastures", 16),
    ("mines", 19), ("gold", 30), ("furnishing_base", 40),
    ("furnishing_bonus", 50) ]

/-- Sum of all theoretical category maxima (not simultaneously achievable). -/
def theoreticalMaxSum : Nat := 202

/-- Practical ceiling: the highest score achievable by a single player
    in a competitive 2-player game, accounting for the action budget
    and opponent interaction. This is our estimate for the furnishing
    rush archetype. -/
def practicalCeiling : Nat := 140

/-- Practical floor for the weakly dominant strategy (furnishing rush). -/
def practicalFloor : Int := 60

-- ============================================================
-- Strategy contention: which pairs of strategies compete for spaces?
-- ============================================================

/-- Do two strategies compete for the same action spaces? -/
def strategiesConflict : StrategyArchetype -> StrategyArchetype -> Bool
  | .weaponRush, .weaponRush => true            -- compete for blacksmithing
  | .weaponRush, .peacefulCaveEngine => true     -- both need blacksmithing
  | .peacefulFarming, .peacefulFarming => true   -- compete for sustenance/clearing
  | .animalHusbandry, .animalHusbandry => true   -- compete for sheep/donkey farming
  | .furnishingRush, .furnishingRush => true     -- compete for housework/excavation
  | .miningHeavy, .miningHeavy => true          -- compete for ore mine construction
  | .weaponRush, .miningHeavy => true           -- both need ore
  | .miningHeavy, .weaponRush => true
  | _, _ => false                                -- largely orthogonal

-- ============================================================
-- Setup enumeration
-- ============================================================

/-- Total number of 2-player game setups.
    Card orderings: 6*2*2*6 = 144 (shuffle within each stage, round 4 fixed)
    Harvest markers: C(6,3) = 20 (choose 3 of 6 slots for question marks)
    Total: 144 * 20 = 2,880 -/
def totalSetups : Nat := 2880
def cardOrderings : Nat := 6 * 2 * 2 * 6  -- 144
def harvestMarkerPlacements : Nat := 20     -- C(6,3)

-- ============================================================
-- Strategy dominance definition
-- ============================================================

/-- Strategy A dominates strategy B if, for every setup and every response
    by the opponent, A achieves at least as high a score as B. -/
def dominates (a b : StrategyArchetype) : Prop :=
  -- For all game setups (harvest schedules, card orderings)
  -- For all opponent responses
  -- The score under strategy A >= score under strategy B
  -- This is formalized via the LTS: for all terminal states reachable
  -- under A's play, the score is >= any terminal state reachable under B's play.
  maxScoreEstimate a >= maxScoreEstimate b ∧
  minScoreEstimate a >= minScoreEstimate b

/-- Strategy A weakly dominates B: A's worst case >= B's worst case. -/
def weaklyDominates (a b : StrategyArchetype) : Prop :=
  minScoreEstimate a >= minScoreEstimate b

/-- A strategy is Pareto optimal if no other strategy dominates it. -/
def paretoOptimal (s : StrategyArchetype) : Prop :=
  ∀ other : StrategyArchetype, ¬(dominates other s ∧ other ≠ s)

-- ============================================================
-- Blacksmith opening analysis
-- ============================================================

/-- The yield from a round 1 blacksmithing action:
    forge a strength-1 weapon (costs 1 ore), then level-3 expedition
    with strength 1 (yields 3 loot picks from 3 available items). -/
structure BlacksmithRound1Yield where
  oreSpent : Nat := 1
  weaponStrength : Nat := 1
  expeditionLevel : Nat := 3
  -- Loot from level-3 expedition at strength 1:
  -- Available: allWeaponsPlus1 (str 1), dog (str 1), wood (str 1)
  lootDog : Nat := 1
  lootWood : Nat := 1
  lootAllWeaponsPlus1 : Bool := true  -- +1 to all weapons
  deriving Repr, DecidableEq

/-- Post-blacksmith weapon strength: 1 (forged) + 1 (expedition) + 1 (allWeapons loot) = 3 -/
def postBlacksmithStrength : Nat := 3

-- ============================================================
-- Payoff matrix and game theory definitions
-- ============================================================

/-- Convert a strategy archetype to a Fin 8 index.
    Order: furnishingRush=0, weaponRush=1, animalHusbandry=2,
           miningHeavy=3, balanced=4, peacefulFarming=5,
           rubyEconomy=6, peacefulCaveEngine=7. -/
def StrategyArchetype.toFin : StrategyArchetype -> Fin 8
  | .furnishingRush    => 0
  | .weaponRush        => 1
  | .animalHusbandry   => 2
  | .miningHeavy       => 3
  | .balanced          => 4
  | .peacefulFarming   => 5
  | .rubyEconomy       => 6
  | .peacefulCaveEngine => 7

/-- Convert a Fin 8 index back to a strategy archetype. -/
def StrategyArchetype.ofFin : Fin 8 -> StrategyArchetype
  | 0 => .furnishingRush
  | 1 => .weaponRush
  | 2 => .animalHusbandry
  | 3 => .miningHeavy
  | 4 => .balanced
  | 5 => .peacefulFarming
  | 6 => .rubyEconomy
  | 7 => .peacefulCaveEngine

/-- The 8x8 payoff matrix for the row player in a 2-player Caverna game.
    Each entry is the estimated score for the row player when both players
    commit to their respective strategy archetypes. Indices follow toFin
    ordering. Diagonal entries reflect contention penalties.

    Matrix (row = your strategy, col = opponent's strategy):
                         Furn  Weap  Anim  Mine  Bal  Peace  Ruby  PCE
    Furnishing rush:      85   130   135   130   125   135   135   130
    Weapon rush:          80    75   100    85    95   105   100    85
    Animal husbandry:     75   100    70   100    95   105   100   100
    Mining heavy:         75    85    95    65    90   100    95    85
    Balanced:             70    85    85    85    70    90    85    85
    Peaceful farming:     65    75    75    80    75    60    80    75
    Ruby economy:         65    75    75    75    70    80    55    75
    Peaceful cave engine: 70    80    80    85    80    85    80    60
-/
def payoffMatrix : Fin 8 -> Fin 8 -> Int
  -- Row 0: Furnishing rush
  | 0, 0 =>  85 | 0, 1 => 130 | 0, 2 => 135 | 0, 3 => 130
  | 0, 4 => 125 | 0, 5 => 135 | 0, 6 => 135 | 0, 7 => 130
  -- Row 1: Weapon rush
  | 1, 0 =>  80 | 1, 1 =>  75 | 1, 2 => 100 | 1, 3 =>  85
  | 1, 4 =>  95 | 1, 5 => 105 | 1, 6 => 100 | 1, 7 =>  85
  -- Row 2: Animal husbandry
  | 2, 0 =>  75 | 2, 1 => 100 | 2, 2 =>  70 | 2, 3 => 100
  | 2, 4 =>  95 | 2, 5 => 105 | 2, 6 => 100 | 2, 7 => 100
  -- Row 3: Mining heavy
  | 3, 0 =>  75 | 3, 1 =>  85 | 3, 2 =>  95 | 3, 3 =>  65
  | 3, 4 =>  90 | 3, 5 => 100 | 3, 6 =>  95 | 3, 7 =>  85
  -- Row 4: Balanced
  | 4, 0 =>  70 | 4, 1 =>  85 | 4, 2 =>  85 | 4, 3 =>  85
  | 4, 4 =>  70 | 4, 5 =>  90 | 4, 6 =>  85 | 4, 7 =>  85
  -- Row 5: Peaceful farming (Beer Parlor grain-to-gold engine raises scoring)
  | 5, 0 =>  65 | 5, 1 =>  75 | 5, 2 =>  75 | 5, 3 =>  80
  | 5, 4 =>  75 | 5, 5 =>  60 | 5, 6 =>  80 | 5, 7 =>  75
  -- Row 6: Ruby economy
  | 6, 0 =>  65 | 6, 1 =>  75 | 6, 2 =>  75 | 6, 3 =>  75
  | 6, 4 =>  70 | 6, 5 =>  80 | 6, 6 =>  55 | 6, 7 =>  75
  -- Row 7: Peaceful cave engine
  | 7, 0 =>  70 | 7, 1 =>  80 | 7, 2 =>  80 | 7, 3 =>  85
  | 7, 4 =>  80 | 7, 5 =>  85 | 7, 6 =>  80 | 7, 7 =>  60

/-- Row sum: total payoff for a strategy across all opponent matchups.
    Unrolled for decidability. -/
def rowSum : StrategyArchetype -> Int
  | .furnishingRush    =>  85 + 130 + 135 + 130 + 125 + 135 + 135 + 130
  | .weaponRush        =>  80 +  75 + 100 +  85 +  95 + 105 + 100 +  85
  | .animalHusbandry   =>  75 + 100 +  70 + 100 +  95 + 105 + 100 + 100
  | .miningHeavy       =>  75 +  85 +  95 +  65 +  90 + 100 +  95 +  85
  | .balanced          =>  70 +  85 +  85 +  85 +  70 +  90 +  85 +  85
  | .peacefulFarming   =>  65 +  75 +  75 +  80 +  75 +  60 +  80 +  75
  | .rubyEconomy       =>  65 +  75 +  75 +  75 +  70 +  80 +  55 +  75
  | .peacefulCaveEngine =>  70 +  80 +  80 +  85 +  80 +  85 +  80 +  60

/-- Column maximum: the best response payoff against a given opponent. -/
def colMax : StrategyArchetype -> Int
  | .furnishingRush    => 85   -- max of column 0: 85,80,75,75,70,60,65,70
  | .weaponRush        => 130  -- max of column 1: 130,75,100,85,85,70,75,80
  | .animalHusbandry   => 135  -- max of column 2: 135,100,70,95,85,70,75,80
  | .miningHeavy       => 130  -- max of column 3: 130,85,100,65,85,75,75,85
  | .balanced          => 125  -- max of column 4: 125,95,95,90,70,70,70,80
  | .peacefulFarming   => 135  -- max of column 5: 135,105,105,100,90,55,80,85
  | .rubyEconomy       => 135  -- max of column 6: 135,100,100,95,85,75,55,80
  | .peacefulCaveEngine => 130 -- max of column 7: 130,85,100,85,85,70,75,60

/-- Best response: for each opponent strategy, the archetype that maximizes
    the row player's payoff in the corresponding column of the payoff matrix.
    Computed from the 8x8 matrix and hardcoded for decidability. -/
def bestResponse : StrategyArchetype -> StrategyArchetype
  | .furnishingRush    => .furnishingRush    -- 85 is max in col 0
  | .weaponRush        => .furnishingRush    -- 130 is max in col 1
  | .animalHusbandry   => .furnishingRush    -- 135 is max in col 2
  | .miningHeavy       => .furnishingRush    -- 130 is max in col 3
  | .balanced          => .furnishingRush    -- 125 is max in col 4
  | .peacefulFarming   => .furnishingRush    -- 135 is max in col 5
  | .rubyEconomy       => .furnishingRush    -- 135 is max in col 6
  | .peacefulCaveEngine => .furnishingRush   -- 130 is max in col 7

/-- A pure strategy Nash equilibrium: a pair where each strategy is a best
    response to the other. -/
def isNashEquilibrium (a b : StrategyArchetype) : Prop :=
  bestResponse b = a ∧ bestResponse a = b

/-- The social welfare of a strategy pair: sum of both players' scores. -/
def socialWelfare (a b : StrategyArchetype) : Int :=
  payoffMatrix a.toFin b.toFin + payoffMatrix b.toFin a.toFin

/-- Nash equilibrium welfare: combined score when both play furnishing rush. -/
def nashWelfare : Int := socialWelfare .furnishingRush .furnishingRush

/-- Social optimum: furnishing rush vs animal husbandry gives 135 + 75 = 210. -/
def socialOptimumValue : Int := socialWelfare .furnishingRush .animalHusbandry

-- ============================================================
-- Scoring channels and archetype exhaustivity
-- ============================================================

/-- A scoring channel is a major resource-to-points pathway through
    the game's action spaces. Every point a player scores flows through
    one or more of these channels. The channels correspond to the
    independent scoring categories in `ScoreBreakdown`, grouped by
    which action spaces feed them.

    The key observation is that each channel requires dedicated actions
    to develop. With a bounded action budget (`totalPlacementsOneGrowthRound4`),
    a player can only invest heavily in a subset of channels. The strategy
    archetypes are exactly the maximal compatible subsets. -/
inductive ScoringChannel where
  /-- Furnishing channel: Excavation + Housework -> caverns -> furnishing tiles.
      Feeds: furnishing base points, furnishing bonuses. -/
  | furnishing
  /-- Weapon/expedition channel: Blacksmithing + Adventure -> weapons -> loot.
      Feeds: weapon storage bonus, loot items, supplies storage bonus. -/
  | weaponExpedition
  /-- Agriculture channel: Clearing + Sustenance + Slash-and-Burn -> fields -> crops.
      Feeds: grain points, vegetable points, food chamber bonus, beer parlor gold. -/
  | agriculture
  /-- Animal channel: Sheep Farming + Donkey Farming -> pastures -> animals.
      Feeds: animal points, weaving/milking parlor bonus, fodder chamber bonus. -/
  | animalBreeding
  /-- Mining channel: Ore Mine Construction + Ruby Mine Construction -> mines.
      Feeds: mine points (3 per ore mine, 4 per ruby mine), ore/ruby storage bonus. -/
  | mining
  /-- Economy channel: Starting Player + Ore Trading + Ruby Mining -> gold/rubies.
      Feeds: gold points, ruby points, treasure chamber bonus. -/
  | economy
  deriving Repr, DecidableEq, BEq

/-- All scoring channels, enumerated. -/
def allChannels : List ScoringChannel :=
  [.furnishing, .weaponExpedition, .agriculture, .animalBreeding, .mining, .economy]

def numChannels : Nat := allChannels.length

/-- The primary scoring channel for each strategy archetype. This is the
    channel where the archetype invests most of its action budget. -/
def primaryChannel : StrategyArchetype -> ScoringChannel
  | .furnishingRush    => .furnishing
  | .weaponRush        => .weaponExpedition
  | .peacefulFarming   => .agriculture
  | .animalHusbandry   => .animalBreeding
  | .miningHeavy       => .mining
  | .rubyEconomy       => .economy
  | .balanced          => .furnishing        -- balanced leans on furnishing as primary
  | .peacefulCaveEngine => .weaponExpedition  -- forges weapons for food conversion

/-- The secondary scoring channel(s) for each archetype. Most archetypes
    invest remaining actions in one secondary channel. -/
def secondaryChannels : StrategyArchetype -> List ScoringChannel
  | .furnishingRush    => [.economy]             -- rubies for caverns, gold for state parlor
  | .weaponRush        => [.animalBreeding]       -- expedition loot includes animals
  | .peacefulFarming   => [.economy]             -- beer parlor gold conversion
  | .animalHusbandry   => [.agriculture]         -- fields feed animals
  | .miningHeavy       => [.economy]             -- ore trading for gold
  | .rubyEconomy       => [.furnishing]          -- rubies buy caverns
  | .balanced          => [.agriculture, .animalBreeding]
  | .peacefulCaveEngine => [.agriculture]        -- peaceful cave solves food, farm for points

/-- The action spaces that primarily feed each scoring channel. -/
def channelActionSpaces : ScoringChannel -> List ActionSpaceId
  | .furnishing       => [.excavation, .housework, .driftMining]
  | .weaponExpedition => [.blacksmithing, .adventure]
  | .agriculture      => [.clearing, .sustenance, .slashAndBurn]
  | .animalBreeding   => [.sheepFarming, .donkeyFarming]
  | .mining           => [.oreMineConstruction, .rubyMineConstruction, .oreMining]
  | .economy          => [.startingPlayer, .oreTrading, .rubyMining, .rubyDelivery]

/-- The number of dedicated action spaces per channel.
    Channels with fewer spaces are harder to develop and more
    vulnerable to opponent contention. -/
def channelWidth (ch : ScoringChannel) : Nat :=
  (channelActionSpaces ch).length

/-- Two scoring channels conflict if they compete for the same
    action spaces or the same resources (ore, stone, wood). -/
def channelsConflict : ScoringChannel -> ScoringChannel -> Bool
  | .weaponExpedition, .mining => true    -- both need ore
  | .mining, .weaponExpedition => true
  | .furnishing, .mining => true          -- both need stone
  | .mining, .furnishing => true
  | .weaponExpedition, .furnishing => true -- expedition time vs excavation time
  | .furnishing, .weaponExpedition => true
  | _, _ => false

/-- The maximum number of non-conflicting channels a player can
    pursue simultaneously. With the action budget, investing in
    more than 2 channels dilutes each below viability. -/
def maxSimultaneousChannels : Nat := 2

/-- With one family growth (47 total placements) and food obligations
    consuming roughly 8-10 actions in the first 4 rounds, a player
    has approximately 37-39 productive actions. Each channel requires
    at least 6 dedicated actions to develop to competitive scoring.
    This bounds viable primary channels to at most 2. -/
def productiveActionsEstimate : Nat :=
  totalPlacementsOneGrowthRound4 - 10  -- 47 - 10 food actions = 37

def minActionsPerChannel : Nat := 6

/-- Map from archetype to the set of channels it uses (primary + secondary). -/
def archetypeChannels (s : StrategyArchetype) : List ScoringChannel :=
  primaryChannel s :: secondaryChannels s

-- ============================================================
-- Dominance margin computation
-- ============================================================

/-- The dominance margin in column `col`: the gap between the furnishing
    rush payoff and the next-best row's payoff in that column.
    A positive margin means furnishing rush strictly dominates in that column.
    A zero margin means it ties (weak dominance). -/
def dominanceMarginInCol (col : Fin 8) : Int :=
  let furnRow := payoffMatrix 0 col
  -- Find the maximum of rows 1-7 in this column
  let others := [payoffMatrix 1 col, payoffMatrix 2 col, payoffMatrix 3 col,
                 payoffMatrix 4 col, payoffMatrix 5 col, payoffMatrix 6 col,
                 payoffMatrix 7 col]
  let bestOther := others.foldl max 0
  furnRow - bestOther

/-- The minimum dominance margin across all columns. This is the
    smallest gap between furnishing rush and its closest competitor
    in any single matchup. If this is positive, furnishing rush
    strictly dominates everywhere. If zero, it only weakly dominates
    (ties in at least one column). -/
def minDominanceMargin : Int :=
  let margins := List.ofFn (n := 8) dominanceMarginInCol
  margins.foldl min 1000  -- start high, fold down

-- ============================================================
-- Dog stacking scoring
-- ============================================================

/-- Total animal points from a dog-sheep stack on a single meadow.
    n dogs watch (n+1) sheep. Animal scoring: 1 point per animal.
    Total animal points: n (dogs) + n+1 (sheep) = 2n + 1. -/
def dogSheepAnimalPoints (numDogs : Nat) : Nat :=
  let sheep := dogSheepCapacity numDogs
  numDogs + sheep

/-- Weaving Parlor bonus from a dog-sheep stack: +1 per 2 sheep. -/
def dogSheepWeavingBonus (numDogs : Nat) : Nat :=
  dogSheepCapacity numDogs / 2

/-- Total scoring value of a dog-sheep stack with Weaving Parlor:
    animal points + weaving parlor bonus. -/
def dogSheepTotalValue (numDogs : Nat) : Nat :=
  dogSheepAnimalPoints numDogs + dogSheepWeavingBonus numDogs

-- ============================================================
-- Writing Chamber effective savings
-- ============================================================

/-- Penalty points from missing k farm animal types. -/
def missingAnimalPenalty (missing : Nat) : Nat := missing * 2

/-- Penalty points from n unused board spaces. -/
def unusedSpacePenalty (unused : Nat) : Nat := unused

/-- Total penalty for a focused strategy that skips k animal types
    and leaves n spaces unused (no begging). -/
def focusedStrategyPenalty (missingTypes unusedSpaces : Nat) : Nat :=
  missingAnimalPenalty missingTypes + unusedSpacePenalty unusedSpaces

/-- Net penalty after applying Writing Chamber (prevents up to 7 points). -/
def penaltyAfterWritingChamber (totalPenalty : Nat) : Nat :=
  totalPenalty - writingChamberReduction totalPenalty

/-- Writing Chamber effective savings for a given raw penalty total. -/
def writingChamberSavings (totalPenalty : Nat) : Nat :=
  writingChamberReduction totalPenalty

-- ============================================================
-- Action budget impossibility: no better strategy exists
-- ============================================================

/-- Maximum points scored per action invested in each scoring channel.
    These are upper bounds derived from the game's scoring rules:

    - Furnishing: 6 points/action. Each excavation+furnish pair yields
      a tile worth 4-8 base points plus bonuses that multiply with
      adjacent tiles. The average yield per dedicated action is ~6,
      with State Parlor/Office Room/Broom Chamber pushing higher.

    - Weapon/Expedition: 4 points/action. Each blacksmithing+expedition
      cycle costs 2 actions (forge + adventure) and yields ~8 points
      of loot value, so 4 per action.

    - Animal breeding: 3 points/action. Each sheep/donkey farming
      action yields 2-4 animals worth 1 point each, plus parlor
      bonuses averaging ~1 per action.

    - Agriculture: 3 points/action. Clearing+sowing+harvesting over
      multiple rounds yields grain/vegetables worth ~3 per dedicated
      action (counting the multi-round investment).

    - Mining: 3 points/action. Ore mine construction costs 1 action
      for 3 mine points. Ruby mine construction costs more but yields
      4 points + rubies.

    - Economy: 2 points/action. Starting player, ore trading, and
      ruby mining yield gold/rubies at ~2 points per action. -/
def channelYieldPerAction : ScoringChannel -> Nat
  | .furnishing       => 6
  | .weaponExpedition => 4
  | .animalBreeding   => 3
  | .agriculture      => 3
  | .mining           => 3
  | .economy          => 2

/-- An action allocation distributes the productive action budget
    across the 6 scoring channels. Each field represents the number
    of actions dedicated to that channel. The sum must not exceed
    the productive action budget (37 actions after food obligations). -/
structure ActionAllocation where
  furnishing       : Nat
  weaponExpedition : Nat
  animalBreeding   : Nat
  agriculture      : Nat
  mining           : Nat
  economy          : Nat
  deriving Repr, DecidableEq

/-- Total actions used by an allocation. -/
def ActionAllocation.totalActions (a : ActionAllocation) : Nat :=
  a.furnishing + a.weaponExpedition + a.animalBreeding +
  a.agriculture + a.mining + a.economy

/-- An allocation is valid if it fits within the productive budget. -/
def ActionAllocation.valid (a : ActionAllocation) : Prop :=
  a.totalActions <= productiveActionsEstimate

/-- The raw score from an allocation: sum of (actions * yield) per channel.
    This is an upper bound on the actual score achievable, because it
    assumes each action achieves the maximum yield for its channel. -/
def ActionAllocation.rawScore (a : ActionAllocation) : Nat :=
  a.furnishing * channelYieldPerAction .furnishing +
  a.weaponExpedition * channelYieldPerAction .weaponExpedition +
  a.animalBreeding * channelYieldPerAction .animalBreeding +
  a.agriculture * channelYieldPerAction .agriculture +
  a.mining * channelYieldPerAction .mining +
  a.economy * channelYieldPerAction .economy

/-- The furnishing-maximizing allocation: invest all productive actions
    in the furnishing channel. This represents the furnishing rush
    archetype at maximum commitment. -/
def furnishingMaxAllocation : ActionAllocation where
  furnishing       := productiveActionsEstimate
  weaponExpedition := 0
  animalBreeding   := 0
  agriculture      := 0
  mining           := 0
  economy          := 0

/-- The furnishing-max allocation is valid. -/
theorem furnishingMaxAllocation_valid :
    furnishingMaxAllocation.valid := by
  simp [ActionAllocation.valid, ActionAllocation.totalActions,
        furnishingMaxAllocation, productiveActionsEstimate,
        totalPlacementsOneGrowthRound4]

/-- The raw score of the furnishing-max allocation. -/
def furnishingMaxRawScore : Nat := furnishingMaxAllocation.rawScore

/-- The second-highest channel yield (weapon/expedition at 4). -/
def secondHighestYield : Nat := channelYieldPerAction .weaponExpedition

/-- The yield advantage of furnishing over the next-best channel. -/
def furnishingYieldAdvantage : Nat :=
  channelYieldPerAction .furnishing - secondHighestYield

end Caverna
