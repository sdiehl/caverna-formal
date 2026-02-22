/-
  Caverna.Types -- Core game types
  ================================

  Foundational types modeling the Caverna game state: resources, animals,
  board spaces, dwarf workers, weapons, and the player state.
-/

namespace Caverna

/-- The six types of resources (building materials + currency). -/
inductive Resource where
  | wood
  | stone
  | ore
  | food
  | gold
  | ruby
  deriving Repr, DecidableEq, BEq

/-- The five animal types in Caverna. Dogs are special (not farm animals). -/
inductive AnimalType where
  | dog
  | sheep
  | donkey
  | wildBoar
  | cattle
  deriving Repr, DecidableEq, BEq

/-- The four farm animal types (excludes dogs). -/
inductive FarmAnimalType where
  | sheep
  | donkey
  | wildBoar
  | cattle
  deriving Repr, DecidableEq, BEq

/-- Crop types that can be sown on fields. -/
inductive CropType where
  | grain
  | vegetable
  deriving Repr, DecidableEq, BEq

/-- A weapon carried by a dwarf. Strength ranges from 1 to 14. -/
structure Weapon where
  strength : Nat
  h_min : strength >= 1
  h_max : strength <= 14

instance : Repr Weapon where
  reprPrec w _ := s!"Weapon({w.strength})"

/-- A dwarf worker. May be armed or unarmed. -/
structure Dwarf where
  weapon : Option Weapon
  isOffspring : Bool  -- born this round (pays only 1 food)
  deriving Repr

/-- The types of spaces on the Mountain (right) side of the home board. -/
inductive MountainSpace where
  | empty           -- bare rock, unexcavated
  | cavern          -- excavated, can be furnished
  | tunnel          -- ordinary tunnel
  | deepTunnel      -- deep tunnel (part of ore mine)
  | oreMine         -- ore mine (covers 2 tunnels)
  | rubyMine        -- ruby mine (covers 1 tunnel)
  | furnished (name : String) (points : Nat)  -- furnished cavern
  deriving Repr

/-- The types of spaces on the Forest (left) side of the home board. -/
inductive ForestSpace where
  | forest              -- untouched forest
  | forestWithStable    -- stable on uncleared forest (holds 1 wild boar)
  | meadow              -- cleared, unfenced
  | meadowWithStable    -- meadow + stable (holds 1 any animal)
  | field (crop : Option CropType) (tokens : Nat)  -- plowed field
  | smallPasture        -- fenced single meadow (holds 2 same-type)
  | smallPastureStable  -- small pasture + stable (holds 4 same-type)
  | largePasture        -- fenced 2 meadows (holds 4 same-type, uses 2 spaces)
  | largePastureStable  -- large pasture + 1 stable (holds 8 same-type)
  | largePasture2Stable -- large pasture + 2 stables (holds 16 same-type)
  deriving Repr

/-- Aggregate counts of animals a player has. -/
structure AnimalCounts where
  dogs : Nat := 0
  sheep : Nat := 0
  donkeys : Nat := 0
  wildBoars : Nat := 0
  cattle : Nat := 0
  deriving Repr

/-- A player's complete resource supply. -/
structure Supply where
  wood : Nat := 0
  stone : Nat := 0
  ore : Nat := 0
  food : Nat := 0
  gold : Nat := 0
  rubies : Nat := 0
  grain : Nat := 0
  vegetables : Nat := 0
  deriving Repr

/-- Furnishing tile representation with cost and point value. -/
structure FurnishingTile where
  name : String
  woodCost : Nat := 0
  stoneCost : Nat := 0
  oreCost : Nat := 0
  points : Nat := 0
  bonusPoints : Nat := 0  -- conditional bonus points
  deriving Repr

/-- The complete state of a single player. -/
structure PlayerState where
  dwarfs : List Dwarf
  supply : Supply
  animals : AnimalCounts
  mountainSpaces : List MountainSpace  -- 12 mountain spaces (4x3 grid)
  forestSpaces : List ForestSpace       -- 12 forest spaces (4x3 grid)
  stables : Nat                         -- stables placed (max 3)
  furnishings : List FurnishingTile
  beggingMarkers : Nat := 0
  smallPastures : Nat := 0
  largePastures : Nat := 0
  oreMines : Nat := 0
  rubyMines : Nat := 0
  deriving Repr

/-- The four stages of the game, each introducing new action space cards. -/
inductive Stage where
  | one   -- rounds 1-3
  | two   -- rounds 4-6
  | three -- rounds 7-9
  | four  -- rounds 10-12
  deriving Repr, DecidableEq, BEq

/-- Round number (1-12). -/
abbrev RoundNum := Fin 12

/-- Number of players (1-7). -/
structure PlayerCount where
  val : Nat
  h_min : val >= 1
  h_max : val <= 7

/-- Total number of dwarfs a player has in play. -/
def PlayerState.numDwarfs (ps : PlayerState) : Nat :=
  ps.dwarfs.length

/-- Number of armed dwarfs (carrying weapons). -/
def PlayerState.numArmedDwarfs (ps : PlayerState) : Nat :=
  ps.dwarfs.filter (fun d => d.weapon.isSome) |>.length

/-- Maximum dwarfs allowed (normally 5, 6 with Additional Dwelling). -/
def PlayerState.maxDwarfs (ps : PlayerState) : Nat :=
  if ps.furnishings.any (fun f => f.name == "Additional dwelling")
  then 6
  else 5

/-- Count of unused (empty) spaces on a player's home board. -/
def PlayerState.unusedSpaces (ps : PlayerState) : Nat :=
  let unusedMountain := ps.mountainSpaces.filter (fun s =>
    match s with
    | MountainSpace.empty => true
    | _ => false) |>.length
  let unusedForest := ps.forestSpaces.filter (fun s =>
    match s with
    | ForestSpace.forest => true
    | _ => false) |>.length
  unusedMountain + unusedForest

/-- Count of fields with crops still on them (for grain scoring). -/
def PlayerState.grainOnFields (ps : PlayerState) : Nat :=
  ps.forestSpaces.foldl (fun acc s =>
    match s with
    | ForestSpace.field (some CropType.grain) n => acc + n
    | _ => acc) 0

/-- Count of fields with vegetables still on them. -/
def PlayerState.vegsOnFields (ps : PlayerState) : Nat :=
  ps.forestSpaces.foldl (fun acc s =>
    match s with
    | ForestSpace.field (some CropType.vegetable) n => acc + n
    | _ => acc) 0

/-- Total grain count (supply + on fields). -/
def PlayerState.totalGrain (ps : PlayerState) : Nat :=
  ps.supply.grain + ps.grainOnFields

/-- Total vegetable count (supply + on fields). -/
def PlayerState.totalVegetables (ps : PlayerState) : Nat :=
  ps.supply.vegetables + ps.vegsOnFields

/-- Total animal count (all types). -/
def AnimalCounts.total (ac : AnimalCounts) : Nat :=
  ac.dogs + ac.sheep + ac.donkeys + ac.wildBoars + ac.cattle

/-- Count of missing farm animal types (for -2 penalty each). -/
def AnimalCounts.missingFarmTypes (ac : AnimalCounts) : Nat :=
  let s := if ac.sheep == 0 then 1 else 0
  let d := if ac.donkeys == 0 then 1 else 0
  let w := if ac.wildBoars == 0 then 1 else 0
  let c := if ac.cattle == 0 then 1 else 0
  s + d + w + c

-- ============================================================
-- Finite State Machine: 2-Player Game
-- ============================================================

/-- In a 2-player game there are 11 rounds (round 9 is skipped). -/
def twoPlayerRounds : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]

/-- The actions available on the pre-printed board (2-player / 1-3 player side).
    Each action space can hold at most one dwarf per round. -/
inductive ActionSpaceId where
  -- Pre-printed (always available)
  | driftMining        -- stone + Cavern/Tunnel tile
  | logging            -- accumulates wood
  | woodGathering      -- accumulates wood
  | excavation         -- stone + Cavern/Tunnel or Cavern/Cavern tile
  | supplies           -- 1 wood, 1 stone, 1 ore, 1 food, 2 gold
  | clearing           -- wood + Meadow/Field tile
  | startingPlayer     -- become start player + accumulated food + 2 ore
  | oreMining          -- accumulates ore (+ bonus ore per ore mine)
  | sustenance         -- accumulates grain/vegetable + Meadow/Field tile
  | rubyMining         -- accumulates rubies (from round 3 in 2p)
  | housework          -- +1 dog, and/or furnish a cavern
  | slashAndBurn       -- Meadow/Field tile, and then/or sow
  -- Round cards (revealed 1 per round)
  | blacksmithing      -- forge weapon, and then/or level 3 expedition
  | sheepFarming       -- accumulates sheep, build fences/stables
  | oreMineConstruction -- build ore mine, and then/or level 2 expedition
  | wishForChildren    -- furnish dwelling OR family growth (round 4 card)
  | donkeyFarming      -- accumulates donkeys, build fences/stables
  | rubyMineConstruction -- build ruby mine, or level 2 expedition
  | oreDelivery        -- accumulates ore (+ bonus per ore mine)
  | familyLife         -- family growth, and/or sow
  | oreTrading         -- exchange ore for gold + food
  | adventure          -- forge weapon, and then 2x level 1 expedition
  | rubyDelivery       -- accumulates rubies (+ bonus if 2+ ruby mines)
  deriving Repr, DecidableEq, BEq

/-- Which round each card is revealed in (for the 2-player game).
    Round 9 is skipped (Exploration card removed). The "Wish for children"
    card is always dealt to round 4 regardless of shuffle. -/
def actionSpaceRound : ActionSpaceId -> Option Nat
  | .blacksmithing       => some 1  -- stage 1
  | .sheepFarming         => some 2  -- stage 1
  | .oreMineConstruction  => some 3  -- stage 1
  | .wishForChildren      => some 4  -- always round 4
  | .donkeyFarming        => some 5  -- stage 2
  | .rubyMineConstruction => some 6  -- stage 2
  | .oreDelivery          => some 7  -- stage 3
  | .familyLife           => some 8  -- stage 3
  -- round 9 skipped in 2-player
  | .oreTrading           => some 10 -- stage 4
  | .adventure            => some 11 -- stage 4
  | .rubyDelivery         => some 12 -- stage 4
  -- pre-printed spaces have no reveal round
  | _ => none

/-- Which player goes first in a given round.
    Starting player only changes if someone takes the Starting Player action. -/
inductive TurnOrder where
  | player1First
  | player2First
  deriving Repr, DecidableEq, BEq

/-- A harvest event type (from the harvest markers on rounds 6-12). -/
inductive HarvestEvent where
  | normalHarvest              -- green leaf: full field + feeding + breeding
  | noHarvest                  -- 1st question mark: no harvest at all
  | payOnePerDwarf             -- 2nd question mark: 1 food per dwarf, no field/breed
  | skipFieldOrBreeding        -- 3rd question mark: choose field OR breeding, must feed
  deriving Repr, DecidableEq, BEq

/-- The complete state of a 2-player game at any point in time. -/
structure GameState where
  round : Nat                              -- current round (1-12, skipping 9)
  player1 : PlayerState
  player2 : PlayerState
  turnOrder : TurnOrder
  occupiedSpaces : List (ActionSpaceId × Bool)  -- (space, true=p1 false=p2)
  accumulatedGoods : ActionSpaceId -> Nat   -- goods sitting on accumulating spaces
  harvestMarkers : List HarvestEvent        -- unrevealed markers for rounds 6-12
  questionMarksRevealed : Nat               -- how many ? markers seen so far
  revealedCards : List ActionSpaceId        -- action cards flipped so far

/-- The phases within a single round, forming the FSM transitions. -/
inductive RoundPhase where
  | addActionSpace       -- phase 1: flip new action card
  | replenish            -- phase 2: add goods to accumulating spaces
  | workPhase            -- phase 3: alternating dwarf placement
  | returnHome           -- phase 4: dwarfs go back to dwellings
  | harvestTime          -- phase 5: field phase, feeding, breeding
  deriving Repr, DecidableEq, BEq

/-- A player action: place a dwarf on a space and execute the action. -/
structure PlayerAction where
  space : ActionSpaceId
  -- Additional choices made during the action (simplified)
  builtTile : Bool := false
  forgedWeapon : Option Nat := none  -- ore spent on weapon
  expeditionLoot : List Nat := []    -- indices of chosen loot items
  grewFamily : Bool := false
  sowed : Bool := false

/-- The harvest schedule for a 2-player game.
    Rounds 1,2: no harvest. Round 3: normal harvest.
    Round 4: pay 1 food per dwarf (special).
    Rounds 5-12 (except 9): harvest by default, modified by markers. -/
def twoPlayerHarvestSchedule : Nat -> HarvestEvent
  | 1 => HarvestEvent.noHarvest
  | 2 => HarvestEvent.noHarvest
  | 3 => HarvestEvent.normalHarvest
  | 4 => HarvestEvent.payOnePerDwarf
  -- Rounds 5+ default to normal harvest; markers on 6-12 may override
  | _ => HarvestEvent.normalHarvest

/-- How many dwarfs each player has at the start of a 2-player game. -/
def initialDwarfCount : Nat := 2

/-- Starting food for player 1 (starting player) in a 2-player game. -/
def startingFoodP1 : Nat := 1

/-- Starting food for player 2 (second player) in a 2-player game. -/
def startingFoodP2 : Nat := 1

/-- Initial player state for the starting player in a 2-player game. -/
def initialPlayerState (food : Nat) : PlayerState :=
  { dwarfs := [{ weapon := none, isOffspring := false },
               { weapon := none, isOffspring := false }]
  , supply := { food := food }
  , animals := {}
  , mountainSpaces :=
      -- 12 mountain spaces: 2 pre-printed caverns (entry-level dwelling + empty cavern),
      -- 10 empty rock faces
      [.furnished "Entry-level dwelling" 0, .cavern] ++
      List.replicate 10 .empty
  , forestSpaces := List.replicate 12 .forest
  , stables := 0
  , furnishings := [{ name := "Entry-level dwelling", points := 0 }]
  , beggingMarkers := 0
  , smallPastures := 0
  , largePastures := 0
  , oreMines := 0
  , rubyMines := 0
  }

/-- The initial game state for a 2-player game. -/
def initialGameState : GameState :=
  { round := 1
  , player1 := initialPlayerState startingFoodP1
  , player2 := initialPlayerState startingFoodP2
  , turnOrder := TurnOrder.player1First
  , occupiedSpaces := []
  , accumulatedGoods := fun _ => 0
  , harvestMarkers := []  -- filled during setup with shuffled markers
  , questionMarksRevealed := 0
  , revealedCards := []
  }

/-- In a 2-player game, each player places 2 dwarfs in rounds 1-3,
    potentially more after family growth. The total dwarf-actions per
    round equals the sum of dwarfs across both players. -/
def totalActionsInRound (gs : GameState) : Nat :=
  gs.player1.numDwarfs + gs.player2.numDwarfs

/-- Available action spaces in a given round (pre-printed + revealed cards). -/
def availableSpaces (gs : GameState) : List ActionSpaceId :=
  let preprinted := [
    .driftMining, .logging, .woodGathering, .excavation,
    .supplies, .clearing, .startingPlayer, .oreMining,
    .sustenance, .rubyMining, .housework, .slashAndBurn
  ]
  preprinted ++ gs.revealedCards

/-- Action spaces NOT yet occupied this round. -/
def unoccupiedSpaces (gs : GameState) : List ActionSpaceId :=
  let occupied := gs.occupiedSpaces.map Prod.fst
  (availableSpaces gs).filter (fun s => !occupied.contains s)

end Caverna
