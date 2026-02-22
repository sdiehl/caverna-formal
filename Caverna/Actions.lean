/-
  Caverna.Actions -- Complete action space effect catalog
  ========================================================

  Models every action space in the 2-player Caverna game with full effects.
  Each action space is a function from player state + game state to
  updated player state + game state.

  The 2-player game has:
  - 12 pre-printed action spaces (always available)
  - 11 round cards (one revealed per round, round 9 skipped)
  - No Imitation spaces (3+ players only)
  - No Weekly Market (5+ players only)
  - Starting player gives 2 Ore (not 1 Ruby like 4-7 players)

  Each action space may provide:
  - Resources (goods taken from the space or supply)
  - Tiles (twin tiles, single tiles placed on home board)
  - Bonus actions (furnish, sow, fence, stable, expedition, family growth)
  - Accumulation collection (goods that have piled up on the space)
-/

import Caverna.Types
import Caverna.Furnishings
import Caverna.Board
import Caverna.Expedition
import Caverna.Food
import Caverna.Weapons

namespace Caverna

-- ============================================================
-- Player state for the full model
-- ============================================================

/-- Complete player state tracking all game-relevant quantities.
    Uses the compact representation (no board geometry abstraction)
    but includes all resource flows and scoring dimensions. -/
structure FullPlayer where
  -- Resources
  food : Nat := 0
  wood : Nat := 0
  stone : Nat := 0
  ore : Nat := 0
  gold : Nat := 0
  rubies : Nat := 0
  grain : Nat := 0
  vegetables : Nat := 0
  -- Workers
  dwarfs : Nat := 2
  offspring : Nat := 0        -- born this round, eat 1 food instead of 2
  weapons : List Nat := []    -- weapon strengths for each armed dwarf
  -- Animals
  dogs : Nat := 0
  sheep : Nat := 0
  donkeys : Nat := 0
  wildBoars : Nat := 0
  cattle : Nat := 0
  -- Board state (abstracted counts, not spatial)
  emptyCaverns : Nat := 1    -- starts with 1 empty cavern
  tunnels : Nat := 0
  deepTunnels : Nat := 0
  oreMines : Nat := 0
  rubyMines : Nat := 0
  meadows : Nat := 0
  fields : Nat := 0
  fieldsWithGrain : Nat := 0
  fieldsWithVeg : Nat := 0
  smallPastures : Nat := 0
  largePastures : Nat := 0
  stables : Nat := 0         -- max 3
  forestStables : Nat := 0   -- stables on forest spaces
  unusedMountain : Nat := 10  -- 12 - 2 pre-printed caverns
  unusedForest : Nat := 12
  -- Furnishing tiles owned
  furnishings : List FurnishingId := []
  -- Scoring / penalties
  beggingMarkers : Nat := 0
  -- Derived: max dwarf cap
  hasDwellingCapacity : Bool := false  -- has room for more dwarfs beyond current
  maxDwarfCap : Nat := 5              -- 5 normally, 6 with Additional Dwelling
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- Accumulation state
-- ============================================================

/-- Goods accumulated on each action space. -/
structure AccState where
  logging : Nat := 0            -- 3(1) wood: 1/round normally, 3 if empty
  woodGathering : Nat := 0      -- 1 wood/round
  oreMining : Nat := 0          -- 2 ore/round
  startingPlayer : Nat := 0     -- 1 food/round
  sustenance : Nat := 0         -- 1 grain if empty, 1 veg if not
  sustainanceHasGoods : Bool := false  -- tracks whether sustenance has goods
  sheepFarming : Nat := 0       -- 1 sheep/round (from stage 1)
  donkeyFarming : Nat := 0      -- 1 donkey/round (from stage 2)
  rubyMining : Nat := 0         -- 1 ruby/round from round 3 (2-player)
  oreDelivery : Nat := 0        -- 2 ore/round (from stage 3)
  rubyDelivery : Nat := 0       -- 1 ruby/round (from stage 4)
  deriving Repr, DecidableEq, BEq

/-- Replenish accumulation spaces at the start of a round. -/
def AccState.replenish (acc : AccState) (round : Nat) : AccState :=
  let logging' := if acc.logging == 0 then 3 else acc.logging + 1
  let woodGathering' := acc.woodGathering + 1
  let oreMining' := acc.oreMining + 2
  let startingPlayer' := acc.startingPlayer + 1
  -- Sustenance: 1 grain if empty, 1 vegetable if not
  let (sust', hasGoods') :=
    if acc.sustainanceHasGoods then (acc.sustenance + 1, true)  -- add 1 veg
    else (1, true)  -- was empty, put 1 grain
  let sheepFarming' := if round >= 2 then acc.sheepFarming + 1 else acc.sheepFarming
  let donkeyFarming' := if round >= 5 then acc.donkeyFarming + 1 else acc.donkeyFarming
  let rubyMining' := if round >= 3 then acc.rubyMining + 1 else acc.rubyMining
  let oreDelivery' := if round >= 7 then acc.oreDelivery + 2 else acc.oreDelivery
  let rubyDelivery' := if round >= 12 then acc.rubyDelivery + 1 else acc.rubyDelivery
  { logging := logging'
  , woodGathering := woodGathering'
  , oreMining := oreMining'
  , startingPlayer := startingPlayer'
  , sustenance := sust'
  , sustainanceHasGoods := hasGoods'
  , sheepFarming := sheepFarming'
  , donkeyFarming := donkeyFarming'
  , rubyMining := rubyMining'
  , oreDelivery := oreDelivery'
  , rubyDelivery := rubyDelivery'
  }

-- ============================================================
-- Full game state for the LTS
-- ============================================================

/-- The complete 2-player game state for the LTS. -/
structure FullGState where
  round : Nat                    -- current round (1-12, 9 skipped)
  p1 : FullPlayer
  p2 : FullPlayer
  p1IsFirst : Bool               -- starting player
  placementsLeft : Nat           -- dwarf placements remaining this round
  isP1Turn : Bool                -- whose turn to place next
  acc : AccState                 -- accumulation trackers
  occupiedSpaces : List ActionSpaceId := []
  -- Harvest schedule
  harvestSchedule : Nat -> HarvestEvent  -- round -> what kind of harvest
  questionMarksRevealed : Nat := 0
  -- Card reveal order (determines which spaces available when)
  revealedCards : List ActionSpaceId := []
  -- Phase tracking
  phase : RoundPhase := .addActionSpace
  -- Wish for children flip state
  wishIsUrgent : Bool := false   -- flips when Family Life card appears

-- ============================================================
-- Action space effects (full fidelity)
-- ============================================================

/-- Choice made when placing a dwarf on an action space.
    Different spaces require different sub-choices. -/
inductive ActionChoice where
  -- Resource collection (no choice needed for most accumulation spaces)
  | collectOnly
  -- Twin tile placement
  | placeCavernTunnel        -- place Cavern/Tunnel twin tile
  | placeCavernCavern        -- place Cavern/Cavern twin tile (Excavation only)
  | placeMeadowField         -- place Meadow/Field twin tile
  -- Furnishing
  | furnish (fid : FurnishingId)  -- furnish a specific tile
  -- Forging + expedition
  | forgeAndExpedition (oreSpent : Nat) (loot : List LootItem)
  | forgeOnly (oreSpent : Nat)
  -- Fencing
  | buildSmallPasture        -- fence 1 meadow (2 wood)
  | buildLargePasture        -- fence 2 adjacent meadows (4 wood)
  | buildBothPastures        -- small + large pasture
  -- Stabling
  | buildStable              -- 1 stone for 1 stable
  -- Family growth
  | growFamily
  -- Sow
  | sowGrain                 -- sow grain on a field
  | sowVegetable             -- sow vegetable on a field
  | sowBoth                  -- sow grain + vegetable
  -- Combinations
  | compound (choices : List ActionChoice)
  deriving Repr, BEq

/-- Apply the effect of collecting an accumulating space. -/
def collectAccumulation (p : FullPlayer) (acc : AccState) (space : ActionSpaceId)
    : FullPlayer × AccState :=
  match space with
  | .logging =>
    ({ p with wood := p.wood + acc.logging }, { acc with logging := 0 })
  | .woodGathering =>
    ({ p with wood := p.wood + acc.woodGathering }, { acc with woodGathering := 0 })
  | .oreMining =>
    let bonus := p.oreMines * 2
    ({ p with ore := p.ore + acc.oreMining + bonus }, { acc with oreMining := 0 })
  | .startingPlayer =>
    ({ p with food := p.food + acc.startingPlayer, ore := p.ore + 2 },
     { acc with startingPlayer := 0 })
  | .sustenance =>
    -- Gives whatever is on the space (grain or vegetable mix)
    -- Simplified: give grain equal to accumulation
    ({ p with grain := p.grain + acc.sustenance },
     { acc with sustenance := 0, sustainanceHasGoods := false })
  | .sheepFarming =>
    ({ p with sheep := p.sheep + acc.sheepFarming }, { acc with sheepFarming := 0 })
  | .donkeyFarming =>
    ({ p with donkeys := p.donkeys + acc.donkeyFarming }, { acc with donkeyFarming := 0 })
  | .rubyMining =>
    let bonus := if p.rubyMines >= 1 then 1 else 0
    ({ p with rubies := p.rubies + acc.rubyMining + bonus }, { acc with rubyMining := 0 })
  | .oreDelivery =>
    let bonus := p.oreMines * 2
    ({ p with ore := p.ore + acc.oreDelivery + bonus }, { acc with oreDelivery := 0 })
  | .rubyDelivery =>
    let bonus := if p.rubyMines >= 2 then 1 else 0
    ({ p with rubies := p.rubies + acc.rubyDelivery + bonus }, { acc with rubyDelivery := 0 })
  | _ => (p, acc)

/-- Apply the Supplies action: 1 wood, 1 stone, 1 ore, 1 food, 2 gold. -/
def applySupplies (p : FullPlayer) : FullPlayer :=
  { p with wood := p.wood + 1, stone := p.stone + 1,
           ore := p.ore + 1, food := p.food + 1, gold := p.gold + 2 }

/-- Apply sowing action. 1 grain from supply -> field gets 3 total. -/
def applySowGrain (p : FullPlayer) : FullPlayer :=
  if p.grain >= 1 && p.fields > p.fieldsWithGrain + p.fieldsWithVeg then
    { p with grain := p.grain - 1, fieldsWithGrain := p.fieldsWithGrain + 1 }
  else p

/-- Apply sowing vegetable. 1 veg from supply -> field gets 2 total. -/
def applySowVeg (p : FullPlayer) : FullPlayer :=
  if p.vegetables >= 1 && p.fields > p.fieldsWithGrain + p.fieldsWithVeg then
    { p with vegetables := p.vegetables - 1, fieldsWithVeg := p.fieldsWithVeg + 1 }
  else p

/-- Apply forging a weapon. -/
def applyForge (p : FullPlayer) (oreSpent : Nat) : FullPlayer :=
  if oreSpent >= 1 && oreSpent <= 8 && p.ore >= oreSpent then
    { p with ore := p.ore - oreSpent, weapons := p.weapons ++ [oreSpent] }
  else p

/-- Apply family growth. -/
def applyFamilyGrowth (p : FullPlayer) : FullPlayer :=
  let totalDwarfs := p.dwarfs + p.offspring
  if totalDwarfs < p.maxDwarfCap && p.hasDwellingCapacity then
    { p with offspring := p.offspring + 1 }
  else p

/-- Apply furnishing a cavern with a specific tile.
    Deducts all resource costs (wood, stone, ore, gold, grain, veg, food). -/
def applyFurnishing (p : FullPlayer) (fid : FurnishingId) : FullPlayer :=
  let spec := furnishingSpec fid
  if p.emptyCaverns >= 1 &&
     canAffordFurnishing fid p.wood p.stone p.ore p.gold p.grain p.vegetables p.food then
    let p' := { p with wood := p.wood - spec.woodCost,
                       stone := p.stone - spec.stoneCost,
                       ore := p.ore - spec.oreCost,
                       gold := p.gold - spec.goldCost,
                       grain := p.grain - spec.grainCost,
                       vegetables := p.vegetables - spec.vegCost,
                       food := p.food - spec.foodCost,
                       emptyCaverns := p.emptyCaverns - 1,
                       furnishings := p.furnishings ++ [fid] }
    -- If it's a dwelling, update dwelling capacity
    if fid.isDwelling then
      let newCap := if fid.raisesMaxDwarfs then 6 else p'.maxDwarfCap
      { p' with hasDwellingCapacity := true, maxDwarfCap := newCap }
    else p'
  else p

/-- Apply building a small pasture (2 wood, 1 meadow -> small pasture). -/
def applySmallPasture (p : FullPlayer) : FullPlayer :=
  if p.wood >= 2 && p.meadows >= 1 then
    { p with wood := p.wood - 2, meadows := p.meadows - 1,
             smallPastures := p.smallPastures + 1 }
  else p

/-- Apply building a large pasture (4 wood, 2 adjacent meadows). -/
def applyLargePasture (p : FullPlayer) : FullPlayer :=
  if p.wood >= 4 && p.meadows >= 2 then
    { p with wood := p.wood - 4, meadows := p.meadows - 2,
             largePastures := p.largePastures + 1 }
  else p

/-- Apply building a stable (1 stone, max 3 total). -/
def applyBuildStable (p : FullPlayer) : FullPlayer :=
  if p.stone >= 1 && p.stables < 3 then
    { p with stone := p.stone - 1, stables := p.stables + 1 }
  else p

/-- Apply excavation: place Cavern/Tunnel twin tile. -/
def applyExcavationCT (p : FullPlayer) : FullPlayer :=
  if p.unusedMountain >= 2 then
    { p with unusedMountain := p.unusedMountain - 2,
             emptyCaverns := p.emptyCaverns + 1,
             tunnels := p.tunnels + 1 }
  else p

/-- Apply excavation: place Cavern/Cavern twin tile. -/
def applyExcavationCC (p : FullPlayer) : FullPlayer :=
  if p.unusedMountain >= 2 then
    { p with unusedMountain := p.unusedMountain - 2,
             emptyCaverns := p.emptyCaverns + 2 }
  else p

/-- Apply Meadow/Field twin tile placement. -/
def applyMeadowField (p : FullPlayer) : FullPlayer :=
  if p.unusedForest >= 2 then
    { p with unusedForest := p.unusedForest - 2,
             meadows := p.meadows + 1,
             fields := p.fields + 1 }
  else p

/-- Apply ore mine construction: cover 2 adjacent tunnels, gain 3 ore. -/
def applyOreMineConstruction (p : FullPlayer) : FullPlayer :=
  if p.tunnels >= 2 then
    { p with tunnels := p.tunnels - 2,
             oreMines := p.oreMines + 1,
             deepTunnels := p.deepTunnels + 1,
             ore := p.ore + 3 }
  else p

/-- Apply ruby mine construction on a tunnel.
    If placed on a deep tunnel, gain 1 ruby immediately. -/
def applyRubyMineConstruction (p : FullPlayer) : FullPlayer :=
  if p.tunnels >= 1 then
    { p with tunnels := p.tunnels - 1,
             rubyMines := p.rubyMines + 1 }
  else if p.deepTunnels >= 1 then
    { p with deepTunnels := p.deepTunnels - 1,
             rubyMines := p.rubyMines + 1,
             rubies := p.rubies + 1 }  -- bonus ruby for deep tunnel
  else p

/-- Apply ore trading: 2 ore -> 2 gold + 1 food, up to 3 times. -/
def applyOreTrading (p : FullPlayer) (times : Nat) : FullPlayer :=
  let t := min times 3
  let oreNeeded := t * 2
  if p.ore >= oreNeeded then
    { p with ore := p.ore - oreNeeded,
             gold := p.gold + t * 2,
             food := p.food + t }
  else p

-- ============================================================
-- Scoring for full player state
-- ============================================================

/-- Compute the total score for a FullPlayer at game end. -/
def FullPlayer.score (p : FullPlayer) : Int :=
  -- Positive points
  let animals := (p.dogs + p.sheep + p.donkeys + p.wildBoars + p.cattle : Int)
  let grainPts := (((p.grain + p.fieldsWithGrain * 3) + 1) / 2 : Int)  -- half, rounded up
  let vegPts := ((p.vegetables + p.fieldsWithVeg * 2) : Int)
  let rubyPts := (p.rubies : Int)
  let dwarfPts := ((p.dwarfs + p.offspring) : Int)
  let pasturePts := (p.smallPastures * 2 + p.largePastures * 4 : Int)
  let minePts := (p.oreMines * 3 + p.rubyMines * 4 : Int)
  let goldPts := (p.gold : Int)
  let furnPts := p.furnishings.foldl (fun acc fid =>
    acc + ((furnishingSpec fid).basePoints : Int)) (0 : Int)
  -- Negative points
  let missingTypes :=
    (if p.sheep == 0 then 1 else 0) + (if p.donkeys == 0 then 1 else 0) +
    (if p.wildBoars == 0 then 1 else 0) + (if p.cattle == 0 then 1 else 0)
  let unusedPenalty := (p.unusedMountain + p.unusedForest : Int)
  let beggingPenalty := (p.beggingMarkers * 3 : Int)
  let missingPenalty := (missingTypes * 2 : Int)
  -- Total
  animals + grainPts + vegPts + rubyPts + dwarfPts + pasturePts +
  minePts + goldPts + furnPts - unusedPenalty - beggingPenalty - missingPenalty

-- ============================================================
-- Feeding logic
-- ============================================================

/-- Feed a player during harvest. Adults cost 2 food, offspring cost 1.
    Uses food first, then converts goods, then takes begging markers. -/
def FullPlayer.feed (p : FullPlayer) : FullPlayer :=
  let cost := p.dwarfs * 2 + p.offspring * 1
  if p.food >= cost then
    { p with food := p.food - cost }
  else
    let deficit := cost - p.food
    let p' := { p with food := 0 }
    -- Try converting grain (1 food each)
    let grainUsed := min p'.grain deficit
    let p'' := { p' with grain := p'.grain - grainUsed }
    let deficit' := deficit - grainUsed
    -- Try converting vegetables (2 food each)
    let vegUsed := min p''.vegetables (deficit' / 2 + deficit' % 2)
    let vegFood := min (vegUsed * 2) deficit'
    let p''' := { p'' with vegetables := p''.vegetables - vegUsed }
    let deficit'' := deficit' - vegFood
    -- Remaining deficit becomes begging markers
    { p''' with beggingMarkers := p'''.beggingMarkers + deficit'' }

/-- Feed during round 4 special (1 food per dwarf including offspring). -/
def FullPlayer.feedRound4 (p : FullPlayer) : FullPlayer :=
  let cost := p.dwarfs + p.offspring
  if p.food >= cost then
    { p with food := p.food - cost }
  else
    let deficit := cost - p.food
    { p with food := 0, beggingMarkers := p.beggingMarkers + deficit }

-- ============================================================
-- Initial state
-- ============================================================

/-- Initial player state for the 2-player game. -/
def initialFullPlayer : FullPlayer :=
  { food := 1
  , dwarfs := 2
  , emptyCaverns := 1    -- 1 empty cavern ready to furnish
  , unusedMountain := 10  -- 12 - 2 (entry-level + empty cavern)
  , unusedForest := 12
  , maxDwarfCap := 5
  }

end Caverna
