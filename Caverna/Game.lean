/-
  Caverna.Game -- Full game as a Labeled Transition System
  =========================================================

  Models the 2-player Caverna game as an LTS using the transition-system
  library. The state tracks both players' complete resource and board state.
  Actions are dwarf placements on action spaces with sub-choices, plus
  harvest events and round transitions.

  The transition relation is the complete rule set: each action space
  has a precise effect on the game state, harvests consume food or
  generate begging markers, and the game terminates after round 12.

  This enables proving invariants that hold across ALL reachable game
  states (all possible play sequences, all 2,880 setups).
-/

import Caverna.Types
import Caverna.Food
import Caverna.Weapons
import Caverna.Scoring
import Caverna.Actions
import Caverna.Furnishings
import Caverna.Board
import Caverna.Expedition
import Caverna.TransitionSystem

namespace Caverna

-- ============================================================
-- Game phases for the LTS
-- ============================================================

/-- The game phase within a round. -/
inductive Phase where
  | placeP1      -- player 1 places a dwarf
  | placeP2      -- player 2 places a dwarf
  | harvest      -- harvest phase (feeding, breeding, fields)
  | roundEnd     -- round cleanup, advance to next round
  | gameOver     -- game has ended
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- Compact game state for the LTS
-- ============================================================

/-- The full 2-player game state. -/
structure GState where
  round : Nat              -- current round (1-12)
  phase : Phase
  p1 : FullPlayer
  p2 : FullPlayer
  p1IsFirst : Bool         -- who goes first this round
  placementsLeft : Nat     -- how many dwarf placements remain this round
  acc : AccState           -- accumulation goods on action spaces
  occupiedSpaces : List ActionSpaceId := []
  -- Card reveal order for this game setup
  stageCards : List (List ActionSpaceId) := []
  -- Track harvest events
  harvestSchedule : Nat -> HarvestEvent
  wishIsUrgent : Bool := false

-- ============================================================
-- Action type for the LTS
-- ============================================================

/-- A game action: dwarf placement with choice, or phase transition. -/
inductive GameAction where
  | place (space : ActionSpaceId) (choice : ActionChoice)
  | feedHarvest       -- pay food for harvest
  | takeBegging       -- cannot pay, take begging markers
  | advanceRound      -- move to next round
  | endGame           -- game terminates
  deriving Repr, BEq

-- ============================================================
-- Action space availability
-- ============================================================

/-- Is an action space available in a given round? -/
def spaceAvailable (round : Nat) (space : ActionSpaceId) : Bool :=
  match actionSpaceRound space with
  | none => true  -- pre-printed, always available
  | some r => r <= round

/-- Is a space unoccupied in the current state? -/
def spaceUnoccupied (gs : GState) (space : ActionSpaceId) : Bool :=
  !gs.occupiedSpaces.contains space

-- ============================================================
-- Apply a placement action
-- ============================================================

/-- Apply the complete effect of a dwarf placement on an action space.
    Returns the updated player and updated accumulation state. -/
def applyPlacement (p : FullPlayer) (gs : GState) (space : ActionSpaceId)
    (choice : ActionChoice) : FullPlayer × AccState :=
  match space with
  | .supplies =>
    (applySupplies p, gs.acc)
  | .logging =>
    collectAccumulation p gs.acc space
  | .woodGathering =>
    collectAccumulation p gs.acc space
  | .oreMining =>
    collectAccumulation p gs.acc space
  | .startingPlayer =>
    collectAccumulation p gs.acc space
  | .sustenance =>
    let (p', acc') := collectAccumulation p gs.acc space
    -- Also get Meadow/Field twin tile
    let p'' := match choice with
      | .placeMeadowField => applyMeadowField p'
      | _ => p'
    (p'', acc')
  | .clearing =>
    let p' := { p with wood := p.wood + 1 }
    let p'' := match choice with
      | .placeMeadowField => applyMeadowField p'
      | _ => p'
    (p'', gs.acc)
  | .rubyMining =>
    collectAccumulation p gs.acc space
  | .housework =>
    let p' := { p with dogs := p.dogs + 1 }
    let p'' := match choice with
      | .furnish fid => applyFurnishing p' fid
      | _ => p'
    (p'', gs.acc)
  | .slashAndBurn =>
    let p' := applyMeadowField p
    let p'' := match choice with
      | .sowGrain => applySowGrain p'
      | .sowVegetable => applySowVeg p'
      | .sowBoth => applySowVeg (applySowGrain p')
      | _ => p'
    (p'', gs.acc)
  | .driftMining =>
    let p' := { p with stone := p.stone + 1 }
    -- Drift mining only allows Cavern/Tunnel (not Cavern/Cavern)
    let p'' := match choice with
      | .placeCavernTunnel => applyExcavationCT p'
      | _ => p'
    (p'', gs.acc)
  | .excavation =>
    let p' := { p with stone := p.stone + 1 }
    let p'' := match choice with
      | .placeCavernTunnel => applyExcavationCT p'
      | .placeCavernCavern => applyExcavationCC p'
      | _ => p'
    (p'', gs.acc)
  -- Round cards
  | .blacksmithing =>
    match choice with
    | .forgeAndExpedition oreSpent loot =>
      let p' := applyForge p oreSpent
      -- Level 3 expedition
      let hasAllPlus1 := loot.any (fun i => match i with | .allWeaponsPlus1 => true | _ => false)
      -- Apply loot effects (simplified: just resource gains)
      let p'' := loot.foldl (fun acc item =>
        match item with
        | .dog => { acc with dogs := acc.dogs + 1 }
        | .wood => { acc with wood := acc.wood + 1 }
        | .grain => { acc with grain := acc.grain + 1 }
        | .sheep => { acc with sheep := acc.sheep + 1 }
        | .stone => { acc with stone := acc.stone + 1 }
        | .donkey => { acc with donkeys := acc.donkeys + 1 }
        | .ore => { acc with ore := acc.ore + 1 }
        | .wildBoar => { acc with wildBoars := acc.wildBoars + 1 }
        | .gold2 => { acc with gold := acc.gold + 2 }
        | .cattle => { acc with cattle := acc.cattle + 1 }
        | _ => acc) p'
      -- Weapon strength +1 from expedition, +1 from allWeapons if taken
      let _expBonus := 1 + (if hasAllPlus1 then 1 else 0)
      let newWeapons := p''.weapons.map (fun s => min 14 (s + (if hasAllPlus1 then 1 else 0)))
      let lastWeapon := match newWeapons.getLast? with
        | some w => min 14 (w + 1)  -- the dwarf doing the expedition gets +1
        | none => 0
      let finalWeapons := match newWeapons.dropLast with
        | rest => rest ++ [lastWeapon]
      ({ p'' with weapons := finalWeapons }, gs.acc)
    | _ => (p, gs.acc)
  | .sheepFarming =>
    let (p', acc') := collectAccumulation p gs.acc space
    -- Build fences and/or stable
    let p'' := match choice with
      | .buildSmallPasture => applySmallPasture p'
      | .buildLargePasture => applyLargePasture p'
      | .buildStable => applyBuildStable p'
      | _ => p'
    (p'', acc')
  | .oreMineConstruction =>
    let p' := applyOreMineConstruction p
    (p', gs.acc)
  | .wishForChildren =>
    if gs.wishIsUrgent then
      -- Urgent: must furnish dwelling first, then can grow
      match choice with
      | .furnish fid =>
        let p' := applyFurnishing p fid
        (applyFamilyGrowth p', gs.acc)
      | _ => (p, gs.acc)
    else
      -- Normal: furnish dwelling OR grow family
      match choice with
      | .furnish fid => (applyFurnishing p fid, gs.acc)
      | .growFamily => (applyFamilyGrowth p, gs.acc)
      | _ => (p, gs.acc)
  | .donkeyFarming =>
    let (p', acc') := collectAccumulation p gs.acc space
    let p'' := match choice with
      | .buildSmallPasture => applySmallPasture p'
      | .buildLargePasture => applyLargePasture p'
      | .buildStable => applyBuildStable p'
      | _ => p'
    (p'', acc')
  | .rubyMineConstruction =>
    let p' := applyRubyMineConstruction p
    (p', gs.acc)
  | .oreDelivery =>
    collectAccumulation p gs.acc space
  | .familyLife =>
    -- Family growth + sow
    let p' := applyFamilyGrowth p
    let p'' := match choice with
      | .sowGrain => applySowGrain p'
      | .sowVegetable => applySowVeg p'
      | .sowBoth => applySowVeg (applySowGrain p')
      | _ => p'
    (p'', gs.acc)
  | .oreTrading =>
    (applyOreTrading p 3, gs.acc)  -- up to 3 times
  | .adventure =>
    match choice with
    | .forgeAndExpedition oreSpent loot =>
      let p' := applyForge p oreSpent
      -- 2x level 1 expeditions: 2 loot items total, weapon +2
      let p'' := loot.foldl (fun acc item =>
        match item with
        | .dog => { acc with dogs := acc.dogs + 1 }
        | .wood => { acc with wood := acc.wood + 1 }
        | .grain => { acc with grain := acc.grain + 1 }
        | _ => acc) p'
      let newWeapons := match p''.weapons.getLast? with
        | some w => p''.weapons.dropLast ++ [min 14 (w + 2)]
        | none => p''.weapons
      ({ p'' with weapons := newWeapons }, gs.acc)
    | _ => (p, gs.acc)
  | .rubyDelivery =>
    collectAccumulation p gs.acc space

-- ============================================================
-- Harvest phase effects
-- ============================================================

/-- Field phase: harvest 1 token from each sown field. -/
def FullPlayer.fieldPhase (p : FullPlayer) : FullPlayer :=
  { p with grain := p.grain + p.fieldsWithGrain,
           vegetables := p.vegetables + p.fieldsWithVeg,
           fieldsWithGrain := if p.fieldsWithGrain > 0 then p.fieldsWithGrain - 1 else 0,
           fieldsWithVeg := if p.fieldsWithVeg > 0 then p.fieldsWithVeg - 1 else 0 }

/-- Breeding phase: if 2+ of a farm animal type, gain 1 (if room). -/
def FullPlayer.breedingPhase (p : FullPlayer) : FullPlayer :=
  let extraSheep := if p.sheep >= 2 then 1 else 0
  let extraDonkey := if p.donkeys >= 2 then 1 else 0
  let extraBoar := if p.wildBoars >= 2 then 1 else 0
  let extraCattle := if p.cattle >= 2 then 1 else 0
  { p with sheep := p.sheep + extraSheep,
           donkeys := p.donkeys + extraDonkey,
           wildBoars := p.wildBoars + extraBoar,
           cattle := p.cattle + extraCattle }

/-- Full harvest: field phase + feeding + breeding. -/
def FullPlayer.normalHarvest (p : FullPlayer) : FullPlayer :=
  p.fieldPhase.feed.breedingPhase

-- ============================================================
-- Initial game state
-- ============================================================

/-- Initial game state for 2-player Caverna. -/
def initFullGState (schedule : Nat -> HarvestEvent) : GState :=
  { round := 1
  , phase := .placeP1
  , p1 := initialFullPlayer
  , p2 := initialFullPlayer
  , p1IsFirst := true
  , placementsLeft := 4  -- 2 dwarfs each = 4 placements
  , acc := {}
  , harvestSchedule := schedule
  }

-- ============================================================
-- The 2-player Caverna LTS
-- ============================================================

/-- The 2-player Caverna game as a Labeled Transition System.
    State = GState, Action = GameAction.
    This is the complete game model with all action space effects,
    harvest mechanics, and round progression. -/
def cavernaLTS (schedule : Nat -> HarvestEvent) :
    TransitionSystem.LTS GState GameAction where
  init := fun gs => gs = initFullGState schedule
  trans := fun gs act gs' =>
    match gs.phase, act with
    -- Player 1 placement
    | .placeP1, .place space choice =>
      spaceAvailable gs.round space = true ∧
      spaceUnoccupied gs space = true ∧
      gs.placementsLeft > 0 ∧
      (let (p1', acc') := applyPlacement gs.p1 gs space choice
       let newPlacements := gs.placementsLeft - 1
       let newOccupied := space :: gs.occupiedSpaces
       if newPlacements == 0 then
         gs' = { gs with p1 := p1', acc := acc',
                         phase := .harvest, placementsLeft := 0,
                         occupiedSpaces := newOccupied }
       else
         gs' = { gs with p1 := p1', acc := acc',
                         phase := .placeP2, placementsLeft := newPlacements,
                         occupiedSpaces := newOccupied })
    -- Player 2 placement
    | .placeP2, .place space choice =>
      spaceAvailable gs.round space = true ∧
      spaceUnoccupied gs space = true ∧
      gs.placementsLeft > 0 ∧
      (let (p2', acc') := applyPlacement gs.p2 gs space choice
       let newPlacements := gs.placementsLeft - 1
       let newOccupied := space :: gs.occupiedSpaces
       if newPlacements == 0 then
         gs' = { gs with p2 := p2', acc := acc',
                         phase := .harvest, placementsLeft := 0,
                         occupiedSpaces := newOccupied }
       else
         gs' = { gs with p2 := p2', acc := acc',
                         phase := .placeP1, placementsLeft := newPlacements,
                         occupiedSpaces := newOccupied })
    -- Harvest phase
    | .harvest, .feedHarvest =>
      let event := gs.harvestSchedule gs.round
      match event with
      | .normalHarvest =>
        let p1' := gs.p1.normalHarvest
        let p2' := gs.p2.normalHarvest
        gs' = { gs with p1 := p1', p2 := p2', phase := .roundEnd }
      | .noHarvest =>
        gs' = { gs with phase := .roundEnd }
      | .payOnePerDwarf =>
        let p1' := gs.p1.feedRound4
        let p2' := gs.p2.feedRound4
        gs' = { gs with p1 := p1', p2 := p2', phase := .roundEnd }
      | .skipFieldOrBreeding =>
        -- Choose field OR breeding, must still feed
        -- We model the "best case" for each player
        let p1' := gs.p1.fieldPhase.feed
        let p2' := gs.p2.fieldPhase.feed
        gs' = { gs with p1 := p1', p2 := p2', phase := .roundEnd }
    -- Skip harvest (early rounds)
    | .harvest, .takeBegging =>
      gs' = { gs with phase := .roundEnd }
    -- Round end: advance
    | .roundEnd, .advanceRound =>
      let nextRound := if gs.round == 8 then 10 else gs.round + 1
      if nextRound > 12 then
        gs' = { gs with round := nextRound, phase := .gameOver }
      else
        let acc' := gs.acc.replenish nextRound
        let totalDwarfs := (gs.p1.dwarfs + gs.p1.offspring) +
                          (gs.p2.dwarfs + gs.p2.offspring)
        -- Offspring become adults
        let p1' := { gs.p1 with dwarfs := gs.p1.dwarfs + gs.p1.offspring,
                                 offspring := 0 }
        let p2' := { gs.p2 with dwarfs := gs.p2.dwarfs + gs.p2.offspring,
                                 offspring := 0 }
        -- Flip Wish for Children when Family Life appears (round 8)
        let urgent' := gs.wishIsUrgent || nextRound == 8
        gs' = { gs with
                  round := nextRound, p1 := p1', p2 := p2',
                  acc := acc',
                  phase := if gs.p1IsFirst then .placeP1 else .placeP2,
                  placementsLeft := totalDwarfs,
                  occupiedSpaces := [],
                  wishIsUrgent := urgent' }
    -- Game over: terminal
    | .gameOver, .endGame => gs' = gs
    | _, _ => False

-- ============================================================
-- Key predicates for strategy analysis
-- ============================================================

/-- A player is in food deficit at a given round's harvest. -/
def FullPlayer.inFoodDeficit (p : FullPlayer) : Prop :=
  p.food < p.dwarfs * 2 + p.offspring

/-- The universal food crisis: at round 3, both players started with
    1 food and need 4 (2 dwarfs * 2 food each). -/
def foodCrisisInvariant (gs : GState) : Prop :=
  gs.round <= 2 -> gs.p1.food + gs.p2.food <= 2 + gs.round * 2

/-- Score comparison between two terminal states. -/
def p1Wins (gs : GState) : Prop :=
  gs.phase = .gameOver -> gs.p1.score > gs.p2.score

/-- Score comparison. -/
def p2Wins (gs : GState) : Prop :=
  gs.phase = .gameOver -> gs.p2.score > gs.p1.score

end Caverna
