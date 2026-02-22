/-
  Caverna.Scoring -- End-game scoring system
  ============================================

  Models the complete end-game scoring formula from the rulebook (p.23).
  Each scoring category is computed independently, then summed.
-/

import Caverna.Types

namespace Caverna

/-- Points from animals: 1 Gold per animal (including dogs). -/
def scoreAnimals (ac : AnimalCounts) : Nat :=
  ac.total

/-- Penalty for missing farm animal types: -2 per missing type. -/
def penaltyMissingAnimals (ac : AnimalCounts) : Nat :=
  ac.missingFarmTypes * 2

/-- Points from grain: 1/2 Gold per grain, rounded up. -/
def scoreGrain (totalGrain : Nat) : Nat :=
  (totalGrain + 1) / 2

/-- Points from vegetables: 1 Gold per vegetable. -/
def scoreVegetables (totalVegs : Nat) : Nat :=
  totalVegs

/-- Points from rubies: 1 Gold per ruby. -/
def scoreRubies (rubies : Nat) : Nat :=
  rubies

/-- Points from dwarfs: 1 Gold per dwarf in play. -/
def scoreDwarfs (numDwarfs : Nat) : Nat :=
  numDwarfs

/-- Penalty for unused spaces: -1 Gold per unused space. -/
def penaltyUnusedSpaces (unused : Nat) : Nat :=
  unused

/-- Points from furnishing tiles (printed value). -/
def scoreFurnishings (furnishings : List FurnishingTile) : Nat :=
  furnishings.foldl (fun acc f => acc + f.points) 0

/-- Bonus points from parlors, storages, chambers. -/
def scoreBonuses (furnishings : List FurnishingTile) : Nat :=
  furnishings.foldl (fun acc f => acc + f.bonusPoints) 0

/-- Points from pastures: 2 per small, 4 per large. -/
def scorePastures (small large : Nat) : Nat :=
  small * 2 + large * 4

/-- Points from mines: 3 per ore mine, 4 per ruby mine. -/
def scoreMines (oreMines rubyMines : Nat) : Nat :=
  oreMines * 3 + rubyMines * 4

/-- Points from gold coins. -/
def scoreGold (gold : Nat) : Nat :=
  gold

/-- Penalty from begging markers: -3 per marker. -/
def penaltyBegging (markers : Nat) : Nat :=
  markers * 3

/-- Complete scoring breakdown for a player. -/
structure ScoreBreakdown where
  animals : Nat
  missingAnimalPenalty : Nat
  grain : Nat
  vegetables : Nat
  rubies : Nat
  dwarfs : Nat
  unusedSpacePenalty : Nat
  furnishings : Nat
  bonuses : Nat
  pastures : Nat
  mines : Nat
  gold : Nat
  beggingPenalty : Nat
  deriving Repr

/-- Net score from a breakdown (positives minus negatives). -/
def ScoreBreakdown.netScore (sb : ScoreBreakdown) : Int :=
  (sb.animals + sb.grain + sb.vegetables + sb.rubies + sb.dwarfs +
   sb.furnishings + sb.bonuses + sb.pastures + sb.mines + sb.gold : Int) -
  (sb.missingAnimalPenalty + sb.unusedSpacePenalty + sb.beggingPenalty : Int)

/-- Compute the full score breakdown for a player state. -/
def computeScore (ps : PlayerState) : ScoreBreakdown :=
  { animals := scoreAnimals ps.animals
  , missingAnimalPenalty := penaltyMissingAnimals ps.animals
  , grain := scoreGrain ps.totalGrain
  , vegetables := scoreVegetables ps.totalVegetables
  , rubies := scoreRubies ps.supply.rubies
  , dwarfs := scoreDwarfs ps.numDwarfs
  , unusedSpacePenalty := penaltyUnusedSpaces ps.unusedSpaces
  , furnishings := scoreFurnishings ps.furnishings
  , bonuses := scoreBonuses ps.furnishings
  , pastures := scorePastures ps.smallPastures ps.largePastures
  , mines := scoreMines ps.oreMines ps.rubyMines
  , gold := scoreGold ps.supply.gold
  , beggingPenalty := penaltyBegging ps.beggingMarkers
  }

end Caverna
