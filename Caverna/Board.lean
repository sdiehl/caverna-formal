/-
  Caverna.Board -- Home board geometry
  =====================================

  Models the 4x3 Forest + 4x3 Mountain home board layout with adjacency
  constraints, placement rules, water source and wild boar preserve
  locations, and the overhang mechanic (Office Room).

  The board is 4 columns x 3 rows on each side (Forest = left, Mountain = right).
  Coordinates use (col, row) where col is 0-3 and row is 0-2.

  Key placement rules:
  - Cave entrance is at Mountain col=0
  - First Meadow/Field twin tile must be placed in front of cave entrance
  - Mountain tiles must be adjacent to existing cave system
  - Twin tiles must be placed on horizontally or vertically adjacent spaces
  - Ore Mine twin tile must cover 2 ordinary adjacent Tunnels
  - Large pasture covers 2 adjacent Meadows
-/

import Caverna.Types
import Caverna.Furnishings

namespace Caverna

-- ============================================================
-- Board coordinates
-- ============================================================

/-- A position on the 4x3 grid. col in [0,3], row in [0,2]. -/
structure Pos where
  col : Fin 4
  row : Fin 3
  deriving Repr, DecidableEq, BEq

/-- Are two positions horizontally or vertically adjacent? -/
def Pos.adjacent (a b : Pos) : Bool :=
  (a.col == b.col && (a.row.val + 1 == b.row.val || b.row.val + 1 == a.row.val)) ||
  (a.row == b.row && (a.col.val + 1 == b.col.val || b.col.val + 1 == a.col.val))

-- ============================================================
-- Mountain board state (right half)
-- ============================================================

/-- State of a mountain space on the home board. -/
inductive MtnCell where
  | empty            -- unexcavated rock
  | cavern           -- excavated, can be furnished
  | tunnel           -- ordinary tunnel
  | deepTunnel       -- deep tunnel (from ore mine construction)
  | oreMine          -- ore mine (covers this + adjacent tunnel)
  | rubyMine         -- ruby mine (on a tunnel)
  | furnished (fid : FurnishingId) -- furnished cavern
  deriving Repr, DecidableEq, BEq

/-- The 4x3 mountain grid, stored as a list of 12 cells. -/
structure MountainBoard where
  cells : List MtnCell
  h_size : cells.length = 12
  deriving Repr

/-- Initial mountain board: entry-level dwelling at idx 0, empty cavern at idx 1,
    rest is empty rock. -/
def initialMountainBoard : MountainBoard where
  cells := [.furnished .dwelling, .cavern] ++ List.replicate 10 .empty
  h_size := by native_decide

-- ============================================================
-- Forest board state (left half)
-- ============================================================

/-- State of a forest space on the home board. -/
inductive ForCell where
  | forest              -- untouched forest
  | forestStable        -- stable on uncleared forest (holds 1 wild boar)
  | meadow              -- cleared, unfenced
  | meadowStable        -- meadow + stable
  | field (crop : Option CropType) (tokens : Nat)  -- plowed field
  | smallPasture        -- fenced single meadow
  | smallPastureStable  -- small pasture + stable
  | largePastureHalf    -- half of a large pasture
  | largePastureHalfStable  -- large pasture half + stable
  deriving Repr, DecidableEq, BEq

/-- The 4x3 forest grid, stored as a list of 12 cells. -/
structure ForestBoard where
  cells : List ForCell
  h_size : cells.length = 12
  deriving Repr

/-- Initial forest board: all forest. -/
def initialForestBoard : ForestBoard where
  cells := List.replicate 12 .forest
  h_size := by native_decide

-- ============================================================
-- Water source and wild boar preserve locations
-- ============================================================

/-- Food gained from covering a water source at a given index. -/
def waterSourceFood (idx : Nat) : Nat :=
  if idx == 8 then 1       -- position (2,0) = index 2 in row-major
  else if idx == 11 then 2  -- position (3,2) = index 11
  else 0

-- ============================================================
-- Home board: combined forest + mountain
-- ============================================================

/-- Complete home board for one player. -/
structure HomeBoard where
  forest : ForestBoard
  mountain : MountainBoard
  stables : Nat := 0        -- total stables placed (max 3)
  deriving Repr

/-- Initial home board at game start. -/
def initialHomeBoard : HomeBoard :=
  { forest := initialForestBoard
  , mountain := initialMountainBoard
  , stables := 0
  }

-- ============================================================
-- Board queries
-- ============================================================

/-- Is a mountain cell "occupied" (part of the cave system)? -/
def MtnCell.isOccupied : MtnCell -> Bool
  | .empty => false
  | _ => true

/-- Is a forest cell "developed" (not raw forest)? -/
def ForCell.isDeveloped : ForCell -> Bool
  | .forest => false
  | _ => true

/-- Count of unused (undeveloped) spaces on a home board. -/
def HomeBoard.unusedSpaces (hb : HomeBoard) : Nat :=
  let mtnUnused := hb.mountain.cells.filter (fun c => !c.isOccupied) |>.length
  let forUnused := hb.forest.cells.filter (fun c => !c.isDeveloped) |>.length
  mtnUnused + forUnused

/-- Count of empty caverns available for furnishing. -/
def HomeBoard.emptyCaverns (hb : HomeBoard) : Nat :=
  hb.mountain.cells.filter (fun c =>
    match c with | .cavern => true | _ => false) |>.length

/-- Count of ordinary tunnels (for ore mine construction). -/
def HomeBoard.ordinaryTunnels (hb : HomeBoard) : Nat :=
  hb.mountain.cells.filter (fun c =>
    match c with | .tunnel => true | _ => false) |>.length

/-- Count of meadows (for pasture construction). -/
def HomeBoard.meadowCount (hb : HomeBoard) : Nat :=
  hb.forest.cells.filter (fun c =>
    match c with | .meadow => true | .meadowStable => true | _ => false) |>.length

/-- Count of fields. -/
def HomeBoard.fieldCount (hb : HomeBoard) : Nat :=
  hb.forest.cells.filter (fun c =>
    match c with | .field _ _ => true | _ => false) |>.length

/-- Count of furnishing tiles placed. -/
def HomeBoard.furnishingCount (hb : HomeBoard) : Nat :=
  hb.mountain.cells.filter (fun c =>
    match c with | .furnished _ => true | _ => false) |>.length

/-- Count of ore mines. -/
def HomeBoard.oreMineCount (hb : HomeBoard) : Nat :=
  hb.mountain.cells.filter (fun c =>
    match c with | .oreMine => true | _ => false) |>.length

/-- Count of ruby mines. -/
def HomeBoard.rubyMineCount (hb : HomeBoard) : Nat :=
  hb.mountain.cells.filter (fun c =>
    match c with | .rubyMine => true | _ => false) |>.length

-- ============================================================
-- Overhang mechanic (Office Room)
-- ============================================================

/-- The Office Room allows twin tiles to "overhang" the 4x3 grid.
    Each overhanging twin tile gives +2 gold points at game end. -/
structure OverhangState where
  count : Nat := 0       -- number of overhanging twin tiles
  goldBonus : Nat := 0   -- 2 gold per overhang
  deriving Repr, DecidableEq, BEq

end Caverna
