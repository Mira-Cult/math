import Shared.PNP.Record285.PhysicalSweeps
import Shared.PNP.Record285.ArtifactEndpoint

/-! Row-bound productive sweeps occurring in the literal initialization.
These contracts apply to any finite tape satisfying their displayed patterns;
they do not by themselves establish a complete source-entry configuration. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.InitializationSweeps
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps

structure PairSpec where
  q : Fin 285
  p : Fin 285
  read : Bool
  firstWrite : Bool
  secondWrite : Bool

def digit (s : PairSpec) : Nat := 2*bitVal s.firstWrite+bitVal s.secondWrite

inductive LeftPair where
  | scan110 | shift48 | scan51
  deriving DecidableEq

def leftSpec : LeftPair → PairSpec
  | .scan110 => ⟨⟨110,by decide⟩,⟨111,by decide⟩,false,false,true⟩
  | .shift48 => ⟨⟨48,by decide⟩,⟨49,by decide⟩,false,true,false⟩
  | .scan51 => ⟨⟨51,by decide⟩,⟨52,by decide⟩,false,false,true⟩

inductive RightPair where
  | boot6 | shift14 | scan46
  deriving DecidableEq

def rightSpec : RightPair → PairSpec
  | .boot6 => ⟨⟨6,by decide⟩,⟨7,by decide⟩,true,true,false⟩
  | .shift14 => ⟨⟨14,by decide⟩,⟨50,by decide⟩,false,true,false⟩
  | .scan46 => ⟨⟨46,by decide⟩,⟨47,by decide⟩,false,false,true⟩

theorem left_rows (kind : LeftPair) :
    let s := leftSpec kind
    Record285.machine.table.row s.q s.read = ⟨s.firstWrite,.left,s.p,false⟩ ∧
    Record285.machine.table.row s.p (!s.read) = ⟨s.secondWrite,.left,s.q,false⟩ := by
  cases kind <;> constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem right_rows (kind : RightPair) :
    let s := rightSpec kind
    Record285.machine.table.row s.q s.read = ⟨s.firstWrite,.right,s.p,false⟩ ∧
    Record285.machine.table.row s.p (!s.read) = ⟨s.secondWrite,.right,s.q,false⟩ := by
  cases kind <;> constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

/-- The three selected left-moving row pairs act correctly on every matching
finite tape; the time is positive and the entire segment is event-free. -/
theorem left_sweep (kind : LeftPair) (k : Nat) (last : Bool) (tail right : Nat) (head : Int) :
    let s := leftSpec kind
    silent Record285.machine (2*(k+1)) ⟨s.q,head,pairPattern s.read k last tail,s.read,right⟩ =
      some ⟨s.q,head-2*(k+1),tail,last,push (k+1) (digit s) right⟩ := by
  let s := leftSpec kind
  have hrows := left_rows kind
  apply pair_sweep_left Record285.machine s.q s.read (digit s)
  intro head left right hlow
  simpa only [digit,Nat.add_assoc] using
    pair_left Record285.machine s.q s.p s.read s.firstWrite s.secondWrite
      hrows.1 hrows.2 head left right hlow

/-- Corresponding right-moving literal row pairs. -/
theorem right_sweep (kind : RightPair) (k : Nat) (last : Bool) (tail left : Nat) (head : Int) :
    let s := rightSpec kind
    silent Record285.machine (2*(k+1)) ⟨s.q,head,left,s.read,pairPattern s.read k last tail⟩ =
      some ⟨s.q,head+2*(k+1),push (k+1) (digit s) left,last,tail⟩ := by
  let s := rightSpec kind
  have hrows := right_rows kind
  apply pair_sweep_right Record285.machine s.q s.read (digit s)
  intro head left right hlow
  simpa only [digit,Nat.add_assoc] using
    pair_right Record285.machine s.q s.p s.read s.firstWrite s.secondWrite
      hrows.1 hrows.2 head left right hlow

structure RunSpec where
  q : Fin 285
  read : Bool
  write : Bool

inductive LeftRun where
  | clear1 | shift48 | scan51 | scan110 | scan119
  deriving DecidableEq

def leftRunSpec : LeftRun → RunSpec
  | .clear1 => ⟨⟨1,by decide⟩,true,false⟩
  | .shift48 => ⟨⟨48,by decide⟩,true,true⟩
  | .scan51 => ⟨⟨51,by decide⟩,true,true⟩
  | .scan110 => ⟨⟨110,by decide⟩,true,true⟩
  | .scan119 => ⟨⟨119,by decide⟩,false,false⟩

inductive RightRun where
  | fill10 | scan11 | scan12 | scan14 | scan15 | scan16 | scan46
  | scan55 | erase56 | scan109
  deriving DecidableEq

def rightRunSpec : RightRun → RunSpec
  | .fill10 => ⟨⟨10,by decide⟩,false,true⟩
  | .scan11 => ⟨⟨11,by decide⟩,true,true⟩
  | .scan12 => ⟨⟨12,by decide⟩,true,true⟩
  | .scan14 => ⟨⟨14,by decide⟩,true,true⟩
  | .scan15 => ⟨⟨15,by decide⟩,true,true⟩
  | .scan16 => ⟨⟨16,by decide⟩,true,true⟩
  | .scan46 => ⟨⟨46,by decide⟩,true,true⟩
  | .scan55 => ⟨⟨55,by decide⟩,false,false⟩
  | .erase56 => ⟨⟨56,by decide⟩,true,false⟩
  | .scan109 => ⟨⟨109,by decide⟩,false,false⟩

theorem left_run_row (kind : LeftRun) :
    let s := leftRunSpec kind
    Record285.machine.table.row s.q s.read = ⟨s.write,.left,s.q,false⟩ := by
  cases kind <;> dsimp only [leftRunSpec] <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem right_run_row (kind : RightRun) :
    let s := rightRunSpec kind
    Record285.machine.table.row s.q s.read = ⟨s.write,.right,s.q,false⟩ := by
  cases kind <;> dsimp only [rightRunSpec] <;> rw [ArtifactEndpoint.literal_rows] <;> decide

/-- Literal left-going single-state runs with exact physical cost and tape. -/
theorem left_run (kind : LeftRun) (k : Nat) (last : Bool) (tail right : Nat) (head : Int) :
    let s := leftRunSpec kind
    silent Record285.machine (k+1) ⟨s.q,head,runPattern s.read k last tail,s.read,right⟩ =
      some ⟨s.q,head-(k+1),tail,last,pushBit (k+1) s.write right⟩ :=
  run_sweep_left Record285.machine _ _ _ (left_run_row kind) k last tail right head

/-- Literal right-going single-state runs with exact physical cost and tape. -/
theorem right_run (kind : RightRun) (k : Nat) (last : Bool) (tail left : Nat) (head : Int) :
    let s := rightRunSpec kind
    silent Record285.machine (k+1) ⟨s.q,head,left,s.read,runPattern s.read k last tail⟩ =
      some ⟨s.q,head+(k+1),pushBit (k+1) s.write left,last,tail⟩ :=
  run_sweep_right Record285.machine _ _ _ (right_run_row kind) k last tail left head

end Shared.PNP.Record285.InitializationSweeps
