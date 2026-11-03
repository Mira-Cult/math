import Shared.PNP.Record285.IncrementCleanup

/-! Generic literal redispatch: a detector-safe control word and its forward
row path suffice, for arbitrary lengths and arbitrary full-tape tails. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GenericDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.SymbolicDispatch

/-- Consecutive-zero detector control in the literal table. -/
def detectorState : Nat → Fin 285
  | 0 => ⟨110,by decide⟩ | 1 => ⟨111,by decide⟩
  | 2 => ⟨112,by decide⟩ | 3 => ⟨113,by decide⟩
  | 4 => ⟨114,by decide⟩ | _ => ⟨110,by decide⟩

def detectorNext (d : Nat) (b : Bool) : Option Nat :=
  if b then some 0 else if d < 4 then some (d+1) else none

def detectorRun : Nat → List Bool → Option Nat
  | d,[] => some d
  | d,b::bs => (detectorNext d b).bind (fun next => detectorRun next bs)

theorem detector_bound (d d' : Nat) (b : Bool) (hd : d < 5)
    (h : detectorNext d b = some d') : d' < 5 := by
  cases b <;> simp only [detectorNext,Bool.false_eq_true,if_false,if_true] at h
  · split at h <;> simp_all <;> omega
  · simp only [Option.some.injEq] at h; omega

theorem detector_row (d d' : Nat) (b : Bool) (hd : d < 5)
    (h : detectorNext d b = some d') :
    NumericTables.target.table.row (detectorState d) b = ⟨b,.left,detectorState d',false⟩ := by
  have hs : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [detectorNext] at h <;> subst d' <;> decide

theorem run_add (a b : Nat) (c : Config) :
    run (a+b) c = (run a c).bind (run b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    simp only [Nat.succ_add,run]
    cases h : SymbolicDispatch.step c <;> simp [ih]

/-- A symbolic head scans `word` to its left and then reaches `last`. -/
def leftWord (q : Fin 285) (head : Int) (word : List Bool) (last : Bool)
    (left right : List Bool) : Config :=
  match word with
  | [] => ⟨q,head,left,last,right⟩
  | b::bs => ⟨q,head,bs++last::left,b,right⟩

theorem detector_scan (word : List Bool) (d d' : Nat) (hd : d < 5)
    (hok : detectorRun d word = some d') (head : Int) (last : Bool)
    (left right : List Bool) :
    run word.length (leftWord (detectorState d) head word last left right) =
      some ⟨detectorState d',head-word.length,left,last,word.reverse++right⟩ := by
  induction word generalizing d head right with
  | nil =>
    simp only [detectorRun,Option.some.injEq] at hok
    subst d'
    simp [leftWord,run]
  | cons b bs ih =>
    simp only [detectorRun] at hok
    cases hn : detectorNext d b with
    | none => simp [hn] at hok
    | some next =>
      simp only [hn,Option.bind_some] at hok
      have hnext := detector_bound d next b hd hn
      have hrow := detector_row d next b hd hn
      have hstep : SymbolicDispatch.step (leftWord (detectorState d) head (b::bs) last left right) =
          some (leftWord (detectorState next) (head-1) bs last left (b::right)) := by
        cases bs <;> simp [leftWord,SymbolicDispatch.step,hrow]
      simp only [List.length_cons,run,hstep,Option.bind_some]
      have hh := ih next hnext hok (head-1) (b::right)
      have hp : head-1-(bs.length:Int) = head-((bs.length:Int)+1) := by omega
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,Int.natCast_succ,hp] using hh

/-- A forward route follows only literal right-moving, tape-preserving,
unmarked transitions. It is an executable finite check on the control bits. -/
def route : Fin 285 → List Bool → Option (Fin 285)
  | q,[] => some q
  | q,b::bs =>
    let row := NumericTables.target.table.row q b
    if row.write = b ∧ row.move = .right ∧ row.beep = false then
      route row.next bs
    else none

/-- A symbolic head scans `word` to its right and then reaches `last`. -/
def rightWord (q : Fin 285) (head : Int) (word : List Bool) (last : Bool)
    (left right : List Bool) : Config :=
  match word with
  | [] => ⟨q,head,left,last,right⟩
  | b::bs => ⟨q,head,left,b,bs++last::right⟩

theorem route_scan (word : List Bool) (q q' : Fin 285)
    (hok : route q word = some q') (head : Int) (last : Bool)
    (left right : List Bool) :
    run word.length (rightWord q head word last left right) =
      some ⟨q',head+word.length,word.reverse++left,last,right⟩ := by
  induction word generalizing q head left with
  | nil =>
    simp only [route,Option.some.injEq] at hok
    subst q'
    simp [rightWord,run]
  | cons b bs ih =>
    simp only [route] at hok
    split at hok
    next hrow =>
      obtain ⟨hw,hm,hb⟩ := hrow
      have hstep : SymbolicDispatch.step (rightWord q head (b::bs) last left right) =
          some (rightWord (NumericTables.target.table.row q b).next (head+1) bs last (b::left) right) := by
        cases bs <;> simp [rightWord,SymbolicDispatch.step,hw,hm,hb]
      simp only [List.length_cons,run,hstep,Option.bind_some]
      have hh := ih (NumericTables.target.table.row q b).next hok (head+1) (b::left)
      have hp : head+1+(bs.length:Int) = head+((bs.length:Int)+1) := by omega
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,Int.natCast_succ,hp] using hh
    next hrow => simp at hok

def rootScan : Fin 285 := ⟨109,by decide⟩
def rootFirst : Fin 285 := ⟨115,by decide⟩
def rootSecond : Fin 285 := ⟨116,by decide⟩
def treeRoot : Fin 285 := ⟨284,by decide⟩

theorem detector_zero0 : NumericTables.target.table.row (detectorState 0) false =
    ⟨false,.left,detectorState 1,false⟩ := by decide
theorem detector_zero1 : NumericTables.target.table.row (detectorState 1) false =
    ⟨false,.left,detectorState 2,false⟩ := by decide
theorem detector_zero2 : NumericTables.target.table.row (detectorState 2) false =
    ⟨false,.left,detectorState 3,false⟩ := by decide
theorem detector_zero3 : NumericTables.target.table.row (detectorState 3) false =
    ⟨false,.left,detectorState 4,false⟩ := by decide
theorem detector_zero4 : NumericTables.target.table.row (detectorState 4) false =
    ⟨false,.left,rootScan,false⟩ := by decide
theorem root_scan_zero : NumericTables.target.table.row rootScan false =
    ⟨false,.right,rootScan,false⟩ := by decide
theorem root_scan_one : NumericTables.target.table.row rootScan true =
    ⟨true,.right,rootFirst,false⟩ := by decide
theorem root_first_one : NumericTables.target.table.row rootFirst true =
    ⟨true,.right,rootSecond,false⟩ := by decide
theorem root_second_zero : NumericTables.target.table.row rootSecond false =
    ⟨false,.right,treeRoot,false⟩ := by decide

/-- The fixed five-zero detector and `110` root traversal, with an arbitrary
following word. Six zeros are available before the root. -/
theorem reset_root (code : List Bool) (head : Int) :
    run 14 ⟨detectorState 0,head,List.replicate 5 false,false,
      [true,true,false]++code++[true,false]⟩ =
      some (rightWord treeRoot (head+4) code true
        ([false,true,true]++List.replicate 6 false) [false]) := by
  cases code <;>
    simp [run,SymbolicDispatch.step,rightWord,detector_zero0,detector_zero1,detector_zero2,
      detector_zero3,detector_zero4,root_scan_zero,root_scan_one,root_first_one,root_second_zero] <;>
    omega

end Shared.PNP.Record285.GenericDispatch
