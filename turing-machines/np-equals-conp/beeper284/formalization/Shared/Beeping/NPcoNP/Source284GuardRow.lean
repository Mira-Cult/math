import Shared.Beeping.NPcoNP.Source284SearchSelectTM2
import Shared.Beeping.NPcoNP.Source284EncodedRows
import Shared.ComplexityBridge.TM2ListUnaryLength

/-! An explicit encoded countdown-guard row computed from a finite encoded
original row list and a unary cutoff. Search and lookup are executable; this
file does not claim polynomial time or construct the whole output table. -/
namespace Shared.Beeping.NPcoNP.Source284GuardRow

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284BoundedPairTM2
open Shared.Beeping.NPcoNP.Source284SearchSelectTM2
open Shared.Beeping.NPcoNP.Source284TableCountdown

abbrev Input := (List Bool × EncRows) × (Nat × Bool)

def nTokens (rows : EncRows) : List Bool := TM2ListUnaryLength.unaryLength rows

def budget (cutoff : List Bool) (rows : EncRows) : List Bool := cutoff ++ nTokens rows

def sinkCode (cutoff : List Bool) (rows : EncRows) : Nat :=
  if cutoff.isEmpty then 0 else pairBounded (budget cutoff rows,(cutoff.length,rows.length))

def selection (p : Input) : Result := select ((nTokens p.1.2,p.1.1),p.2.1)

def defaultPair : EncRow × EncRow := ((false,false,false,0),(false,false,false,0))

def selectedPair (p : Input) : EncRow × EncRow :=
  TM2ListLookup.lookup (p.1.2,((selection p).2.2, defaultPair))

def selectedRow (p : Input) : EncRow :=
  if p.2.2 then (selectedPair p).2 else (selectedPair p).1

def nextLive (p : Input) : Bool :=
  TM2BoundedWitnessGuard.guard (p.1.1,(selection p).2.1+1) &&
    TM2BoundedWitnessGuard.guard (nTokens p.1.2,(selectedRow p).2.2.2)

def destination (p : Input) : Nat :=
  if nextLive p then
    pairBounded (budget p.1.1 p.1.2,((selection p).2.1+1,(selectedRow p).2.2.2))
  else sinkCode p.1.1 p.1.2

def sinkRow (cutoff : List Bool) (rows : EncRows) (read : Bool) : EncRow :=
  (read,false,true,sinkCode cutoff rows)

def guardedRow (p : Input) : EncRow :=
  if (selection p).1 then
    let r := selectedRow p
    if r.2.2.1 then (r.1,r.2.1,true,destination p) else (r.1,r.2.1,false,0)
  else sinkRow p.1.1 p.1.2 p.2.2

@[simp] theorem nTokens_length (rows : EncRows) : (nTokens rows).length = rows.length := by
  simp [nTokens, TM2ListUnaryLength.unaryLength]

@[simp] theorem budget_length (cutoff : List Bool) (rows : EncRows) :
    (budget cutoff rows).length = cutoff.length + rows.length := by
  simp [budget]

theorem sinkCode_correct (cutoff : List Bool) (rows : EncRows) :
    sinkCode cutoff rows = Source284TableCountdown.sink rows.length cutoff.length := by
  have hp := pairBounded_correct (budget cutoff rows) cutoff.length rows.length
    (by simp) (by simp)
  cases cutoff with
  | nil => simp [sinkCode, Source284TableCountdown.sink]
  | cons b bs =>
    simp only [List.length_cons] at hp
    simpa [sinkCode, Source284TableCountdown.sink] using hp

end Shared.Beeping.NPcoNP.Source284GuardRow
