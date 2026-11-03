import Shared.PNP.Record285.GrammarAnchoredContinue

/-! Exact positive physical durations from the already-verified root-to-root
operation contracts. These are certificates for one action, not upper bounds. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.IncrementReturn (completeCost)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.SymbolicDispatch (pathCost)
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.ControlContinue (peelZeros)

/-- Exact clean zero-marker increment duration. -/
def incTime (code : List Bool) (gap target : Nat) (before fields : List Nat) : Nat :=
  let p := peel code.reverse
  code.length+((2*gap+5)+pathCost code+
    2*(IncrementSelector.cost (gap::before++[target])+IncrementShift.cost fields))+
    (3*p.1+2*gap+9)+(p.2.reverse.length+17)

def decZeroTime (code : List Bool) (gap : Nat) (before : List Nat) : Nat :=
  let p := peel code.reverse
  let q := peel p.2
  code.length+((2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
    (3*(p.1+q.1)+2*gap+12)+(q.2.reverse.length+17))

def decPositiveTime (code : List Bool) (gap k : Nat) (before fields : List Nat) : Nat :=
  let p := peel code.reverse
  let scan := DecrementNonzeroScan.scanCost k fields
  code.length+((2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)+(2+scan)+
    (2+completeCost (foldRuns fields []) k)+(1+completeCost (foldRuns before []) gap)+
    (3*p.1+2*gap+9)+(p.2.reverse.length+17))

def halfZeroTime (code : List Bool) (gap : Nat) (before : List Nat) : Nat :=
  let p := peel code.reverse
  let q := peel p.2
  let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
  let back := 2+(1+completeCost (0::foldRuns before []) gap)
  start+back+(3*(p.1+q.1)+2*gap+12)+(q.2.reverse.length+17)

def halfOneTime (code : List Bool) (gap : Nat) (before fields : List Nat) : Nat :=
  let p := peel code.reverse
  let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
  let back := 1+completeCost (0::foldRuns before []) gap
  start+(4+HalfOne.shiftCost fields)+back+(3*p.1+2*gap+9)+(p.2.reverse.length+17)

def halfEvenTime (code : List Bool) (gap n : Nat) (before fields : List Nat) : Nat :=
  let p := peel code.reverse
  let q := peel p.2
  let carried := fields++List.replicate n 0
  let start := code.length+(2*gap+5)+pathCost code+
    IncrementSelector.cost (gap::before)+2+HalfCycle.cyclesCost n 0 fields
  let finish := 1+HalfEvenShift.shiftCost carried
  let back := 1+completeCost ((n+1)::foldRuns before []) gap
  start+finish+back+(3*(p.1+q.1)+2*gap+12)+(q.2.reverse.length+17)

def halfOddTime (code : List Bool) (gap n : Nat) (before fields : List Nat) : Nat :=
  let p := peel code.reverse
  let carried := fields++List.replicate n 0
  let start := code.length+(2*gap+5)+pathCost code+
    IncrementSelector.cost (gap::before)+2+HalfCycle.cyclesCost n 1 fields
  let finish := 2+DecrementNonzeroScan.scanCost 0 carried+HalfOdd.shiftCost carried+1+HalfOdd.secondCost carried
  let back := 1+completeCost ((n+1)::foldRuns before []) gap
  start+finish+back+(3*p.1+2*gap+9)+(p.2.reverse.length+17)

def breakZeroTime (code pre : List Bool) (gap : Nat) : Nat :=
  let p := peel pre.reverse
  code.length+(3*p.1+2*((gap+2)+1)+5)+(p.2.reverse.length+17)

def breakOneTime (code pre : List Bool) (gap : Nat) : Nat :=
  let p := peel pre.reverse
  let q := peel p.2
  code.length+((p.1+1)+(3*q.1+2*(p.1+(gap+2)+2)+5)+(q.2.reverse.length+17))

def breakTwoTime (code pre : List Bool) (gap : Nat) : Nat :=
  let p := peel pre.reverse
  let q := peel p.2
  let r := peel q.2
  code.length+(p.1+1)+((q.1+1)+(3*r.1+2*(q.1+(p.1+(gap+2)+1)+2)+5)+(r.2.reverse.length+17))

def continueOneTime (code pre : List Bool) : Nat :=
  let p := peelZeros pre.reverse
  code.length+p.1+1+(p.2.reverse.length+17)

def continueTwoTime (code pre : List Bool) : Nat :=
  let p := peelZeros pre.reverse
  let q := peelZeros p.2
  code.length+(p.1+1)+(q.1+1+(q.2.reverse.length+17))

/-- A derivation identifies the precise duration of the verified local action
using the actual finite control word and the complete clean bank. -/
inductive Duration : Edge → List Nat → List Bool → Nat → Nat → Prop
  | inc (before fields : List Nat) (target : Nat) (code : List Bool) (gap : Nat) :
      Duration (.inc before.length) (before++[target]++fields) code gap (incTime code gap target before fields)
  | decZero (before fields : List Nat) (code : List Bool) (gap : Nat) :
      Duration (.dec before.length) (before++[0]++fields) code gap (decZeroTime code gap before)
  | decPositive (before fields : List Nat) (k : Nat) (code : List Bool) (gap : Nat) :
      Duration (.dec before.length) (before++[k+1]++fields) code gap (decPositiveTime code gap k before fields)
  | halfZero (before fields : List Nat) (code : List Bool) (gap : Nat) :
      Duration (.half before.length) (before++[0]++fields) code gap (halfZeroTime code gap before)
  | halfOne (before fields : List Nat) (code : List Bool) (gap : Nat) :
      Duration (.half before.length) (before++[1]++fields) code gap (halfOneTime code gap before fields)
  | halfEven (before fields : List Nat) (n : Nat) (code : List Bool) (gap : Nat) :
      Duration (.half before.length) (before++[2*n+2]++fields) code gap (halfEvenTime code gap n before fields)
  | halfOdd (before fields : List Nat) (n : Nat) (code : List Bool) (gap : Nat) :
      Duration (.half before.length) (before++[2*n+3]++fields) code gap (halfOddTime code gap n before fields)
  | beep (fields : List Nat) (code : List Bool) (gap : Nat) :
      Duration .beep fields code gap (beepDuration false gap)
  | brkZero (fields : List Nat) (code pre : List Bool) (gap : Nat) (hcode : code = pre++[true]) :
      Duration (.brk 0) fields code gap (breakZeroTime code pre gap)
  | brkOne (fields : List Nat) (code pre : List Bool) (gap : Nat) (hcode : code = pre++[true]) :
      Duration (.brk 1) fields code gap (breakOneTime code pre gap)
  | brkTwo (fields : List Nat) (code pre : List Bool) (gap : Nat) (hcode : code = pre++[true]) :
      Duration (.brk 2) fields code gap (breakTwoTime code pre gap)
  | contOne (fields : List Nat) (code pre : List Bool) (gap : Nat) (hcode : code = pre++[true]) :
      Duration (.cont 1) fields code gap (continueOneTime code pre)
  | contTwo (fields : List Nat) (code pre : List Bool) (gap : Nat) (hcode : code = pre++[true]) :
      Duration (.cont 2) fields code gap (continueTwoTime code pre)

end Shared.PNP.Record285.GrammarExact
