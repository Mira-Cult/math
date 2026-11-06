import Shared.Beeping.NPcoNP.Source284SquareLoopBase

/-! Fixed finite control for repeated token growth with an exhaustion exit.
The final writes and moves are unchanged when the two reference sink rows
are redirected. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SquareLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284SquareLoopBase (base)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=41 then let r := base q b; ⟨r.write,r.turn,some 88⟩
  else if q=86 then let r := base q b; ⟨r.write,r.turn,some 0⟩
  else if q<88 then base q b
  else shiftRow 88 (continuation (q-88) b)

theorem row41 (b : Bool) : base 41 b = ⟨b,true,some 44⟩ := by cases b <;> rfl
theorem row86 (b : Bool) : base 86 b = ⟨b,true,some 87⟩ := by cases b <;> rfl
theorem row44 (b : Bool) : base 44 b = ⟨b,false,some 44⟩ := by cases b <;> rfl
theorem row87 (b : Bool) : base 87 b = ⟨b,false,some 87⟩ := by cases b <;> rfl

def sinkIndex (q : Nat) : Nat := if q=41 then 44 else 87

theorem sink_step (c : Config) (q : Nat) (hq : q=44 ∨ q=87) (hc : c.state=some q) :
    (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at hc
    subst state
    rcases hq with rfl | rfl <;> simp [step,row44,row87]

theorem sink_run (c : Config) (q : Nat) (hq : q=44 ∨ q=87) (hc : c.state=some q) (fuel : Nat) :
    (run base c fuel).state = some q := by
  induction fuel with
  | zero => exact hc
  | succ fuel ih => exact sink_step _ q hq ih

theorem terminal_step (c : Config) (q : Nat) (hq : q=41 ∨ q=86) (hc : c.state=some q) :
    (step base c).state = some (sinkIndex q) := by
  cases c with
  | mk left right state =>
    simp only at hc
    subst state
    rcases hq with rfl | rfl <;> simp [step,row41,row86,sinkIndex]

theorem avoid_before (c : Config) (limit final : Nat) (hfinal : final=41 ∨ final=86)
    (hend : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, q=41 ∨ q=86 → (run base c t).state ≠ some q := by
  intro t ht q hq hstate
  have hs : (run base c (t+1)).state = some (sinkIndex q) := by
    simp only [run]
    exact terminal_step _ q hq hstate
  have hsi : sinkIndex q=44 ∨ sinkIndex q=87 := by rcases hq with rfl | rfl <;> simp [sinkIndex]
  have h := sink_run (run base c (t+1)) (sinkIndex q) hsi hs (limit-(t+1))
  rw [← Source284PayloadPop.run_add] at h
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hend] at h
  have hh : sinkIndex q=final := Option.some.inj h.symm
  rcases hq with rfl | rfl <;> rcases hfinal with rfl | rfl <;> simp [sinkIndex] at hh

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (hv : Valid 88 c) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, q=41 ∨ q=86 → (run base c t).state ≠ some q) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, q=41 ∨ q=86 → (run base c t).state ≠ some q := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    have hvalid := valid_run 88 base c Source284SquareLoopBase.closed hv fuel
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq : q < 88 := hvalid q (by simp [hc])
        have h41 : q ≠ 41 := by
          intro he; subst q; exact hrows fuel (by omega) 41 (Or.inl rfl) (by simp [hc])
        have h86 : q ≠ 86 := by
          intro he; subst q; exact hrows fuel (by omega) 86 (Or.inr rfl) (by simp [hc])
        simp [step,table,h41,h86,hq]

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (88+q) b = shiftRow 88 (continuation q b) := by
  simp [table,show 88+q ≠ 41 by omega,show 88+q ≠ 86 by omega,show ¬ 88+q < 88 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 88 c) = shiftConfig 88 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 88 c) fuel = shiftConfig 88 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem redirect_growth (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨2*right,left,some 86⟩ = ⟨left,2*right,some 0⟩ := by
  simp [step,table,row86,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem redirect_exhaust (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨2*right,left,some 41⟩ = ⟨left,2*right,some 88⟩ := by
  simp [step,table,row41,bit,Nat.testBit_zero] <;> split_ifs <;> omega

/-- One available outer token triggers a finite growth round and restarts the
same marker table, with no proof-supplied runtime decision. -/
theorem growth (continuation : Nat → Bool → Row) (m k n : Nat) (rest w : List Bool)
    (certificate higher : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*flipped w (counter n higher),some 0⟩ (Source284NestedGrowthStep.cost m k n w.length) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      2*flipped w (counter (n+m) (halves m higher)),some 0⟩ := by
  let c : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ false::rest) certificate),2*flipped w (counter n higher),some 0⟩
  let limit := Source284NestedGrowthStep.cost m k n w.length-1
  have hv : Valid 88 c := by intro q hq; simp [c] at hq; subst q; omega
  have hp := Source284SquareLoopBase.growth_pre m k n rest w certificate higher
  change run base c limit = _ at hp
  have hf : (run base c limit).state=some 86 := by rw [hp]
  have he := run_agree continuation c hv limit (avoid_before c limit 86 (Or.inr rfl) hf)
  have hc : 0 < Source284NestedGrowthStep.cost m k n w.length := by
    simp [Source284NestedGrowthStep.cost] <;> omega
  have ht : Source284NestedGrowthStep.cost m k n w.length = limit+1 := by dsimp [limit]; omega
  change run (table continuation) c _ = _
  rw [ht,run,he,hp,redirect_growth]

/-- With every outer token marked, the fixed table enters its caller's
continuation, preserving both blocks and the scratch stream. -/
theorem exhausted_then (continuation : Nat → Bool → Row) (m k certificate stream fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
      (4*m+4*k+14+fuel) =
    shiftConfig 88 (run continuation
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,some 0⟩ fuel) := by
  let c : Config := ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
  let limit := 4*m+4*k+13
  have hv : Valid 88 c := by intro q hq; simp [c] at hq; subst q; omega
  have hp := Source284SquareLoopBase.exhausted_pre m k certificate stream
  change run base c limit = _ at hp
  have hf : (run base c limit).state=some 41 := by rw [hp]
  have he := run_agree continuation c hv limit (avoid_before c limit 41 (Or.inl rfl) hf)
  have ht : 4*m+4*k+14+fuel = (limit+1)+fuel := by dsimp [limit] <;> omega
  change run (table continuation) c _ = _
  rw [ht,Source284ScratchScanner.run_add,run,he,hp,redirect_exhaust]
  simpa [shiftConfig] using (relocated_run continuation
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,some 0⟩ fuel)

end Shared.Beeping.NPcoNP.Source284SquareLoop
