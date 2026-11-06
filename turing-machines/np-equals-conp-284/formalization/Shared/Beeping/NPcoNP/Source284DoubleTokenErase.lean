import Shared.Beeping.NPcoNP.Source284NestedErase

/-! Erase two nested unary blocks from the outside inward. A pre-existing
zero block behind them remains contiguous with the newly cleared cells. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284DoubleTokenErase

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284NestedErase.table (Source284NestedReturn.table (Source284UnaryErase.table continuation))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (29+states) (table continuation) := by
  have h1 := Source284UnaryErase.closed states continuation hn hv
  have h2 := Source284NestedReturn.closed (7+states) (Source284UnaryErase.table continuation) (by omega) h1
  have h3 := Source284NestedErase.closed (10+(7+states))
    (Source284NestedReturn.table (Source284UnaryErase.table continuation)) (by omega) h2
  have he : 12+(10+(7+states))=29+states := by omega
  rw [he] at h3
  exact h3

/-- Both temporary blocks become zeros, without changing the underlying
certificate or scratch stream. -/
theorem erase_then (continuation : Nat → Bool → Row) (m : Nat) (outer : List Bool)
    (certificate stream fuel : Nat) :
    run (table continuation) ⟨pairTape (List.replicate m false) (pairTape outer certificate),2*stream,some 0⟩
      (8*m+4*outer.length+18+fuel) =
    shiftConfig 29 (run continuation
      ⟨4^(m+1)*(4^(outer.length+1)*certificate),2*stream,some 0⟩ fuel) := by
  have ht : 8*m+4*outer.length+18+fuel =
      (4*m+4*outer.length+12)+((4*m+6)+fuel) := by omega
  rw [ht]
  unfold table
  rw [Source284NestedErase.erase_then]
  have he := Source284UnaryErase.clear_then continuation (List.replicate m false)
    (4^(outer.length+1)*certificate) stream fuel
  simp only [List.length_replicate] at he
  rw [he,Source284SourceRelocation.shiftConfig_add]

/-- The combined erase is executed by the actual finite numeric encoding. -/
theorem source_erase_then (states : Nat) (continuation : Nat → Bool → Row)
    (m : Nat) (outer : List Bool) (certificate stream fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (29+states) (table continuation) 1)
      (Source284Relative.initial (2*stream) (pairTape (List.replicate m false) (pairTape outer certificate)))
      (8*m+4*outer.length+18+fuel) =
    Source284SourceRelocation.lift 29 (Source284Relative.run (encode states continuation 1)
      ⟨4^(m+1)*(4^(outer.length+1)*certificate),2*stream,active 0⟩ fuel) := by
  let start : Config := ⟨pairTape (List.replicate m false) (pairTape outer certificate),2*stream,some 0⟩
  have hi : Valid (29+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (29+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (8*m+4*outer.length+18+fuel)
  rw [erase_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨4^(m+1)*(4^(outer.length+1)*certificate),2*stream,some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

namespace Fixtures

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨pairTape [] (pairTape [] 3),0,some 0⟩ 18 = ⟨48,0,some 29⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [false] (pairTape [true] 3),0,some 0⟩ 30 = ⟨768,0,some 29⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284DoubleTokenErase
