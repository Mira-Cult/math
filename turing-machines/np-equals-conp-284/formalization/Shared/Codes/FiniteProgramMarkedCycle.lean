import Shared.Codes.FiniteProgramNoZero
import Shared.Codes.FiniteProgramTapeEquiv

/-! Exact entry-state trace for one concrete tagged serializer cycle. The
only marked visit during the cycle is its first state-zero transition. This
is a finite-program result; the source-row trace bridge is separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Codes.FiniteProgramMarkedCycle

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical cost)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

def observed (p : Program) (c : Config) : Nat → List Bool
  | 0 => []
  | n+1 => observed p c n ++
      match run p c n with
      | some (.inr d) => if d.1 = 0 then [d.2.2.1] else []
      | _ => []

theorem none_stable (p : Program) (c : Config) {m n : Nat} (hm : m ≤ n)
    (h : run p c m = none) : run p c n = none := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [run_add,h]
  induction d with
  | zero => rfl
  | succ d ih => simp [Function.iterate_succ_apply,ih,advance]

/-- A later live configuration guarantees every earlier status was live. -/
theorem live_prefix (p : Program) (c last : Config) (n i : Nat) (hi : i ≤ n)
    (hfinal : run p c n = some (.inr last)) : ∃ d, run p c i = some (.inr d) := by
  cases hr : run p c i with
  | none =>
    have h := none_stable p c hi hr
    rw [h] at hfinal
    contradiction
  | some v => cases v with
    | inl b =>
      have h := run_result_stable p c hi hr
      rw [h] at hfinal
      cases hfinal
    | inr d => exact ⟨d,rfl⟩

/-- Blank-equivalent initial tapes have the same live control state at every
finite time. -/
theorem related_live (p : Program) (c c' d : Config) (i : Nat)
    (hq : c.1 = c'.1) (ht : TapeRel c.2 c'.2)
    (hr : run p c i = some (.inr d)) :
    ∃ d', run p c' i = some (.inr d') ∧ d.1 = d'.1 := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related p c c' hq ht i
  rw [hr] at h
  cases hs : run p c' i with
  | none => simp [hs,StatusRel] at h
  | some v => cases v with
    | inl z => simp [hs,StatusRel] at h
    | inr d' =>
      have he : d.1 = d'.1 ∧ TapeRel d.2 d'.2 := by simpa [hs,StatusRel] using h
      exact ⟨d',rfl,he.1⟩

/-- A cycle from any equivalent prepared tape has no intermediate return to
entry state zero. -/
theorem no_early_related (zero one : List Bool) (b p : Bool) (xs L : List Bool)
    (c d : Config) (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2)
    (i : Nat) (hi : 0 < i) (hlt : i < cost zero one b xs)
    (hr : run (Shared.Codes.FiniteProgramTaggedLoop.program zero one) c i = some (.inr d)) :
    d.1 ≠ 0 := by
  let reference := canonical (p::L) b xs
  obtain ⟨d',hr',he⟩ := related_live _ c reference d i (by simpa [reference,canonical] using hq) ht hr
  have hne := Shared.Codes.FiniteProgramNoZero.tagged_cycle_no_early zero one b false p xs L i hi hlt d' (by
    simpa [reference,canonical] using hr')
  simpa [he] using hne

/-- On every positive prefix ending no later than one completed cycle, the
entry-state observation is exactly the initial source bit. -/
theorem observed_cycle (zero one : List Bool) (b p : Bool) (xs L : List Bool)
    (c : Config) (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2)
    (i : Nat) (hi : 0 < i) (hle : i ≤ cost zero one b xs) :
    observed (Shared.Codes.FiniteProgramTaggedLoop.program zero one) c i = [b] := by
  let program := Shared.Codes.FiniteProgramTaggedLoop.program zero one
  obtain ⟨last,hfinal,_,_⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycle_related zero one b p xs L c hq ht
  have hhead : c.2.2.1 = b := by
    have h := Shared.Codes.FiniteProgramTapeEquiv.tape_head ht
    simpa [canonical,tapeAt] using h
  have hfirst : observed program c 1 = [b] := by simp [observed,hq,hhead]
  induction i with
  | zero => omega
  | succ i ih =>
    cases i with
    | zero => exact hfirst
    | succ j =>
      have hi' : 0 < j+1 := by omega
      have hle' : j+1 ≤ cost zero one b xs := by omega
      have hbefore : j+1 < cost zero one b xs := by omega
      obtain ⟨d,hd⟩ := live_prefix program c last _ (j+1) hle' hfinal
      have hne := no_early_related zero one b p xs L c d hq ht (j+1) hi' hbefore hd
      change observed program c (j+1) ++
        (match run program c (j+1) with
          | some (.inr e) => if e.1 = 0 then [e.2.2.1] else []
          | _ => []) = [b]
      rw [ih hi' hle',hd]
      simp [hne]

end Shared.Codes.FiniteProgramMarkedCycle
