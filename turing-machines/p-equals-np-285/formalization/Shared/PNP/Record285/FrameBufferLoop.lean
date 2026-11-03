import Shared.PNP.Record285.FrameBufferLoader
import Mathlib.Tactic.Linarith

/-! Finite, progress-sensitive repetition of the physical raw-frame counter
and tagged-buffer cycle. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.FrameBufferLoop
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.FrameBufferLoader

def cost (gap stored : Nat) : Nat → Nat
  | 0 => 2*gap+7
  | n+1 => 4*gap+2*n+4*stored+23 + cost (gap+2) (stored+1) n

def workLeft (gap : Nat) (stored remaining workspace : List Bool) : List Bool :=
  false::(List.replicate gap false ++ List.replicate remaining.length true ++
    true::false::(tagged stored ++ List.replicate (2*remaining.length) false ++ workspace))

/-- Every payload bit is stored, every required counter mark is consumed,
and the next unread bit and arbitrary workspace suffix are preserved. The
last counter test takes its genuine exhausted-anchor exit. -/
theorem run_loop (gap : Nat) (stored remaining workspace : List Bool) (next : Bool) (rest : List Bool) :
    run program (0,tapeAt (workLeft gap stored remaining workspace) (remaining ++ next::rest))
      (cost gap stored.length remaining.length) =
      some (.inr (15,tapeAt
        (List.replicate (gap+2*remaining.length) false ++
          true::false::(tagged (stored++remaining) ++ workspace)) (false::next::rest))) := by
  induction remaining generalizing gap stored with
  | nil =>
    have h := counter_cycle next false gap (tagged stored ++ workspace) rest
    simpa [workLeft,cost,List.append_assoc] using h
  | cons bit remaining ih =>
    let unread := remaining ++ next::rest
    have hunread : unread.head?.getD false::unread.tail = unread := by
      dsimp [unread]
      cases remaining <;> simp
    have hones : List.replicate (remaining.length+1) true ++ true::false::
        (tagged stored ++ false::false::(List.replicate (2*remaining.length) false ++ workspace)) =
      true::true::List.replicate remaining.length true ++ false::
        (tagged stored ++ false::false::(List.replicate (2*remaining.length) false ++ workspace)) := by
      have h : List.replicate remaining.length true ++ [true] = true::List.replicate remaining.length true := by
        rw [← List.replicate_succ',List.replicate_succ]
      simp only [List.replicate_succ,List.cons_append]
      simpa [List.append_assoc] using congrArg
        (fun z => true::(z ++ false::(tagged stored ++ false::false::
          (List.replicate (2*remaining.length) false ++ workspace)))) h
    have hwork : workLeft gap stored (bit::remaining) workspace =
      false::(List.replicate gap false ++ true::true::List.replicate remaining.length true ++
        false::(tagged stored ++ false::false::(List.replicate (2*remaining.length) false ++ workspace))) := by
      unfold workLeft
      simp only [List.length_cons]
      have hblank : List.replicate (2*(remaining.length+1)) false =
          false::false::List.replicate (2*remaining.length) false := by
        have he : 2*(remaining.length+1) = (2*remaining.length)+2 := by omega
        rw [he]
        simp [List.replicate_succ]
      rw [hblank]
      simp only [List.cons_append,List.append_assoc] at hones ⊢
      rw [hones]
    have hcycle := counter_and_accumulate bit (unread.head?.getD false) gap remaining.length stored
      (List.replicate (2*remaining.length) false ++ workspace) unread.tail
    rw [hunread] at hcycle
    have hnew :
      false::(List.replicate (gap+2) false ++ List.replicate remaining.length true ++
        true::false::(tagged stored ++ bit::true::(List.replicate (2*remaining.length) false ++ workspace))) =
      workLeft (gap+2) (stored++[bit]) remaining workspace := by
      simp [workLeft,tagged_append,List.append_assoc]
    rw [hnew] at hcycle
    dsimp only [unread] at hcycle
    have hc : cost gap stored.length (bit::remaining).length =
        (4*gap+2*remaining.length+4*stored.length+23) +
          cost (gap+2) (stored++[bit]).length remaining.length := by
      simp [cost]
    simp only [List.cons_append] at hcycle ⊢
    rw [hwork,hc,run_continue _ _ _ _ _ hcycle,ih]
    have hlen : gap+2+2*remaining.length = gap+2*(bit::remaining).length := by simp; omega
    rw [hlen]
    simp [List.append_assoc]

/-- A single quadratic bound pays for every counter scan, buffer insertion,
and final exhausted-anchor test. -/
theorem cost_bound (gap stored n : Nat) :
    cost gap stored n ≤ n*(4*gap+12*n+4*stored+30) + 2*gap+4*n+7 := by
  induction n generalizing gap stored with
  | zero => simp [cost]
  | succ n ih =>
    have h := ih (gap+2) (stored+1)
    simp only [cost]
    nlinarith

end Shared.PNP.Record285.FrameBufferLoop
