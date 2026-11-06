import Shared.Beeping.NPcoNP.NativeHalfSelectorScan
import Shared.Beeping.MachineLightCone
import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! A quantitative progress bound for the literal selector.  This proves
only the state-83-to-state-92 scan, not the remaining graph simulation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectorBound
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- If every cell at distance at least `k` is zero, a chain of `m` selector
rows finishes within `k+m` transitions. The tape is unchanged, each step
moves the head left, and the entire segment is silent. -/
theorem chain_progress_bound {m : Nat} {q r : Fin 284} (hc : Chain m q r)
    (t : Int → Bool) (h : Int) (k : Nat)
    (hz : ∀ j : Nat, k ≤ j → t (h-(j : Int)) = false) :
    ∃ n : Nat, m ≤ n ∧ n ≤ k+m ∧
      silentSegment machine (cfg q h t) (cfg r (h-(n : Int)) t) n := by
  induction hc generalizing h k with
  | refl q =>
    refine ⟨0, by omega, by omega, ?_⟩
    simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
  | @cons m q r s row rest ih =>
    obtain ⟨n,hn,hbound,hs⟩ := scan row k h t (hz k (by omega))
    have hz' : ∀ j : Nat, k-n ≤ j →
        t ((h-(n : Int))-(j : Int)) = false := by
      intro j hj
      have hj' : k ≤ n+j := by omega
      have hh : (h-(n : Int))-(j : Int) = h-((n+j : Nat) : Int) := by
        push_cast
        omega
      rw [hh]
      exact hz (n+j) hj'
    obtain ⟨l,hl,hlbound,hs'⟩ := ih (h-(n : Int)) (k-n) hz'
    refine ⟨n+l, by omega, by omega, ?_⟩
    have hseg := segAdd machine _ _ _ n l hs hs'
    have he : h-(n : Int)-(l : Int) = h-((n+l : Nat) : Int) := by
      push_cast
      omega
    simpa [he] using hseg

/-- From state 83, a known zero tail at distance `k` yields a silent,
tape-preserving return to state 92 after between 14 and `k+14` steps. -/
theorem selector_progress_bound (t : Int → Bool) (h : Int) (k : Nat)
    (hz : ∀ j : Nat, k ≤ j → t (h-(j : Int)) = false) :
    ∃ n : Nat, 14 ≤ n ∧ n ≤ k+14 ∧
      silentSegment machine (cfg 83 h t) (cfg 92 (h-(n : Int)) t) n :=
  chain_progress_bound chain83 t h k hz

/-- The bound applies to every reachable state-83 visit for any supplied
left-zero cutoff; reachability of that state is not asserted. -/
theorem reachable_selector_progress_bound (time : Nat)
    (hstate : (machine.system.run time).state=83) (k : Nat)
    (hz : ∀ j : Nat, k ≤ j →
      (machine.system.run time).tape ((machine.system.run time).head-(j : Int))=false) :
    ∃ n : Nat, 14 ≤ n ∧ n ≤ k+14 ∧
      silentSegment machine (machine.system.run time)
        (cfg 92 ((machine.system.run time).head-(n : Int)) (machine.system.run time).tape) n := by
  let c := machine.system.run time
  obtain ⟨n,hn,hb,hs⟩ := selector_progress_bound c.tape c.head k hz
  refine ⟨n,hn,hb,?_⟩
  have hc : c = cfg 83 c.head c.tape := by
    have he : c = cfg c.state c.head c.tape := by cases c; rfl
    have hh : c.state=83 := hstate
    simpa only [hh] using he
  simpa [← hc] using hs

/-- A state-83 visit at blank-start time `time` completes its fourteen
left scans silently within `2*time+15` transitions. This bound follows from
the finite propagation speed of the physical tape; no supplied zero-tail
witness or graph-state hypothesis is needed. -/
theorem reachable_selector_time_bound (time : Nat)
    (hstate : (machine.system.run time).state=83) :
    ∃ n : Nat, 14 ≤ n ∧ n ≤ 2*time+15 ∧
      silentSegment machine (machine.system.run time)
        (cfg 92 ((machine.system.run time).head-(n : Int)) (machine.system.run time).tape) n := by
  have light := machine.run_lightCone time
  have hz : ∀ j : Nat, 2*time+1 ≤ j →
      (machine.system.run time).tape ((machine.system.run time).head-(j : Int))=false := by
    intro j hj
    have hp : (machine.system.run time).head-(j : Int) < machine.startHead-(time : Int) := by
      have hh := light.2.1
      omega
    have hb := light.2.2.1 _ hp
    simpa [machine_starts_zero.2.1] using hb
  obtain ⟨n,hn,hb,hs⟩ := reachable_selector_progress_bound time hstate (2*time+1) hz
  exact ⟨n,hn,by omega,hs⟩

/-- A reachable state-97 scan with a one at or left of its head completes
all three scans through state 93 in at most `6*time+33` silent transitions.
The marker hypothesis remains explicit. -/
theorem reachable_97_to_93_time_bound (time : Nat)
    (hstate : (machine.system.run time).state=97)
    (p : Int) (hp : p ≤ (machine.system.run time).head)
    (hone : (machine.system.run time).tape p=true) :
    ∃ n : Nat, 0<n ∧ n≤6*time+33 ∧
      ∃ e : Config 284, e.state=93 ∧ e.tape=(machine.system.run time).tape ∧
        silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  change p ≤ c.head at hp
  let k := (c.head-p).toNat
  have hk : (k : Int)=c.head-p := Int.toNat_of_nonneg (by omega)
  have hpos : c.head-(k : Int)=p := by omega
  have light := machine.run_lightCone time
  have hpmin : machine.startHead-(time : Int) ≤ p := by
    by_contra hn
    have hb := light.2.2.1 p (by omega)
    have hb' : c.tape p=false := by simpa [c,machine_starts_zero.2.1] using hb
    have ho : c.tape p=true := hone
    rw [ho] at hb'
    contradiction
  have hkbound : k≤2*time := by
    have hh : c.head≤machine.startHead+(time : Int) := light.2.1
    omega
  have hm : c.tape (c.head-(k : Int))=true := by rw [hpos]; exact hone
  obtain ⟨n,hn,hnb,hmark,hs⟩ := scan97_marked k c.head c.tape hm
  have hz : ∀ j : Nat, 2*time+1≤j →
      c.tape ((c.head-(n : Int))-(j : Int))=false := by
    intro j hj
    have hh : c.head≤machine.startHead+(time : Int) := light.2.1
    have hlt : (c.head-(n : Int))-(j : Int)<machine.startHead-(time : Int) := by omega
    have hb := light.2.2.1 _ hlt
    simpa [c,machine_starts_zero.2.1] using hb
  obtain ⟨m,hm14,hmb,ht⟩ := selector_progress_bound c.tape (c.head-(n : Int)) (2*time+1) hz
  have hmark' : c.tape ((c.head-(n : Int)-(m : Int))+((m+1 : Nat) : Int))=true := by
    have he : (c.head-(n : Int)-(m : Int))+((m+1 : Nat) : Int)=c.head-(n : Int)+1 := by
      push_cast
      omega
    rw [he]
    exact hmark
  obtain ⟨l,hl,hlb,hu⟩ := scan92_to_one (m+1) (c.head-(n : Int)-(m : Int)) c.tape hmark'
  let e : Config 284 := cfg 93 (c.head-(n : Int)-(m : Int)+(l : Int)) c.tape
  have hc : c=cfg 97 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hh : c.state=97 := hstate
    simpa only [hh] using he
  refine ⟨n+m+l,by omega,by omega,e,rfl,rfl,?_⟩
  change silentSegment machine c e (n+m+l)
  rw [hc]
  exact segAdd machine _ _ _ (n+m) l (segAdd machine _ _ _ n m hs ht) hu

#print axioms reachable_97_to_93_time_bound
#print axioms reachable_selector_time_bound
#print axioms chain_progress_bound
#print axioms selector_progress_bound
#print axioms reachable_selector_progress_bound
end Shared.Beeping.NPcoNP.NativeHalfSelectorBound
