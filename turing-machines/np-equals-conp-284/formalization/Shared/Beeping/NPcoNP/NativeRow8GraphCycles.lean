import Shared.Beeping.NPcoNP.NativeRow8Cycles

/-! Source-graph events for the finite positive physical iteration. -/
namespace Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Both actual graph transitions use the expected control states and are silent. -/
def CycleGood (bank : Bank 12) : Prop :=
  let first := target.system.step ⟨8,bank⟩
  let second := target.system.step ⟨9,first.1.bank⟩
  first.1.state=9 ∧ second.1.state=8 ∧ first.2=[] ∧ second.2=[]

def CyclesGood : Nat → Bank 12 → Prop
  | 0, _ => True
  | n+1, bank => CycleGood bank ∧ CyclesGood n (cycleBank bank)

/-- The actual graph follows the positive two-step path, with empty event
words, at every cycle up to the supplied finite count. -/
theorem graph_cycles_good (n : Nat) (a b : Nat) (prior : List Nat)
    (v z : Nat) (bank : Bank 12) (hlen : prior.length=8)
    (hgraph : arrayBank bank=(a::b::prior) ++ [v+n,z]) :
    CyclesGood n bank := by
  induction n generalizing b bank with
  | zero => trivial
  | succ n ih =>
    have hgraph' : arrayBank bank=(a::b::prior) ++ [(v+n)+1,z] := by
      have he : v+(n+1)=(v+n)+1 := by omega
      simpa only [he] using hgraph
    obtain ⟨hfirst,hsecond,harr,hev1,hev2⟩ :=
      row8_then9_array bank a b prior (v+n) z hlen hgraph'
    have hnext : arrayBank (cycleBank bank)=(a::(b+1)::prior) ++ [v+n,z] := harr
    have next := ih (b+1) (cycleBank bank) hnext
    exact ⟨⟨hfirst,hsecond,hev1,hev2⟩,next⟩

/-- The literal-table finite segment and all graph event words agree: both
are silent, and every source cycle takes its actual positive branch. -/
theorem finite_positive_cycles_match (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior (v+n) z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), n≤k ∧ (n=0 → k=0) ∧ (0<n → 0<k) ∧
      Ready h separator out a (b+n) prior v z (rest++List.replicate n 0) (cycleBanks n bank) ∧
      CyclesGood n bank ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 273 (h+8) out) k := by
  obtain ⟨k,out,hcount,hzero,hpos,hready,hseg⟩ :=
    finite_positive_cycles n h separator t a b prior v z rest bank ready
  exact ⟨k,out,hcount,hzero,hpos,hready,graph_cycles_good n a b prior v z bank ready.prior_length ready.graph,hseg⟩

#print axioms graph_cycles_good
#print axioms finite_positive_cycles_match
end Shared.Beeping.NPcoNP.NativeRow8GraphCycles
