import Shared.Beeping.NPcoNP.NativeRow8ToRow9BlankTail
import Shared.Beeping.NPcoNP.NativeRow8Repack

/-! Finite iteration of the supplied positive row-8/row-9 physical cycle. -/
namespace Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeRow8ToRow9BlankTail
open Shared.Beeping.NPcoNP.NativeRow8Repack
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

def bankWord (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) : List Bool :=
  encode (a::b::prior) ++ (encode (v::z::rest) ++ [false,false])

def cycleBank (bank : Bank 12) : Bank 12 :=
  (target.system.step ⟨9,(target.system.step ⟨8,bank⟩).1.bank⟩).1.bank

def cycleBanks : Nat → Bank 12 → Bank 12
  | 0, bank => bank
  | n+1, bank => cycleBanks n (cycleBank bank)

/-- A supplied prepared physical layout, including a blank suffix beginning
immediately after its explicit bank word. This is not a reachability claim. -/
structure Ready (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (bank : Bank 12) : Prop where
  long : h+12≤separator
  prior_length : prior.length=8
  graph : arrayBank bank=(a::b::prior) ++ [v,z]
  path : Holds t (h-4) fifthPath
  left : ∀ q, q<h-4 → t q=false
  mark : t (h+7)=true
  zero8 : t (h+8)=false
  zero9 : t (h+9)=false
  control : ∀ q, h+10≤q → q<separator → t q=true
  sep : t separator=false
  word : Holds t (separator+1) (bankWord a b prior v z rest)
  blank : ∀ q, separator+1+((bankWord a b prior v z rest).length : Int)≤q → t q=false

/-- A positive graph value pays for one complete physical cycle and produces
another prepared layout; both corresponding graph steps have no event. -/
theorem one_cycle (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior (v+1) z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      Ready h separator out a (b+1) prior v z (rest++[0]) (cycleBank bank) ∧
      (target.system.step ⟨8,bank⟩).2=[] ∧
      (target.system.step ⟨9,(target.system.step ⟨8,bank⟩).1.bank⟩).2=[] ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 273 (h+8) out) k := by
  let boundary := separator+1+((bankWord a b prior (v+1) z rest).length : Int)
  have hright : ∀ q, boundary≤q → t q=false := ready.blank
  have hbank : Holds t (separator+1)
      (encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])) := ready.word
  have hblank : ∀ q, separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)≤q → t q=false := ready.blank
  obtain ⟨k,out,hk,hpath,hleft,h7,h89,hones,hsep,_,hframe,hword,
    hfirst,hsecond,hev1,hev2,hdecode,hseg⟩ :=
    positive_row8_then_row9_blank_tail h boundary separator t a b prior v z rest bank
      ready.prior_length ready.graph ready.long ready.path ready.left ready.mark
      ready.zero8 ready.zero9 ready.control ready.sep hright hbank hblank
  have hgraph : arrayBank (cycleBank bank)=(a::(b+1)::prior) ++ [v,z] := by
    exact (row8_then9_array bank a b prior v z ready.prior_length ready.graph).2.2.1
  have heq := next_word bank a b prior v z rest ready.prior_length ready.graph
  have hword' : Holds out (separator+1) (bankWord a (b+1) prior v z (rest++[0])) := by
    change Holds out (separator+1)
      (encode (a::(b+1)::prior) ++ (encode (v::z::(rest++[0])) ++ [false,false]))
    rw [←heq]
    exact hword
  have hlen : (bankWord a b prior (v+1) z rest).length+2 =
      (bankWord a (b+1) prior v z (rest++[0])).length := by
    simp [bankWord,encode_append,encode,block_length]
    omega
  have hblank' : ∀ q, separator+1+((bankWord a (b+1) prior v z (rest++[0])).length : Int)≤q → out q=false := by
    intro q hq
    have hq' : separator+1+((bankWord a b prior (v+1) z rest).length : Int)≤q := by
      rw [←hlen] at hq
      push_cast at hq
      omega
    have hf : out q=t q := hframe q hq'
    rw [hf]
    exact ready.blank q hq'
  refine ⟨k,out,hk,?_,hev1,hev2,hseg⟩
  exact ⟨ready.long,ready.prior_length,hgraph,hpath,hleft,h7,h89.1,h89.2,hones,hsep,hword',hblank'⟩

/-- Every requested finite number of positive cycles completes; the final
physical layout corresponds to the actual iterated graph bank. -/
theorem finite_positive_cycles (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior (v+n) z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), n≤k ∧ (n=0 → k=0) ∧ (0<n → 0<k) ∧
      Ready h separator out a (b+n) prior v z (rest++List.replicate n 0) (cycleBanks n bank) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 273 (h+8) out) k := by
  induction n generalizing b t rest bank with
  | zero =>
    refine ⟨0,t,by omega,by intro _; rfl,by omega,?_,?_⟩
    · simpa [cycleBanks] using ready
    · simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    have r : Ready h separator t a b prior ((v+n)+1) z rest bank := by
      have he : v+(n+1)=(v+n)+1 := by omega
      simpa only [he] using ready
    obtain ⟨k,mid,hk,rmid,_,_,hs⟩ := one_cycle h separator t a b prior (v+n) z rest bank r
    obtain ⟨m,out,hmcount,hm0,hmpos,rout,hs'⟩ := ih mid (b+1) (rest++[0]) (cycleBank bank) rmid
    have all := segAdd machine _ _ _ k m hs hs'
    refine ⟨k+m,out,by omega,by omega,by omega,?_,all⟩
    have hb : b+1+n=b+(n+1) := by omega
    have hr : (rest++[0])++List.replicate n 0 = rest++List.replicate (n+1) 0 := by
      simp [List.replicate_succ,List.append_assoc]
    have hc : cycleBanks n (cycleBank bank)=cycleBanks (n+1) bank := rfl
    rw [hb,hr,hc] at rout
    exact rout

#print axioms one_cycle
#print axioms finite_positive_cycles
end Shared.Beeping.NPcoNP.NativeRow8Cycles
