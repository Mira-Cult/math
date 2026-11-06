import Shared.ComplexityBridge.TM2TypedPairMap
import Shared.ComplexityBridge.TM2ListReverse

set_option maxHeartbeats 3000000

/-! Executable bit-list implementation and elementary operation accounting
for the CNF selector clause. A token list controls the number of iterations.
The counters count recursive inspections and Boolean-list construction; they
are mathematical instrumentation and are not themselves an implementation of
unbounded integer arithmetic. This is not yet a TM2 loop simulation. -/
namespace Shared.ComplexityBridge.CNFChoiceBitCosts
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction
open Shared.Codes.BitTableValidation (increment)
open Shared.ComplexityBridge.CNFNatBitCosts (reverseCopy)

def delimitCost : List Bool → List Bool × Nat
  | [] => ([false],1)
  | b::bs => let r := delimitCost bs; (true::b::r.1,r.2+3)

theorem delimitCost_correct (bits : List Bool) :
    delimitCost bits = (BitstringEncoding.delimit bits,3*bits.length+1) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [delimitCost,BitstringEncoding.delimit,ih]; omega

def appendCost : List Bool → List Bool → List Bool × Nat
  | [], ys => (ys,1)
  | b::bs, ys => let r := appendCost bs ys; (b::r.1,r.2+2)

theorem appendCost_correct (xs ys : List Bool) : appendCost xs ys = (xs++ys,2*xs.length+1) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [appendCost,ih]; omega

/-- A full clause-element block for the positive selector whose index has the
supplied little-endian binary representation. -/
def block (bits : List Bool) : List Bool :=
  BitstringEncoding.delimit (BitstringEncoding.delimit (true::bits) ++ [true])

def blockCost (bits : List Bool) : List Bool × Nat :=
  let inner := delimitCost (true::bits)
  let literal := appendCost inner.1 [true]
  let outer := delimitCost literal.1
  (outer.1,inner.2+literal.2+outer.2)

theorem blockCost_correct (bits : List Bool) : (blockCost bits).1 = block bits := by
  simp [blockCost,block,delimitCost_correct,appendCost_correct]

theorem block_length (bits : List Bool) : (block bits).length = 4*bits.length+9 := by
  simp [block,BitstringEncoding.length_delimit]
  omega

theorem blockCost_bound (bits : List Bool) : (blockCost bits).2 ≤ 20*bits.length+30 := by
  simp [blockCost,delimitCost_correct,appendCost_correct,BitstringEncoding.length_delimit]
  omega

theorem block_index (n : Nat) : block n.bits = BitstringEncoding.delimit
    (BitstringEncoding.bitEncode (selector n,true)) := by
  have he : BitstringEncoding.bitEncode (selector n,true) =
      BitstringEncoding.delimit (true::n.bits) ++ [true] := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode (selector n)) ++ [true] = _
    have hn : BitstringEncoding.bitEncode (selector n) = (selector n).bits :=
      Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits (selector n)
    rw [hn]
    simp [selector,Nat.bit1_bits]
  simp [block,he]

/-- One iteration emits one framed literal in reverse byte order and updates
the binary index. The increment charge includes the actual finite TM2
incrementer's linear block bound, rather than treating the numeral as one unit. -/
def step (bits acc : List Bool) : (List Bool × List Bool) × Nat :=
  let b := blockCost bits
  let out := reverseCopy b.1 acc
  let next := increment bits
  ((next.1,out.1),b.2+out.2+(2*bits.length+3))

theorem step_correct (bits acc : List Bool) :
    (step bits acc).1 = ((increment bits).1,(block bits).reverse++acc) := by
  simp [step,blockCost_correct,Shared.ComplexityBridge.CNFNatBitCosts.reverseCopy_correct]

theorem step_cost (bits acc : List Bool) : (step bits acc).2 ≤ 30*bits.length+52 := by
  have hb := blockCost_bound bits
  have hl := block_length bits
  simp only [step,Shared.ComplexityBridge.CNFNatBitCosts.reverseCopy_correct,blockCost_correct]
  omega

def loop : List Bool → List Bool → List Bool → (List Bool × List Bool) × Nat
  | [], bits, acc => ((bits,acc),1)
  | _::fuel, bits, acc =>
      let s := step bits acc
      let r := loop fuel s.1.1 s.1.2
      (r.1,s.2+r.2+1)

theorem loop_bits_length (fuel bits acc : List Bool) :
    (loop fuel bits acc).1.1.length ≤ bits.length+fuel.length := by
  induction fuel generalizing bits acc with
  | nil => simp [loop]
  | cons t fuel ih =>
    simp only [loop,step_correct,Prod.fst,Prod.snd]
    have h := ih (step bits acc).1.1 (step bits acc).1.2
    have hs := Shared.Codes.BitTableValidation.increment_length bits
    rw [step_correct] at h
    simp only [Prod.fst] at h
    simp only [List.length_cons]
    omega

/-- The proof-side cost is quadratic in the token length and initial bit
length; no unit-cost unbounded arithmetic is assumed by the generator. -/
theorem loop_cost (fuel bits acc : List Bool) :
    (loop fuel bits acc).2 ≤ (fuel.length+1)*(30*(bits.length+fuel.length)+54) := by
  induction fuel generalizing bits acc with
  | nil => simp [loop]
  | cons t fuel ih =>
    have hs := step_cost bits acc
    have hb := Shared.Codes.BitTableValidation.increment_length bits
    have hr := ih (step bits acc).1.1 (step bits acc).1.2
    rw [step_correct] at hr
    simp only [Prod.fst] at hr
    have hupper : 30*((increment bits).1.length+fuel.length)+54 ≤
        30*(bits.length+(fuel.length+1))+54 := by omega
    have hm := Nat.mul_le_mul_left (fuel.length+1) hupper
    simp only [loop,List.length_cons,step_correct,Prod.fst,Prod.snd]
    have he : (fuel.length+1+1)*(30*(bits.length+(fuel.length+1))+54) =
        (fuel.length+1)*(30*(bits.length+(fuel.length+1))+54) +
          (30*(bits.length+(fuel.length+1))+54) := by ring
    rw [he]
    omega

theorem choices_cons (start count : Nat) :
    choices start (count+1) = (selector start,true)::choices (start+1) count := by
  simp [choices,List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem encode_choices_cons (start count : Nat) :
    BitstringEncoding.bitEncode (choices start (count+1)) =
      block start.bits ++ BitstringEncoding.bitEncode (choices (start+1) count) := by
  rw [choices_cons]
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode (selector start,true)) ++
    BitstringEncoding.bitEncode (choices (start+1) count) = _
  rw [block_index]

theorem loop_correct (fuel : List Bool) (start : Nat) (acc : List Bool) :
    (loop fuel start.bits acc).1.2 =
      (BitstringEncoding.bitEncode (choices start fuel.length)).reverse ++ acc := by
  induction fuel generalizing start acc with
  | nil =>
    have he : BitstringEncoding.bitEncode ([] : Clause) = [] := rfl
    simp [loop,choices,he]
  | cons b fuel ih =>
    simp only [loop,step_correct,Prod.fst,Prod.snd]
    rw [Shared.ComplexityBridge.CNFBinaryIncrement.increment_bits,ih]
    simp only [List.length_cons,encode_choices_cons,List.reverse_append,List.append_assoc]

theorem loop_final_index (fuel : List Bool) (start : Nat) (acc : List Bool) :
    (loop fuel start.bits acc).1.1 = (start+fuel.length).bits := by
  induction fuel generalizing start acc with
  | nil => simp [loop]
  | cons b fuel ih =>
    simp only [loop,step_correct,Prod.fst,Prod.snd]
    rw [Shared.ComplexityBridge.CNFBinaryIncrement.increment_bits,ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem loop_acc_length (fuel bits acc : List Bool) :
    (loop fuel bits acc).1.2.length ≤ acc.length + fuel.length*(4*(bits.length+fuel.length)+9) := by
  induction fuel generalizing bits acc with
  | nil => simp [loop]
  | cons b fuel ih =>
    have hb := Shared.Codes.BitTableValidation.increment_length bits
    have hr := ih (step bits acc).1.1 (step bits acc).1.2
    rw [step_correct] at hr
    simp only [Prod.fst,Prod.snd,List.length_append,List.length_reverse,block_length] at hr
    have hupper : 4*((increment bits).1.length+fuel.length)+9 ≤
        4*(bits.length+(fuel.length+1))+9 := by omega
    have hm := Nat.mul_le_mul_left fuel.length hupper
    simp only [loop,List.length_cons,step_correct,Prod.fst,Prod.snd]
    have he : (fuel.length+1)*(4*(bits.length+(fuel.length+1))+9) =
        fuel.length*(4*(bits.length+(fuel.length+1))+9) +
          (4*(bits.length+(fuel.length+1))+9) := by ring
    rw [he]
    omega

/-- Execute the loop and reverse its accumulated output bytes. -/
def generate (fuel bits : List Bool) : List Bool × Nat :=
  let r := loop fuel bits []
  let out := reverseCopy r.1.2 []
  (out.1,r.2+out.2)

/-- The bit-level program returns the exact pinned serialized `choices`
clause. The number of iterations is the actual token-list length. -/
theorem generate_correct (fuel : List Bool) (start : Nat) :
    (generate fuel start.bits).1 = BitstringEncoding.bitEncode (choices start fuel.length) := by
  simp [generate,Shared.ComplexityBridge.CNFNatBitCosts.reverseCopy_correct,loop_correct]

theorem generate_cost (fuel bits : List Bool) :
    (generate fuel bits).2 ≤
      (fuel.length+1)*(30*(bits.length+fuel.length)+54) +
        2*(fuel.length*(4*(bits.length+fuel.length)+9))+1 := by
  have hc := loop_cost fuel bits []
  have hl := loop_acc_length fuel bits []
  simp only [List.length_nil,Nat.zero_add] at hl
  simp only [generate,Shared.ComplexityBridge.CNFNatBitCosts.reverseCopy_correct]
  omega

namespace Fixtures
example : (generate [] []).1 = BitstringEncoding.bitEncode (choices 0 0) := by
  simpa using generate_correct [] 0
example : (generate [true,false,true] []).1 = BitstringEncoding.bitEncode (choices 0 3) := by
  simpa using generate_correct [true,false,true] 0
end Fixtures

end Shared.ComplexityBridge.CNFChoiceBitCosts
