import Shared.Beeping.NPcoNP.Source284JoinedDecodeTM2
import Shared.ComplexityBridge.TM2Diagonal

/-! A finite TM2 prefix transducer for the raw joined layout. It reads exactly
the joined input/witness prefix, preserves the unread high suffix on its input
stack, and writes the Google pair encoding of `(joinedBits x w, [])` to its
output stack. The machine reaches a continuing `done` label, not `haltList`;
linking this phase to the source-table verifier remains a separate obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2ListCodec (Stack stackVals)
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)

inductive Label where | lead | data | marker | gap | witnessMarker | witnessPayload | sentinel | restore | done | bad
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList
  [.lead,.data,.marker,.gap,.witnessMarker,.witnessPayload,.sentinel,.restore,.done,.bad]
  (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .lead => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .data)))
        (.goto (fun _ => .bad)))
  | .data => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .marker)))
        (.goto (fun _ => .bad)))
  | .marker => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false)
        (.branch (fun v => v.getD false) (.goto (fun _ => .data)) (.goto (fun _ => .gap))))
        (.goto (fun _ => .bad)))
  | .gap => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .witnessMarker)))
        (.goto (fun _ => .bad)))
  | .witnessMarker => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false)
        (.branch (fun v => v.getD false) (.goto (fun _ => .witnessPayload)) (.goto (fun _ => .sentinel))))
        (.goto (fun _ => .bad)))
  | .witnessPayload => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .witnessMarker)))
        (.goto (fun _ => .bad)))
  | .sentinel => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false)
        (.push .output (fun _ => false) (.goto (fun _ => .restore)))) (.goto (fun _ => .bad)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun _ => false) (.push .output (fun _ => true)
          (.push .output (fun v => v.getD false) (.push .output (fun _ => true)
            (.push .output (fun _ => true) (.push .output (fun _ => true) (.goto (fun _ => .restore))))))))
        (.load (fun _ => none) (.goto (fun _ => .done))))
  | .done => .goto (fun _ => .done)
  | .bad => .goto (fun _ => .bad)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .lead
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem lead_step (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .lead v (b::xs) scratch out) = some (cfg .data (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_step (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .data v (b::xs) scratch out) = some (cfg .marker (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem marker_true (v : Option Bool) (xs scratch out : List Bool) :
    machine.step (cfg .marker v (true::xs) scratch out) = some (cfg .data (some true) xs (true::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem marker_false (v : Option Bool) (xs scratch out : List Bool) :
    machine.step (cfg .marker v (false::xs) scratch out) = some (cfg .gap (some false) xs (false::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem gap_step (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .gap v (b::xs) scratch out) = some (cfg .witnessMarker (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem witness_true (v : Option Bool) (xs scratch out : List Bool) :
    machine.step (cfg .witnessMarker v (true::xs) scratch out) = some (cfg .witnessPayload (some true) xs (true::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem witness_false (v : Option Bool) (xs scratch out : List Bool) :
    machine.step (cfg .witnessMarker v (false::xs) scratch out) = some (cfg .sentinel (some false) xs (false::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem payload_step (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .witnessPayload v (b::xs) scratch out) = some (cfg .witnessMarker (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem sentinel_step (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .sentinel v (b::xs) scratch out) =
      some (cfg .restore (some b) xs (b::scratch) (false::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch out : List Bool) :
    machine.step (cfg .restore v input (b::scratch) out) =
      some (cfg .restore (some b) input scratch (true::true::true::b::true::false::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (input out : List Bool) :
    machine.step (cfg .restore v input [] out) = some (cfg .done none input [] out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_blocks (xs rest scratch out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (2*xs.length)
      (cfg .data v (reverseBlocks xs ++ rest) scratch out) =
      some (cfg .data v' rest ((reverseBlocks xs).reverse++scratch) out) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by simp [reverseBlocks,runSteps]⟩
  | cons b bs ih =>
    obtain ⟨v',h⟩ := ih (true::b::scratch) (some true)
    refine ⟨v',?_⟩
    have hn : 2*(b::bs).length = (2*bs.length+1)+1 := by simp; omega
    rw [hn,runSteps_front]
    change (machine.step (cfg .data v (b::true::(reverseBlocks bs++rest)) scratch out)).bind _ = _
    rw [data_step]
    change runSteps machine.step (2*bs.length+1)
      (cfg .marker (some b) (true::(reverseBlocks bs++rest)) (b::scratch) out) = _
    rw [runSteps_front,marker_true]
    simpa [reverseBlocks,List.reverse_cons,List.append_assoc] using h

theorem scan_witness (w extra scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (2*w.length+2)
      (cfg .witnessMarker v (frameBits w [true] ++ extra) scratch out) =
      some (cfg .restore (some true) extra ((frameBits w [true]).reverse++scratch) (false::out)) := by
  induction w generalizing scratch v with
  | nil =>
    have ht : 2*(([] : List Bool).length)+2 = 1+1 := by decide
    rw [ht,runSteps_front]
    change (machine.step (cfg .witnessMarker v (false::true::extra) scratch out)).bind _ = _
    rw [witness_false]
    change machine.step (cfg .sentinel (some false) (true::extra) (false::scratch) out) = _
    simpa [frameBits] using sentinel_step (some false) true extra (false::scratch) out
  | cons b bs ih =>
    have hn : 2*(b::bs).length+2 = (2*bs.length+2+1)+1 := by simp; omega
    rw [hn,runSteps_front]
    change (machine.step (cfg .witnessMarker v (true::b::(frameBits bs [true]++extra)) scratch out)).bind _ = _
    rw [witness_true]
    change runSteps machine.step (2*bs.length+2+1)
      (cfg .witnessPayload (some true) (b::(frameBits bs [true]++extra)) (true::scratch) out) = _
    rw [runSteps_front,payload_step]
    simpa [frameBits,List.reverse_cons,List.append_assoc] using ih (b::true::scratch) (some b)

theorem scan_joined (x w extra : List Bool) :
    runSteps machine.step (joinedBits x w).length
      (cfg .lead none (joinedBits x w ++ extra) [] []) =
      some (cfg .restore (some true) extra (joinedBits x w).reverse [false]) := by
  obtain ⟨v,hblocks⟩ := scan_blocks x.reverse
    ([false,false,false] ++ frameBits w [true] ++ extra) [false] [] (some false)
  have hlen : (joinedBits x w).length = 1+(2*x.length+(3+(2*w.length+2))) := by
    rw [joined_length]; omega
  rw [hlen,runSteps_add]
  change (machine.step (cfg .lead none (joinedBits x w ++ extra) [] [])).bind _ = _
  have hinput : joinedBits x w ++ extra =
      false :: (reverseBlocks x.reverse ++ ([false,false,false] ++ frameBits w [true] ++ extra)) := by
    simp [joinedBits,reversed_frame,List.append_assoc]
  rw [hinput,lead_step]
  change runSteps machine.step (2*x.length+(3+(2*w.length+2)))
    (cfg .data (some false) (reverseBlocks x.reverse ++ ([false,false,false] ++ frameBits w [true] ++ extra)) [false] []) = _
  rw [runSteps_add]
  simp only [List.length_reverse] at hblocks
  rw [hblocks]
  change runSteps machine.step (3+(2*w.length+2))
    (cfg .data v (false::false::false::(frameBits w [true]++extra))
      ((reverseBlocks x.reverse).reverse++[false]) []) = _
  rw [show 3+(2*w.length+2) = ((2*w.length+2)+1)+1+1 by omega,runSteps_front,data_step]
  simp only [Option.bind_some]
  rw [runSteps_front,marker_false]
  simp only [Option.bind_some]
  rw [runSteps_front,gap_step]
  simp only [Option.bind_some]
  rw [scan_witness]
  simp [joinedBits,reversed_frame,List.reverse_cons,List.reverse_append,List.append_assoc]

theorem restore_loop (scratch input out : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v input scratch out) =
      some (cfg .done none input [] (Shared.ComplexityBridge.TM2Diagonal.prefixBits scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil => simpa [runSteps,Shared.ComplexityBridge.TM2Diagonal.prefixBits] using restore_nil v input out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [Shared.ComplexityBridge.TM2Diagonal.prefixBits,List.reverse_cons,List.flatMap_append,List.append_assoc]
      using ih (true::true::true::b::true::false::out) (some b)

theorem initial_eq (bits : List Bool) : Turing.initList machine bits = cfg .lead none bits [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

/-- The actual finite TM2 reads the exact joined prefix, writes its canonical
Google pair encoding, and reaches `done` in `2*prefixLength+1` whole blocks.
The arbitrary high input suffix remains intact and is not traversed. -/
theorem encode_joined (x w extra : List Bool) :
    runSteps machine.step (2*(joinedBits x w).length+1)
      (Turing.initList machine (joinedBits x w ++ extra)) =
      some (cfg .done none extra []
        (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))) := by
  have hs := scan_joined x w extra
  have hr := restore_loop (joinedBits x w).reverse extra [false] (some true)
  simp only [List.length_reverse,List.reverse_reverse] at hr
  have hout : Shared.ComplexityBridge.TM2Diagonal.prefixBits (joinedBits x w) ++ [false] =
      BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)) := by
    change Shared.ComplexityBridge.TM2Diagonal.prefixBits (joinedBits x w) ++ [false] =
      BitstringEncoding.delimit (BitstringEncoding.bitEncode (joinedBits x w)) ++ []
    rw [List.append_nil,← Shared.ComplexityBridge.TM2Diagonal.encoded_eq,
      Shared.ComplexityBridge.TM2Diagonal.prefix_eq]
  have ht : 2*(joinedBits x w).length+1 = (joinedBits x w).length+((joinedBits x w).length+1) := by omega
  rw [ht,initial_eq,runSteps_add,hs]
  simp only [Option.bind_some]
  rw [hr,hout]

/-- The actual prefix transducer uses a linear number of whole TM2 statement
blocks, bounded by the original witness cutoff and parsed input length. -/
theorem encode_joined_cost (x w : List Bool) (limit : Nat) (hw : w.length ≤ limit) :
    2*(joinedBits x w).length+1 ≤ 4*x.length+4*limit+13 := by
  rw [joined_length]
  omega

/-- The encoder writes the exact library pair serialization and its full bit
length. No unit-cost unbounded arithmetic is used by the finite TM2. -/
theorem output_length (x w : List Bool) :
    (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))).length =
      12*x.length+12*w.length+37 :=
  Source284JoinedDecodeTM2.canonical_joined_length x w

/-- The handoff label is a continuing state, so the finite prefix does not
implicitly turn into ordinary halting. -/
theorem done_step (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .done v input scratch output) = some (cfg .done v input scratch output) := by
  rfl

theorem done_run (v : Option Bool) (input scratch output : List Bool) (fuel : Nat) :
    runSteps machine.step fuel (cfg .done v input scratch output) =
      some (cfg .done v input scratch output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [runSteps_front,done_step]
    exact ih

namespace Fixtures
example : runSteps machine.step 13
    (Turing.initList machine (joinedBits [] [] ++ [true,false])) =
    some (cfg .done none [true,false] [] (BitstringEncoding.bitEncode (joinedBits [] [],([] : List Bool)))) := by
  simpa [joined_length] using encode_joined [] [] [true,false]

example : runSteps machine.step 29
    (Turing.initList machine (joinedBits [false,true] [true,false] ++ [true,true])) =
    some (cfg .done none [true,true] []
      (BitstringEncoding.bitEncode (joinedBits [false,true] [true,false],([] : List Bool)))) := by
  simpa [joined_length] using encode_joined [false,true] [true,false] [true,true]
end Fixtures
end Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2
