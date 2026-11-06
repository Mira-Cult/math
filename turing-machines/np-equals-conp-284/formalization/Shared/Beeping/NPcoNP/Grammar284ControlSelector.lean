import Shared.Beeping.NPcoNP.Grammar284PathSelector
import Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
/-! A control-path interface with explicit continuation and unary zero
reserve. Actual control-point correspondence remains a separate obligation. -/
namespace Shared.Beeping.NPcoNP.Grammar284ControlSelector

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PathSelector
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def controlWord (path continuation : List Bool) : List Bool :=
  let word := path++continuation
  word ++ encode (List.replicate (14-word.count false) 0)

def controlRuns (path continuation : List Bool) : List Nat :=
  (runsAux 0 (controlWord path continuation)).1

theorem controlWord_final_zero (path continuation : List Bool)
    (hz : (path++continuation).count false≤13) :
    (runsAux 0 (controlWord path continuation)).2=0 := by
  have hpos : 0<14-(path++continuation).count false := by omega
  have hne : List.replicate (14-(path++continuation).count false) 0 ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_replicate,List.length_nil] at hl
    omega
  obtain ⟨front,hfront⟩ := encode_ends_zero _ hne
  have he : controlWord path continuation=(path++continuation++front)++[false] := by
    dsimp [controlWord]
    rw [hfront]
    simp [List.append_assoc]
  rw [he]
  exact runsAux_ends_zero 0 _

theorem controlWord_blocks (path continuation : List Bool)
    (hz : (path++continuation).count false≤13) :
    blocks (controlRuns path continuation)=controlWord path continuation := by
  have h := runsAux_word 0 (controlWord path continuation)
  rw [controlWord_final_zero path continuation hz] at h
  simpa [controlRuns] using h

theorem controlRuns_length (path continuation : List Bool)
    (hz : (path++continuation).count false≤13) :
    (controlRuns path continuation).length=14 := by
  have h := runsAux_length 0 (controlWord path continuation)
  change (controlRuns path continuation).length = (controlWord path continuation).count false at h
  simp [controlWord] at h
  simp only [List.count_append] at hz
  omega

theorem controlWord_selector (path continuation : List Bool)
    (hz : (path++continuation).count false≤13)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (controlWord path continuation ++ rest)) :
    0<(controlWord path continuation).length ∧
    downHolds tape (h-((controlWord path continuation).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((controlWord path continuation).length : Int)) tape)
      (controlWord path continuation).length := by
  have hpos : 0<(controlWord path continuation).length := by
    have hlen : (controlWord path continuation).length =
        (path++continuation).length + 2*(14-(path++continuation).count false) := by
      simp [controlWord,zeros_length,Nat.add_assoc]
    rw [hlen]
    omega
  have hw' : downHolds tape h (blocks (controlRuns path continuation) ++ rest) := by
    rw [controlWord_blocks path continuation hz]
    exact hw
  have hs := chain_blocks chain83 (controlRuns path continuation) h tape rest
    (controlRuns_length path continuation hz) hw'
  rw [controlWord_blocks path continuation hz] at hs
  exact ⟨hpos,hs.1,hs.2⟩

/-- Exact cost in bits; this makes the continuation length explicit. -/
theorem controlWord_length (path continuation : List Bool) :
    (controlWord path continuation).length =
      path.length+continuation.length+2*(14-(path++continuation).count false) := by
  simp [controlWord,zeros_length,Nat.add_assoc]

/-- A prepared grammar path plus a finite continuation has a positive silent
selector segment. Its cost is bounded in terms of that continuation length. -/
theorem prepared_control_selector (path : List Bool) (last : Leaf)
    (hp : PreparedWalk path last) (continuation : List Bool)
    (hz : (path++continuation).count false≤13)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (controlWord path continuation ++ rest)) :
    0<(controlWord path continuation).length ∧
    (controlWord path continuation).length≤81+continuation.length ∧
    downHolds tape (h-((controlWord path continuation).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((controlWord path continuation).length : Int)) tape)
      (controlWord path continuation).length := by
  have hb := prepared_path_bound path last hp
  have hnonzero : 1≤(path++continuation).count false := by
    obtain ⟨raw,he,hwalk⟩ := hp
    rw [he]
    simp [preparedPrefix,List.count_append]
  have hbound : (controlWord path continuation).length≤81+continuation.length := by
    rw [controlWord_length]
    omega
  have hs := controlWord_selector path continuation hz tape h rest hw
  exact ⟨hs.1,hbound,hs.2.1,hs.2.2⟩

#print axioms controlWord_length
#print axioms prepared_control_selector

#print axioms controlWord_selector

open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths

theorem expanded_leaf_control_selector (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × String) (hmem : entry ∈ e.leaves.toList) (continuation : List Bool)
    (hz : (entry.1++continuation).count false≤13)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (controlWord entry.1 continuation ++ rest)) :
    PreparedWalk entry.1 (.op entry.2) ∧
    0<(controlWord entry.1 continuation).length ∧
    downHolds tape (h-((controlWord entry.1 continuation).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((controlWord entry.1 continuation).length : Int)) tape)
      (controlWord entry.1 continuation).length := by
  exact ⟨expanded_leaf_follows e he entry hmem, controlWord_selector entry.1 continuation hz tape h rest hw⟩

theorem expanded_start_control_selector (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × Nat) (hmem : entry ∈ e.starts.toList) (continuation : List Bool)
    (hz : (entry.1++continuation).count false≤13)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (controlWord entry.1 continuation ++ rest)) :
    (∃ last, PreparedWalk entry.1 last) ∧
    0<(controlWord entry.1 continuation).length ∧
    downHolds tape (h-((controlWord entry.1 continuation).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((controlWord entry.1 continuation).length : Int)) tape)
      (controlWord entry.1 continuation).length := by
  exact ⟨expanded_start_follows e he entry hmem, controlWord_selector entry.1 continuation hz tape h rest hw⟩

#print axioms expanded_leaf_control_selector
#print axioms expanded_start_control_selector

end Shared.Beeping.NPcoNP.Grammar284ControlSelector
