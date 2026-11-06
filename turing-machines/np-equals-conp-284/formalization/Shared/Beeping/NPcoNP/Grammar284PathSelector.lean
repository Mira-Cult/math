import Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
import Shared.Beeping.NPcoNP.NativeHalfSelectorExact
/-! A synthetic consecutive-zero padding interface for the literal selector.
The physical descending tape layout is an explicit premise. It is false at
the checked visit in `Bootstrap284ControlSelector`; use the continuation and
unary-reserve interface there for that boundary. -/
namespace Shared.Beeping.NPcoNP.Grammar284PathSelector

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def runsAux : Nat → List Bool → List Nat × Nat
  | n, [] => ([],n)
  | n, true::xs => runsAux (n+1) xs
  | n, false::xs => let p := runsAux 0 xs; (n::p.1,p.2)

theorem runsAux_word (n : Nat) (xs : List Bool) :
    blocks (runsAux n xs).1 ++ List.replicate (runsAux n xs).2 true =
      List.replicate n true ++ xs := by
  induction xs generalizing n with
  | nil => simp [runsAux,blocks]
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [runsAux,blocks]
      have h := ih 0
      simp only [List.replicate_zero,List.nil_append] at h
      simpa [List.cons_append,List.append_assoc] using
        congrArg (fun w => List.replicate n true ++ false::w) h
    | true =>
      simp only [runsAux]
      rw [ih (n+1)]
      simp [List.replicate_succ',List.append_assoc]

theorem runsAux_length (n : Nat) (xs : List Bool) :
    (runsAux n xs).1.length = xs.count false := by
  induction xs generalizing n with
  | nil => simp [runsAux]
  | cons b xs ih =>
    cases b <;> simp [runsAux,ih]

theorem runsAux_ends_zero (n : Nat) (xs : List Bool) :
    (runsAux n (xs++[false])).2 = 0 := by
  induction xs generalizing n with
  | nil => simp [runsAux]
  | cons b xs ih =>
    cases b <;> simp [runsAux,ih]

/-- Synthetic padding for a supplied tape word. It is not the actual unary
zero-block reserve and is incompatible with the checked bootstrap visit. -/
def paddedPath (path : List Bool) : List Bool :=
  path ++ List.replicate (14-path.count false) false

def pathRuns (path : List Bool) : List Nat := (runsAux 0 (paddedPath path)).1

theorem paddedPath_final_zero (path : List Bool) (hz : path.count false≤11) :
    (runsAux 0 (paddedPath path)).2=0 := by
  have hpos : 0<14-path.count false := by omega
  have hn : 14-path.count false = (14-path.count false-1)+1 := by omega
  have he : paddedPath path = (path ++ List.replicate (14-path.count false-1) false) ++ [false] := by
    dsimp [paddedPath]
    conv_lhs => rw [hn,List.replicate_succ']
    simp [List.append_assoc]
  rw [he]
  exact runsAux_ends_zero 0 _

theorem paddedPath_blocks (path : List Bool) (hz : path.count false≤11) :
    blocks (pathRuns path)=paddedPath path := by
  have h := runsAux_word 0 (paddedPath path)
  rw [paddedPath_final_zero path hz] at h
  simpa [pathRuns] using h

theorem pathRuns_length (path : List Bool) (hz : path.count false≤11) :
    (pathRuns path).length=14 := by
  have h := runsAux_length 0 (paddedPath path)
  change (pathRuns path).length = (paddedPath path).count false at h
  simp only [paddedPath,List.count_append,List.count_replicate_self] at h
  omega

theorem preparedPath_selector (path : List Bool) (last : Leaf) (hp : PreparedWalk path last)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (paddedPath path ++ rest)) :
    0<(paddedPath path).length ∧ (paddedPath path).length≤68 ∧
    downHolds tape (h-((paddedPath path).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((paddedPath path).length : Int)) tape) (paddedPath path).length := by
  have hb := prepared_path_bound path last hp
  have hnonzero : 1≤path.count false := by
    obtain ⟨raw,he,hwalk⟩ := hp
    rw [he]
    simp [preparedPrefix,List.count_append]
  have hpos : 0<(paddedPath path).length := by
    obtain ⟨raw,he,hwalk⟩ := hp
    rw [he]
    simp [paddedPath,preparedPrefix]
  have hlen : (paddedPath path).length≤68 := by
    simp [paddedPath]
    omega
  have hw' : downHolds tape h (blocks (pathRuns path) ++ rest) := by
    rw [paddedPath_blocks path hb.2]
    exact hw
  have hs := chain_blocks chain83 (pathRuns path) h tape rest (pathRuns_length path hb.2) hw'
  rw [paddedPath_blocks path hb.2] at hs
  exact ⟨hpos,hlen,hs.1,hs.2⟩

#print axioms preparedPath_selector


open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths

theorem expanded_leaf_selector (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × String) (hmem : entry ∈ e.leaves.toList)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (paddedPath entry.1 ++ rest)) :
    0<(paddedPath entry.1).length ∧ (paddedPath entry.1).length≤68 ∧
    downHolds tape (h-((paddedPath entry.1).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((paddedPath entry.1).length : Int)) tape) (paddedPath entry.1).length :=
  preparedPath_selector entry.1 (.op entry.2) (expanded_leaf_follows e he entry hmem) tape h rest hw

theorem expanded_start_selector (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × Nat) (hmem : entry ∈ e.starts.toList)
    (tape : Int → Bool) (h : Int) (rest : List Bool)
    (hw : downHolds tape h (paddedPath entry.1 ++ rest)) :
    0<(paddedPath entry.1).length ∧ (paddedPath entry.1).length≤68 ∧
    downHolds tape (h-((paddedPath entry.1).length : Int)) rest ∧
    silentSegment machine (cfg 83 h tape)
      (cfg 92 (h-((paddedPath entry.1).length : Int)) tape) (paddedPath entry.1).length := by
  obtain ⟨last,hpath⟩ := expanded_start_follows e he entry hmem
  exact preparedPath_selector entry.1 last hpath tape h rest hw

#print axioms expanded_leaf_selector
#print axioms expanded_start_selector

end Shared.Beeping.NPcoNP.Grammar284PathSelector
