import Shared.Codes.FiniteProgramProtectedCompressStep
import Shared.Codes.FiniteProgramProtectedScanLoop
import Shared.Codes.FiniteProgramRestartTwo

/-! Restart the unmarked branch of the protected block compactor and retain
the marked branch as a terminal placeholder. This finite program does not
validate malformed occupied bits or finish the output representation. -/
namespace Shared.Codes.FiniteProgramProtectedCompressLoop
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramProtectedScanLoop (block blocks)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def source (w : Nat) : Program := Shared.Codes.FiniteProgramProtectedCompressStep.program w
def finish (w : Nat) (marked : Bool) : Nat := Shared.Codes.FiniteProgramProtectedCompressStep.finish w marked
def program (w : Nat) : Program := Shared.Codes.FiniteProgramRestartTwo.program (source w)
  (finish w false) (finish w false)

@[simp] theorem program_length (w : Nat) : (program w).length = 38*w+162 := by
  simp [program,source]

theorem program_valid (w : Nat) : valid (program w) = true :=
  Shared.Codes.FiniteProgramRestartTwo.program_valid _ _ _
    (Shared.Codes.FiniteProgramProtectedCompressStep.program_valid w)

theorem finish_bound (w : Nat) (marked : Bool) : finish w marked < (source w).length := by
  cases marked <;> simp [finish,source,Shared.Codes.FiniteProgramProtectedCompressStep.finish,
    Shared.Codes.FiniteProgramProtectedCompressStep.entry,Shared.Codes.FiniteProgramFork.off₀,
    Shared.Codes.FiniteProgramFork.off₁,Shared.Codes.FiniteProgramProtectedCompressStep.source,
    Shared.Codes.FiniteProgramProtectedCompressStep.worker,
    Shared.Codes.FiniteProgramAppendSkipFixed.offset_value] <;> omega

theorem finish_distinct (w : Nat) : finish w false ≠ finish w true :=
  Shared.Codes.FiniteProgramProtectedCompressStep.finish_distinct w

theorem marked_placeholder (w : Nat) (t : Tape) :
    step (program w) (finish w true,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramRestartTwo.source_other (source w) (finish w false) (finish w false)
    (finish w true,t) (finish_bound w true) (Ne.symm (finish_distinct w)) (Ne.symm (finish_distinct w))
  change step (source w) (finish w true,t) = step (program w) (finish w true,t) at h
  rw [← h]
  exact Shared.Codes.FiniteProgramProtectedCompressStep.finish_placeholder w true t

def cost (w : Nat) (xs : List Bool) : Nat :=
  (2*w+2)+2+((16*xs.length+29)+2+(w+2)*(10*(xs.length+1)+7))

theorem cost_eq (w : Nat) (xs : List Bool) :
    cost w xs = (10*w+36)*xs.length+19*w+69 := by
  simp [cost]
  ring

/-- The source block run is retained until the selected marker state. -/
theorem process (w : Nat) (data marked next : Bool) (payload L xs : List Bool)
    (hlen : payload.length = w) (t : Tape)
    (ht : TapeRel t (canonical (payload ++ marked::true::next::L) data xs).2) :
    ∃ u, run (program w) (0,t) (cost w xs) = some (.inr (finish w marked,u)) ∧
      TapeRel u (canonical L next (xs++[data])).2 := by
  obtain ⟨u,hu,hurel⟩ := Shared.Codes.FiniteProgramProtectedCompressStep.compress_block_related
    w data marked next payload L xs hlen (0,t) rfl ht
  let a := finish w false
  have hs : ∃ r, ∀ t, step (source w) (a,t) = some (.inl r) :=
    ⟨false,Shared.Codes.FiniteProgramProtectedCompressStep.finish_placeholder w false⟩
  have hp := Shared.Codes.FiniteProgramRestartTwo.first_entry (source w) a a (0,t) (finish w marked,u)
    (cost w xs) (Shared.Codes.FiniteProgramProtectedCompressStep.program_valid w)
    (by simp [source]) hs hs (by simpa [source,finish,cost] using hu)
  exact ⟨u,by simpa [program,a] using hp,hurel⟩

/-- An unmarked block appends its data and returns to state zero after two
additional tape-preserving transitions. -/
theorem cycle (w : Nat) (data next : Bool) (payload L xs : List Bool)
    (hlen : payload.length = w) (t : Tape)
    (ht : TapeRel t (canonical (payload ++ false::true::next::L) data xs).2) :
    ∃ u, run (program w) (0,t) (cost w xs+2) = some (.inr (0,u)) ∧
      TapeRel u (canonical L next (xs++[data])).2 := by
  obtain ⟨u,hu,hurel⟩ := process w data false next payload L xs hlen t ht
  have hr := Shared.Codes.FiniteProgramRestartTwo.restart_second (source w)
    (finish w false) (finish w false) (finish_bound w false) u
  refine ⟨Shared.Codes.FiniteProgramThreeExit.bounce u,?_,?_⟩
  · rw [run_continue _ _ _ _ _ hu]
    exact hr
  · exact (Shared.Codes.FiniteProgramThreeExit.bounce_related u).trans hurel

/-- Charged run time: every unmarked block costs a pass and a restart; the
last marked block costs a pass and stops at its continuation placeholder. -/
def totalCost (w : Nat) : List (Bool × List Bool) → List Bool → Nat
  | [], xs => cost w xs
  | (b,_)::rest, xs => cost w xs+2+totalCost w rest (xs++[b])

/-- Starting at the rightmost block, process every unmarked block and then
the marked block in a single finite table. Data are appended in scan order;
the fixed-width payload and true occupancy tag are input invariants. -/
theorem run_to_marked (w : Nat) (before : List (Bool × List Bool))
    (hbefore : ∀ x ∈ before, x.2.length = w)
    (last next : Bool) (payload L xs : List Bool) (hlen : payload.length = w)
    (t : Tape)
    (ht : TapeRel t (tapeLeft (blocks before ++ block last payload true ++ next::L)
      (false::tagged xs ++ [false,false,false]))) :
    ∃ u, run (program w) (0,t) (totalCost w before xs) = some (.inr (finish w true,u)) ∧
      TapeRel u (canonical L next (xs ++ before.map Prod.fst ++ [last])).2 := by
  induction before generalizing xs t with
  | nil =>
    have hin : TapeRel t (canonical (payload ++ true::true::next::L) last xs).2 := by
      simpa [blocks,block,canonical,tapeLeft,Shared.ComplexityBridge.PairMarkedScanner.tapeAt,
        List.append_assoc] using ht
    obtain ⟨u,hu,hurel⟩ := process w last true next payload L xs hlen t hin
    refine ⟨u,?_,?_⟩
    · simpa [totalCost] using hu
    · simpa using hurel
  | cons x rest ih =>
    rcases x with ⟨data,word⟩
    have hword : word.length = w := hbefore (data,word) (by simp)
    have htail : ∀ x ∈ rest, x.2.length = w := by
      intro x hx
      exact hbefore x (by simp [hx])
    have hexists : ∃ b tail, blocks rest ++ block last payload true ++ next::L = b::tail := by
      cases rest with
      | nil =>
        refine ⟨last,payload ++ true::true::next::L,?_⟩
        simp [blocks,block,List.append_assoc]
      | cons y ys =>
        rcases y with ⟨b,part⟩
        refine ⟨b,part ++ false::true::(blocks ys ++ block last payload true ++ next::L),?_⟩
        simp [blocks,block,List.append_assoc]
    obtain ⟨b,tail,heq⟩ := hexists
    have heq' := heq
    simp [blocks,block,List.append_assoc] at heq'
    have hin : TapeRel t (canonical (word ++ false::true::b::tail) data xs).2 := by
      simpa [blocks,block,canonical,tapeLeft,Shared.ComplexityBridge.PairMarkedScanner.tapeAt,
        List.append_assoc,heq'] using ht
    obtain ⟨u,hu,hurel⟩ := cycle w data b word tail xs hword t hin
    have htailTape : TapeRel u (tapeLeft (blocks rest ++ block last payload true ++ next::L)
        (false::tagged (xs++[data]) ++ [false,false,false])) := by
      simpa [heq,canonical,tapeLeft,Shared.ComplexityBridge.PairMarkedScanner.tapeAt] using hurel
    obtain ⟨v,hv,hvrel⟩ := ih htail (xs++[data]) u htailTape
    refine ⟨v,?_,?_⟩
    · change run (program w) (0,t) (cost w xs+2+totalCost w rest (xs++[data])) = _
      rw [show cost w xs+2+totalCost w rest (xs++[data]) =
        (cost w xs+2)+totalCost w rest (xs++[data]) by omega,
        run_continue _ _ _ _ _ hu]
      exact hv
    · simpa [List.append_assoc] using hvrel

/-- A uniform polynomial upper bound in block count, initial buffer length,
and fixed encoded-cell width. It includes every unmarked restart. -/
theorem totalCost_bound (w : Nat) (before : List (Bool × List Bool)) (xs : List Bool) :
    totalCost w before xs ≤
      (before.length+1)*((10*w+36)*(xs.length+before.length)+19*w+69)+2*before.length := by
  induction before generalizing xs with
  | nil => simp [totalCost,cost_eq]
  | cons x rest ih =>
    rcases x with ⟨data,payload⟩
    let n := rest.length
    let bound := (10*w+36)*(xs.length+(n+1))+19*w+69
    have hlocal : cost w xs ≤ bound := by
      rw [cost_eq]
      dsimp [bound]
      have hm := Nat.mul_le_mul_left (10*w+36) (show xs.length ≤ xs.length+(n+1) by omega)
      omega
    have htail : totalCost w rest (xs++[data]) ≤ (n+1)*bound+2*n := by
      have h := ih (xs++[data])
      simpa [n,bound,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    change cost w xs+2+totalCost w rest (xs++[data]) ≤ (n+2)*bound+2*(n+1)
    calc
      _ ≤ bound+2+((n+1)*bound+2*n) := by omega
      _ = (n+2)*bound+2*(n+1) := by ring

end Shared.Codes.FiniteProgramProtectedCompressLoop
