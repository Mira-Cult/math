import Shared.Codes.FiniteProgramProtectedScan
import Shared.Codes.FiniteProgramWriteWord
import Shared.ComplexityBridge.TM2OutputProtectedCodec

/-! Physical scanning of a written protected output block. The scanner's
continuation states are placeholders; copying or compacting bits is separate. -/
namespace Shared.ComplexityBridge.TM2OutputProtectedScan
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTwoWordClassify (mask)
open Shared.Codes.FiniteProgramProtectedScan (state)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputProtectedCodec
open Shared.ComplexityBridge.TM2OutputCellCompare (cell)
open Shared.Codes.FiniteProgramWriteWord (leftRows leftRow rewind rewind_word left_run)
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

/-- The generic table scans a canonical protected block, retaining its data
and marker and moving to the next cell on its left. -/
theorem scan_dataBlock (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (b marked : Bool) (L R : List Bool) :
    run (Shared.Codes.FiniteProgramProtectedScan.program width)
      (0,tapeLeft (dataBlock tm enc out marked b ++ L) R) (width+3) =
      some (.inr (state (width+3) (mask b marked),
        tapeLeft L (true::marked::((enc (cell tm out marked b)).toList ++ b::R)))) := by
  have h := Shared.Codes.FiniteProgramProtectedScan.scan_block width b marked
    (enc (cell tm out marked b)).toList.reverse L R (by simp)
  have hw := written_block tm enc dec hdec enc0 out marked b
  change dataBlock tm enc out marked b = _ at hw
  rw [hw]
  simpa [List.append_assoc] using h

/-- The scan remains valid for every blank-equivalent physical tape. -/
theorem scan_dataBlock_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (b marked : Bool) (L R : List Bool) (t : Tape)
    (ht : TapeRel t (tapeLeft (dataBlock tm enc out marked b ++ L) R)) :
    ∃ t', run (Shared.Codes.FiniteProgramProtectedScan.program width) (0,t) (width+3) =
        some (.inr (state (width+3) (mask b marked),t')) ∧
      TapeRel t' (tapeLeft L (true::marked::((enc (cell tm out marked b)).toList ++ b::R))) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related
    (Shared.Codes.FiniteProgramProtectedScan.program width) (0,t)
    (0,tapeLeft (dataBlock tm enc out marked b ++ L) R) rfl ht (width+3)
  rw [scan_dataBlock tm enc dec hdec enc0 out b marked L R] at h
  cases hr : run (Shared.Codes.FiniteProgramProtectedScan.program width) (0,t) (width+3) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = state (width+3) (mask b marked) ∧ _ at h
      refine ⟨t',?_,h.2⟩
      rw [h.1]

/-- The positioning rows move left over the blank terminator and onto the
first written data bit. -/
def positioning (width : Nat) : Program := leftRows 0 (width+4)

def positioned (width : Nat) : Program :=
  link (positioning width) (Shared.Codes.FiniteProgramProtectedScan.program width) []

@[simp] theorem positioning_length (width : Nat) : (positioning width).length = width+4 := by
  simp [positioning,Shared.Codes.FiniteProgramWriteWord.leftRows_length]

@[simp] theorem positioned_length (width : Nat) : (positioned width).length = 5*(width+4) := by
  simp [positioned,link]
  omega

private theorem leftRows_all (q n bound : Nat) (h : q+n < bound) :
    (leftRows q n).all (fun r => validRow bound r.1 && validRow bound r.2) = true := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have hnext : q+1 < bound := by omega
    have htail : q+1+n < bound := by omega
    simp only [leftRows,List.all_cons]
    rw [ih (q+1) htail]
    simp [leftRow,validRow,hnext]

/-- The positioning rows and relocated scanner together form a valid table. -/
theorem positioned_valid (width : Nat) : valid (positioned width) = true := by
  let m := (positioned width).length
  have hm : m = 5*(width+4) := by simp [m]
  have hpre : (positioning width).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    change (leftRows 0 (width+4)).all _ = true
    apply leftRows_all
    omega
  have hscanner := Shared.Codes.FiniteProgramProtectedScan.program_valid width
  have hrows : ∀ r ∈ Shared.Codes.FiniteProgramProtectedScan.program width,
      validRow (Shared.Codes.FiniteProgramProtectedScan.program width).length r.1 = true ∧
      validRow (Shared.Codes.FiniteProgramProtectedScan.program width).length r.2 = true := by
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hscanner
    intro r hr
    simpa only [Bool.and_eq_true] using hscanner.2 r hr
  have hall : (positioned width).all
      (fun r => validRow (positioned width).length r.1 && validRow (positioned width).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ positioning width ∨ r ∈
        (Shared.Codes.FiniteProgramProtectedScan.program width).map (shiftPair (positioning width).length) := by
      simpa [positioned,link,List.mem_append] using hr
    change (validRow m r.1 && validRow m r.2) = true
    rcases hr' with hp | hs
    · exact (List.all_eq_true.mp hpre) r hp
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hs
      obtain ⟨h₁,h₂⟩ := hrows r' hr'
      have hm' : m = (positioning width).length +
          (Shared.Codes.FiniteProgramProtectedScan.program width).length := by simp [hm]; omega
      rw [hm']
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 _ _ h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 _ _ h₂⟩
  have hn : (positioned width).isEmpty = false := by
    cases h : positioned width with
    | nil => have hl := positioned_length width; rw [h] at hl; simp at hl
    | cons r rs => rfl
  change (!(positioned width).isEmpty && (positioned width).all
    (fun r => validRow (positioned width).length r.1 && validRow (positioned width).length r.2)) = true
  rw [hn,hall]
  rfl

/-- Positioning takes one physical transition for each traversed cell. -/
theorem positioning_run (width : Nat) (t : Tape) :
    run (positioned width) (0,t) (width+4) =
      some (.inr (width+4,rewind (width+4) t)) := by
  have h := left_run []
    ((Shared.Codes.FiniteProgramProtectedScan.program width).map (shiftPair (width+4))) (width+4) t
  simpa [positioned,positioning,link,Shared.Codes.FiniteProgramWriteWord.leftRows_length] using h

/-- Starting immediately after the all-blank output terminator, position on
and scan the adjacent protected block in exactly `2*width+7` transitions. -/
theorem positioned_scan (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (b marked : Bool) (L : List Bool) :
    run (positioned width)
      (0,Shared.ComplexityBridge.PairMarkedScanner.tapeAt
        (List.replicate (width+3) false ++ dataBlock tm enc out marked b ++ L) [])
      ((width+4)+(width+3)) =
      some (.inr ((width+4) + state (width+3) (mask b marked),
        tapeLeft L (true::marked::((enc (cell tm out marked b)).toList ++
          b::(List.replicate (width+3) false ++ [false]))))) := by
  let payload := (enc (cell tm out marked b)).toList.reverse
  let blanks := List.replicate (width+3) false
  let rest := payload ++ [marked,true] ++ L
  let traversed := b::blanks
  have hblock : dataBlock tm enc out marked b = b::(payload ++ [marked,true]) :=
    written_block tm enc dec hdec enc0 out marked b
  have hre := rewind_word traversed rest false []
  have hpos : rewind (width+4)
      (Shared.ComplexityBridge.PairMarkedScanner.tapeAt (blanks ++ dataBlock tm enc out marked b ++ L) []) =
      tapeLeft (dataBlock tm enc out marked b ++ L) (blanks ++ [false]) := by
    rw [hblock]
    simpa [traversed,blanks,rest,Shared.ComplexityBridge.PairMarkedScanner.tapeAt,
      tapeLeft,List.reverse_cons,List.reverse_append,List.append_assoc] using hre
  have hp := positioning_run width
    (Shared.ComplexityBridge.PairMarkedScanner.tapeAt (blanks ++ dataBlock tm enc out marked b ++ L) [])
  rw [hpos] at hp
  have hs := run_shift (positioning width) (Shared.Codes.FiniteProgramProtectedScan.program width) []
    (Shared.Codes.FiniteProgramProtectedScan.program_valid width)
    (0,tapeLeft (dataBlock tm enc out marked b ++ L) (blanks ++ [false]))
    (by simp [Shared.Codes.FiniteProgramProtectedScan.program_length]) (width+3)
  rw [scan_dataBlock tm enc dec hdec enc0 out b marked L (blanks ++ [false])] at hs
  rw [run_continue _ _ _ _ _ hp]
  simpa [positioned,positioning_length,shiftConfig,shiftStatus,blanks] using hs

/-- Position and scan correctly from any blank-equivalent physical tape. -/
theorem positioned_scan_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (b marked : Bool) (L : List Bool) (t : Tape)
    (ht : TapeRel t (Shared.ComplexityBridge.PairMarkedScanner.tapeAt
      (List.replicate (width+3) false ++ dataBlock tm enc out marked b ++ L) [])) :
    ∃ t', run (positioned width) (0,t) ((width+4)+(width+3)) =
        some (.inr ((width+4)+state (width+3) (mask b marked),t')) ∧
      TapeRel t' (tapeLeft L (true::marked::((enc (cell tm out marked b)).toList ++
        b::(List.replicate (width+3) false ++ [false])))) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (positioned width) (0,t)
    (0,Shared.ComplexityBridge.PairMarkedScanner.tapeAt
      (List.replicate (width+3) false ++ dataBlock tm enc out marked b ++ L) []) rfl ht ((width+4)+(width+3))
  rw [positioned_scan tm enc dec hdec enc0 out b marked L] at h
  cases hr : run (positioned width) (0,t) ((width+4)+(width+3)) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = (width+4)+state (width+3) (mask b marked) ∧ _ at h
      refine ⟨t',?_,h.2⟩
      rw [h.1]

end Shared.ComplexityBridge.TM2OutputProtectedScan
