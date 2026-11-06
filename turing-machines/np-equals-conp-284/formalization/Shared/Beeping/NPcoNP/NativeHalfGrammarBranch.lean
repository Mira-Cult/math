import Shared.Beeping.NPcoNP.NativeHalfParityControl
import Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser

/-! A layout-conditioned bridge from paid physical HALF returns to the pinned
producer grammar's bounded parser. The parser is a mathematical observer of
a supplied tape accessor, not a proved physical parser or graph simulation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfGrammarBranch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryTo93
open Shared.Beeping.NPcoNP.NativeHalfCarryTo93
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfParityControl
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284TapeLeafUnique
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- A descending word strictly below a preserved boundary is unchanged. -/
theorem downHolds_of_left_frame (back out : Int → Bool) (p h : Int) (xs : List Bool)
    (hp : h<p) (frame : ∀ q<p, out q=back q) (word : downHolds back h xs) :
    downHolds out h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons b xs ih =>
    change back h=b ∧ downHolds back (h-1) xs at word
    change out h=b ∧ downHolds out (h-1) xs
    exact ⟨(frame h hp).trans word.1, ih (h-1) (by omega) word.2⟩

/-- A descending concatenation contains its first word. -/
theorem downHolds_prefix (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (word : downHolds t h (xs++ys)) : downHolds t h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons b xs ih =>
    simp only [List.cons_append,downHolds] at word ⊢
    exact ⟨word.1,ih (h-1) word.2⟩

/-- The selected HALF entry reaches the parity-specific state-83 return,
preserving both overlapping prepared paths and its bank postcondition. -/
theorem half_return_to83_overlapping_paths (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (evenPath suffix : List Bool)
    (oddName evenName : String) (hz : ∀ q≤z, back q=false)
    (separator : back (ctrl-1)=false)
    (code : downHolds back (ctrl-2) (preparedPrefix ++ evenPath ++ suffix))
    (oddWalk : PreparedWalk (preparedPrefix ++ evenPath ++ suffix) (.op oddName))
    (evenWalk : PreparedWalk evenPath (.op evenName)) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let oddPath := preparedPrefix ++ evenPath ++ suffix
    ∃ (n : Nat) (p : Int) (e : Config 284), 0<n ∧ e.state=83 ∧ e.head=p-1 ∧
      (value%2=1 → p=ctrl-1) ∧ (value%2=0 → p=ctrl-4) ∧
      (e.tape (ctrl-1)=true ↔ value%2=1) ∧ e.tape p=true ∧
      (value%2=1 → parsePreparedTape 52 e.tape (p-1)=some (oddName,oddPath.length)) ∧
      (value%2=0 → parsePreparedTape 52 e.tape (p-1)=some (evenName,evenPath.length)) ∧
      (∀ q<p, e.tape q=back q) ∧
      (∃ (head : Int) (k : Nat), p=head-(k : Int) ∧
        BankPost back ctrl value left right head k e.tape) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right)) e n := by
  dsimp only
  let base := before back ctrl (leftSuffix left)
  let b := ctrl+2+((leftSuffix left).length : Int)
  let oddPath := preparedPrefix ++ evenPath ++ suffix
  obtain ⟨m,p,c,hm,hstate,hhead,hcarry,hmarker,hfound,hprefix,hseg⟩ :=
    selected_entry_to83 back ctrl z value left right hz
  obtain ⟨head,k,t,stop,hp,hodd,heven,hstop,hones,hword,hbank,hcanonical,
    htprefix,hstopFirst,hrightFrame,hphysicalBank,hexact⟩ := hcarry
  have hpost : BankPost back ctrl value left right head k c.tape :=
    ⟨t,stop,hbank,hcanonical,htprefix,hstopFirst,hrightFrame,hphysicalBank,hexact⟩
  obtain ⟨hoddpos,_hevenpos,hbit⟩ :=
    parity_from_bankPost back ctrl value left right head k p c.tape separator hp hodd heven hword hmarker hpost
  have hcarry2 : downHolds back (ctrl-2) (List.replicate 2 true ++ [false]) := by
    have hc := code
    simp only [preparedPrefix,List.cons_append,downHolds] at hc
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,downHolds]
    exact ⟨hc.1,hc.2.1,hc.2.2.1,trivial⟩
  have hevenpos : value%2=0 → p=ctrl-4 := by
    intro hv
    have hbound := heven hv
    have hh : head=ctrl-2 := by
      by_contra hn
      have ht := hones hv (ctrl-1) (by omega) (by omega)
      rw [separator] at ht
      contradiction
    have hk : k=2 := by
      apply carry_length_unique back (ctrl-2) k 2
      · simpa only [hh] using hword
      · exact hcarry2
    rw [hh,hk] at hp
    norm_num only [Nat.cast_ofNat] at hp
    omega
  have htail := down_tail back (ctrl-2) preparedPrefix (evenPath++suffix) (by
    simpa [List.append_assoc] using code)
  have hevenword : downHolds back (ctrl-5) evenPath := by
    have hh := downHolds_prefix back (ctrl-2-(preparedPrefix.length : Int)) evenPath suffix htail
    have he : ctrl-2-((preparedPrefix.length : Nat):Int)=ctrl-5 := by simp [preparedPrefix]; omega
    simpa only [he] using hh
  have hoddparse : value%2=1 → parsePreparedTape 52 c.tape (p-1)=some (oddName,oddPath.length) := by
    intro hv
    have hp' := hoddpos hv
    have hw : downHolds c.tape (p-1) oddPath := by
      apply downHolds_of_left_frame back c.tape p (p-1) oddPath (by omega) hprefix
      simpa only [hp',show ctrl-1-1=ctrl-2 by omega,oddPath] using code
    exact (parsePreparedTape_iff c.tape (p-1) oddName oddPath.length).2 ⟨oddPath,oddWalk,rfl,hw⟩
  have hevenparse : value%2=0 → parsePreparedTape 52 c.tape (p-1)=some (evenName,evenPath.length) := by
    intro hv
    have hp' := hevenpos hv
    have hw : downHolds c.tape (p-1) evenPath := by
      apply downHolds_of_left_frame back c.tape p (p-1) evenPath (by omega) hprefix
      simpa only [hp',show ctrl-4-1=ctrl-5 by omega] using hevenword
    exact (parsePreparedTape_iff c.tape (p-1) evenName evenPath.length).2 ⟨evenPath,evenWalk,rfl,hw⟩
  exact ⟨m,p,c,hm,hstate,hhead,hoddpos,hevenpos,hbit,hmarker,hoddparse,hevenparse,hprefix,
    ⟨head,k,hp,hpost⟩,hseg⟩


/-- If one supplied control word contains both valid prepared grammar paths
in the stated overlap, the literal HALF return exposes the correct path for
each parity. The odd marker is at `ctrl-1`; the even marker is at `ctrl-4`.
All transitions through the following selector scan are finite and silent.
The grammar walks and initial control-word placement are explicit hypotheses. -/
theorem half_return_parses_overlapping_paths (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (evenPath suffix : List Bool)
    (oddName evenName : String) (hz : ∀ q≤z, back q=false)
    (separator : back (ctrl-1)=false)
    (code : downHolds back (ctrl-2) (preparedPrefix ++ evenPath ++ suffix))
    (oddWalk : PreparedWalk (preparedPrefix ++ evenPath ++ suffix) (.op oddName))
    (evenWalk : PreparedWalk evenPath (.op evenName)) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let oddPath := preparedPrefix ++ evenPath ++ suffix
    ∃ (n : Nat) (p : Int) (e : Config 284), 0<n ∧ e.state=93 ∧
      (value%2=1 → p=ctrl-1) ∧ (value%2=0 → p=ctrl-4) ∧
      (e.tape (ctrl-1)=true ↔ value%2=1) ∧ e.tape p=true ∧
      (value%2=1 → parsePreparedTape 52 e.tape (p-1)=some (oddName,oddPath.length)) ∧
      (value%2=0 → parsePreparedTape 52 e.tape (p-1)=some (evenName,evenPath.length)) ∧
      (∀ q<p, e.tape q=back q) ∧
      (∃ (head : Int) (k : Nat), p=head-(k : Int) ∧
        BankPost back ctrl value left right head k e.tape) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right)) e n := by
  dsimp only
  let base := before back ctrl (leftSuffix left)
  let b := ctrl+2+((leftSuffix left).length : Int)
  obtain ⟨m,p,c,hm,hstate,hhead,hoddpos,hevenpos,hbit,hmarker,hoddparse,hevenparse,hprefix,hpost,hseg⟩ :=
    half_return_to83_overlapping_paths back ctrl z value left right evenPath suffix oddName evenName
      hz separator code oddWalk evenWalk
  have hfound : c.tape (c.head+1)=true := by rw [hhead]; simpa using hmarker
  have hleft : ∀ q≤min z (p-1), c.tape q=false := by
    intro q hq
    have hzq : q≤z := le_trans hq (min_le_left _ _)
    have hpq : q<p := by have := le_trans hq (min_le_right z (p-1)); omega
    rw [hprefix q hpq]
    exact hz q hzq
  obtain ⟨n,e,hn,hstate',htape,hcont⟩ :=
    state83_to_93 c.head (min z (p-1)) c.tape hleft hfound
  have hcfg : c=cfg 83 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hstate] using he
  have hseg' : silentSegment machine c e n := by simpa [← hcfg] using hcont
  refine ⟨m+n,p,e,by omega,hstate',hoddpos,hevenpos,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htape]; exact hbit
  · rw [htape]; exact hmarker
  · intro hv; rw [htape]; exact hoddparse hv
  · intro hv; rw [htape]; exact hevenparse hv
  · intro q hq; rw [htape]; exact hprefix q hq
  · rw [htape]; exact hpost
  · exact segAdd machine _ _ _ m n hseg hseg'

#print axioms half_return_to83_overlapping_paths
#print axioms half_return_parses_overlapping_paths
end Shared.Beeping.NPcoNP.NativeHalfGrammarBranch
