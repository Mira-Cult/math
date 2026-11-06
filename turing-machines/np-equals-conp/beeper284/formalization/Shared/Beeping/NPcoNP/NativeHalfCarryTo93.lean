import Shared.Beeping.NPcoNP.NativeHalfCarryTo83

/-! The prepared exceptional HALF path through the complete selector scan,
under an explicit zero tail in the supplied protected prefix. This does not
establish that the prepared boundary is reached from the blank tape. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCarryTo93
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfCarryTo83

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A left zero tail completes all 14 selector scans; the one just right of
state 83's head then completes the final rightward scan. Tape is preserved. -/
theorem state83_to_93 (h z : Int) (t : Int → Bool)
    (hz : ∀ q ≤ z, t q=false) (hmark : t (h+1)=true) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state=93 ∧ e.tape=t ∧
      silentSegment machine (cfg 83 h t) e n := by
  obtain ⟨m,hm,hchain⟩ := chain_progress chain83 t z hz h
  let k := m+1
  have hpos : h-(m : Int)+(k : Int)=h+1 := by dsimp [k]; push_cast; omega
  have hm' : t (h-(m : Int)+(k : Int))=true := by rw [hpos]; exact hmark
  obtain ⟨n,hn,_,hscan⟩ := scan92_to_one k (h-(m : Int)) t hm'
  refine ⟨m+n,cfg 93 (h-(m : Int)+(n : Int)) t,by omega,rfl,rfl,?_⟩
  exact segAdd machine _ _ _ m n hchain hscan

/-- Under a supplied zero tail in the protected prefix and a finite carry,
the exceptional state-30 path reaches state 93 silently with its carry
marker and more distant prefix intact. -/
theorem exceptional_through_93 (back : Int → Bool) (gap : Int)
    (left values : List Nat) (k : Nat)
    (hm : downHolds back (gap-1) (List.replicate k true ++ [false]))
    (z : Int) (hz : ∀ q ≤ z, back q=false) :
    let suffix := leftSuffix left
    let base := before back gap suffix
    let b := gap+1+(suffix.length : Int)
    let p := gap-1-(k : Int)
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state=93 ∧ e.tape p=true ∧
      (∀ q, q < p → e.tape q=back q) ∧
      silentSegment machine (cfg 30 b (prior base b (false :: UnaryBank.encode values))) e n := by
  dsimp only
  let p := gap-1-(k : Int)
  obtain ⟨m,c,hmpos,hstate,hmarker,hfound,hprefix,hseg⟩ :=
    exceptional_through_83 back gap left values k hm
  have htail : ∀ q ≤ min z (p-1), c.tape q=false := by
    intro q hq
    have hzq : q ≤ z := le_trans hq (min_le_left _ _)
    have hpq : q < p := by have := le_trans hq (min_le_right z (p-1)); omega
    rw [hprefix q hpq]
    exact hz q hzq
  obtain ⟨n,e,hn,hstate',htape,hcont⟩ :=
    state83_to_93 c.head (min z (p-1)) c.tape htail hfound
  have hcfg : c = cfg 83 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hstate] using he
  have hseg' : silentSegment machine c e n := by simpa [← hcfg] using hcont
  refine ⟨m+n,e,by omega,hstate',?_,?_,?_⟩
  · rw [htape]; exact hmarker
  · intro q hq; rw [htape]; exact hprefix q hq
  · exact segAdd machine _ _ _ m n hseg hseg'

end Shared.Beeping.NPcoNP.NativeHalfCarryTo93
