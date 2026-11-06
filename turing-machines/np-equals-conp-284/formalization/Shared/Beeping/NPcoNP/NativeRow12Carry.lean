import Shared.Beeping.NPcoNP.NativeRow11LongCarry
import Shared.Beeping.NPcoNP.NativeBeepZeroReturn
import Shared.Beeping.NPcoNP.NativeSelectorParserGeneric

/-! State-1 carry after the physical row-12 increment. -/
namespace Shared.Beeping.NPcoNP.NativeRow12Carry
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
open Shared.Beeping.NPcoNP.NativeRow11LongCarry
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

def nextPath : List Bool := [true,true,false,true,true,false,false,true,true,true,true,true,false,false]

theorem next_path_walk : PreparedWalk nextPath (.op "3.$native-half:$coalesced.0.decnz") := by
  refine ⟨[true,true,false,false,true,true,true,true,true,false,false],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,true,true,true,true,false,false] (.node producerGrammar.root)
  decide

theorem next_selector (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) nextPath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+6) t) (cfg 93 (h-3) t) 35 := by
  have hv := word
  simp only [nextPath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,_,_,_,_⟩ := hv
  let ks : List Nat := [4,0,2,2] ++ List.replicate 10 0
  have hw : downHolds t (h+6) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | (convert a4 using 1 <;> congr 1 <;> omega) | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert b6 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hs := selector_to_parser t (h+6) (h-4) ks nextPath
    "3.$native-half:$coalesced.0.decnz" (by decide) hw (by simp [ks,blocks]; omega)
    left a4 next_path_walk word
  have hd : (h-4-(h+6-22)).toNat=12 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,nextPath,hd,he] using hs.2.1

/-- The increment's supplied control frame completes the carry and selector,
preserving its entire bank suffix and leaving the next parsed path. -/
theorem carry_to_next (h separator bound : Int) (t : Int → Bool)
    (hlong : h+14≤separator) (path : Holds t (h-4) zeroPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false) (h11 : t (h+11)=true)
    (control : ∀ q, h+12≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, bound≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) nextPath ∧
      parseForward 52 out (h-4)=some ("3.$native-half:$coalesced.0.decnz",14) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+7<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+8) t) (cfg 93 (h-3) out) n := by
  have hv := path
  simp only [zeroPath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,b8,_⟩ := hv
  have h7 : t (h+7)=false := by convert b7 using 1 <;> congr 1 <;> omega
  have h8 : t (h+8)=true := by convert b8 using 1 <;> congr 1 <;> omega
  let u := put t (h+8) false
  have hu7 : u (h+7)=false := by simpa [u,put] using h7
  have hu8 : u (h+8)=false := by simp [u,put]
  have hu9 : u (h+9)=false := by simpa [u,put] using h9
  have hu10 : u (h+10)=false := by simpa [u,put] using h10
  have hu11 : u (h+11)=true := by simpa [u,put] using h11
  have huright : ∀ q, max bound (h+9)≤q → u q=false := by
    intro q hq
    have hb : bound≤q := le_trans (le_max_left _ _) hq
    have hn : q≠h+8 := by have hh := le_trans (le_max_right _ _) hq; omega
    simpa [u,put,hn] using right q hb
  obtain ⟨n,out,hit,stop,hn,hmark,hframe,_,hclear,hhit,hhitp,hhitstop,
      hhitOne,hstopOne,hstopZero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear (h+7) (h+11) (max bound (h+9)) u hu7 (by omega) hu11 huright
  have hhitge : h+11≤hit := by
    by_contra ht
    have he : hit=h+8 ∨ hit=h+9 ∨ hit=h+10 := by omega
    rcases he with he | he | he
    · rw [he,hu8] at hhitOne; contradiction
    · rw [he,hu9] at hhitOne; contradiction
    · rw [he,hu10] at hhitOne; contradiction
  have hstopLt : stop<separator := by
    by_contra ht
    have ho := hones separator (by omega) (by omega)
    have husep : u separator=false := by simpa [u,put,show separator≠h+8 by omega] using sep
    rw [husep] at ho
    contradiction
  have hstopEq : stop+1=separator := by
    by_contra ht
    have ho := control (stop+1) (by omega) (by omega)
    have hu : u (stop+1)=true := by simpa [u,put,show stop+1≠h+8 by omega] using ho
    rw [hstopZero] at hu
    contradiction
  have hleft : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    simpa [u,put,show q≠h+8 by omega] using left q hq
  have hprefix : ∀ q, q<h+7 → out q=t q := by
    intro q hq
    rw [hframe q hq]
    simp [u,put,show q≠h+8 by omega]
  have hgap : ∀ q, h+7<q → q<separator-1 → out q=false := by
    intro q hq hq'
    exact hclear q hq (by omega)
  have hpath : Holds out (h-4) nextPath := by
    have before : Holds out (h-4) [true,true,false,true,true,false,false,true,true,true,true] := by
      have ht : Holds t (h-4) [true,true,false,true,true,false,false,true,true,true,true] := by
        apply holds_prefix_word t (h-4) [true,true,false,true,true,false,false,true,true,true,true] [false,true]
        simpa [zeroPath] using path
      apply holds_transport t out _ _ ht
      intro q hq hq'
      exact (hprefix q (by simp at hq'; omega)).symm
    have after : Holds out (h+7) [true,false,false] := by
      change out (h+7)=true ∧ out (h+7+1)=false ∧ out (h+7+1+1)=false ∧ True
      have ha : out (h+8)=false := hgap _ (by omega) (by omega)
      have hb : out (h+9)=false := hgap _ (by omega) (by omega)
      simpa only [show h+7+1=h+8 by omega,show h+7+1+1=h+9 by omega,show h+8+1=h+9 by omega] using And.intro hmark (And.intro ha (And.intro hb True.intro))
    have hall := NativeIncBank.holds_append_intro out (h-4)
      [true,true,false,true,true,false,false,true,true,true,true] [true,false,false] before
      (by simpa only [show ([true,true,false,true,true,false,false,true,true,true,true] : List Bool).length=11 by decide,Nat.cast_ofNat,show h-4+11=h+7 by omega] using after)
    simpa [nextPath] using hall
  have hparse : parseForward 52 out (h-4)=some ("3.$native-half:$coalesced.0.decnz",14) := by
    exact (parseForward_iff out (h-4) _ 14).2 ⟨nextPath,next_path_walk,rfl,hpath⟩
  have hmarker : out (separator-1)=true := by
    have he : separator-1=stop := by omega
    rw [he,hsuffix stop (le_refl _)]
    exact hstopOne
  have hright : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hsuffix q (by omega)]
    simp [u,put,show q≠h+8 by omega]
  have first := oneSeg machine _ _ (step_one (h+8) t h8)
  have first' : silentSegment machine (cfg 1 (h+8) t) (cfg 1 (h+7) u) 1 := by
    simpa only [show h+8-1=h+7 by omega,u] using first
  have hs' : silentSegment machine (cfg 1 (h+7) u) (cfg 83 (h+6) out) n := by
    simpa only [show h+7-1=h+6 by omega] using hseg
  exact ⟨1+n+35,out,by omega,hpath,hparse,hleft,hgap,hmarker,hright,
    segAdd machine _ _ _ (1+n) 35 (segAdd machine _ _ _ 1 n first' hs') (next_selector h out hpath hleft)⟩

#print axioms next_path_walk
#print axioms next_selector
#print axioms carry_to_next
end Shared.Beeping.NPcoNP.NativeRow12Carry
