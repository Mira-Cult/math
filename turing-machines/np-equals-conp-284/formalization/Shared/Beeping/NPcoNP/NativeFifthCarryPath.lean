import Shared.Beeping.NPcoNP.NativeFifthNextPath

/-! The state-1 carry to the next positive-branch prepared path. -/
namespace Shared.Beeping.NPcoNP.NativeFifthCarryPath
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- Given the fifth path and its supplied control gap, state 1 reaches the
sixth path, preserving the complete suffix from the separator. -/
theorem carry_to_sixth_path (h b separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (hw : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h7 : t (h+7)=false) (h8 : t (h+8)=false)
    (control : ∀ q, h+9≤q → q<separator → t q=true)
    (hsep : t separator=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+6) t) (cfg 93 (h-3) out) n := by
  have hv := hw
  simp only [fifthPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,hp5,hp6,_⟩ := hv
  have hm4' : t (h-4)=true := hm4
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=true := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=true := by convert hp4 using 1 <;> congr 1 <;> omega
  have hp5' : t (h+5)=false := by convert hp5 using 1 <;> congr 1 <;> omega
  have hp6' : t (h+6)=false := by convert hp6 using 1 <;> congr 1 <;> omega
  have hp9 : t (h+9)=true := control _ (by omega) (by omega)
  obtain ⟨n,out,hit,stop,hn,hmark,hframe,_hzero,hclear,hhit,hhitp,hhitstop,
      hhitOne,hstopOne,hstopZero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear (h+6) (h+9) b t hp6' (by omega) hp9 right
  have hhitge : h+9≤hit := by
    by_contra hn'
    have he : hit=h+7 ∨ hit=h+8 := by omega
    rcases he with he | he
    · rw [he,h7] at hhitOne; contradiction
    · rw [he,h8] at hhitOne; contradiction
  have hstopLt : stop<separator := by
    by_contra hn'
    have ho := hones separator (by omega) (by omega)
    rw [hsep] at ho
    contradiction
  have hstopEq : stop+1=separator := by
    by_contra hn'
    have ho := control (stop+1) (by omega) (by omega)
    rw [hstopZero] at ho
    contradiction
  have hleft : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have a4 : out (h-4)=true := by rw [hframe _ (by omega)]; exact hm4'
  have a3 : out (h-3)=true := by rw [hframe _ (by omega)]; exact hm3'
  have a2 : out (h-2)=false := by rw [hframe _ (by omega)]; exact hm2'
  have a1 : out (h-1)=true := by rw [hframe _ (by omega)]; exact hm1'
  have a0 : out h=true := by rw [hframe _ (by omega)]; exact h0'
  have b1 : out (h+1)=false := by rw [hframe _ (by omega)]; exact hp1'
  have b2 : out (h+2)=false := by rw [hframe _ (by omega)]; exact hp2'
  have b3 : out (h+3)=true := by rw [hframe _ (by omega)]; exact hp3'
  have b4 : out (h+4)=true := by rw [hframe _ (by omega)]; exact hp4'
  have b5 : out (h+5)=false := by rw [hframe _ (by omega)]; exact hp5'
  have hgap : ∀ q, h+6<q → q<separator-1 → out q=false := by
    intro q hq hq2
    exact hclear q hq (by omega)
  have hpath : Holds out (h-4) sixthPath := by
    dsimp [sixthPath,Holds]
    repeat' constructor
    all_goals first | exact a4 | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert hmark using 1 <;> congr 1 <;> omega) | (apply hgap <;> omega)
  have hselector := sixth_selector h out hpath hleft
  have hseg' : silentSegment machine (cfg 1 (h+6) t) (cfg 83 (h+5) out) n := by
    have he : h+6-1=h+5 := by omega
    simpa only [he] using hseg
  have hall := segAdd machine _ _ _ n 32 hseg' hselector
  refine ⟨n+32,out,by omega,hpath,sixth_path_parse out (h-4) hpath,hleft,hgap,?_,?_,?_⟩
  · have he : separator-1=stop := by omega
    rw [he,hsuffix stop (le_refl _)]
    exact hstopOne
  · intro q hq
    exact hsuffix q (by omega)
  · exact hall

#print axioms carry_to_sixth_path
end Shared.Beeping.NPcoNP.NativeFifthCarryPath
