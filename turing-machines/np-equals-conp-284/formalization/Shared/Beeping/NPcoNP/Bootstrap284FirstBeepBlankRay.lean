import Shared.Beeping.NPcoNP.Bootstrap284TerminalMarkerBlankRay
import Shared.Beeping.NPcoNP.Bootstrap284TerminalMarker
import Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn
import Shared.Beeping.NPcoNP.Table284Flags
import Shared.Beeping.NPcoNP.NativeTerminalMarkerGeometry

/-! First literal-table beep from the genuine blank-start configuration. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284FirstBeepBlankRay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeTerminalMarkerFill
open Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn
open Shared.Beeping.NPcoNP.NativeTerminalMarkerGeometry
open Shared.Beeping.NPcoNP.Bootstrap284TerminalMarker
open Shared.Beeping.NPcoNP.Bootstrap284TerminalMarkerBlankRay
open Shared.Beeping.NPcoNP.NativeShortStageBlankRay
open Shared.Beeping.NPcoNP.NativeShortCycleStage
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000

/-- The finite blank-start run reaches the pre-transition state for the first
beep, and every preceding transition in this prefix is silent. -/
theorem blank_start_reaches_first_beep_with_blank_ray :
    ∃ (n : Nat) (out : Int → Bool), out (-3817)=true ∧
      out (-3821)=true ∧ out (-3820)=true ∧ out (-3819)=false ∧ out (-3818)=false ∧
      out (-3816)=false ∧ out (-3814)=true ∧ out 4=false ∧
      Holds out 5 ((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])) ++
        [true,false,false]) ++ List.replicate 76 false) ∧
      (∀ q, q< -3821 → out q=false) ∧ out (-3815)=false ∧
      (∀ q, -3814≤q → q<4 → out q=true) ∧
      ZeroRay (-3820) 0 3813 0
        ((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]) out ∧
      silentSegment machine (machine.system.run 0) (cfg 99 (-3817) out) n := by
  obtain ⟨n,t,hn,hleft0,hleft1,hray,hmark,hcorr,hstop,hdelim,hbank,hblankTail,hfirst⟩ :=
    blank_start_terminal_marker_with_ray
  have hround := terminal_marker_roundtrip t (-3820) 3817 (by decide) (by simpa using hray) (by simpa using hleft0) (by simpa using hleft1) hmark
    (by simpa using hcorr) (by simpa using hstop)
  norm_num only at hround
  let out := fillRange (setAt (-3817) t) (-3814) 3
  have hround' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 7670 ∧
      out (-3820)=true ∧ out (-3819)=false ∧ out (-3818)=false ∧ out (-3817)=true := by
    simpa only [out] using hround
  obtain ⟨hreturn,h0,h1,h2,h3⟩ := hround'
  have hput : put out (-3819) false=out := by
    funext q
    by_cases hq : q= -3819
    · subst q; simp [put,h1]
    · simp [put,hq]
  have hs1 := oneSeg machine _ _ (step93_one (-3820) out h0)
  have hs2 : silentSegment machine (cfg 94 (-3819) out) (cfg 259 (-3818) out) 1 := by
    simpa only [hput,show (-3819:Int)+1= -3818 by norm_num] using oneSeg machine _ _ (step94 (-3819) out)
  have hs3 : silentSegment machine (cfg 259 (-3818) out) (cfg 99 (-3817) out) 1 := by
    simpa using oneSeg machine _ _ (step259_zero (-3818) out h2)
  have hend : silentSegment machine (cfg 93 (-3820) out) (cfg 99 (-3817) out) 3 := by
    exact segAdd machine _ _ _ 2 1 (segAdd machine _ _ _ 1 1 hs1 hs2) hs3
  have hall := segAdd machine _ _ _ n (7670+3) hfirst
    (segAdd machine _ _ _ 7670 3 hreturn hend)
  have hpre : out (-3821)=true := by
    simpa [out,fillRange,setAt] using hleft1
  have hafter : out (-3816)=false := by
    have hh := hcorr (-3816) (by omega) (by omega)
    simpa [out,fillRange,setAt] using hh
  have hmark' : out (-3814)=true := by simp [out,fillRange]
  have hsep : out 4=false := by simpa [out,fillRange,setAt] using hdelim
  have hframe : ∀ q, 5≤q → out q=t q := by
    intro q hq
    simp [out,fillRange,setAt,show ¬(-3814≤q ∧ q<3) by omega,show q≠ -3817 by omega]
  have hright : ZeroRay (-3820) 0 3813 0
      ((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]) out := by
    intro q hq
    have hq5 : 5≤q := by
      change 5+((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]))).length : Int)+1≤q at hq
      have hn : 0≤((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]))).length : Int) := by omega
      omega
    rw [hframe q hq5]
    exact hblankTail q hq
  have hbankfull : Holds out 5 ((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])) ++
      [true,false,false]) ++ List.replicate 76 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    exact (hframe q hq).symm
  have hzero : t (-3815)=false := hcorr _ (by omega) (by omega)
  have hgeo := terminal_fill_full_geometry t (-3820) 3817
    (by simpa using hray) (by simpa using hleft0) (by simpa using hzero)
  norm_num only at hgeo
  have hgeo' : (∀ q, q< -3821 → out q=false) ∧ out (-3815)=false ∧
      (∀ q, -3814≤q → q<3 → out q=true) := by
    simpa only [out] using hgeo
  have hstop' : out 3=true := by simpa [out,fillRange,setAt] using hstop
  have hallones : ∀ q, -3814≤q → q<4 → out q=true := by
    intro q hq hq'
    by_cases he : q=3
    · simpa only [he] using hstop'
    · exact hgeo'.2.2 q hq (by omega)
  exact ⟨n+(7670+3),out,h3,hpre,h0,h1,h2,hafter,hmark',hsep,hbankfull,
    hgeo'.1,hgeo'.2.1,hallones,hright,hall⟩


#print axioms blank_start_reaches_first_beep_with_blank_ray
end Shared.Beeping.NPcoNP.Bootstrap284FirstBeepBlankRay
