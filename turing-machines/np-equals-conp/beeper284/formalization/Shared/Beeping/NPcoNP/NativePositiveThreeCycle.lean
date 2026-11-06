import Shared.Beeping.NPcoNP.NativeManyTerminalWindow
import Shared.Beeping.NPcoNP.NativeThreeCarryNextWindow

/-! Connect the positive terminal selector to the exact three-one return.
The input is an explicitly supplied tape layout, not an all-run invariant. -/
namespace Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeThreeCarryNextWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 15000000
attribute [local irreducible] machine

/-- The return does not alter the tape at or beyond the supplied run's
right delimiter. Positivity is needed to put that ray past the first clear. -/
theorem return_output_right (d : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (hr : 0<r) (hq : d+2+(r : Int)≤q) : outTape d r t q=t q := by
  change put (clearRange (scanTape d t) (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true q=t q
  rw [put_other _ _ _ _ (by omega)]
  change (if d+3≤q ∧ q<d+2+(r : Int) then false else scanTape d t q)=t q
  rw [if_neg (by omega)]
  change put (carryTape d t) (d+2) false q=t q
  rw [put_other _ _ _ _ (by omega)]
  change put (cleared t (d-1) 3) ((d-1)-((3 : Nat):Int)) true q=t q
  rw [put_other _ _ _ _ (by omega)]
  change (if (d-1)-((3 : Nat):Int)<q ∧ q≤d-1 then false else t q)=t q
  rw [if_neg (by omega)]

def bankSuffix (w : Nat) (rest : List Nat) : List Bool :=
  List.replicate w true ++ rest.flatMap (fun z => false :: List.replicate (z+1) true)

def selectorOutput (a : Int) (r w : Nat) (rest : List Nat) (t : Int → Bool) : Int → Bool :=
  spec (clearAt (a+30) t)
    (a+36+(r : Int)+2+((bankSuffix w rest).length : Int)) ((bankSuffix w rest).length+2)

/-- A positive terminal selector and its independently delimited bank
complete the selector operation and exact return, producing the next all-zero
window. The earlier-marker cell is preserved; it need not be true. -/
theorem positive_three_cycle (a : Int) (r w : Nat) (rest : List Nat) (t : Int → Bool)
    (oldWindow : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (left1 : t (a-1)=true)
    (window : Holds t (a+2) (markerWindow (List.replicate 12 0 ++ [3,r])))
    (extension : Holds t (a+33+(r : Int)) (List.replicate 2 true ++ [false]))
    (bank : Holds t (a+36+(r : Int)) (encode ((w+1)::rest) ++ [false,false])) :
    let out := selectorOutput a r w rest t
    let final := outTape (a+30) (r+3) out
    silentSegment machine (cfg 83 (a+32+(r : Int)) t) (cfg 83 (a+25) final)
      ((2*r+74+2*(bankSuffix w rest).length)+(3*(r+3)+18)) ∧
    Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
    final (a-3)=t (a-3) ∧ final (a+26)=true ∧
    Holds final (a+36+(r : Int)) (encode (w::rest) ++ [true,false,false]) := by
  dsimp only
  let base := a+36+(r : Int)
  let suffix := bankSuffix w rest
  let out := selectorOutput a r w rest t
  let final := outTape (a+30) (r+3) out
  have hlen : (encode (List.replicate 12 0 ++ [3,r])).length=r+31 := by
    simp [encode_append,encode,block_length,zeros_length]
    omega
  have hmark := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) oldWindow 1 (by decide)
  have hb1 : (markerWindow (List.replicate 13 0 ++ [0]))[1]=true := by decide
  rw [hb1] at hmark
  have hmarker : t (a+2-1)=true := by
    have hp : a+2-1=a+1 := by omega
    rw [hp]
    simpa using hmark
  have hext : Holds t (a+2+((encode (List.replicate 12 0 ++ [0+3,r])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    change Holds t (a+2+((encode (List.replicate 12 0 ++ [3,r])).length : Int)) _
    rw [hlen]
    have hp : a+2+((r+31 : Nat):Int)=a+33+(r : Int) := by push_cast; omega
    rw [hp]
    exact extension
  have hbank : Holds t (a+2+((2*12 : Nat):Int)+4+(0:Int)+(r:Int)+(2:Int)+4)
      (encode ((w+1)::rest) ++ [false,false]) := by
    have hp : a+2+((2*12 : Nat):Int)+4+(0:Int)+(r:Int)+(2:Int)+4=base := by
      dsimp [base]; push_cast; omega
    rw [hp]
    exact bank
  have hsel := terminal_selector_to_bank t (a+2) 12 0 r 2 w rest
    (by simp) hmarker window hext hbank
  dsimp only at hsel
  have hd : a+2+((2*12 : Nat):Int)+4=a+30 := by norm_num; omega
  rw [hd] at hsel
  simp only [Nat.cast_zero,Nat.cast_ofNat] at hsel
  have hx : a+30+(0:Int)+(r:Int)+(2:Int)+4=base := by dsimp [base]; omega
  rw [hx] at hsel
  obtain ⟨houtbank,hframe,hentry⟩ := hsel
  have hframe' : ∀ q, q≠a+30 → (q<base ∨ base+2+((suffix.length : Nat):Int)<q) → out q=t q := by
    simpa only [out,selectorOutput,base,suffix,bankSuffix] using hframe
  have hbankout : Holds out base (encode (w::rest) ++ [true,false,false]) := by
    simpa only [out,selectorOutput,base,suffix,bankSuffix] using houtbank
  have hentry' : silentSegment machine (cfg 83 (a+32+(r : Int)) t) (cfg 23 (a+34+(r : Int)) out)
      (2*r+74+2*suffix.length) := by
    rw [hlen] at hentry
    have hp : a+2+((r+31 : Nat):Int)-1=a+32+(r : Int) := by push_cast; omega
    have hh : base-2=a+34+(r : Int) := by dsimp [base]; omega
    have hc : (r+31)+1+(2*12+0+r+2+
        2*(List.replicate w true ++ rest.flatMap (fun z => false :: List.replicate (z+1) true)).length+16)=
        2*r+74+2*suffix.length := by
      dsimp [suffix,bankSuffix]
      omega
    rw [hp,hh,hc] at hentry
    simpa only [out,selectorOutput,base,suffix,bankSuffix] using hentry
  have hbelow : ∀ q, q≠a+30 → q<base → out q=t q := by
    intro q hne hq
    exact hframe' q hne (Or.inl hq)
  have hold : Holds out a (markerWindow (List.replicate 13 0 ++ [0])) := by
    apply holds_transport t out _ _ oldWindow
    intro q hq hq'
    have hwlen : (markerWindow (List.replicate 13 0 ++ [0])).length=28 := by decide
    rw [hwlen] at hq'
    exact (hbelow q (by omega) (by dsimp [base]; omega)).symm
  have hleft0 : out (a-2)=false := by rw [hbelow _ (by omega) (by dsimp [base]; omega)]; exact left0
  have hleft1 : out (a-1)=true := by rw [hbelow _ (by omega) (by dsimp [base]; omega)]; exact left1
  have hw := window
  rw [terminal_many_window 12 0 r] at hw
  have hblock := holds_append_tail t (a+2+1) (encode (List.replicate 12 0))
    (block (0+3) ++ List.replicate (r+1) true) hw.2
  have hpblock : a+2+1+((encode (List.replicate 12 0)).length : Int)=a+27 := by
    rw [zeros_length]
    norm_num
    omega
  rw [hpblock] at hblock
  have hb := holds_prefix_word t (a+27) (block 3) (List.replicate (r+1) true) hblock
  simp only [block,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at hb
  have hc2 : t (a+28)=true := by
    have hp : a+27+1=a+28 := by omega
    simpa only [hp] using hb.2.1
  have hc3 : t (a+29)=true := by
    have hp : a+27+1+1=a+29 := by omega
    simpa only [hp] using hb.2.2.1
  have hc2' : out (a+28)=true := by rw [hbelow _ (by omega) (by dsimp [base]; omega)]; exact hc2
  have hc3' : out (a+29)=true := by rw [hbelow _ (by omega) (by dsimp [base]; omega)]; exact hc3
  have hz0 : out (a+30)=false := by
    change spec (clearAt (a+30) t) (base+2+((suffix.length : Nat):Int)) (suffix.length+2) (a+30)=false
    rw [spec_outside _ _ _ _ (Or.inl (by dsimp [base]; push_cast; omega))]
    simp [clearAt]
  have hscan := terminal_scan_words t (a+2) 12 0 r 2 window hext
  dsimp only at hscan
  rw [hd] at hscan
  simp only [Nat.cast_zero,Nat.cast_ofNat] at hscan
  obtain ⟨_hhead,hzero,hrun⟩ := hscan
  have hz1 : t (a+31)=false := by
    have hp : a+30+1=a+31 := by omega
    rw [hp] at hzero
    simpa [Holds] using hzero
  have hz1' : out (a+31)=false := by rw [hbelow _ (by omega) (by dsimp [base]; omega)]; exact hz1
  have hrun' : Holds t (a+32) (List.replicate (r+3) true ++ [false]) := by
    have hp : a+30+(0:Int)+2=a+32 := by omega
    rw [hp] at hrun
    have hn : r+1+2=r+3 := by omega
    simpa only [hn] using hrun
  have hsplit := split_ones (r+3) (a+32) t [false] hrun'
  have hones : ∀ i : Nat, i<r+3 → out (a+32+(i : Int))=true := by
    intro i hi
    rw [hbelow _ (by omega) (by dsimp [base]; omega)]
    exact hsplit.1 i hi
  have hstop : out (a+32+((r+3 : Nat):Int))=false := by
    rw [hbelow _ (by push_cast; omega) (by dsimp [base]; push_cast; omega)]
    simpa [Holds] using hsplit.2
  obtain ⟨hreturn,hwindow,hearlier,hnewmarker⟩ :=
    return_next_window a (r+3) out (by omega) hold hleft0 hleft1 hc2' hc3' hz0 hz1' hones hstop
  have hh : a+31+((r+3 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
  rw [hh] at hreturn
  have hseg := segAdd machine _ _ _ (2*r+74+2*suffix.length) (3*(r+3)+18) hentry' hreturn
  have hbefore : final (a-3)=t (a-3) := by
    change outTape (a+30) (r+3) out (a-3)=t (a-3)
    rw [hearlier,hbelow _ (by omega) (by dsimp [base]; omega)]
  have hfull : Holds final base (encode (w::rest) ++ [true,false,false]) := by
    apply holds_transport out final base _ hbankout
    intro q hq _
    symm
    exact return_output_right (a+30) (r+3) out q (by omega) (by dsimp [base] at hq; push_cast; omega)
  exact ⟨hseg,hwindow,hbefore,hnewmarker,hfull⟩

#print axioms return_output_right
#print axioms positive_three_cycle
end Shared.Beeping.NPcoNP.NativePositiveThreeCycle
