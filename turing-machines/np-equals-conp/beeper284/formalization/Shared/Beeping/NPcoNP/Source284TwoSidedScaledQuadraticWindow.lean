import Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadratic
import Shared.Beeping.NPcoNP.Source284ScratchWindowExact

/-! Fixed-coefficient quadratic finite observation windows for the actual two-sided loader,
including arbitrary certificate and high input-suffix aliases. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadratic

def leftData (k : Nat) (w : List Bool) (certificate : Nat) : Nat :=
  4^(w.length+1)*(4^(w.length+1)*
    (2^(k*(w.length*w.length)+1)*pairTape (List.replicate w.length false)
      (pairTape (List.replicate w.length false) certificate)))

def rightData (k : Nat) (w : List Bool) (suffix : Nat) : Nat :=
  2*flipped (w++[false]) (2^(k*(w.length*w.length)+1)*finalTail k w.length suffix)

theorem left_agree (k : Nat) (w : List Bool) (first second depth : Nat)
    (hdepth : depth ≤ k*(w.length*w.length)+1) : Agree depth (leftData k w first) (leftData k w second) := by
  have hd (certificate : Nat) : 2^depth ∣ leftData k w certificate := by
    unfold leftData
    have h : 2^depth ∣ 2^(k*(w.length*w.length)+1) := pow_dvd_pow 2 hdepth
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _) _
  simp [Agree,Nat.mod_eq_zero_of_dvd (hd first),Nat.mod_eq_zero_of_dvd (hd second)]

theorem right_agree (k : Nat) (w : List Bool) (first second depth : Nat)
    (hdepth : depth ≤ k*(w.length*w.length)+1) : Agree depth (rightData k w first) (rightData k w second) := by
  unfold rightData
  apply Source284ScratchWindowExact.right_agree_of_tail (w++[false]) _ _ _
  have hd : depth-(2*(w++[false]).length+3) ≤ k*(w.length*w.length)+1 := by omega
  apply agree_mono hd
  simp [Agree]

/-- Same parsed payload and arbitrary hidden input/certificate tails yield
the same finite output window whenever radius plus clock fits the constructed
quadratic zero blocks. -/
theorem source_alias_window (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert firstSuffix secondSuffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hsize : radius+clock ≤ k*(w.length*w.length)+1) :
    Window radius
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w firstSuffix) firstCert) (totalCost k w+clock))
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w secondSuffix) secondCert) (totalCost k w+clock)) := by
  let a : Config := ⟨leftData k w firstCert,rightData k w firstSuffix,some 0⟩
  let b : Config := ⟨leftData k w secondCert,rightData k w secondSuffix,some 0⟩
  have ha : Valid states a := by intro q hq; simp [a] at hq; subst q; exact hn
  have hb : Valid states b := by intro q hq; simp [b] at hq; subst q; exact hn
  have hi : Window (radius+clock) (toSource a) (toSource b) := by
    refine ⟨rfl,?_,?_⟩
    · exact left_agree k w firstCert secondCert _ hsize
    · exact right_agree k w firstSuffix secondSuffix _ hsize
  have hr := Source284Relative.run_window (encode states continuation 1) clock radius _ _ hi
  have hl := Source284RepeatWorkspaceWindow.lift_window radius (840+220*k) _ _ hr
  rw [run_toSource states continuation 1 a hv ha clock,
    run_toSource states continuation 1 b hv hb clock] at hl
  repeat rw [Source284SourceRelocation.lift_toSource] at hl
  rw [source_then k states continuation w firstCert firstSuffix clock hn hv,
    source_then k states continuation w secondCert secondSuffix clock hn hv]
  exact hl


/-- The fixed-coefficient program covers every natural input, including zero
and all noncanonical suffixes. -/
theorem source_all_inputs_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input certificate fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (totalCost k w+fuel) =
      toSource (shiftConfig (840+220*k) (run continuation
        ⟨leftData k w certificate,rightData k w suffix,some 0⟩ fuel)) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_then k states continuation w certificate suffix fuel hn hv

end Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow
