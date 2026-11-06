import Shared.Beeping.NPcoNP.Source284JoinedPrefixScan

/-! A finite executable detector for the exact reversed joined-body grammar.
It stops on the final input-frame delimiter, before any arbitrary high suffix.
This is the control automaton only: a paid product with the tagged serializer
and a physical transition-table handoff remain to be constructed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284JoinedEndDetector

open Shared.Beeping.NPcoNP.Source284JoinedFrames (reverseBlocks)
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)

inductive State where
  | lead | witnessData | witnessZeroMarker | witnessOneMarker | gap
  | inputMarker | inputData | done | bad
  deriving DecidableEq, Repr

instance : Fintype State := Fintype.ofList
  [.lead,.witnessData,.witnessZeroMarker,.witnessOneMarker,.gap,
   .inputMarker,.inputData,.done,.bad] (by intro q; cases q <;> simp)

/-- A finite transition function; the two marker states remember one bit of
witness data so that a malformed separator cannot masquerade as `000`. -/
def step : State → Bool → State
  | .lead, false => .witnessData
  | .lead, true => .bad
  | .witnessData, false => .witnessZeroMarker
  | .witnessData, true => .witnessOneMarker
  | .witnessZeroMarker, false => .gap
  | .witnessZeroMarker, true => .witnessData
  | .witnessOneMarker, false => .bad
  | .witnessOneMarker, true => .witnessData
  | .gap, false => .inputMarker
  | .gap, true => .bad
  | .inputMarker, false => .done
  | .inputMarker, true => .inputData
  | .inputData, _ => .inputMarker
  | .done, _ => .done
  | .bad, _ => .bad

/-- Run until the first accepting state, reporting the number of consumed bits
and the untouched suffix. A malformed or truncated prefix returns `none`. -/
def scan (q : State) (bits : List Bool) : Option (Nat × List Bool) :=
  match q with
  | .done => some (0,bits)
  | .bad => none
  | _ => match bits with
    | [] => none
    | b::bs => (scan (step q b) bs).map (fun p => (p.1+1,p.2))

theorem blocks (bits suffix : List Bool) :
    scan .witnessData (reverseBlocks bits ++ suffix) =
      (scan .witnessData suffix).map (fun p => (p.1+2*bits.length,p.2)) := by
  induction bits with
  | nil => cases h : scan .witnessData suffix <;> simp [reverseBlocks,h]
  | cons b bs ih =>
    cases b <;>
      simp [reverseBlocks,scan,step,ih,Option.map_map,Function.comp_def,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] <;>
      congr 1 <;> funext p <;> congr 1 <;> omega

/-- A forward input frame is accepted exactly at its delimiter. -/
theorem input_frame (bits suffix : List Bool) :
    scan .inputMarker (frameBits bits [] ++ suffix) = some (2*bits.length+1,suffix) := by
  induction bits with
  | nil => simp [frameBits,scan,step]
  | cons b bs ih =>
    cases b <;> simp [frameBits,scan,step,ih,Nat.mul_add] <;> omega

/-- This identity fixes the exact bit order inspected by the detector. -/
theorem body_shape (x w : List Bool) :
    (Source284JoinedPrefixScan.joinedBody x w).reverse =
      false::(reverseBlocks w.reverse ++ [false,false,false] ++ frameBits x []) := by
  simp only [Source284JoinedPrefixScan.joinedBody,List.reverse_append,List.reverse_reverse]
  rw [Source284JoinedFrames.reversed_frame]
  simp [List.append_assoc]

/-- For every valid joined body and every high suffix, the executable
finite automaton consumes precisely the body and leaves that suffix intact. -/
theorem scan_body (x w extra : List Bool) :
    scan .lead ((Source284JoinedPrefixScan.joinedBody x w).reverse ++ extra) =
      some ((Source284JoinedPrefixScan.joinedBody x w).length,extra) := by
  have hlen : (Source284JoinedPrefixScan.joinedBody x w).length =
      2*x.length+2*w.length+5 := by
    have h := congrArg List.length (Source284JoinedPrefixScan.joined_eq_body x w)
    simp only [List.length_append,List.length_singleton,Source284JoinedFrames.joined_length] at h
    omega
  rw [body_shape]
  simp only [List.cons_append,scan,step]
  rw [show reverseBlocks w.reverse ++ [false,false,false] ++ frameBits x [] ++ extra =
    reverseBlocks w.reverse ++ ([false,false,false] ++ (frameBits x [] ++ extra)) by simp [List.append_assoc]]
  rw [blocks]
  have hg : scan .witnessData ([false,false,false] ++ (frameBits x [] ++ extra)) =
      some (2*x.length+4,extra) := by
    change Option.map (fun p => (p.1+1,p.2))
      (Option.map (fun p => (p.1+1,p.2))
        (Option.map (fun p => (p.1+1,p.2)) (scan .inputMarker (frameBits x [] ++ extra)))) = _
    rw [input_frame]
    simp
  rw [hg]
  simp [hlen]
  omega

/-- A completed detection count cannot exceed the supplied finite input. -/
theorem scan_length (q : State) (bits : List Bool) (n : Nat) (suffix : List Bool)
    (h : scan q bits = some (n,suffix)) : n+suffix.length = bits.length := by
  induction bits generalizing q n suffix with
  | nil =>
    cases q <;> simp [scan] at h <;> simp_all
  | cons b bs ih =>
    cases q <;> simp only [scan] at h
    case done => simp at h; rcases h with ⟨rfl,rfl⟩; simp
    case bad => contradiction
    all_goals
      obtain ⟨⟨j,rest⟩,hs,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      have hh := ih _ _ _ hs
      simp only [List.length_cons]
      omega

/-- Appending unread data after a successful detection preserves the first
acceptance time and appends it to the reported suffix. -/
theorem scan_append (q : State) (bits : List Bool) (n : Nat) (suffix extra : List Bool)
    (h : scan q bits = some (n,suffix)) :
    scan q (bits++extra) = some (n,suffix++extra) := by
  induction bits generalizing q n suffix with
  | nil =>
    cases q <;> simp [scan] at h <;> simp_all [scan]
  | cons b bs ih =>
    cases q <;> simp only [scan] at h ⊢
    case done => simp at h; rcases h with ⟨rfl,rfl⟩; rfl
    case bad => contradiction
    all_goals
      obtain ⟨⟨j,rest⟩,hs,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      have hh := ih _ _ _ hs
      simp only [List.cons_append,scan]
      rw [hh]
      rfl

/-- No proper prefix of a genuine joined body can trigger the detector.
This establishes the first-detection boundary, including for empty payloads. -/
theorem no_early_detection (x w : List Bool) (j : Nat)
    (hj : j < (Source284JoinedPrefixScan.joinedBody x w).length) :
    scan .lead ((Source284JoinedPrefixScan.joinedBody x w).reverse.take j) = none := by
  let body := (Source284JoinedPrefixScan.joinedBody x w).reverse
  have hlen : body.length = (Source284JoinedPrefixScan.joinedBody x w).length := by simp [body]
  have hfull : scan .lead body = some (body.length,[]) := by
    simpa [body] using scan_body x w []
  cases he : scan .lead (body.take j) with
  | none => rfl
  | some p =>
    rcases p with ⟨n,suffix⟩
    have hl := scan_length .lead (body.take j) n suffix he
    have ha := scan_append .lead (body.take j) n suffix (body.drop j) he
    rw [List.take_append_drop,hfull] at ha
    simp only [Option.some.injEq,Prod.mk.injEq] at ha
    have htake : (body.take j).length ≤ j := by simp
    omega

namespace Fixtures
example : scan .lead ((Source284JoinedPrefixScan.joinedBody [] []).reverse ++ [true,false]) =
    some (5,[true,false]) := by decide +kernel
example : scan .lead ((Source284JoinedPrefixScan.joinedBody [true,false] [true]).reverse ++ [false,true]) =
    some (11,[false,true]) := by decide +kernel
example : scan .lead [false,true,false] = none := by decide +kernel
example : scan .lead [false,false,false,true] = none := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284JoinedEndDetector
