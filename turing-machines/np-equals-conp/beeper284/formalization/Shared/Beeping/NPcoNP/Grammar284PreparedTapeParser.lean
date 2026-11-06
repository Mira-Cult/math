import Shared.Beeping.NPcoNP.Grammar284TapeLeafUnique

/-! Sound and complete bounded decoding of prepared grammar leaves from a
supplied tape accessor. This is not a physical-table implementation. -/
namespace Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284TapeLeafUnique
open Shared.Beeping.NPcoNP.NativeHalfSweep
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- Every successful bounded tape parse corresponds to an actual grammar
walk and a matching descending tape word. -/
theorem parseTape_sound (g : Grammar) (fuel : Nat) (start : Leaf)
    (tape : Int → Bool) (h : Int) (name : String) (length : Nat)
    (success : parseTape g fuel start tape h=some (name,length)) :
    ∃ path : List Bool, Walk g start path (.op name) ∧ path.length=length ∧
      path.length≤fuel ∧ downHolds tape h path := by
  induction fuel generalizing start h name length with
  | zero =>
    cases start with
    | op s =>
      simp [parseTape] at success
      obtain ⟨rfl,rfl⟩ := success
      exact ⟨[],Walk.stop _,rfl,by decide,trivial⟩
    | node i => simp [parseTape] at success
  | succ fuel ih =>
    cases start with
    | op s =>
      simp [parseTape] at success
      obtain ⟨rfl,rfl⟩ := success
      exact ⟨[],Walk.stop _,rfl,by simp,trivial⟩
    | node idx =>
      cases hget : g.nodes[idx]? with
      | none => simp [parseTape,hget] at success
      | some pair =>
        obtain ⟨hi,hvalue⟩ := Array.getElem?_eq_some_iff.mp hget
        let i : Fin g.nodes.size := ⟨idx,hi⟩
        cases hb : tape h with
        | false =>
          cases hp : parseTape g fuel pair.1 tape (h-1) with
          | none => simp [parseTape,hget,hb,hp] at success
          | some parsed =>
            rcases parsed with ⟨found,n⟩
            simp [parseTape,hget,hb,hp] at success
            obtain ⟨rfl,rfl⟩ := success
            obtain ⟨path,hw,hlen,hbound,htape⟩ := ih pair.1 (h-1) found n hp
            have hchild : Walk g (g.nodes[i.val]'i.isLt).1 path (.op found) := by
              change Walk g (g.nodes[idx]'hi).1 path (.op found)
              rw [hvalue]
              exact hw
            refine ⟨false::path,Walk.left i path (.op found) hchild,?_,?_,?_⟩
            · simpa using congrArg Nat.succ hlen
            · simp only [List.length_cons]
              omega
            · simpa [downHolds,hb] using htape
        | true =>
          cases hp : parseTape g fuel pair.2 tape (h-1) with
          | none => simp [parseTape,hget,hb,hp] at success
          | some parsed =>
            rcases parsed with ⟨found,n⟩
            simp [parseTape,hget,hb,hp] at success
            obtain ⟨rfl,rfl⟩ := success
            obtain ⟨path,hw,hlen,hbound,htape⟩ := ih pair.2 (h-1) found n hp
            have hchild : Walk g (g.nodes[i.val]'i.isLt).2 path (.op found) := by
              change Walk g (g.nodes[idx]'hi).2 path (.op found)
              rw [hvalue]
              exact hw
            refine ⟨true::path,Walk.right i path (.op found) hchild,?_,?_,?_⟩
            · simpa using congrArg Nat.succ hlen
            · simp only [List.length_cons]
              omega
            · simpa [downHolds,hb] using htape

/-- Check the fixed three-bit prepared prefix, then parse at most `fuel`
grammar edges. The returned count includes the three prefix bits. Execution
is relative to the supplied tape accessor. -/
def parsePreparedTape (fuel : Nat) (tape : Int → Bool) (h : Int) : Option (String × Nat) :=
  if tape h=true ∧ tape (h-1)=true ∧ tape (h-2)=false then
    (parseTape producerGrammar fuel (.node producerGrammar.root) tape (h-3)).map
      (fun result => (result.1,result.2+3))
  else none

/-- A successful prepared parse establishes a matching prepared leaf path. -/
theorem parsePreparedTape_sound (fuel : Nat) (tape : Int → Bool) (h : Int)
    (name : String) (length : Nat)
    (success : parsePreparedTape fuel tape h=some (name,length)) :
    ∃ path : List Bool, PreparedWalk path (.op name) ∧ path.length=length ∧
      path.length≤fuel+3 ∧ downHolds tape h path := by
  unfold parsePreparedTape at success
  split_ifs at success with hpre
  · cases hp : parseTape producerGrammar fuel (.node producerGrammar.root) tape (h-3) with
    | none => simp [hp] at success
    | some parsed =>
      rcases parsed with ⟨found,n⟩
      simp [hp] at success
      obtain ⟨rfl,rfl⟩ := success
      obtain ⟨path,hw,hlen,hbound,htape⟩ :=
        parseTape_sound producerGrammar fuel (.node producerGrammar.root) tape (h-3) found n hp
      refine ⟨preparedPrefix++path,⟨path,rfl,hw⟩,?_,?_,?_⟩
      · simp [preparedPrefix,hlen]
      · simp [preparedPrefix] at ⊢
        omega
      · simp only [preparedPrefix,List.cons_append,downHolds]
        refine ⟨hpre.1,hpre.2.1,?_,?_⟩
        · have he : h-1-1=h-2 := by omega
          simpa only [he] using hpre.2.2
        · have he : h-1-1-1=h-3 := by omega
          simpa only [he, List.nil_append] using htape

/-- The proved grammar depth bound makes 52 edges sufficient for every
prepared completed leaf path present on the supplied tape. -/
theorem parsePreparedTape_complete (tape : Int → Bool) (h : Int)
    (path suffix : List Bool) (name : String)
    (walk : PreparedWalk path (.op name)) (hw : downHolds tape h (path++suffix)) :
    parsePreparedTape 52 tape h=some (name,path.length) := by
  obtain ⟨raw,hpath,hwalk⟩ := walk
  have hbound := (producer_path_bound raw (.op name) hwalk).1
  have ht : downHolds tape (h-3) (raw++suffix) := by
    have hh := down_tail tape h preparedPrefix (raw++suffix) (by simpa [hpath,List.append_assoc] using hw)
    simpa [preparedPrefix] using hh
  have hpre : tape h=true ∧ tape (h-1)=true ∧ tape (h-2)=false := by
    have hh := hw
    rw [hpath] at hh
    simp only [preparedPrefix,List.cons_append,downHolds] at hh
    have he : h-1-1=h-2 := by omega
    exact ⟨hh.1,hh.2.1,by simpa only [he] using hh.2.2.1⟩
  have hp := walk_parseTape producerGrammar hwalk name rfl tape (h-3) suffix 52 hbound ht
  simp [parsePreparedTape,hpre,hp,hpath,preparedPrefix]

/-- A successful fixed-budget parse is exactly a prepared leaf word on the
supplied tape, with the returned length including the prefix. -/
theorem parsePreparedTape_iff (tape : Int → Bool) (h : Int) (name : String) (length : Nat) :
    parsePreparedTape 52 tape h = some (name,length) ↔
      ∃ path : List Bool, PreparedWalk path (.op name) ∧ path.length=length ∧
        downHolds tape h path := by
  constructor
  · intro success
    obtain ⟨path,hw,hlen,_,htape⟩ := parsePreparedTape_sound 52 tape h name length success
    exact ⟨path,hw,hlen,htape⟩
  · rintro ⟨path,hw,hlen,htape⟩
    have hh : downHolds tape h (path++[]) := by simpa using htape
    have result := parsePreparedTape_complete tape h path [] name hw hh
    simpa [hlen] using result

#print axioms parsePreparedTape_iff
#print axioms parseTape_sound
#print axioms parsePreparedTape_sound
#print axioms parsePreparedTape_complete
end Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
