import Shared.Beeping.NPcoNP.Grammar284LeafPrefix

/-! Unique completed leaf path at a supplied physical tape head. This does
not assert that the path is the executing graph program counter. -/
namespace Shared.Beeping.NPcoNP.Grammar284TapeLeafUnique
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- Fuel-bounded parsing reads supplied tape bits, stopping at the first
operation. Invalid nodes and exhausted fuel fail. This is executable relative
to the supplied tape accessor; no physical parser implementation is asserted. -/
def parseTape (g : Grammar) : Nat → Leaf → (Int → Bool) → Int → Option (String × Nat)
  | _, .op name, _, _ => some (name,0)
  | 0, .node _, _, _ => none
  | fuel+1, .node i, tape, h => do
      let pair ← g.nodes[i]?
      let result ← parseTape g fuel (if tape h then pair.2 else pair.1) tape (h-1)
      pure (result.1,result.2+1)

/-- A supplied grammar walk is found by the bounded parser relative to the
supplied tape accessor whenever the descending tape contains its path. -/
theorem walk_parseTape (g : Grammar) {start last : Leaf} {path : List Bool}
    (walk : Walk g start path last) (name : String) (finish : last=.op name)
    (tape : Int → Bool) (h : Int) (suffix : List Bool) (fuel : Nat)
    (enough : path.length≤fuel) (hw : downHolds tape h (path++suffix)) :
    parseTape g fuel start tape h=some (name,path.length) := by
  induction walk generalizing h fuel with
  | stop leaf =>
    subst leaf
    cases fuel <;> simp [parseTape]
  | left i path last walk ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp only [List.cons_append,downHolds] at hw
      have hs := ih finish (h-1) fuel (by simp at enough; omega) hw.2
      simp [parseTape,hw.1,hs]
  | right i path last walk ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp only [List.cons_append,downHolds] at hw
      have hs := ih finish (h-1) fuel (by simp at enough; omega) hw.2
      simp [parseTape,hw.1,hs]

/-- Equal-length prefixes read from the same deterministic tape are equal. -/
theorem down_same_length (tape : Int → Bool) (h : Int) (p q s t : List Bool)
    (lengths : p.length=q.length)
    (hp : downHolds tape h (p++s)) (hq : downHolds tape h (q++t)) : p=q := by
  induction p generalizing h q with
  | nil => cases q <;> simp_all
  | cons b p ih =>
    cases q with
    | nil => simp at lengths
    | cons c q =>
      simp only [List.length_cons,Nat.succ.injEq] at lengths
      simp only [List.cons_append,downHolds] at hp hq
      have he : b=c := hp.1.symm.trans hq.1
      have hr := ih (h-1) q lengths hp.2 hq.2
      simp [he,hr]

/-- A completed leaf path and operation read from a given tape head are
unique, independently of the word that follows the path. -/
theorem tape_leaf_unique (g : Grammar) (start : Leaf) (tape : Int → Bool) (h : Int)
    (p q s t : List Bool) (name name' : String)
    (hp : Walk g start p (.op name)) (hq : Walk g start q (.op name'))
    (hpTape : downHolds tape h (p++s)) (hqTape : downHolds tape h (q++t)) :
    p=q ∧ name=name' := by
  let fuel := max p.length q.length
  have h1 := walk_parseTape g hp name rfl tape h s fuel (by dsimp [fuel]; omega) hpTape
  have h2 := walk_parseTape g hq name' rfl tape h t fuel (by dsimp [fuel]; omega) hqTape
  rw [h2] at h1
  have he : (name',q.length)=(name,p.length) := Option.some.inj h1
  have hn : name=name' := (congrArg Prod.fst he).symm
  have hl : p.length=q.length := (congrArg Prod.snd he).symm
  exact ⟨down_same_length tape h p q s t hl hpTape hqTape,hn⟩

/-- Dropping a finite descending prefix preserves the explicitly supplied
continuation. -/
theorem down_tail (tape : Int → Bool) (h : Int) (p s : List Bool)
    (hw : downHolds tape h (p++s)) : downHolds tape (h-(p.length : Int)) s := by
  induction p generalizing h with
  | nil => simpa using hw
  | cons b p ih =>
    simp only [List.cons_append,downHolds] at hw
    have hh := ih (h-1) hw.2
    have he : h-1-(p.length : Int)=h-((b::p).length : Int) := by simp; omega
    simpa only [he] using hh

/-- For prepared paths, the common three-bit prefix is consumed before
applying the grammar parser to the remaining path. -/
theorem prepared_tape_leaf_unique (tape : Int → Bool) (h : Int)
    (p q s t : List Bool) (name name' : String)
    (hp : PreparedWalk p (.op name)) (hq : PreparedWalk q (.op name'))
    (hpTape : downHolds tape h (p++s)) (hqTape : downHolds tape h (q++t)) :
    p=q ∧ name=name' := by
  obtain ⟨raw,hp',hwp⟩ := hp
  obtain ⟨raw',hq',hwq⟩ := hq
  have ht1 : downHolds tape (h-(preparedPrefix.length : Int)) (raw++s) := by
    apply down_tail tape h preparedPrefix (raw++s)
    simpa [hp',List.append_assoc] using hpTape
  have ht2 : downHolds tape (h-(preparedPrefix.length : Int)) (raw'++t) := by
    apply down_tail tape h preparedPrefix (raw'++t)
    simpa [hq',List.append_assoc] using hqTape
  obtain ⟨he,hn⟩ := tape_leaf_unique producerGrammar (.node producerGrammar.root) tape
    (h-(preparedPrefix.length : Int)) raw raw' s t name name' hwp hwq ht1 ht2
  exact ⟨by rw [hp',hq',he],hn⟩

#print axioms walk_parseTape
#print axioms down_same_length
#print axioms tape_leaf_unique
#print axioms prepared_tape_leaf_unique
end Shared.Beeping.NPcoNP.Grammar284TapeLeafUnique
