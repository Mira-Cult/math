import PASoundness.M236Classification
import PASoundness.M236PayloadInvariant
/-! Canonical root preservation for the literal physical machine. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def Canonical (word : List Bool) (gap : Nat) (registers : RegisterMachine.Bank 9)
    (reserve : List Nat) (head : Int) (left : List Bool) (c : Config 237) : Prop :=
  Related ⟨79, head,
    ⟨false :: true :: true :: (List.replicate 7 false ++ left),
      word ++ false :: false :: (List.replicate gap false ++ true :: false ::
        bank (UnaryNine.values registers ++ reserve))⟩⟩ c

theorem canonical_selected (word : List Bool) (gap : Nat) (registers : RegisterMachine.Bank 9)
    (reserve : List Nat) (r : Fin 9) (head : Int) (left : List Bool) (c : Config 237)
    (h : Canonical word gap registers reserve head left c) :
    Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve [])⟩⟩ c := by
  have hh := related_selected_from_canonical registers r reserve
    (word ++ false :: false :: (List.replicate gap false ++ [true, false])) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) c (by
      simpa [Canonical, List.append_assoc] using h)
  simpa [List.replicate_succ, List.append_assoc] using hh

theorem canonical_increment (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left : List Bool) (c : Config 237)
    (hrel : Canonical word gap registers reserve head left c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      (word, next) ∈ adjacentPaths ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Canonical next gap' (RegisterMachine.execute (.inc r) registers).bank reserve endHead left finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨next, gap', time, endHead, finish, hpair, hc, hb, ht, hp, hr, hq, hd⟩ :=
    physical_increment_preserves_gap_budget registers r reserve gap word write hpath hbudget head left [] c
      (canonical_selected word gap registers reserve r head left c hrel)
  exact ⟨next, gap', time, endHead, finish, hpair, hc, hb, ht, hp, by simpa [Canonical] using hr, hq⟩

theorem canonical_positive (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat)
    (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left : List Bool) (c : Config 237)
    (hrel : Canonical word gap registers reserve head left c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      (word, next) ∈ adjacentPaths ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Canonical next gap' (RegisterMachine.execute (.decNZ r) registers).bank (reserve ++ [0]) endHead left finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨next, gap', time, endHead, finish, hpair, hc, hb, ht, hp, hr, hq, hd, hout⟩ :=
    physical_positive_preserves_gap_budget registers r value hvalue reserve gap word write hpath hbudget head left [] c
      (canonical_selected word gap registers reserve r head left c hrel)
  exact ⟨next, gap', time, endHead, finish, hpair, hc, hb, ht, hp, by simpa [Canonical] using hr, hq⟩

theorem canonical_zero (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left : List Bool) (c : Config 237)
    (hrel : Canonical word gap registers reserve head left c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Grammar.LeafPath Grammar.nodes 157 next ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Canonical next gap' registers reserve endHead left finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨next, gap', time, endHead, finish, hleaf, hc, hb, ht, hp, hr, hq, hd, hout⟩ :=
    physical_zero_preserves_gap_budget registers r hzero reserve gap word write hpath hbudget head left [] c
      (canonical_selected word gap registers reserve r head left c hrel)
  have hr' : Related ⟨79, endHead,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (next ++ false :: false :: (List.replicate gap' false ++ true :: false ::
          bank (UnaryNine.values registers ++ reserve))) ++ [false]⟩⟩ finish := by
    simpa [List.append_assoc] using hr
  exact ⟨next, gap', time, endHead, finish, hleaf, hc, hb, ht, hp, related_drop_false hr', hq⟩

/-- The local root-level effect, retaining literal edge identity, register
changes, reserve growth and event polarity. It does not assert source semantics. -/
inductive BranchEffect : Grammar.Edge → RegisterMachine.Bank 9 → List Nat →
    RegisterMachine.Bank 9 → List Nat → List Bool → Prop where
  | inc (r : Fin 9) (write : Bool) (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none)
        bank reserve (RegisterMachine.execute (.inc r) bank).bank reserve []
  | positive (r : Fin 9) (write : Bool) (bank : RegisterMachine.Bank 9) (reserve : List Nat)
      (v : Nat) (h : bank r = v + 1) :
      BranchEffect (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)
        bank reserve (RegisterMachine.execute (.decNZ r) bank).bank (reserve ++ [0]) []
  | zero (r : Fin 9) (write : Bool) (bank : RegisterMachine.Bank 9) (reserve : List Nat) (h : bank r = 0) :
      BranchEffect (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)
        bank reserve bank reserve []
  | continue1 (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf "_continue.1" 72 false .left none) bank reserve bank reserve []
  | continue2 (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf "_continue.2" 73 false .left none) bank reserve bank reserve []
  | continue3 (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf "_continue.3" 74 false .left none) bank reserve bank reserve []
  | break1 (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf "_break.1" 69 false .left none) bank reserve bank reserve []
  | break3 (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf "_break.3" 71 false .left none) bank reserve bank reserve []
  | emitContinue (b : Bool) (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf (Emit.emitName b) 72 true .left (some b)) bank reserve bank reserve [b]
  | emitCleanup (b : Bool) (bank : RegisterMachine.Bank 9) (reserve : List Nat) :
      BranchEffect (.leaf (Emit.emitName b) 68 false .left (some b)) bank reserve bank reserve [b]

/-- Every prepared literal leaf makes positive physical progress to another
canonical leaf, preserving its control budget and the named branch effect. -/
theorem canonical_physical_step (word : List Bool) (gap : Nat)
    (registers : RegisterMachine.Bank 9) (reserve : List Nat)
    (head : Int) (left : List Bool) (c : Config 237)
    (hpath : Grammar.LeafPath Grammar.nodes 157 word)
    (hbudget : 25 ≤ gap + word.length)
    (hrel : Canonical word gap registers reserve head left c) :
    ∃ (edge : Grammar.Edge) (last : Bool) (next : List Bool) (gap' time : Nat)
      (nextRegisters : RegisterMachine.Bank 9) (nextReserve : List Nat) (out : List Bool)
      (endHead : Int) (finish : Config 237),
      Preparation.NamedPath Grammar.nodes 157 word edge ∧ word.getLast? = some last ∧
      BranchEffect edge registers reserve nextRegisters nextReserve out ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish out ∧
      Canonical next gap' nextRegisters nextReserve endHead left finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) out := by
  obtain ⟨last, edge, hl, hn, hs⟩ := leaf_named_supported hpath
  obtain ⟨pre, hw⟩ := List.getLast?_eq_some_iff.mp hl
  subst word
  unfold supportedLeaf at hs
  rcases hs with hi | hd | hc1 | hc2 | hc3 | hb1 | hb3 | ho1 | ho2
  · obtain ⟨r, write, he⟩ := hi
    subst edge
    obtain ⟨next, gap', time, endHead, finish, hpair, hc, hb, ht, hp, hr, hq⟩ :=
      canonical_increment registers r reserve gap (pre ++ [last]) write hn hbudget head left c hrel
    exact ⟨_, last, next, gap', time, _, reserve, [], endHead, finish, hn, hl,
      .inc r write registers reserve, adjacent_next_leaf hpair, hc, hb, ht, hp, hr, hq⟩
  · obtain ⟨r, write, he⟩ := hd
    subst edge
    cases hv : registers r with
    | zero =>
      obtain ⟨next, gap', time, endHead, finish, hleaf, hc, hb, ht, hp, hr, hq⟩ :=
        canonical_zero registers r hv reserve gap (pre ++ [last]) write hn hbudget head left c hrel
      exact ⟨_, last, next, gap', time, registers, reserve, [], endHead, finish, hn, hl,
        .zero r write registers reserve hv, hleaf, hc, hb, ht, hp, hr, hq⟩
    | succ v =>
      obtain ⟨next, gap', time, endHead, finish, hpair, hc, hb, ht, hp, hr, hq⟩ :=
        canonical_positive registers r v hv reserve gap (pre ++ [last]) write hn hbudget head left c hrel
      exact ⟨_, last, next, gap', time, _, reserve ++ [0], [], endHead, finish, hn, hl,
        .positive r write registers reserve v hv, adjacent_next_leaf hpair, hc, hb, ht, hp, hr, hq⟩
  · subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_continue1_preserves_gap_budget pre last hn gap hbudget head left
        (true :: false :: bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, last, next, gap', time, registers, reserve, [], endHead, finish, hn, hl,
      .continue1 registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩
  · subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_continue2_preserves_gap_budget pre last hn gap hbudget head left
        (true :: false :: bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, last, next, gap', time, registers, reserve, [], endHead, finish, hn, hl,
      .continue2 registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩
  · subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_continue3_preserves_gap_budget pre last hn gap hbudget head left
        (true :: false :: bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, last, next, gap', time, registers, reserve, [], endHead, finish, hn, hl,
      .continue3 registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩
  · subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_break1_preserves_gap_budget pre last hn gap hbudget head left
        (bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, last, next, gap', time, registers, reserve, [], endHead, finish, hn, hl,
      .break1 registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩
  · subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_break3_preserves_gap_budget pre last hn gap hbudget head left
        (bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, last, next, gap', time, registers, reserve, [], endHead, finish, hn, hl,
      .break3 registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩
  · obtain ⟨b, hlast, he⟩ := ho1
    subst last
    subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_emit_continue_preserves_gap_budget b pre hn gap hbudget head left
        (bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, false, next, gap', time, registers, reserve, [b], endHead, finish, hn, hl,
      .emitContinue b registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩
  · obtain ⟨b, hlast, he⟩ := ho2
    subst last
    subst edge
    obtain ⟨next, source, gap', time, endHead, finish, hsource, hnext, hc, hb, ht, hp, hr, hq⟩ :=
      physical_emit_cleanup_preserves_gap_budget b pre hn gap hbudget head left
        (bank (UnaryNine.values registers ++ reserve)) c hrel
    exact ⟨_, true, next, gap', time, registers, reserve, [b], endHead, finish, hn, hl,
      .emitCleanup b registers reserve, resolveZeros_sound Grammar.nodes 158 157 source next hnext,
      hc, hb, ht, hp, hr, hq⟩

/-- The invariant at a physical grammar root, with the exact blank-start
control-space budget and arbitrary finite register and reserve contents. -/
def RootGood (c : Config 237) : Prop :=
  ∃ word gap registers reserve head,
    Grammar.LeafPath Grammar.nodes 157 word ∧ word.length + gap = 3819 ∧
    Canonical word gap registers reserve head [] c

/-- A finite chain records each positive-duration literal physical segment,
its exact event word, named edge and register/reserve effect. -/
inductive RootChain (start : Config 237) : Nat → Nat → List Bool → Config 237 → Prop where
  | nil : RootChain start 0 0 [] start
  | snoc {n elapsed : Nat} {before finish : Config 237} {duration : Nat}
      {word next : List Bool} {gap nextGap : Nat}
      {registers nextRegisters : RegisterMachine.Bank 9} {reserve nextReserve : List Nat}
      {head nextHead : Int} {edge : Grammar.Edge} {out priorOut : List Bool}
      (prior : RootChain start n elapsed priorOut before)
      (hpath : Preparation.NamedPath Grammar.nodes 157 word edge)
      (hbefore : Canonical word gap registers reserve head [] before)
      (heffect : BranchEffect edge registers reserve nextRegisters nextReserve out)
      (hpositive : 0 < duration)
      (hblock : (machineWordSystem raw rawLabels).Block before duration finish out)
      (hafter : Canonical next nextGap nextRegisters nextReserve nextHead [] finish) :
      RootChain start (n + 1) (elapsed + duration) (priorOut ++ out) finish

/-- Every finite number of root steps occurs in one actual blank-start run;
no root segment can consume zero physical transitions. -/
theorem blank_root_chain (n : Nat) :
    ∃ elapsed events finish, n ≤ elapsed ∧
      RootChain ((machineWordSystem raw rawLabels).run 89821408) n elapsed events finish ∧
      finish = (machineWordSystem raw rawLabels).run (89821408 + elapsed) ∧
      (machineWordSystem raw rawLabels).prefixWord (89821408 + elapsed) = events ∧ RootGood finish := by
  induction n with
  | zero =>
    refine ⟨0, [], _, by omega, .nil, ?_, ?_, ?_⟩
    · rw [Nat.add_zero]
    · rw [Nat.add_zero]
      exact raw_initial_canonical_budget.2.2
    · refine ⟨BlankFirst.word, 3815, BlankFirst.zeros, BlankFirst.reserve, -3818,
        Redispatch.named_leaf_path BlankFirst.path, ?_, ?_⟩
      · decide
      · exact raw_initial_canonical_budget.1
  | succ n ih =>
    obtain ⟨elapsed, events, before, htime, hchain, hrun, hprefix, word, gap, registers, reserve, head, hleaf, hsum, hrel⟩ := ih
    have hbudget : 25 ≤ gap + word.length := by omega
    obtain ⟨edge, last, next, gap', duration, regs', reserve', out, endHead, finish,
      hpath, hlast, heffect, hnext, hconserve, hb, hpositive, hblock, hafter, hq⟩ :=
      canonical_physical_step word gap registers reserve head [] before hleaf hbudget hrel
    refine ⟨elapsed + duration, events ++ out, finish, by omega,
      .snoc hchain hpath hrel heffect hpositive hblock hafter, ?_, ?_, ?_⟩
    · rw [← Nat.add_assoc, WordEventSystem.run_add, ← hrun]
      exact hblock.endpoint.symm
    · rw [← Nat.add_assoc, WordEventSystem.prefix_add, hprefix, ← hrun, hblock.output]
    · exact ⟨next, gap', regs', reserve', endHead, hnext, by omega, hafter⟩

/-- The same finite chains occur in the actual selected 236-state blank run,
with exactly the same event prefixes. -/
theorem selected_blank_root_chains (n : Nat) :
    ∃ elapsed events finish, n ≤ elapsed ∧
      RootChain ((machineWordSystem raw rawLabels).run 89821408) n elapsed events finish ∧
      mapConfig finish = (machineWordSystem machine machineLabels).run (89821408 + elapsed) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed) = events ∧
      RootGood finish := by
  obtain ⟨elapsed, events, finish, ht, hchain, hrun, hprefix, hgood⟩ := blank_root_chain n
  refine ⟨elapsed, events, finish, ht, hchain, ?_, ?_, hgood⟩
  · rw [hrun, machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  · rw [← prefix_eq, hprefix]
end PASoundness.M236.Control
