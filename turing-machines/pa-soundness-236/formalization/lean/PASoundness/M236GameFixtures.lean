import PASoundness.M236Game

/-! Small kernel-checked controls for the selected finite semantics and its
wire format. These finite examples do not establish the machine simulation. -/
set_option linter.unusedSimpArgs false

namespace PASoundness.M236GameFixtures

open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Game

/-- Strict code zero is a genuine membership atom, not uniform falsity. -/
example : atom 0 [0, 1] = true := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : atom 0 [0, 0] = false := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]

/-- A missing paid atom slot times out optimistically for both signs. -/
example : path 0 [0, 0] false [] = true := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : path 0 [0, 1] true [] = true := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : path 0 [0, 0] false [37] = false := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : path 0 [0, 1] true [37] = false := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]

/-- Selected-table delivery's published rank-three and rank-five records. -/
example : selectedValue ⟨3, 0, [1, 0, 0]⟩ = true := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : selectedValue ⟨5, 1, [0, 0, 0, 0, 0]⟩ = true := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : selectedValue ⟨3, 0, [1, 1, 0]⟩ = false := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]
example : selectedValue ⟨2, 0, [1, 1000000]⟩ = false := by
  simp (config := { decide := true }) [selectedValue, aligned, path, atom, tag, payload,
    PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]

/-- Bad rank and bad Boolean field are rejected, while equal duplicate frames
remain valid and conflicting duplicate frames fail permanently. -/
example : decodeFields [0, 0, 0] = none := by decide
example : decodeFields [1, 0, 0, 2] = none := by decide

def key : Address := ⟨1, 0, [0]⟩

example : (feedBits {} (encodeFrame key false ++ encodeFrame key false)).numbers.failed = false := by decide
example : (feedBits {} (encodeFrame key false ++ encodeFrame key true)).numbers.failed = true := by decide
example : (feedBits {} (encodeFrame key false ++ encodeFrame key true ++ [false])).numbers.failed = true := by decide

/-- The same fixed observer accepts a complete all-zero source, and rejects
an all-one source. These are observer controls, not PA machine executions. -/
theorem zero_source_accepted :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source (fun _ => false)) := by
  apply (PASoundness.M236Observer.source_trace_accept_iff_strategies _).mpr
  intro n hn p
  apply (PASoundness.M236Observer.strategy_iff _ _ _).mpr
  simpa using (PASoundness.altPrefix_constant .ex n True).mpr trivial

theorem one_source_rejected :
    ¬ PASoundness.M236Observer.TraceAccept (PASoundness.Source.source (fun _ => true)) := by
  intro h
  have hs := (PASoundness.M236Observer.source_trace_accept_iff_strategies _).mp h 1 (by decide) 0
  obtain ⟨s, hs⟩ := hs
  cases s with
  | choose x child =>
    cases child
    simp [PASoundness.M236Observer.Winning] at hs

end PASoundness.M236GameFixtures
