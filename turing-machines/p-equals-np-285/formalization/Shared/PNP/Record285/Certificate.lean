import Shared.PNP.Record285.Machine

/-! Soundness of the finite row checker. These results are uniform in the
parsed table: their hypotheses do not assert that the embedded file passes the
checker. -/
namespace Shared.PNP.Record285
open Shared.Beeping.Machines

/-- The numerical properties expected of the row at a given zero-based index. -/
def RowSpec (i : Nat) (r : RawRow) : Prop :=
  r.state = i / 2 ∧ r.read = i % 2 ∧ r.write < 2 ∧ r.next < 285 ∧
    r.event = (if i == 243 then 1 else 0)

theorem wellFormed_length {rs : List RawRow} (h : wellFormed rs = true) : rs.length = 570 := by
  simpa [wellFormed] using (Bool.and_eq_true _ _).mp h |>.1

theorem wellFormed_row {rs : List RawRow} (h : wellFormed rs = true)
    {i : Nat} {r : RawRow} (hr : rs[i]? = some r) : RowSpec i r := by
  have hall := (Bool.and_eq_true _ _).mp h |>.2
  have hmem : (r,i) ∈ rs.zipIdx := by
    apply List.mem_iff_getElem?.2
    refine ⟨i, ?_⟩
    simp [List.getElem?_zipIdx, hr]
  have hrow := List.all_eq_true.mp hall (r,i) hmem
  simpa [RowSpec, and_assoc] using hrow

/-- For a successful, validated parse, no lookup uses the default row. -/
theorem validated_row (parsed : List RawRow) (hparse : parse = some parsed)
    (hvalid : wellFormed parsed = true) (q : Fin 285) (read : Bool) :
    ∃ r, parsed[2*q.val + (if read then 1 else 0)]? = some r ∧
      RowSpec (2*q.val + (if read then 1 else 0)) r ∧
      table.row q read = physicalRow r := by
  have hlen := wellFormed_length hvalid
  have hi : 2*q.val + (if read then 1 else 0) < parsed.length := by
    rw [hlen]
    have hq := q.isLt
    cases read <;> simp <;> omega
  refine ⟨parsed[2*q.val + (if read then 1 else 0)], ?_, ?_, ?_⟩
  · exact List.getElem?_eq_getElem hi
  · exact wellFormed_row hvalid (List.getElem?_eq_getElem hi)
  · exact row_from_parse parsed hparse q _ read (List.getElem?_eq_getElem hi)



/-- Under validation, the physical row has exactly the decoded fields and the
row's explicit state and read columns name the lookup that selected it. -/
theorem validated_row_exact (parsed : List RawRow) (hparse : parse = some parsed)
    (hvalid : wellFormed parsed = true) (q : Fin 285) (read : Bool) :
    ∃ r, parsed[2*q.val + (if read then 1 else 0)]? = some r ∧
      r.state = q.val ∧ r.read = (if read then 1 else 0) ∧
      r.write < 2 ∧ r.next < 285 ∧
      (table.row q read).write = (r.write == 1) ∧
      (table.row q read).move = r.move ∧
      (table.row q read).next.val = r.next ∧
      (table.row q read).beep = (r.event == 1) := by
  obtain ⟨r, hrow, hs, hr⟩ := validated_row parsed hparse hvalid q read
  rcases hs with ⟨hstate, hread, hwrite, hnext, _⟩
  have hstate' : r.state = q.val := by
    cases read <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero] at hstate <;> omega
  have hread' : r.read = (if read then 1 else 0) := by
    cases read <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero] at hread ⊢ <;> omega
  refine ⟨r, hrow, hstate', hread', hwrite, hnext, ?_, ?_, ?_, ?_⟩ <;>
    simp [hr, physicalRow, Nat.mod_eq_of_lt hnext]

/-- The checker certifies the exact transition-event mask, not a state-visit
or a B-exit convention. -/
theorem validated_event (parsed : List RawRow) (hparse : parse = some parsed)
    (hvalid : wellFormed parsed = true) (q : Fin 285) (read : Bool) :
    (table.row q read).beep = (decide (q.val = 121) && read) := by
  obtain ⟨r, _, hs, hr⟩ := validated_row parsed hparse hvalid q read
  have hevent := hs.2.2.2.2
  rw [hr]
  cases read with
  | false =>
    have hn : 2*q.val ≠ 243 := by omega
    simp [physicalRow, hevent, hn]
  | true =>
    by_cases hq : q.val = 121
    · simp [physicalRow, hevent, hq]
    · have hn : 2*q.val ≠ 242 := by omega
      simp [physicalRow, hevent, hq, hn]

/-- The checked destination is not changed by the totalizing modulo. -/
theorem validated_destination (parsed : List RawRow) (hparse : parse = some parsed)
    (hvalid : wellFormed parsed = true) (q : Fin 285) (read : Bool) :
    ∃ r, parsed[2*q.val + (if read then 1 else 0)]? = some r ∧
      (table.row q read).next.val = r.next ∧ r.next < 285 := by
  obtain ⟨r, hl, hs, hr⟩ := validated_row parsed hparse hvalid q read
  refine ⟨r, hl, ?_, hs.2.2.2.1⟩
  simp [hr, physicalRow, Nat.mod_eq_of_lt hs.2.2.2.1]


/-- Under the explicit certificate premises, a transition beeps precisely on
the selected row of the live physical configuration. -/
theorem validated_beepAt (parsed : List RawRow) (hparse : parse = some parsed)
    (hvalid : wellFormed parsed = true) (t : Nat) :
    machine.system.BeepAt t ↔
      (machine.system.run t).state.val = 121 ∧
        (machine.system.run t).tape (machine.system.run t).head = true := by
  rw [Machine.beepAt_iff_row_flag]
  change (table.row (machine.system.run t).state
    ((machine.system.run t).tape (machine.system.run t).head)).beep = true ↔ _
  rw [validated_event parsed hparse hvalid]
  simp

end Shared.PNP.Record285
