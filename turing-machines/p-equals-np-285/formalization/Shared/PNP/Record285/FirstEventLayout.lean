import Shared.PNP.Record285.FirstEventCertificate

/-! Physical field bits immediately before the first marked transition, under
the checked full-configuration relation. The source-variable allocation is
not imported as a Lean theorem here. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.FirstEventLayout
open Shared.PNP.Record285.FirstEventCertificate
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape

theorem numeric_bits : c12.head = -3815 ∧ c12.right.testBit 3829 = true ∧
    c12.right.testBit 3830 = false ∧ c12.right.testBit 3831 = true ∧
    c12.right.testBit 3832 = true ∧ c12.right.testBit 3833 = false := by decide

theorem numeric_anchor : c12.right.testBit 3817 = true ∧ c12.right.testBit 3818 = false := by decide

theorem anchor (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel c12 physical) : physical.tape 3 = true ∧ physical.tape 4 = false := by
  have hh : physical.head = -3815 := h.2.1.symm.trans numeric_bits.1
  have h3 := h.2.2.2.2 3817
  have h4 := h.2.2.2.2 3818
  simp only [aheadPos, Bool.false_eq_true, if_false, hh] at h3 h4
  change physical.tape 3 = c12.right.testBit 3817 at h3
  change physical.tape 4 = c12.right.testBit 3818 at h4
  exact ⟨h3.trans numeric_anchor.1, h4.trans numeric_anchor.2⟩

def numeric_prefix_check : Bool :=
  (List.range 5).all fun i => c12.right.testBit (3819+2*i) &&
    !(c12.right.testBit (3820+2*i))

theorem numeric_prefix_valid : numeric_prefix_check = true := by decide

theorem first_five_fields (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel c12 physical) : ∀ i : Nat, i < 5 →
      physical.tape (5+2*(i:Int)) = true ∧ physical.tape (6+2*(i:Int)) = false := by
  have hh : physical.head = -3815 := h.2.1.symm.trans numeric_bits.1
  intro i hi
  have ht := List.all_eq_true.mp numeric_prefix_valid i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at ht
  have hz : c12.right.testBit (3820+2*i) = false := by
    cases hhbit : c12.right.testBit (3820+2*i) <;> simp_all
  have ha := h.2.2.2.2 (3819+2*i)
  have hb := h.2.2.2.2 (3820+2*i)
  simp only [aheadPos, Bool.false_eq_true, if_false, hh] at ha hb
  have hpa : (-3815:Int)+((3819+2*i:Nat):Int)+1 = 5+2*(i:Int) := by omega
  have hpb : (-3815:Int)+((3820+2*i:Nat):Int)+1 = 6+2*(i:Int) := by omega
  rw [hpa] at ha
  rw [hpb] at hb
  exact ⟨ha.trans ht.1, hb.trans hz⟩

/-- In the checked tape, field 5 is `10` and field 6 is `110`.
The author allocation identifies these with program and exponent respectively;
that external allocation-to-source correspondence remains a separate proof. -/
theorem field_five_six (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel c12 physical) :
    physical.tape 15 = true ∧ physical.tape 16 = false ∧
    physical.tape 17 = true ∧ physical.tape 18 = true ∧ physical.tape 19 = false := by
  have hh : physical.head = -3815 := h.2.1.symm.trans numeric_bits.1
  have h15 := h.2.2.2.2 3829
  have h16 := h.2.2.2.2 3830
  have h17 := h.2.2.2.2 3831
  have h18 := h.2.2.2.2 3832
  have h19 := h.2.2.2.2 3833
  simp only [aheadPos, Bool.false_eq_true, if_false, hh] at h15 h16 h17 h18 h19
  change physical.tape 15 = c12.right.testBit 3829 at h15
  change physical.tape 16 = c12.right.testBit 3830 at h16
  change physical.tape 17 = c12.right.testBit 3831 at h17
  change physical.tape 18 = c12.right.testBit 3832 at h18
  change physical.tape 19 = c12.right.testBit 3833 at h19
  rw [numeric_bits.2.1] at h15
  rw [numeric_bits.2.2.1] at h16
  rw [numeric_bits.2.2.2.1] at h17
  rw [numeric_bits.2.2.2.2.1] at h18
  rw [numeric_bits.2.2.2.2.2] at h19
  exact ⟨h15,h16,h17,h18,h19⟩

end Shared.PNP.Record285.FirstEventLayout
