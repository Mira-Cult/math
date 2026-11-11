import Sude.FactorSegmentCertificate

/-! Generated factor/Lucas evidence for the 54 odd candidates ending at
the first FTT endpoint. Lean checks every certificate node and row. -/
namespace Sude.GeneratedPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def firstTailNodes : List Lucas.Node := [
  ⟨2, 1, []⟩,
  ⟨3, 2, [(2, 1)]⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨7, 3, [(2, 1), (3, 1)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨13, 2, [(2, 2), (3, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨23, 5, [(2, 1), (11, 1)]⟩,
  ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
  ⟨37, 2, [(2, 2), (3, 2)]⟩,
  ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
  ⟨97, 5, [(2, 5), (3, 1)]⟩,
  ⟨131, 2, [(2, 1), (5, 1), (13, 1)]⟩,
  ⟨173, 2, [(2, 2), (43, 1)]⟩,
  ⟨277, 5, [(2, 2), (3, 1), (23, 1)]⟩,
  ⟨547, 2, [(2, 1), (3, 1), (7, 1), (13, 1)]⟩,
  ⟨1021, 10, [(2, 2), (3, 1), (5, 1), (17, 1)]⟩,
  ⟨1109, 2, [(2, 2), (277, 1)]⟩,
  ⟨1471, 6, [(2, 1), (3, 1), (5, 1), (7, 2)]⟩,
  ⟨1613, 3, [(2, 2), (13, 1), (31, 1)]⟩,
  ⟨3299, 2, [(2, 1), (17, 1), (97, 1)]⟩,
  ⟨9001, 7, [(2, 3), (3, 2), (5, 3)]⟩,
  ⟨28051, 2, [(2, 1), (3, 1), (5, 2), (11, 1), (17, 1)]⟩,
  ⟨30631, 3, [(2, 1), (3, 1), (5, 1), (1021, 1)]⟩,
  ⟨31051, 11, [(2, 1), (3, 3), (5, 2), (23, 1)]⟩,
  ⟨77029, 2, [(2, 2), (3, 1), (7, 2), (131, 1)]⟩,
  ⟨67939523, 2, [(2, 1), (7, 1), (173, 1), (28051, 1)]⟩,
  ⟨67939549, 7, [(2, 2), (3, 1), (17, 1), (37, 1), (9001, 1)]⟩,
  ⟨67939559, 7, [(2, 1), (1109, 1), (30631, 1)]⟩,
  ⟨67939561, 23, [(2, 3), (3, 4), (5, 1), (13, 1), (1613, 1)]⟩,
  ⟨67939579, 2, [(2, 1), (3, 2), (7, 2), (77029, 1)]⟩,
  ⟨67939589, 2, [(2, 2), (547, 1), (31051, 1)]⟩,
  ⟨67939607, 5, [(2, 1), (7, 1), (1471, 1), (3299, 1)]⟩
]

def firstTailFactors : List ℕ := [7, 3, 5, 31, 3, 37, 277, 3, 4027, 1063, 3, 0, 5, 3, 7, 11, 3, 5, 337, 3, 67, 7, 3, 13, 0, 3, 11, 5, 3, 0, 0, 3, 5, 73, 3, 7, 13, 3, 5189, 0, 3, 41, 5, 3, 0, 109, 3, 5, 11, 3, 5237, 977, 3, 0]

theorem firstTailNodes_checked : Lucas.checkCertificate firstTailNodes = true := by
  decide +kernel

theorem firstTailFactors_checked : checkFactorRows (firstTailNodes.map Lucas.Node.value) 67939501 firstTailFactors = true := by
  decide +kernel

theorem firstTailSegment_exact :
    (factorSurvivors 67939501 firstTailFactors).toFinset =
      oddPrimeSegment 67939501 ( 67939501 + 2 * firstTailFactors.length) := by
  apply factor_certificate_segment firstTailNodes 67939501 firstTailFactors
  · exact firstTailNodes_checked
  · exact firstTailFactors_checked
  · decide +kernel

theorem firstTailSegment_count : (factorSurvivors 67939501 firstTailFactors).length = 7 := by
  decide +kernel

theorem firstTailSegment_sum : (factorSurvivors 67939501 firstTailFactors).sum = 475576967 := by
  decide +kernel

theorem firstTailPrimeSegment_count_sum :
    (oddPrimeSegment 67939501 67939609).card = 7 ∧
    (∑ p ∈ oddPrimeSegment 67939501 67939609, p) = 475576967 := by
  have h := factor_certificate_count_sum firstTailNodes 67939501 firstTailFactors
    firstTailNodes_checked firstTailFactors_checked (by decide)
  rw [firstTailSegment_count, firstTailSegment_sum] at h
  simpa only [show firstTailFactors.length = 54 by decide +kernel,
    show 67939501 + 2 * 54 = 67939609 by decide] using h

end Sude.GeneratedPrefix
