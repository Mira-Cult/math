import PASoundness.M236ListScheduleObserver
import PASoundness.Schedule
namespace PASoundness.M236.ListSchedule
example : scheduledAddress 0 = ⟨1, 0, [0]⟩ := by
  simp [scheduledAddress, atStage, decode, Cantor.unpair, Cantor.unpairAux]
example : scheduledAddress 1 = ⟨1, 1, [0]⟩ := by
  simp [scheduledAddress, atStage, decode, Cantor.unpair, Cantor.unpairAux]
example : scheduledAddress 1 ≠ PASoundness.Schedule.scheduledAddress 1 := by
  simp [scheduledAddress, atStage, decode, Cantor.unpair, Cantor.unpairAux,
    PASoundness.Schedule.scheduledAddress, PASoundness.Schedule.decodeCoordinates]
end PASoundness.M236.ListSchedule
