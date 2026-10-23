import Saw38aCore
import L38Data.All

/-! Native controls for the high bits of the 35-bit child indices (k30e). -/

namespace L38.Ctl35

/-- Positive: the 1000 states from index 2^34 pass the check. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates 105432502045487 39656386815908
    17179869184 17179870184 = true := by native_decide

/-- Positive: state 8589934593 has child index 11909347156 (bit 33 set) in slot 0, as in the certificate file. -/
theorem child_ok_b33_s0 : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 8589934593).c0 = 11909347156 := by
  native_decide

/-- Negative: without bit 33 the same child index would be 3319412564; it is not. -/
theorem child_no_b33_s0 :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 8589934593).c0 = 3319412564) = false := by
  native_decide

/-- Positive: state 8589934594 has child index 9721375147 (bit 33 set) in slot 1, as in the certificate file. -/
theorem child_ok_b33_s1 : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 8589934594).c1 = 9721375147 := by
  native_decide

/-- Negative: without bit 33 the same child index would be 1131440555; it is not. -/
theorem child_no_b33_s1 :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 8589934594).c1 = 1131440555) = false := by
  native_decide

/-- Positive: state 8589934597 has child index 9721375154 (bit 33 set) in slot 2, as in the certificate file. -/
theorem child_ok_b33_s2 : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 8589934597).c2 = 9721375154 := by
  native_decide

/-- Negative: without bit 33 the same child index would be 1131440562; it is not. -/
theorem child_no_b33_s2 :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 8589934597).c2 = 1131440562) = false := by
  native_decide

/-- Positive: state 17179869184 has child index 21504313388 (bit 34 set) in slot 0, as in the certificate file. -/
theorem child_ok_b34_s0 : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 17179869184).c0 = 21504313388 := by
  native_decide

/-- Negative: without bit 34 the same child index would be 4324444204; it is not. -/
theorem child_no_b34_s0 :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 17179869184).c0 = 4324444204) = false := by
  native_decide

/-- Positive: state 17179869190 has child index 21504313394 (bit 34 set) in slot 1, as in the certificate file. -/
theorem child_ok_b34_s1 : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 17179869190).c1 = 21504313394 := by
  native_decide

/-- Negative: without bit 34 the same child index would be 4324444210; it is not. -/
theorem child_no_b34_s1 :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 17179869190).c1 = 4324444210) = false := by
  native_decide

/-- Positive: state 17179869189 has child index 21504313393 (bit 34 set) in slot 2, as in the certificate file. -/
theorem child_ok_b34_s2 : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 17179869189).c2 = 21504313393 := by
  native_decide

/-- Negative: without bit 34 the same child index would be 4324444209; it is not. -/
theorem child_no_b34_s2 :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates 17179869189).c2 = 4324444209) = false := by
  native_decide

/-- Negative: with N = 2^34 the window fails (children above 2^34 are out of range). -/
theorem window_bound_fails : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates 17179869184 105432502045487 39656386815908
    17179869184 17179870184 = false := by native_decide

/-- Negative: with a misaligned record layout (chunk size + 1) the window fails. -/
theorem window_misaligned_fails : Saw38aCore.checkRange L38.Data.chunks (L38.Data.chunkStates + 1) L38.Data.numStates
    105432502045487 39656386815908 17179869184 17179870184 = false := by native_decide

end L38.Ctl35
