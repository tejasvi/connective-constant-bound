import Saw38aCore
import L38Data.All

/-! Native controls at the worst state 7814884826 of the k30e certificate, where the first C++ checker
(checker/check_saw.cpp of the supplement) attains the largest ratio: the exact ratio passes, and num - 1 fails. -/

namespace L38.CtlWorst

/-- Positive: states 7814884326 .. 7814885325 (1000 states around the worst state) pass with the exact ratio. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    105432502045487 39656386815908 7814884326 7814885326 = true := by native_decide

/-- Positive: the worst state alone passes with the exact ratio. -/
theorem worst_ok : Saw38aCore.checkState L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    105432502045487 39656386815908 7814884826 = true := by native_decide

/-- Negative: the worst state fails with num - 1, so the ratio is attained exactly there. -/
theorem worst_num_minus_one : Saw38aCore.checkState L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    105432502045486 39656386815908 7814884826 = false := by native_decide

end L38.CtlWorst
