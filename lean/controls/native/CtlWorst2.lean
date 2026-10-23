import Saw38aCore
import L38Data.All

/-! Native controls at state 1944116169 of the k30e certificate, where independent/check38a.cpp of the supplement first
attains the largest ratio (a tie with state 7814884826, CtlWorst.lean): the exact ratio passes, and num - 1 fails. -/

namespace L38.CtlWorst2

/-- Positive: states 1944115669 .. 1944116668 (1000 states around the state) pass with the exact ratio. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    105432502045487 39656386815908 1944115669 1944116669 = true := by native_decide

/-- Positive: the state alone passes with the exact ratio. -/
theorem tie_ok : Saw38aCore.checkState L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    105432502045487 39656386815908 1944116169 = true := by native_decide

/-- Negative: the state fails with num - 1, so the ratio is attained exactly there too. -/
theorem tie_num_minus_one : Saw38aCore.checkState L38.Data.chunks L38.Data.chunkStates L38.Data.numStates
    105432502045486 39656386815908 1944116169 = false := by native_decide

end L38.CtlWorst2
