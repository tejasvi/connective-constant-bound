import Saw38aKP.MainB
import Saw38a.Count
import Saw38a.Mu
import Saw38a.Bridge
import Saw38a.HW
import K26FData.Top

/-!
# The main theorems for the certificate of order 26 (file prefix k26f), from the range check

Everything except the kernel checks of the records: given `checkRangeB2 rd NT num den 0 NT = true` (proved in
`K26F/Root.lean` from the shard modules), the records of `K26FData` form a valid certificate of order 26 with ratio at
most `2725816588621027200 / 1024176292618053632` (`valid_of_checkB2`). With Theorem 4.1 (`Bridge.lean`), Lemma 5.1
(`Count.lean`), Fekete (`Fekete.lean`, `Mu.lean`) and the Hammersley-Welsh bound (`HW.lean`):
`μ(ℤ²) ≤ 2725816588621027200 / 1024176292618053632 < 2.6614721`.
-/

namespace Saw38a

open Saw38aCore Saw38aK Filter Topology

/-- Theorem 4.1 and Lemma 5.1 together (as in the k30e assembly). -/
theorem bridge_bound_of_cert' (c : Cert) {K num den : ℕ} (hc : c.Valid K) (hr : c.RatioLE num den)
    (hden : 0 < den) : ∃ C : ℝ, ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * ((num : ℝ) / den) ^ n :=
  ⟨c.V c.start, fun n => (Nat.cast_le.2 (bridgeCount_le_autCount' c hc n)).trans (autCount_le' c hc hr hden n)⟩

namespace K26FAt

theorem numStates_pos : 0 < K26FData.NT := by decide

theorem start_rec : (K26FData.rd 0).n = 14 ∧ (K26FData.rd 0).T = 0 := by decide +kernel

theorem hstart26 : decode (K26FData.rd 0).n (K26FData.rd 0).T = some (startPath 26) := by
  rw [start_rec.1, start_rec.2]; exact decode_start

variable (hall : checkRangeB2 K26FData.rd K26FData.NT 2725816588621027200 1024176292618053632 0 K26FData.NT = true)

include hall in
theorem all_states26 : ∀ i < K26FData.NT,
    checkStateB2 K26FData.rd K26FData.NT 2725816588621027200 1024176292618053632 i = true :=
  fun i hi => checkRangeB2_sound hall i (Nat.zero_le _) (by omega)

include hall in
/-- The certificate of order 26 (file prefix k26f). -/
theorem cert_exists : ∃ c : Cert, c.Valid 26 ∧ c.RatioLE 2725816588621027200 1024176292618053632 :=
  ⟨certOfB K26FData.rd K26FData.NT numStates_pos, valid_of_checkB2 numStates_pos (all_states26 hall) hstart26⟩

include hall in
/-- Unconditional: `b_n ≤ C λ^n` for the paper's `λ`. -/
theorem bridge_bound : ∃ C : ℝ, ∀ n : ℕ,
    (bridgeCount n : ℝ) ≤ C * ((2725816588621027200 : ℝ) / 1024176292618053632) ^ n := by
  obtain ⟨c, hc, hr⟩ := cert_exists hall
  simpa using bridge_bound_of_cert' c hc hr (by norm_num)

include hall in
/-- Main theorem under `HW`: `μ(ℤ²) ≤ 2725816588621027200 / 1024176292618053632 < 2.6614721`. -/
theorem connective_constant_le (hHW : HW) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (2725816588621027200 : ℝ) / 1024176292618053632 ∧ μ < 2.6614721 := by
  obtain ⟨μ, hμ, hle⟩ := connective_constant_le_of_bridge_bound hHW (by positivity) (bridge_bound hall)
  exact ⟨μ, hμ, hle, lt_of_le_of_lt hle (by norm_num)⟩

end K26FAt

end Saw38a
