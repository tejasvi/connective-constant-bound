import Saw38a.CheckMain
import Saw38a.Count
import Saw38a.Mu
import Saw38a.Bridge
import Saw38a.HW
import L38Shard.All

/-!
# The main theorem for the certificate of order 30 (file prefix k30e)

`cert_exists`: the records of `L38Data` form a valid certificate of order 30 with ratio at most
`105432502045487 / 39656386815908` (180 native_decide shards, `L38Shard`, plus the checker's soundness).
With Theorem 4.1 (`Bridge.lean`), Lemma 5.1 (`Count.lean`), Fekete (`Fekete.lean`, `Mu.lean`) and the
Hammersley-Welsh bound (`HW.lean`): `μ(ℤ²) ≤ 105432502045487 / 39656386815908 < 2.6586513`.
-/

namespace Saw38a

open Saw38aCore Filter Topology

/-- Theorem 4.1 and Lemma 5.1 together. -/
theorem bridge_bound_of_cert' (c : Cert) {K num den : ℕ} (hc : c.Valid K) (hr : c.RatioLE num den)
    (hden : 0 < den) : ∃ C : ℝ, ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * ((num : ℝ) / den) ^ n :=
  ⟨c.V c.start, fun n => (Nat.cast_le.2 (bridgeCount_le_autCount' c hc n)).trans (autCount_le' c hc hr hden n)⟩

namespace K30E

theorem decode_start30 : decode 16 0 = some (startPath 30) := by decide

theorem numStates_pos : 0 < L38.Data.numStates := by decide

theorem hstart30 : decode (readRec L38.Data.chunks L38.Data.chunkStates 0).n
    (readRec L38.Data.chunks L38.Data.chunkStates 0).T = some (startPath 30) := by
  rw [L38.Shard.start_ok.1, L38.Shard.start_ok.2]; exact decode_start30

theorem all_states30 : ∀ i < L38.Data.numStates, checkState L38.Data.chunks L38.Data.chunkStates
    L38.Data.numStates 105432502045487 39656386815908 i = true :=
  checkState_of_shards (M := 180) (B := 138547328) (T := 4000) (by decide) (by decide)
    (fun k hk => L38.Shard.shards_ok k hk)

/-- The certificate of order 30 (file prefix k30e). -/
theorem cert_exists : ∃ c : Cert, c.Valid 30 ∧ c.RatioLE 105432502045487 39656386815908 :=
  ⟨certOf L38.Data.chunks L38.Data.chunkStates L38.Data.numStates numStates_pos,
    valid_of_check numStates_pos all_states30 hstart30⟩

/-- Unconditional: `b_n ≤ C λ^n` for the paper's `λ`. -/
theorem bridge_bound : ∃ C : ℝ, ∀ n : ℕ,
    (bridgeCount n : ℝ) ≤ C * ((105432502045487 : ℝ) / 39656386815908) ^ n := by
  obtain ⟨c, hc, hr⟩ := cert_exists
  simpa using bridge_bound_of_cert' c hc hr (by norm_num)

/-- Main theorem under `HW`: `μ(ℤ²) ≤ 105432502045487 / 39656386815908 < 2.6586513`. -/
theorem connective_constant_le (hHW : HW) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (105432502045487 : ℝ) / 39656386815908 ∧ μ < 2.6586513 := by
  obtain ⟨μ, hμ, hle⟩ := connective_constant_le_of_bridge_bound hHW (by positivity) bridge_bound
  exact ⟨μ, hμ, hle, lt_of_le_of_lt hle (by norm_num)⟩

/-- Main theorem (no hypothesis): `μ(ℤ²) ≤ 105432502045487 / 39656386815908 < 2.6586513`. -/
theorem connective_constant_le_unconditional :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (105432502045487 : ℝ) / 39656386815908 ∧ μ < 2.6586513 :=
  connective_constant_le hw'

end K30E

end Saw38a
