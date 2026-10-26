import K26F.FinalAt
import K26F.Root

/-!
# The main theorem for the certificate of order 26 (file prefix k26f), kernel only

`K26F.Root.all` (the kernel checks of all 960,470,402 records, combined from the shard and part modules) instantiates
`K26F/FinalAt.lean`: `μ(ℤ²) ≤ 2725816588621027200 / 1024176292618053632 < 2.6614721`, with no hypotheses and no
native code.
-/

namespace Saw38a.K26F

open Saw38aCore Filter Topology

/-- The certificate of order 26 (file prefix k26f). -/
theorem cert_exists : ∃ c : Cert, c.Valid 26 ∧ c.RatioLE 2725816588621027200 1024176292618053632 :=
  K26FAt.cert_exists _root_.K26F.Root.all

/-- Unconditional: `b_n ≤ C λ^n` for the paper's `λ`. -/
theorem bridge_bound : ∃ C : ℝ, ∀ n : ℕ,
    (bridgeCount n : ℝ) ≤ C * ((2725816588621027200 : ℝ) / 1024176292618053632) ^ n :=
  K26FAt.bridge_bound _root_.K26F.Root.all

/-- Main theorem under `HW`: `μ(ℤ²) ≤ 2725816588621027200 / 1024176292618053632 < 2.6614721`. -/
theorem connective_constant_le (hHW : HW) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (2725816588621027200 : ℝ) / 1024176292618053632 ∧ μ < 2.6614721 :=
  K26FAt.connective_constant_le _root_.K26F.Root.all hHW

/-- Main theorem (no hypothesis): `μ(ℤ²) ≤ 2725816588621027200 / 1024176292618053632 < 2.6614721`. -/
theorem connective_constant_le_unconditional :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (2725816588621027200 : ℝ) / 1024176292618053632 ∧ μ < 2.6614721 :=
  connective_constant_le hw'

end Saw38a.K26F
