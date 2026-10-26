import Saw38aK.CheckB2
import K26FData.Top

/-!
# Controls of the kernel checker on the k26f table

Each line is a kernel evaluation (`decide +kernel`). Must-pass: the state where the certificate attains its largest
ratio (state 1062168, as printed by the certificate's own checker) passes with the exact ratio. Must-fail: the same state
with the numerator lowered by one; the same state with its weight halved; record 0 with its first child slot emptied
(the step is neither in the state nor trapped); the index just past the table (a padding record that does not decode).
-/

namespace K26FCtl

open Saw38aK Saw38aCore K26FData

/-- Record `1062168` with its weight halved. -/
noncomputable def rdHalfV (i : Nat) : Rec := if i = 1062168 then { rd i with V := (rd i).V / 2 } else rd i

/-- Record `0` with its first child slot emptied. -/
noncomputable def rdNoChild (i : Nat) : Rec := if i = 0 then { rd 0 with c0 := NONEK } else rd i

theorem worst_pass : checkStateB2 rd NT 2725816588621027200 1024176292618053632 1062168 = true := by decide +kernel

theorem worst_num_minus_one : checkStateB2 rd NT 2725816588621027199 1024176292618053632 1062168 = false := by
  decide +kernel

theorem halved_weight : checkStateB2 rdHalfV NT 2725816588621027200 1024176292618053632 1062168 = false := by
  decide +kernel

theorem emptied_slot : checkStateB2 rdNoChild NT 2725816588621027200 1024176292618053632 0 = false := by
  decide +kernel

theorem past_table : checkStateB2 rd NT 2725816588621027200 1024176292618053632 NT = false := by decide +kernel

end K26FCtl
