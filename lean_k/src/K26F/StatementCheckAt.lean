import Saw38a.Statements
import K26F.FinalAt
import Saw38a.Fekete

/-! Before the shard builds: the parametric theorems of `FinalAt` have the statements of `Saw38a/Statements.lean` once the
range check is supplied; axioms of the proof layer. -/

open Saw38aCore Saw38aK in
example (hall : checkRangeB2 K26FData.rd K26FData.NT 2725816588621027200 1024176292618053632 0 K26FData.NT = true) :
    type_of% @Saw38a.cert_exists = type_of% @(Saw38a.K26FAt.cert_exists hall) := rfl

#print axioms Saw38a.K26FAt.cert_exists
#print axioms Saw38a.K26FAt.connective_constant_le
#print axioms Saw38a.valid_of_checkB2
