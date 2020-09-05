/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import common

inductive big_step : (stmt × scope) → scope → Prop
| skip {s : scope} : big_step (stmt.skip, s) s
| assign {x : string} {a : scope → Prop} {s : scope} :
    big_step (stmt.assign x a, s) (s{x ↦ a s})
| seq {S T : stmt} {s t u : scope} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) : big_step (S ;; T, s) u
| ite_true {b : scope → Prop} {S T : stmt} {s t : scope} (hcond : b s)
    (hbody : big_step (S, s) t) : big_step (stmt.ite b S T, s) t
| ite_false {b : scope → Prop} {S T : stmt} {s t : scope} (hcond : ¬ b s)
    (hbody : big_step (T, s) t) : big_step (stmt.ite b S T, s) t
| while_true {b : scope → Prop} {S : stmt} {s t u: scope} (hcond : b s)
    (hbody : big_step (S, s) t) (hrest : big_step (stmt.while b S, t) u) :
        big_step (stmt.while b S, s) u
| while_false {b : scope → Prop} {S : stmt} {s t u : scope} (hcond : ¬ b s) :
    big_step (stmt.while b S, s) s

infix ` ⟹ `:110 := big_step
