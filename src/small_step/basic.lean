/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import common

inductive small_step : (stmt × scope × ℕ) → (stmt × scope × ℕ) → Prop
| assign {x : string} {a : scope → Prop} {s : scope} {i : ℕ}:
    small_step (stmt.assign x a, s, i) (stmt.skip, s{x ↦ a s}, i.succ)
| comp_step {S S' T : stmt} {s s' : scope} {i : ℕ}
    (hS : small_step (S, s, i) (S', s', i.succ)) :
        small_step (S ;; T, s, i) (S' ;; T, s', i.succ)
| comp_skip {T : stmt} {s : scope} {i : ℕ} :
    small_step (stmt.skip ;; T, s, i) (T, s, i)
| ite_true {b : scope → Prop} {S T : stmt} {s : scope} {i : ℕ}
    (hcond : b s) : small_step (stmt.ite b S T, s, i) (S, s, i.succ)
| ite_false {b : scope → Prop} {S T : stmt} {s : scope} {i : ℕ}
    (hcond : ¬ b s) : small_step (stmt.ite b S T, s, i) (T, s, i.succ)
| while {b : scope → Prop} {S : stmt} {s : scope} {i : ℕ} :
    small_step (stmt.while b S, s, i)
        (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i.succ)
| call {f : string} {v₀ v₁ : scope → Prop} {σ : scope → scope} {F : stmt}
    {s : scope} {i : ℕ} (args : v₀ s ∧ v₁ s) :
        small_step (stmt.call f v₀ v₁ σ F, s, i) (F, (σ s), i.succ)

infixr ` ⇒ `:110 := small_step  -- ⇒ \=>
infixr ` => `:110 := small_step

/-
Instructions for how to use small_step and its notation

Small step semantics are used to represent the change in execution state from
a single instruction or composition of instructions that is executed
synchronously/deterministically. A small_step can be defined using the
following notation

                            (S, s, i) ⟹ (T, t, i + 1)

where S T are each a statement (from common.stmt) and s t are each a
scope (from common.basic). i is the step number, where 0 represents the first
instruction in a sequence of instructions. This notation constructs an instance
of small_step that represents the execution of stmt S with scope s that
results in scope t, where stmt S is the ith instruction.
-/
namespace small_step

/-
Sequent:


        Assign  ____________________________________________

                (x := a, s, i) ⇒ (skip, s{x ↦ a s}, i + 1)
-/

/-
Sequent:

                          (S, s, i) ⇒ (S', s', i + 1)
        Comp-Step   ______________________________________

                    (S ;; T, s, i) ⇒ (S' ;; T, s', i + 1)
-/

/-
Sequent:


        Comp-Skip   ______________________________

                    (skip ;; T, s, i) ⇒ (T, s, i)
-/

/-
Sequent:


If-Then-Else-True   ___________________________________________ (b s) is TRUE

                    (if b then S else T, s, i) ⇒ (S, s, i + 1)
-/

/-
Sequent:


If-Then-Else-False  ___________________________________________ (b s) is FALSE

                    (if b then S else T, s, i) ⇒ (T, s, i + 1)
-/

/-
Sequent:

While
    ___________________________________________________________________________

    (while b do S, s, i) ⇒ (if b then (S ;; while b do S) else skip, s, i + 1)
-/

/-
Sequent:


While-True  _____________________________________________________ (b s) is TRUE

            (while b do S, s, i) ⇒ (S ;; while b do S, s, i + 1)
-/

/-
Sequent:


While-False     ________________________________________ (b s) is FALSE

                (while b do S, s, i) ⇒ (skip, s, i + 1)
-/

/-
Sequent:

    Call    _____________________________________________ ∀ args,
                                                        args = (v₀ s) ∧ (v₁ s)
            (call f v₀ v₁ σ F, s, i) ⇒ (F, (σ s), i + 1)
-/

end small_step
