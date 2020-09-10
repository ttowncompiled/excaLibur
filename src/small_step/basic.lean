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
        (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i)
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

/- There is no successor step for skip. -/
lemma skip_no_succ {S' : stmt} {s s' : scope} {i : ℕ} :
    ¬ ((stmt.skip, s, i) ⇒ (S', s', i.succ)) :=
begin
    intro h,
    cases h,
end

/-
Sequent:


        Assign  ____________________________________________

                (x := a, s, i) ⇒ (skip, s{x ↦ a s}, i + 1)
-/
@[simp] lemma assign_iff {x : string} {a : scope → Prop} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} :
    (stmt.assign x a, s, i) ⇒ Us ↔ Us = (stmt.skip, s{x ↦ a s}, i.succ) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        refl,
    },
    {
        intro h₂,
        rw h₂,
        exact assign,
    }
end

/-
Sequent:

                S ≠ skip ∧ (S, s, i) ⇒ (S', s', i + 1)  S = skip ∧ (T, s, i)
        Comp    _____________________________________________________________

                            (S ;; T, s, i) ⇒ (S' ;; T, s', i + 1)
-/
@[simp] lemma comp_iff {S T : stmt} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} : (S ;; T, s, i) ⇒ Us ↔
        ((∃ (S' : stmt) (s' : scope), (S, s, i) ⇒ (S', s', i.succ) ∧
            Us = (S' ;; T, s', i.succ)) ∨ (S = stmt.skip ∧ Us = (T, s, i))) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply or.intro_left,
            apply exists.intro h₁_S',
            apply exists.intro h₁_s',
            apply and.intro h₁_hS (rfl),
        },
        {
            apply or.intro_right,
            apply and.intro (rfl) (rfl),
        }
    },
    {
        intro h₂,
        cases h₂,
        {
            cases h₂ with h₂_S' h₂,
            cases h₂ with h₂_s' h₂,
            cases h₂ with hS hUs,
            rw hUs,
            exact comp_step hS,
        },
        {
            cases h₂ with hS hUs,
            rw [hS, hUs],
            exact comp_skip,
        }
    }
end

/-
Sequent:

                          (S, s, i) ⇒ (S', s', i + 1)
        Comp-Step   ______________________________________

                    (S ;; T, s, i) ⇒ (S' ;; T, s', i + 1)
-/
@[simp] lemma comp_step_iff {S T : stmt} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} (hS : S ≠ stmt.skip) : (S ;; T, s, i) ⇒ Us ↔
        (∃ (S' : stmt) (s' : scope), ((S, s, i) ⇒ (S', s', i.succ) ∧
            Us = (S' ;; T, s', i.succ))) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply exists.intro h₁_S',
            apply exists.intro h₁_s',
            apply and.intro h₁_hS (rfl),
        },
        {
            exfalso,
            apply hS,
            refl,
        }
    },
    {
        intro h₂,
        cases h₂ with S' h₂,
        cases h₂ with s' h₂,
        cases h₂ with h₂_hS h₂_Us,
        rw h₂_Us,
        exact comp_step h₂_hS,
    }
end

/-
Sequent:


        Comp-Skip   ______________________________

                    (skip ;; T, s, i) ⇒ (T, s, i)
-/
@[simp] lemma comp_skip_iff {T : stmt} {s : scope} {i : ℕ}
    {Ut : stmt × scope × ℕ} : (stmt.skip ;; T, s, i) ⇒ Ut ↔ Ut = (T, s, i) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exfalso,
            apply @skip_no_succ h₁_S' s h₁_s' i,
            exact h₁_hS,
        },
        {
            refl,
        }
    },
    {
        intro h₂,
        rw h₂,
        exact comp_skip,
    }
end

/-
Sequent:

                        (b s) ∧ (S, s, i + 1)     ¬ (b s) ∧ (T, s, i+1)
        If-Then-Else    _______________________________________________

                                  (if b then S else T, s, i)
-/
@[simp] lemma ite_iff {b : scope → Prop} {S T : stmt} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} : (stmt.ite b S T, s, i) ⇒ Us ↔
        (b s ∧ Us = (S, s, i.succ)) ∨ (¬ b s ∧ Us = (T, s, i.succ)) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply or.intro_left,
            apply and.intro h₁_hcond (rfl),
        },
        {
            apply or.intro_right,
            apply and.intro h₁_hcond (rfl),
        }
    },
    {
        intro h₂,
        cases h₂,
        {
            cases h₂ with h₂_hcond h₂,
            rw h₂,
            exact ite_true h₂_hcond,
        },
        {
            cases h₂ with h₂_hcond h₂,
            rw h₂,
            exact ite_false h₂_hcond,
        }
    }
end

/-
Sequent:


If-Then-Else-True   ___________________________________________ (b s) is TRUE

                    (if b then S else T, s, i) ⇒ (S, s, i + 1)
-/
@[simp] lemma ite_true_iff {b : scope → Prop} {S T : stmt} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} (hcond : b s) : (stmt.ite b S T, s, i) ⇒ Us ↔
        Us = (S, s, i.succ) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁ with h₁_hcond h₁,
        {
            refl,
        },
        {
            exfalso,
            apply h₁_hcond,
            exact hcond,
        }
    },
    {
        intro h₂,
        rw h₂,
        exact ite_true hcond,
    }
end

/-
Sequent:


If-Then-Else-False  ___________________________________________ (b s) is FALSE

                    (if b then S else T, s, i) ⇒ (T, s, i + 1)
-/
@[simp] lemma ite_false_iff {b : scope → Prop} {S T : stmt} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} (hcond : ¬ b s) : (stmt.ite b S T, s, i) ⇒ Us ↔
        Us = (T, s, i.succ) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exfalso,
            apply hcond,
            exact h₁_hcond,
        },
        {
            refl,
        }
    },
    {
        intro h₂,
        rw h₂,
        exact ite_false hcond,
    }
end

/-
Sequent:

While
    _______________________________________________________________________

    (while b do S, s, i) ⇒ (if b then (S ;; while b do S) else skip, s, i)
-/
lemma while_iff {b : scope → Prop} {S : stmt} {s : scope} {i : ℕ}
    {Us : stmt × scope × ℕ} : (stmt.while b S, s, i) ⇒ Us ↔
        Us = (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        refl,
    },
    {
        intro h₂,
        rw h₂,
        exact while,
    }
end

/-
Sequent:

            (if b then S else T, s, i) ⇒ (S ;; while b do S, s, i + 1)
While-True  __________________________________________________________
                                                                  (b s) is TRUE
              (while b do S, s, i) ⇒* (S ;; while b do S, s, i + 1)
-/
lemma while_true_iff {b : scope → Prop} {S : stmt} {s : scope} {i : ℕ}
    (hcond : b s) : (stmt.while b S, s, i) ⇒
            (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i) ↔
        (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i) ⇒
            ((S ;; stmt.while b S), s, i.succ) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        exact ite_true hcond,
    },
    {
        intro h₂,
        cases h₂,
        exact while,
    }
end

/-
Sequent:

                (if b then S else T, s, i) ⇒ (skip, s, i + 1)
While-False     _____________________________________________ (b s) is FALSE

                  (while b do S, s, i) ⇒* (skip, s, i + 1)
-/
@[simp] lemma while_false_iff {b : scope → Prop} {S : stmt} {s : scope} {i : ℕ}
    (hcond : ¬ b s) : (stmt.while b S, s, i) ⇒
            (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i) ↔
        (stmt.ite b (S ;; stmt.while b S) stmt.skip, s, i) ⇒
            (stmt.skip, s, i.succ) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        exact ite_false hcond,
    },
    {
        intro h₂,
        cases h₂,
        exact while,
    }
end

/-
Sequent:

    Call    _____________________________________________ ∀ args,
                                                        args = (v₀ s) ∧ (v₁ s)
            (call f v₀ v₁ σ F, s, i) ⇒ (F, (σ s), i + 1)
-/
@[simp] lemma call_iff {f : string} {v₀ v₁ : scope → Prop} {σ : scope → scope}
    {F : stmt} {s : scope} {i : ℕ} {Us : stmt × scope × ℕ}
    (args : v₀ s ∧ v₁ s) : (stmt.call f v₀ v₁ σ F, s, i) ⇒ Us ↔
        Us = (F, (σ s), i.succ) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        refl,
    },
    {
        intro h₂,
        rw h₂,
        exact call args,
    }
end

end small_step
