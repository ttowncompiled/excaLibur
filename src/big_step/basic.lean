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
| comp {S T : stmt} {s t u : scope} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) : big_step (S ;; T, s) u
| ite_true {b : scope → Prop} {S T : stmt} {s t : scope} (hcond : b s)
    (hbody : big_step (S, s) t) : big_step (stmt.ite b S T, s) t
| ite_false {b : scope → Prop} {S T : stmt} {s t : scope} (hcond : ¬ b s)
    (hbody : big_step (T, s) t) : big_step (stmt.ite b S T, s) t
| while_true {b : scope → Prop} {S : stmt} {s t u: scope} (hcond : b s)
    (hbody : big_step (S, s) t) (hrest : big_step (stmt.while b S, t) u) :
        big_step (stmt.while b S, s) u
| while_false {b : scope → Prop} {S : stmt} {s : scope} (hcond : ¬ b s) :
    big_step (stmt.while b S, s) s
| call {f : string} {v₀ v₁ : scope → Prop} {F : stmt} {s t : scope}
    {σ : scope → scope} (args : (v₀ s) ∧ (v₁ s)) (hF : big_step (F, (σ s)) t)
        : big_step (stmt.call f v₀ v₁ σ F, s) t

infix ` ⟹ `:110 := big_step -- ⟹ \==>
infix ` ==> `:110 := big_step

/-
Instructions for how to use big_step and its notation

Big step semantics are used to represent the scope change of an instruction or
composition of instructions that is executed synchronously/deterministically.
A big_step can be defined using the following notation

                                (S, s) ⟹ t

where S is a statement (from common.stmt) and s t are each a
scope (from common.basic). This notation constructs an instance of big_step
that represents the execution of stmt S with scope s that results in scope t.
-/
namespace big_step

/-
Sequent:


        Skip    _______________

                (skip, s) ⟹ s
-/
@[simp] lemma skip_iff {s t : scope} : (stmt.skip, s) ⟹ t ↔ t = s :=
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
        exact big_step.skip,
    }
end

/-
Sequent:


        Assign  __________________________

                {x := a, s) ⟹ s{x ↦ a s}
-/
@[simp] lemma assign_iff {x : string} {a : scope → Prop} {s t : scope} :
    (stmt.assign x a, s) ⟹ t ↔ t = (s{x ↦ a s}) :=
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
        exact big_step.assign,
    }
end

/-
Sequent:

                (S, s) ⟹ t  (T, t) ⟹ u
        Comp    ________________________

                    (S ;; T, s) ⟹ u
-/
@[simp] lemma comp_iff {S T : stmt} {s u : scope} :
    (S ;; T, s) ⟹ u ↔ (∃ (t : scope), (S, s) ⟹ t ∧ (T, t) ⟹ u) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        apply exists.intro,
        apply and.intro h₁_hS h₁_hT,
    },
    {
        intro h₂,
        cases h₂,
        cases h₂_h,
        apply big_step.comp h₂_h_left h₂_h_right,
    }
end

/-
Sequent:

                        (b s) ∧ (S, s) ⟹ t     ¬ (b s) ∧ (T, s) ⟹ t
        If-Then-Else    _____________________________________________

                                  (if b then S else T, s) ⟹ t
-/
@[simp] lemma ite_iff {b : scope → Prop} {S T : stmt} {s t : scope} :
    (stmt.ite b S T, s) ⟹ t ↔ (b s ∧ (S, s) ⟹ t) ∨ (¬ b s ∧ (T, s) ⟹ t) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply or.intro_left,
            apply and.intro h₁_hcond h₁_hbody,
        },
        {
            apply or.intro_right,
            apply and.intro h₁_hcond h₁_hbody,
        }
    },
    {
        intro h₂,
        cases h₂,
        {
            cases h₂,
            apply big_step.ite_true h₂_left h₂_right,
        },
        {
            cases h₂,
            apply big_step.ite_false h₂_left h₂_right,
        }
    }
end

/-
Sequent:

                                    (S, s) ⟹ t
        If-Then-Else-True   _____________________________ (b s) is TRUE

                            (if b then S else T, s) ⟹ t
-/
@[simp] lemma ite_true_iff {b : scope → Prop} {S T : stmt} {s t : scope}
    (hcond : b s) : (stmt.ite b S T, s) ⟹ t ↔ (S, s) ⟹ t :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exact h₁_hbody,
        },
        {
            exfalso,
            apply h₁_hcond hcond,
        }
    },
    {
        intro h₂,
        apply big_step.ite_true hcond h₂,
    }
end

/-
Sequent:

                                    (T, s) ⟹ t
        If-Then-Else-False  _____________________________ (b s) is FALSE

                            (if b then S else T, s) ⟹ t
-/
@[simp] lemma ite_false_iff {b : scope → Prop} {S T : stmt} {s t : scope}
    (hcond : ¬ b s) : (stmt.ite b S T, s) ⟹ t ↔ (T, s) ⟹ t :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exfalso,
            apply hcond h₁_hcond,
        },
        {
            exact h₁_hbody,
        }
    },
    {
        intro h₂,
        apply big_step.ite_false hcond h₂,
    }
end

/-
Sequent:

        (b s) ∧ (S, s) ⟹ t  (b s) ∧ (while b do S, t) ⟹ u   ¬ (b s) ∧ u = s
While   _____________________________________________________________________

                            (while b do S, s) ⟹ u
-/
lemma while_iff {b : scope → Prop} {S : stmt} {s u : scope} :
    (stmt.while b S, s) ⟹ u ↔ (b s ∧ (∃ (t : scope), (S, s) ⟹ t
        ∧ (stmt.while b S, t) ⟹ u)) ∨ (¬ b s ∧ u = s) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply or.intro_left,
            split,
                exact h₁_hcond,
            apply exists.intro h₁_t,
            apply and.intro h₁_hbody h₁_hrest,
        },
        {
            apply or.intro_right,
            apply and.intro h₁_hcond (rfl),
        }
    },
    {
        intro h₂,
        cases h₂,
        case or.inl {
            cases h₂ with hb h₂,
            cases h₂ with t h₂,
            cases h₂ with hS hwhile,
            exact big_step.while_true hb hS hwhile,
        },
        case or.inr {
            cases h₂ with hb h₂,
            rw h₂,
            apply big_step.while_false hb,
        }
    }
end

/-
Sequent:

                    (S, s) ⟹ t      (while b do S, t) ⟹ u
        While-True  _______________________________________ (b s) is TRUE

                            (while b do S, s) ⟹ u
-/
lemma while_true_iff {b : scope → Prop} {S : stmt} {s u : scope}
    (hcond : b s) : (stmt.while b S, s) ⟹ u ↔
        (∃ (t : scope), (S, s) ⟹ t ∧ (stmt.while b S, t) ⟹ u) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply exists.intro h₁_t,
            apply and.intro h₁_hbody h₁_hrest,
        },
        {
            exfalso,
            apply h₁_hcond hcond,
        }
    },
    {
        intro h₂,
        cases h₂ with t h₂,
        cases h₂ with hS hwhile,
        apply big_step.while_true hcond hS hwhile,
    }
end

/-
Sequent:


        While-False     ______________________ (b s) is FALSE

                        (while b do S, s) ⟹ s
-/
@[simp] lemma while_false_iff {b : scope → Prop} {S : stmt} {s t:  scope}
    (hcond : ¬ b s) : (stmt.while b S, s) ⟹ t ↔ t = s :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exfalso,
            apply hcond h₁_hcond,
        },
        {
            refl,
        }
    },
    {
        intro h₂,
        rw h₂,
        apply big_step.while_false hcond,
    }
end

/-
Sequent:

                  (F, (σ s)) ⟹ t
    Call    __________________________ ∀ args, args = (v₀ s) ∧ (v₁ s)

            (call f v₀ v₁ σ F, s) ⟹ t
-/
@[simp] lemma call_iff {f : string} {v₀ v₁ : scope → Prop} {F : stmt}
    {s t : scope} {σ : scope → scope} (args : (v₀ s) ∧ (v₁ s)) :
        (stmt.call f v₀ v₁ σ F, s) ⟹ t ↔ ((F, (σ s)) ⟹ t) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        exact h₁_hF,
    },
    {
        intro h₂,
        apply big_step.call args h₂,
    }
end

end big_step
