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
| while_false {b : scope → Prop} {S : stmt} {s t u : scope} (hcond : ¬ b s) :
    big_step (stmt.while b S, s) s
| call {σ₀ : string} {y : scope → Prop} {T : stmt} {s t : scope}
    (hT : big_step (T, s{σ₀ ↦ y s}) t) : big_step (stmt.call σ₀ y, s) t

infix ` ⟹ `:110 := big_step

namespace big_step

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

@[simp] lemma comp_iff {S T : stmt} {s t : scope} :
    (S ;; T, s) ⟹ t ↔ (∃ (u : scope), (S, s) ⟹ u ∧ (T, u) ⟹ t) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        apply exists.intro,
        apply and.intro; assumption
    },
    {
        intro h₂,
        cases h₂,
        cases h₂_h,
        apply big_step.comp; assumption
    }
end

@[simp] lemma ite_iff {b : scope → Prop} {S T : stmt} {s t : scope} :
    (stmt.ite b S T, s) ⟹ t ↔ (b s ∧ (S, s) ⟹ t) ∨ (¬ b s ∧ (T, s) ⟹ t) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply or.intro_left,
            cc,
        },
        {
            apply or.intro_right,
            cc,
        }
    },
    {
        intro h₂,
        cases h₂,
        {
            cases h₂,
            apply big_step.ite_true; assumption
        },
        {
            cases h₂,
            apply big_step.ite_false; assumption
        }
    }
end

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
            apply h₁_hcond; assumption
        }
    },
    {
        intro h₂,
        apply big_step.ite_true; assumption
    }
end

@[simp] lemma ite_false_iff {b : scope → Prop} {S T : stmt} {s t : scope}
    (hcond : ¬ b s) : (stmt.ite b S T, s) ⟹ t ↔ (T, s) ⟹ t :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exfalso,
            apply hcond; assumption
        },
        {
            exact h₁_hbody,
        }
    },
    {
        intro h₂,
        apply big_step.ite_false; assumption
    }
end

lemma while_iff {b : scope → Prop} {S : stmt} {s u : scope} :
    (stmt.while b S, s) ⟹ u ↔ (∃ (t : scope), b s ∧ (S, s) ⟹ t
        ∧ (stmt.while b S, t) ⟹ u) ∨ (¬ b s ∧ u = s) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            apply or.intro_left,
            apply exists.intro h₁_t,
            cc
        },
        {
            apply or.intro_right,
            cc,
        }
    },
    {
        intro h₂,
        cases h₂,
        case or.inl {
            cases h₂ with t h₂,
            cases h₂ with hb h₂,
            cases h₂ with hS hwhile,
            exact big_step.while_true hb hS hwhile,
        },
        case or.inr {
            cases h₂ with hb h₂,
            rw h₂,
            apply big_step.while_false; assumption
        }
    }
end

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
            cc,
        },
        {
            exfalso,
            apply h₁_hcond; assumption
        }
    },
    {
        intro h₂,
        cases h₂ with t h₂,
        cases h₂ with hS hwhile,
        apply big_step.while_true hcond hS hwhile,
    }
end

@[simp] lemma while_false_iff {b : scope → Prop} {S : stmt} {s t:  scope}
    (hcond : ¬ b s) : (stmt.while b S, s) ⟹ t ↔ t = s :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        {
            exfalso,
            apply hcond; assumption
        },
        {
            refl,
        }
    },
    {
        intro h₂,
        rw h₂,
        apply big_step.while_false; assumption
    }
end

lemma call_iff {σ₀ : string} {y : scope → Prop} {s t : scope} :
    (stmt.call σ₀ y, s) ⟹ t ↔ (∃ (T : stmt), (T, s{σ₀ ↦ y s}) ⟹ t) :=
begin
    apply iff.intro,
    {
        intro h₁,
        cases h₁,
        apply exists.intro h₁_T,
        exact h₁_hT,
    },
    {
        intro h₂,
        cases h₂,
        apply big_step.call h₂_h,
    }
end

end big_step
