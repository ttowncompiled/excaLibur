/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import common big_step.basic

def partial_hoare (P : scope → Prop) (S : stmt) (Q : scope → Prop) : Prop :=
    ∀ (s t : scope), P s → (S, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` := partial_hoare P S Q

namespace partial_hoare

lemma skip_intro {P : scope → Prop} : {* P *} stmt.skip {* P *} :=
begin
    intros s t hP hst,
    cases hst,
    exact hP,
end

lemma assign_intro {P : scope → Prop} {x : string} {a : scope → Prop} :
    {* λs, P (s{x ↦ a s}) *} stmt.assign x a {* P *} :=
begin
    intros s t hP hst,
    cases hst,
    exact hP,
end

lemma seq_intro {P Q R : scope → Prop} {S T : stmt} (hS : {* P *} S {* Q *})
    (hT : {* Q *} T {* R *}) : {* P *} S ;; T {* R *} :=
begin
    intros s t hP hst,
    cases hst,
    apply hT,
    {
        apply hS,
        {
            exact hP,
        },
        {
            exact hst_hS,
        }
    },
    {
        exact hst_hT,
    }
end

lemma ite_intro {b P Q : scope → Prop} {S T : stmt}
    (hS : {* λ (s : scope), P s ∧ b s *} S {* Q *})
    (hT : {* λ (s : scope), P s ∧ ¬ b s *} T {* Q *}) :
        {* P *} stmt.ite b S T {* Q *} :=
begin
    intros s t hP hst,
    cases hst,
    {
        apply hS,
        {
            exact and.intro hP hst_hcond,
        },
        {
            exact hst_hbody,
        }
    },
    {
        apply hT,
        {
            exact and.intro hP hst_hcond,
        },
        {
            exact hst_hbody,
        }
    }
end

lemma ite_true_intro {b P Q : scope → Prop} {S T : stmt}
    (hS : {* λ (s : scope), P s ∧ b s *} S {* Q *}) :
        {* λ (s : scope), P s ∧ b s *} stmt.ite b S T {* Q *} :=
begin
    intros s t hP hst,
    cases hst,
    {
        apply hS,
        {
            exact hP,
        },
        {
            exact hst_hbody,
        }
    },
    {
        exfalso,
        apply hst_hcond,
        exact hP.right,
    }
end

lemma ite_false_intro {b P Q : scope → Prop} {S T : stmt}
    (hT : {* λ (s : scope), P s ∧ ¬ b s *} T {* Q *}) :
        {* λ (s : scope), P s ∧ ¬ b s *} stmt.ite b S T {* Q *} :=
begin
    intros s t hP hst,
    cases hst,
    {
        exfalso,
        apply hP.right,
        exact hst_hcond,
    },
    {
        apply hT,
        {
            exact hP,
        },
        {
            exact hst_hbody,
        }
    }
end

lemma while_intro {b I : scope → Prop} {S : stmt}
    (hS : {* λ (s : scope), I s ∧ b s *} S {* I *}) :
        {* I *} stmt.while b S {* λ (s : scope), I s ∧ ¬ b s *} :=
begin
    intros s t hP,
    generalize hws : (stmt.while b S, s) = ws,
    intro hst,
    induction hst generalizing s; cases hws,
    {
        apply hst_ih_hrest hst_t,
        {
            apply hS hst_s,
            {
                exact and.intro hP hst_hcond,
            },
            {
                exact hst_hbody,
            }
        },
        {
            refl,
        }
    },
    {
        exact and.intro hP hst_hcond,
    }
end

lemma while_false_intro {b P : scope → Prop} {S : stmt} :
    {* λ (s : scope), P s ∧ ¬ b s *} stmt.while b S {* λ (s : scope), P s ∧ ¬ b s *} :=
begin
    intros s t hP hst,
    cases hst,
    {
        exfalso,
        apply hP.right,
        exact hst_hcond,
    },
    {
        exact hP,
    }
end

lemma consequence {P P' Q Q' : scope → Prop} {S : stmt}
    (hP : ∀ (s : scope), P' s → P s) (hS : {* P *} S {* Q *})
    (hQ : ∀ (s : scope), Q s → Q' s) : {* P' *} S {* Q' *} :=
begin
    intros s t hP' hst,
    apply hQ t,
    apply hS,
    {
        apply hP s,
        exact hP',
    },
    {
        exact hst,
    }
end

end partial_hoare
