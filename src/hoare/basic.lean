/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import common big_step.basic

def partial_hoare (P : scope → Prop) (S : stmt) (Q : scope → Prop) : Prop :=
    ∀ (s t : scope), P s → (S, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` := partial_hoare P S Q

/-
Instructions for how to use partial_hoare and its notation

A partial Hoare triple is used to represent the pre- and post-condition of
an instruction or composition of instructions. A partial Hoare can be
constructed with the following notation.

                                {* P *} S {* Q *}

P is the pre-condition and Q is the post condition of
statement S (from common.stmt). It states that when stmt S is executed with
pre-condition P, it will either (a) terminate with post-condition Q or
(b) not terminate. These Hoare triples are referred to as partial Hoare triples
precisely because a stmt S executed with pre-condition P may not terminate.

This partial Hoare triple is implemented using big_step semantics, so it is
used to construct proofs of properties of a program which
executes synchronously/deterministically.

Given any big_step (S, s) ⟹ t, there is a corresponding partial Hoare triple

                            {* P s *} S {* Q t *}

Note that P and Q are both defined with the type scope → Prop. Thus, the
pre-condition P is defined over the scope s in which stmt S is executed while
the post-condition Q is defined over the scope t which results from the
execution of stmt S in scope s.

This construction of a partial Hoare triple from big_step semantics allows us
to more easily reason over the properties of statement S. See documentation
in big_step.basic for more information on big_step semantics. See documentation
in common.basic for more information on specifying program properties.
-/
namespace partial_hoare

/-
Sequent:


        Skip     ___________

                {P} skip {P}
-/
lemma skip_intro {P : scope → Prop} : {* P *} stmt.skip {* P *} :=
begin
    intros s t hP hst,
    cases hst,
    exact hP,
end

/-
Sequent:


        Assign   __________________ ,

                {P[a/x]} x := a {P}

where P[a/x] means "the scope P where the proposition of a is substituted
into the predicate x." If there is no predicate x, then one is created.
-/
lemma assign_intro (P : scope → Prop) {x : string} {a : scope → Prop} :
    {* λ (s : scope), P (s{x ↦ a s}) *} stmt.assign x a {* P *} :=
begin
    intros s t hP hst,
    cases hst,
    exact hP,
end

/-
Sequent:

                {P} S {Q}   {Q} T {R}
        Comp    _____________________

                    {P} S ;; T {R}
-/
lemma comp_intro {P Q R : scope → Prop} {S T : stmt} (hS : {* P *} S {* Q *})
    (hT : {* Q *} T {* R *}) : {* P *} S ;; T {* R *} :=
begin
    intros s t hP hst,
    cases hst,
    apply hT hst_t,
    {
        apply hS s,
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

/-
Sequent:

                        {P ∧ b} S {Q}   {P ∧ ¬ b} T {Q}
        If-Then-Else    _______________________________

                            {P} if b then S else T {Q}
-/
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

/-
Sequent:

                       {I ∧ b} S {I}
        While   __________________________

                {I} while b do S {I ∧ ¬ b}
-/
lemma while_intro (I : scope → Prop) {b : scope → Prop} {S : stmt}
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

/-
Sequent:

            P → (v₀ s) ∧ (v₁ s) {P} skip {P[(σ s)]}  {P[(σ s)]} T {Q}
    Call    _________________________________________________________ ,

                            {P} call f v₀ v₁ σ T {Q}

where P[(σ s)] means "the scope P injected with the predicates of (σ s)." The
predicates of (σ s) include input (read-only) parameters, in-out (read-write)
paramters, local variables. These predicates (except for those predicates
relating to v₁) must use a distinct naming convention, so that predicates
of s are not overwritten. Return statements that return a local variable
must be reformulated as an in-out parameter.
-/
lemma call_intro {v₀ v₁ P Q : scope → Prop} {f : string} {T : stmt}
    {σ : scope → scope} (hargs : ∀ (s : scope), P s → (v₀ s ∧ v₁ s))
    (hS : {* P *} stmt.skip {* λ (s : scope), P (σ s) *})
    (hT : {* λ (s : scope), P (σ s) *} T {* Q *}) :
        {* P *} stmt.call f v₀ v₁ σ T {* Q *} :=
begin
    intros s t hP hst,
    cases hst,
    apply hT (σ s),
    {
        apply hS s,
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

/-
Sequent:

                        P' → P  {P} S {Q}   Q → Q'
        Consequence     __________________________

                               {P'} S {Q'}
-/
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

/-
Sequent:

                            P' → P  {P} S {Q}
        Consequence-Left    _________________

                              {P'} S {Q}
-/
lemma consequence_left (P' : scope → Prop) {P Q : scope → Prop} {S : stmt}
    (hP : ∀ (s : scope), P' s → P s) (hS : {* P *} S {* Q *}) :
        {* P' *} S {* Q *} :=
consequence hP hS (by cc)

/-
Sequent:

                            {P} S {Q}   Q → Q'
        Consequence-Right   __________________

                                {P} S {Q'}
-/
lemma consequence_right (Q : scope → Prop) {P Q' : scope → Prop} {S : stmt}
    (hS : {* P *} S {* Q *}) (hQ : ∀ (s : scope), Q s → Q' s) :
        {* P *} S {* Q' *} :=
consequence (by cc) hS hQ

/-
Sequent:

                    P → Q
        Skip'   ____________

                {P} skip {Q}
-/
lemma skip_intro' {P Q : scope → Prop} (hP : ∀ (s : scope), P s → Q s) :
    {* P *} stmt.skip {* Q *} :=
consequence hP skip_intro (by cc)

/-
Sequent:

                  P → Q[a/x]
        Assign' _____________ ,

                {P} x := a {Q}

where Q[a/x] means "the scope Q where the proposition of a is substituted
into the predicate x." If there is no predicate x, then one is created.
-/
lemma assign_intro' {P Q : scope → Prop} {x : string} {a : scope → Prop}
    (hP : ∀ (s : scope), P s → Q (s{x ↦ a s})) :
        {* P *} stmt.assign x a {* Q *} :=
consequence hP (assign_intro Q) (by cc)

/-
Sequent:

                P' → P  {P} S {Q}   {Q} T {R}   R → R'
        Comp'   ______________________________________

                          {P'} S ;; T {R'}
-/
lemma comp_intro' {P P' Q R R' : scope → Prop} {S T : stmt}
    (hP : ∀ (s : scope), P' s → P s) (hS : {* P *} S {* Q *})
    (hT : {* Q *} T {* R *}) (hR : ∀ (s : scope), R s → R' s) :
        {* P' *} S ;; T {* R' *} :=
begin
    apply consequence_left,
    {
        exact hP,
    },
    {
        intros s t hP₂ hst,
        cases hst,
        apply hR,
        apply hT,
        {
            apply hS,
            {
                exact hP₂,
            },
            {
                exact hst_hS,
            }
        },
        {
            exact hst_hT,
        }
    }
end

/-
Sequent:

                    P' → P  {P} S {Q}   {Q} T {R}
        Comp-Left   _____________________________

                          {P'} S ;; T {R}
-/
lemma comp_intro_left (P' : scope → Prop) {P Q R : scope → Prop} {S T : stmt}
    (hP : ∀ (s : scope), P' s → P s) (hS : {* P *} S {* Q *})
    (hT : {* Q *} T {* R *}) : {* P' *} S ;; T {* R *} :=
consequence_left P' hP (comp_intro hS hT)

/-
Sequent:

                    {P} S {Q}   {Q} T {R}   R → R'
        Comp-Right  ______________________________

                           {P} S ;; T {R'}
-/
lemma comp_intro_right (R : scope → Prop) {P Q R' : scope → Prop} {S T : stmt}
    (hS : {* P *} S {* Q *}) (hT : {* Q *} T {* R *})
    (hR : ∀ (s : scope), R s → R' s) : {* P *} S ;; T {* R' *} :=
consequence_right R (comp_intro hS hT) hR

/-
Sequent:

                                P → b      {P} S {Q}
        If-Then-Else-True   __________________________

                            {P} if b then S else T {Q}
-/
lemma ite_true_intro {b P Q : scope → Prop} {S T : stmt}
    (hP : ∀ (s : scope), P s → b s)
    (hS : {* P *} S {* Q *}) :
        {* P *} stmt.ite b S T {* Q *} :=
begin
    intros s t hP' hst,
    apply hS,
    {
        exact hP',
    },
    {
        cases hst,
        {
            exact hst_hbody,
        },
        {
            exfalso,
            apply hst_hcond,
            apply hP,
            exact hP',
        }
    }
end

/-
Sequent:

                                P → ¬ b     {P} T {Q}
        If-Then-Else-False  __________________________

                            {P} if b then S else T {Q}
-/
lemma ite_false_intro {b P Q : scope → Prop} {S T : stmt}
    (hP : ∀ (s : scope), P s → ¬ b s)
    (hT : {* P *} T {* Q *}) :
        {* P *} stmt.ite b S T {* Q *} :=
begin
    intros s t hP' hst,
    apply hT,
    {
        exact hP',
    },
    {
        cases hst,
        {
            exfalso,
            apply hP s hP',
            exact hst_hcond,
        },
        {
            exact hst_hbody,
        }
    }
end

/-
Sequent:

                            P → I   {I ∧ b} S {I}   I ∧ ¬ b → Q
        While-Invariant     ___________________________________

                                  {P} while b do S {Q}
-/
lemma while_invariant {b P Q : scope → Prop} {S : stmt} (I : scope → Prop)
    (hP : ∀ (s : scope), P s → I s)
    (hS : {* λ (s : scope), I s ∧ b s *} S {* I *})
    (hQ : ∀ (s : scope), ¬ b s → I s → Q s) :
        {* P *} stmt.while b S {* Q *} :=
begin
    apply consequence,
    {
        exact hP,
    },
    {
        apply while_intro I hS,
    },
    {
        intros s h,
        apply hQ,
        {
            exact h.right,
        },
        {
            exact h.left,
        }
    }
end

/-
Sequent:

                        {P ∧ b} S ;; while b do S {Q}   P ∧ ¬ b → Q
        While-Right     ___________________________________________

                                   {P} while b do S {Q}
-/
lemma while_right {b P Q : scope → Prop} {S : stmt}
    (hS : {* λ (s : scope), P s ∧ b s *} S ;; stmt.while b S {* Q *})
    (hQ : ∀ (s : scope), ¬ b s → P s → Q s) :
        {* P *} stmt.while b S {* Q *} :=
begin
    intros s t hP hst,
    cases hst,
    {
        apply hS,
        {
            exact and.intro hP hst_hcond,
        },
        {
            apply big_step.comp hst_hbody hst_hrest,
        }
    },
    {
        apply hQ s hst_hcond hP,
    }
end

/-
Sequent:

                                P → b   {P} S ;; while b do S {Q}
        While-Unwind-Right      _________________________________

                                    {P} while b do S {Q}
-/
lemma while_unwind_right {b P Q : scope → Prop} {S : stmt}
    (hP : ∀ (s : scope), P s → b s)
    (hS : {* P *} S ;; stmt.while b S {* Q *}) :
        {* P *} stmt.while b S {* Q *} :=
begin
    intros s t hP' hst,
    cases hst,
    {
        apply hS,
        {
            exact hP',
        },
        {
            apply big_step.comp hst_hbody hst_hrest,
        }
    },
    {
        exfalso,
        apply hst_hcond,
        apply hP s hP',
    }
end

/-
Sequent:

                                P → ¬ b
        While-False     ____________________

                        {P} while b do S {P}
-/
lemma while_false_intro {b P : scope → Prop} {S : stmt}
    (hP : ∀ (s : scope), P s → ¬ b s) : {* P *} stmt.while b S {* P *} :=
begin
    intros s t hP' hst,
    cases hst,
    {
        exfalso,
        apply hP s hP',
        exact hst_hcond,
    },
    {
        exact hP',
    }
end

/-
Sequent:

                                Q
        Assign-Left     ___________________ ,

                        {Q[a/x]} x := a {Q}

where Q[a/x] means "the scope Q where the proposition of a is substituted
into the predicate x." If there is no predicate x, then one is created.
-/
lemma assign_intro_left (Q : scope → Prop) {x : string} {a : scope → Prop}  :
    {* λ (s : scope), ∃ (t₀ : Prop), Q (s{x ↦ t₀}) ∧ t₀ = a s *}
    stmt.assign x a
    {* Q *} :=
begin
    apply assign_intro',
    intros s hP,
    cases hP,
    rw ← hP_h.right,
    exact hP_h.left
end

/-
Sequent:

                                P
        Assign-Right    ___________________ ,

                        {P} x := a {P[a/x]}

where P[a/x] means "the scope P where the proposition of a is substituted
into the predicate x." If there is no predicate x, then one is created.
-/
lemma assign_intro_right (P : scope → Prop) {x : string} {a : scope → Prop}  :
    {* P *}
    stmt.assign x a
    {* λ (s : scope), ∃ (t₀ : Prop), P (s{x ↦ t₀}) ∧ s x = a (s{x ↦ t₀}) *} :=
begin
    apply assign_intro',
    intros s hP,
    apply exists.intro (s x),
    apply and.intro,
    {
        rw (scope.update_squash x (s x) (a s) s),
        rw (scope.update_id x s),
        exact hP
    },
    {
        rw (scope.update_apply x (a s) s),
        rw (scope.update_squash x (s x) (a s) s),
        rw (scope.update_id x s),
    }
end

end partial_hoare
