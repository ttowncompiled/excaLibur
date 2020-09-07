import common hoare.basic big_step.basic

def IS_S2 (I : ℕ): stmt :=
    stmt.ite (λ s, s "Conn" ∧ s "AuthConn" ∧ ¬ s "BuffChng")
        (stmt.assign "I" (λ s, (I = 1))) (stmt.skip)

lemma correct {Conn AuthConn BuffChng: Prop} (I : ℕ) (init : Conn ∧ AuthConn ∧ BuffChng) :
    {* λ s, s "Conn" = Conn ∧ s "AuthConn" = AuthConn ∧ s "BuffChng" = ¬ BuffChng ∧ s "I" = (I = 0) *}
    IS_S2 I
    {* λ s, s "Conn" = Conn ∧ s "AuthConn" = AuthConn ∧ s "BuffChng" = ¬ BuffChng ∧ (s "I" → (0 ≤ I)) *} :=
begin
    rw IS_S2,
    apply partial_hoare.ite_true_intro,
    {
        intros s hS,
        rw [hS.1, hS.2.1, hS.2.2.1],
        cc,
    },
    {
        apply partial_hoare.assign_intro',
        intros s hS,
        cases hS with h₁ h₂,
        cases h₂ with h₃ h₄,
        cases h₄ with h₅ h₆,
        split,
            rw scope.update_apply_ne "I" "Conn" (I = 1) s,
            exact h₁,
        split,
            rw scope.update_apply_ne "I" "AuthConn" (I = 1) s,
            exact h₃,
        split,
            rw scope.update_apply_ne "I" "BuffChng" (I = 1) s,
            exact h₅,
        rw scope.update_apply,
        intro hI,
        exact dec_trivial,
    }
end
