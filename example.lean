import common hoare.basic

def IS_S2 {BuffChng : Prop} (Len Cap I: ℕ) : stmt :=
    stmt.ite (λ s, (s "I" → I ≤ Cap) ∧ s "Conn" ∧ s "AuthConn" ∧ ¬ s "BuffChng")
        ((stmt.assign "I" (λ s, (I = 0))) ;; (stmt.assign "Cap" (λ s, (Cap = Len))) ;; (stmt.assign "BuffChng" (λ s, BuffChng)))
        (stmt.skip)

lemma IS_S2_correct {Conn AuthConn BuffChng : Prop} (Len Cap I : ℕ) (Buff BuffOut : list ℕ) (props : Conn ∧ AuthConn ∧ BuffChng) :
    {* λ s, s "Conn" = Conn ∧ s "AuthConn" = AuthConn ∧ s "BuffChng" = ¬ BuffChng ∧ 0 < Len ∧ s "Cap" = (Cap = Len) ∧ s "I" = (I = 0) *}
    @IS_S2 BuffChng Len Cap I
    {* λ s, s "Conn" = Conn ∧ s "AuthConn" = AuthConn ∧ s "BuffChng" = BuffChng ∧ 0 < Len ∧ (s "Cap" → (Cap = Len)) ∧ (s "Cap" → s "I" → (I ≤ Cap)) *} :=
begin
    rw IS_S2,
    apply partial_hoare.ite_true_intro,
    {
        intros s hS,
        cases hS with h₁ h₂,
        cases h₂ with h₃ h₄,
        cases h₄ with h₅ h₆,
        cases h₆ with h₇ h₈,
        rw [h₈.right, h₁, h₃, h₅],
        split,
            intro hI,
            rw hI,
            exact dec_trivial,
        split,
            exact props.1,
        split,
            exact props.2.1,
        apply non_contradictory_intro,
        exact props.2.2,
    },
    {
        apply partial_hoare.comp_intro,
        {
            apply partial_hoare.assign_intro_right,
        },
        {
            apply partial_hoare.comp_intro,
            {
                apply partial_hoare.assign_intro_right,
            },
            {
                apply partial_hoare.assign_intro',
                intros s ht₀,
                have t₀ : Prop := Cap = Len,
                cases ht₀ with t₀ ht₀_1,
                cases ht₀_1 with ht₀_1 hCap,
                cases ht₀_1 with t₀_1 hS,
                simp at hS,
                cases hS with h₁ h₂,
                cases h₁ with h₁ h₃,
                cases h₃ with h₃ h₄,
                cases h₄ with h₄ h₅,
                cases h₅ with h₅ h₆,
                cases h₆ with h₆ h₇,
                simp,
                split,
                    exact h₁,
                split,
                    exact h₃,
                split,
                    exact h₅,
                split,
                    intro hsCap,
                    rw hCap at hsCap,
                    exact hsCap,
                rw h₂,
                rw hCap,
                intros hCap hI,
                rw [hI, hCap],
                apply nat.le_of_lt,
                exact h₅,
            }
        }
    }
end
