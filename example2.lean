import common hoare.basic

def IS_S5 {AdminIns InsAdmin : Prop} (D D_in BloodSugar : ℕ) : stmt :=
    (stmt.call "bloodSugarLevel"
              (λ s, s "D" → (D = D_in))
              (λ s, s "BloodSugar" → (BloodSugar = 0))
              (λ (s : scope), s{"bloodSugarCap" ↦ s "D"})
              (stmt.assign "BloodSugar" (λ _, (BloodSugar = D + 1)))) ;;
    (stmt.ite (λ s, s "AdminIns" ∨ (s "D" → s "BloodSugar" → (D < BloodSugar)))
              (stmt.assign "InsAdmin" (λ _, InsAdmin))
              (stmt.skip))

theorem IS_S5_correct {AdminIns InsAdmin : Prop} (D_in D BloodSugar : ℕ) (props : AdminIns ∧ InsAdmin) :
    {* λ s, s "AdminIns" = AdminIns ∧ s "InsAdmin" = ¬ InsAdmin ∧ 0 < D_in ∧ s "D" = (D = D_in) ∧ s "BloodSugar" = (BloodSugar = 0) *}
    @IS_S5 AdminIns InsAdmin D D_in BloodSugar
    {* λ s, s "AdminIns" = AdminIns ∧ s "InsAdmin" = InsAdmin ∧ 0 < D_in ∧ s "D" = (D = D_in) ∧ s "BloodSugar" = (BloodSugar = D + 1) *} :=
begin
    rw IS_S5,
    apply partial_hoare.comp_intro,
    {
        apply partial_hoare.call_intro,
        {
            intros s₁ args,
            cases args with a₁ a₂,
            cases a₂ with a₂ a₃,
            cases a₃ with a₃ a₄,
            cases a₄ with a₄ a₅,
            split,
                intro ha₄,
                rw ← a₄,
                exact ha₄,
            intro ha₅,
            rw ← a₅,
            exact ha₅,
        },
        {
            apply partial_hoare.skip_intro',
            intros s₂ hS,
            cases hS with h₁ h₂,
            cases h₂ with h₂ h₃,
            cases h₃ with h₃ h₄,
            cases h₄ with h₄ h₅,
            split,
                rw ← h₁,
                apply scope.update_apply_ne,
            split,
                rw ← h₂,
                apply scope.update_apply_ne,
            split,
                exact h₃,
            split,
                rw ← h₄,
                apply scope.update_apply_ne,
            rw ← h₅,
            apply scope.update_apply_ne,
        },
        {
            apply partial_hoare.assign_intro_right,
        }
    },
    {
        apply partial_hoare.ite_true_intro,
        {
            intros s hS,
            cases hS with t₀ h₁,
            cases h₁ with h₁ h₂,
            cases h₁ with h₁ h₃,
            cases h₃ with h₃ h₄,
            cases h₄ with h₄ h₅,
            cases h₅ with h₅ h₆,
            cases h₆ with h₆ h₇,
            repeat {rw scope.update_apply_ne at h₁},
            rw h₁,
            left,
            exact props.1,
        },
        {
            apply partial_hoare.assign_intro',
            intros s hS,
            cases hS with t₀ h₁,
            cases h₁ with h₁ h₂,
            cases h₁ with h₁ h₃,
            cases h₃ with h₃ h₄,
            cases h₄ with h₄ h₅,
            cases h₅ with h₅ h₆,
            simp,
            split,
                rw ← h₁,
                symmetry,
                apply scope.update_apply_ne,
            split,
                exact h₄,
            split,
                repeat {rw scope.update_apply_ne at h₅},
                exact h₅,
            exact h₂,
        }
    }
end
