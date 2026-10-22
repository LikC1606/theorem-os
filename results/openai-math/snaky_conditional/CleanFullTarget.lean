import CleanOpeningSemanticsModular
import CertificateRows
namespace OAI.SnakyCertificate.StrategyBridge
open OAI.SnakyConditional.OrdinaryStrategy
theorem empty_winning_35 : Winning Goal 35 ∅ ∅ := by
  apply empty_winning_of_opening_rows
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 406 (by omega)
    rw [memoRow_eq_406] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 533 (by omega)
    rw [memoRow_eq_533] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 557 (by omega)
    rw [memoRow_eq_557] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 584 (by omega)
    rw [memoRow_eq_584] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 586 (by omega)
    rw [memoRow_eq_586] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 587 (by omega)
    rw [memoRow_eq_587] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 590 (by omega)
    rw [memoRow_eq_590] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 591 (by omega)
    rw [memoRow_eq_591] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 595 (by omega)
    rw [memoRow_eq_595] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 601 (by omega)
    rw [memoRow_eq_601] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 602 (by omega)
    rw [memoRow_eq_602] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 603 (by omega)
    rw [memoRow_eq_603] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 611 (by omega)
    rw [memoRow_eq_611] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 614 (by omega)
    rw [memoRow_eq_614] at h
    exact h
  · have h := rowAt_threat (fun i hi hil => entryAt_valid_of_TableValid table_valid_probe i hi hil) 615 (by omega)
    rw [memoRow_eq_615] at h
    exact h
end OAI.SnakyCertificate.StrategyBridge
namespace OAI.SnakyConditional
theorem independently_proved_snaky_winning_strategy_with_legal_states :
    ∃ σ : OrdinaryStrategy.Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, OrdinaryStrategy.LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (OrdinaryStrategy.playState σ 35 β ∅ ∅ 35).1 ∧
        (OrdinaryStrategy.playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (OrdinaryStrategy.playState σ 35 β ∅ ∅ 35).1 (OrdinaryStrategy.playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (OrdinaryStrategy.playState σ 35 β ∅ ∅ k).1 (OrdinaryStrategy.playState σ 35 β ∅ ∅ k).2 ∧
          (OrdinaryStrategy.playState σ 35 β ∅ ∅ k).2.card = k := by
  have hgoal : OAI.SnakyCertificate.StrategyBridge.Goal = HasSnaky := rfl
  have hw := OAI.SnakyCertificate.StrategyBridge.empty_winning_35
  rw [hgoal] at hw
  exact OrdinaryStrategy.ordinary_policy_of_winning HasSnaky 35 (by omega) hw
end OAI.SnakyConditional
#print axioms OAI.SnakyConditional.independently_proved_snaky_winning_strategy_with_legal_states
