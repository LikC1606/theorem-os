import CleanOpeningDefinitionsProbe
namespace OAI.SnakyCertificate.StrategyBridge
def escapeI_1 : Finset Cell := {(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, 1), (1, 2), (1, 3)}
lemma escapestep_1 : ∀ b ∈ escapeI_0, (placementEquiv 6 (0, -2)).symm b ∈ openingRow_406.H → b ∈ escapeI_1 := by decide +kernel
def escapeI_2 : Finset Cell := {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, 1), (1, 2), (1, 3)}
lemma escapestep_2 : ∀ b ∈ escapeI_1, (placementEquiv 0 (0, 1)).symm b ∈ openingRow_533.H → b ∈ escapeI_2 := by decide +kernel
def escapeI_3 : Finset Cell := {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3)}
lemma escapestep_3 : ∀ b ∈ escapeI_2, (placementEquiv 0 (0, 1)).symm b ∈ openingRow_584.H → b ∈ escapeI_3 := by decide +kernel
def escapeI_4 : Finset Cell := {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0)}
lemma escapestep_4 : ∀ b ∈ escapeI_3, (placementEquiv 6 (0, -2)).symm b ∈ openingRow_586.H → b ∈ escapeI_4 := by decide +kernel
def escapeI_5 : Finset Cell := {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0)}
lemma escapestep_5 : ∀ b ∈ escapeI_4, (placementEquiv 6 (0, -2)).symm b ∈ openingRow_587.H → b ∈ escapeI_5 := by decide +kernel
def escapeI_6 : Finset Cell := {(-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0)}
lemma escapestep_6 : ∀ b ∈ escapeI_5, (placementEquiv 2 (0, 1)).symm b ∈ openingRow_590.H → b ∈ escapeI_6 := by decide +kernel
def escapeI_7 : Finset Cell := {(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0)}
lemma escapestep_7 : ∀ b ∈ escapeI_6, (placementEquiv 2 (0, -2)).symm b ∈ openingRow_591.H → b ∈ escapeI_7 := by decide +kernel
def escapeI_8 : Finset Cell := {(-1, -2), (-1, 1), (0, -2), (0, -1), (0, 0)}
lemma escapestep_8 : ∀ b ∈ escapeI_7, (placementEquiv 0 (0, 1)).symm b ∈ openingRow_601.H → b ∈ escapeI_8 := by decide +kernel
def escapeI_9 : Finset Cell := {(-1, -2), (0, -2), (0, -1), (0, 0)}
lemma escapestep_9 : ∀ b ∈ escapeI_8, (placementEquiv 2 (0, 1)).symm b ∈ openingRow_602.H → b ∈ escapeI_9 := by decide +kernel
def escapeI_10 : Finset Cell := {(0, -2), (0, -1), (0, 0)}
lemma escapestep_10 : ∀ b ∈ escapeI_9, (placementEquiv 5 (0, -2)).symm b ∈ openingRow_611.H → b ∈ escapeI_10 := by decide +kernel
def escapeI_11 : Finset Cell := {(0, -1), (0, 0)}
lemma escapestep_11 : ∀ b ∈ escapeI_10, (placementEquiv 4 (1, -1)).symm b ∈ openingRow_614.H → b ∈ escapeI_11 := by decide +kernel

end OAI.SnakyCertificate.StrategyBridge
