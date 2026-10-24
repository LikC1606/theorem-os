import CertificateContext

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.SnakyConditional
open OrdinaryStrategy

run_cmd do IO.eprintln s!"Baseline: proof started monoMs={← IO.monoMsNow}"

def qescapestep_11 : ∀ b ∈ qescapeI_10,(qplacementEquiv 4 (1,-1)).symm b ∈ qo614.H → b ∈ qescapeI_11 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      run_tac qhb (← `(tactic| decide +kernel))

run_cmd do IO.eprintln s!"Baseline: proof elaborated and kernel checked monoMs={← IO.monoMsNow}"

#print axioms qescapestep_11

end OAI.SnakyConditional
