import CandidateLargestRowSmallCommon

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.SnakyConditional
open OrdinaryStrategy

run_cmd do IO.eprintln "certificate context: compiled qsmall_step11 imported"

def qo614 : qR := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (qm614)

def qmem_moveRow_H_iff (r : Fin 8) (t : qCell) (d : qR) (b : qCell) :
    b ∈ (qmoveRow r t d).H ↔ (qplacementEquiv r t).symm b ∈ d.H := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact (by
          change b ∈ d.H.image (qplacementEquiv r t) ↔ _
          constructor
          · intro h
            obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp h
            simpa only [← hab,Equiv.symm_apply_apply] using ha
          · intro h
            exact Finset.mem_image.mpr ⟨_,h,(qplacementEquiv r t).apply_symm_apply b⟩)

def qescapeI_10 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(0,-2),(0,-1),(0,0)})

def qescapeI_11 : Finset qCell := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      exact ({(0,-1),(0,0)})

run_cmd do IO.eprintln "certificate context: exact canonical adapters added"

#print axioms qsmall_step11
#print axioms qmem_moveRow_H_iff

end OAI.SnakyConditional
