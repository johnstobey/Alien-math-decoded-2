import IndependentDuodenary.CanonicalArchitecture
import IndependentDuodenary.SourceFactorization
import IndependentDuodenary.CipherValidator

/-! Composition closure for arbitrary finite validated station programs.
The state is the defined finite algebraic carrier; channel alignment and the
substitution bound remain explicit. No biological interpretation is asserted. -/
namespace IndependentDuodenary

def compileStationProgram : List StationExpr → StationExpr
  | [] => .identity
  | e :: es => .compose (compileStationProgram es) e

def runStationProgram : List StationExpr → {r : ℕ} → RegisterWords r → RegisterWords r
  | [], _, words => words
  | e :: es, _, words => runStationProgram es (stationWordAction e words)

theorem station_word_action_composition (outer inner : StationExpr) {r : ℕ}
    (words : RegisterWords r) :
    stationWordAction (.compose outer inner) words =
      stationWordAction outer (stationWordAction inner words) := by
  funext i
  simp [stationWordAction, stationMeaning, List.map_map, Function.comp_def]

theorem station_program_compilation (ops : List StationExpr) {r : ℕ} (words : RegisterWords r) :
    runStationProgram ops words = stationWordAction (compileStationProgram ops) words := by
  induction ops generalizing words with
  | nil =>
    funext i
    simp [runStationProgram, compileStationProgram, stationWordAction, stationMeaning]
  | cons e es ih =>
    simp only [runStationProgram, compileStationProgram]
    rw [ih, station_word_action_composition]

def stationProgramEquiv (r : ℕ) (ops : List StationExpr) : RegisterWords r ≃ RegisterWords r where
  toFun := runStationProgram ops
  invFun := undoStationWordAction (compileStationProgram ops)
  left_inv words := by rw [station_program_compilation, station_word_action_inverse]
  right_inv words := by
    rw [station_program_compilation]
    funext i
    simp [stationWordAction, undoStationWordAction, List.map_map, Function.comp_def]

def pipelineTransmit {r : ℕ} (h : RegisterTranslation r) (n : ℕ) (ops : List StationExpr)
    (x : CanonicalSubstrate r) : RegisterWords r :=
  runStationProgram ops (((transportRegisterWords (registerStep h))^[n])
    (canonicalEncodingNatural.app r x))

/-- Exact identity back to the initial state, for every finite validated program. -/
theorem pipeline_master_composition {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound (pipelineTransmit h n ops x) received) :
    recoverCanonicalInitial h n (compileStationProgram ops) received = some x := by
  apply canonical_initial_recovery h n (compileStationProgram ops) x received
  simpa only [pipelineTransmit, station_program_compilation] using hnoise

theorem pipeline_noiseless_closure {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) :
    recoverCanonicalInitial h n (compileStationProgram ops)
      (protectRegisterWords (pipelineTransmit h n ops x)) = some x :=
  pipeline_master_composition h n ops x _ (protected_register_noise_bound _)

theorem pipeline_successor_channel_closure {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) :
    recoverCanonicalInitial h n (compileStationProgram ops)
      (successorCorruption (pipelineTransmit h n ops x)) = some x :=
  pipeline_master_composition h n ops x _ (successor_register_noise _)

theorem pipeline_transmission_injective {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) : Function.Injective (pipelineTransmit h n ops) := by
  intro x y heq
  have hr := congrArg (fun words => recoverCanonicalInitial h n (compileStationProgram ops)
    (protectRegisterWords words)) heq
  dsimp only at hr
  rw [pipeline_noiseless_closure, pipeline_noiseless_closure] at hr
  exact Option.some.inj hr

theorem pipeline_recovered_state_unique {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x y : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound (pipelineTransmit h n ops x) received)
    (hrecovered : recoverCanonicalInitial h n (compileStationProgram ops) received = some y) : y = x := by
  rw [pipeline_master_composition h n ops x received hnoise] at hrecovered
  exact (Option.some.inj hrecovered).symm

theorem pipeline_empty_transmission_rejected (h : RegisterTranslation 1) (n : ℕ)
    (ops : List StationExpr) :
    recoverCanonicalInitial h n (compileStationProgram ops) (fun _ => []) = none := rfl

end IndependentDuodenary
