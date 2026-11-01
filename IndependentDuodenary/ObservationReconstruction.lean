import Mathlib.Logic.Function.Iterate

/-! Observation factorization and trajectory distinguishability on arbitrary carriers.
These formalize standard factorization/observability principles. -/
namespace IndependentDuodenary

theorem observation_dynamics_iff_kernel_stable {X Y : Type*} (T : X → X) (O : X → Y) :
    (∃ U : Y → Y, Function.Semiconj O T U) ↔
      ∀ x y, O x = O y → O (T x) = O (T y) := by
  constructor
  · rintro ⟨U, h⟩ x y hxy
    rw [h x, h y, hxy]
  · intro h
    have hf : Function.FactorsThrough (O ∘ T) O := fun {x y} hxy => h x y hxy
    exact ⟨Function.extend O (O ∘ T) id, fun x => (hf.extend_apply id x).symm⟩

def observationTrace {X Y : Type*} (T : X → X) (O : X → Y) (x : X) (n : ℕ) : Y :=
  O ((T^[n]) x)

/-- Trace equality is stable and contains every observation-respecting stable relation. -/
theorem observation_trace_universal {X Y : Type*} (T : X → X) (O : X → Y) :
    (∀ x y, observationTrace T O x = observationTrace T O y →
      O x = O y ∧ observationTrace T O (T x) = observationTrace T O (T y)) ∧
    (∀ R : X → X → Prop,
      (∀ x y, R x y → O x = O y) →
      (∀ x y, R x y → R (T x) (T y)) →
      ∀ x y, R x y → observationTrace T O x = observationTrace T O y) := by
  constructor
  · intro x y h
    exact ⟨congrFun h 0, funext (fun n => congrFun h (n + 1))⟩
  · intro R hO hT x y hxy
    have hi : ∀ n x y, R x y → R ((T^[n]) x) ((T^[n]) y) := by
      intro n
      induction n with
      | zero => exact fun _ _ h => h
      | succ n ih => exact fun x y h => ih (T x) (T y) (hT x y h)
    exact funext (fun n => hO _ _ (hi n x y hxy))

/-- Option permits exact reconstruction even when the source carrier is empty. -/
theorem observation_trace_reconstruction_iff {X Y : Type*} (T : X → X) (O : X → Y) :
    (∃ D : (ℕ → Y) → Option X, ∀ x, D (observationTrace T O x) = some x) ↔
      Function.Injective (observationTrace T O) := by
  constructor
  · rintro ⟨D, hD⟩ x y hxy
    exact Option.some.inj ((hD x).symm.trans ((congrArg D hxy).trans (hD y)))
  · intro h
    exact ⟨Function.extend (observationTrace T O) some (fun _ => none),
      fun x => h.extend_apply some (fun _ => none) x⟩

end IndependentDuodenary
