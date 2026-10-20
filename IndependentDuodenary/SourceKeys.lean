import IndependentDuodenary.BinaryBridge

/-!
# Exact reduced keys and intercept translation

With a chosen splitting V = K × W, metadata contains the retained positions,
IDs and slopes; only the K component of the intercept is translated.
-/
namespace IndependentDuodenary

structure ExactKey (M K W : Type*) where
  metadata : M
  binaryIntercept : K
  complementIntercept : W
  deriving DecidableEq

variable {M K W : Type*}

/-- The canonical vertex retains metadata and the W component. -/
def keyVertex (q : ExactKey M K W) : M × W := (q.metadata, q.complementIntercept)

def translateKey [Add K] (h : K) (q : ExactKey M K W) : ExactKey M K W :=
  ⟨q.metadata, q.binaryIntercept + h, q.complementIntercept⟩

def canonicalKey [Zero K] (q : ExactKey M K W) : ExactKey M K W :=
  ⟨q.metadata, 0, q.complementIntercept⟩

def SameKeyOrbit [Add K] (q r : ExactKey M K W) : Prop :=
  ∃ h : K, translateKey h q = r

theorem translateKey_zero [AddZeroClass K] (q : ExactKey M K W) :
    translateKey 0 q = q := by
  cases q
  simp [translateKey]

theorem translateKey_add [AddSemigroup K] (h g : K) (q : ExactKey M K W) :
    translateKey g (translateKey h q) = translateKey (h + g) q := by
  simp [translateKey, add_assoc]

theorem translateKey_free [AddCancelMonoid K] (h g : K) (q : ExactKey M K W) :
    translateKey h q = translateKey g q ↔ h = g := by
  constructor
  · intro heq
    exact add_left_cancel (congrArg ExactKey.binaryIntercept heq)
  · rintro rfl
    rfl

theorem translateKey_vertex [Add K] (h : K) (q : ExactKey M K W) :
    keyVertex (translateKey h q) = keyVertex q := rfl

theorem canonicalKey_translate [AddZeroClass K] (h : K) (q : ExactKey M K W) :
    canonicalKey (translateKey h q) = canonicalKey q := rfl

theorem canonicalKey_idempotent [Zero K] (q : ExactKey M K W) :
    canonicalKey (canonicalKey q) = canonicalKey q := rfl

theorem canonicalKey_reconstruct [AddZeroClass K] (q : ExactKey M K W) :
    translateKey q.binaryIntercept (canonicalKey q) = q := by
  cases q
  simp [translateKey, canonicalKey]

theorem keyOrbit_iff_vertex_eq [AddGroup K] (q r : ExactKey M K W) :
    SameKeyOrbit q r ↔ keyVertex q = keyVertex r := by
  constructor
  · rintro ⟨h, rfl⟩
    rfl
  · intro h
    have hm := congrArg Prod.fst h
    have hw := congrArg Prod.snd h
    refine ⟨-q.binaryIntercept + r.binaryIntercept, ?_⟩
    cases q
    cases r
    simp only [keyVertex, Prod.fst, Prod.snd] at hm hw
    simp_all [translateKey, ← add_assoc]

theorem canonicalKey_unique [AddGroup K] (q r : ExactKey M K W)
    (horbit : SameKeyOrbit q r) (hz : r.binaryIntercept = 0) :
    r = canonicalKey q := by
  have hv := (keyOrbit_iff_vertex_eq q r).mp horbit
  have hm := congrArg Prod.fst hv
  have hw := congrArg Prod.snd hv
  cases q
  cases r
  simp only [keyVertex, Prod.fst, Prod.snd] at hm hw
  simp_all [canonicalKey]

/-- A labeling of canonical vertices restores the removed intercept. -/
def restoredAnswer [Add K] (label : M × W → K) (q : ExactKey M K W) : K :=
  label (keyVertex q) + q.binaryIntercept

/-- Source equation eq:table-folding in the exact-key model. -/
theorem source_folding [AddSemigroup K] (label : M × W → K)
    (h : K) (q : ExactKey M K W) :
    restoredAnswer label (translateKey h q) = restoredAnswer label q + h := by
  simp [restoredAnswer, translateKey, keyVertex, add_assoc]

theorem exact_key_answers_equal [Add K] (label : M × W → K)
    (q r : ExactKey M K W) (h : q = r) :
    restoredAnswer label q = restoredAnswer label r := congrArg _ h

/-- A residue-valued observable uses an explicitly chosen binary functional. -/
def residueAnswerTwelve [AddMonoid K] (χ : K →+ ZMod 2)
    (label : M × W → ZMod 12) (q : ExactKey M K W) : ZMod 12 :=
  label (keyVertex q) + bridgeTwelve χ q.binaryIntercept

def residueAnswer144 [AddMonoid K] (χ : K →+ ZMod 2)
    (label : M × W → ZMod 144) (q : ExactKey M K W) : ZMod 144 :=
  label (keyVertex q) + bridge144 χ q.binaryIntercept

theorem residue_folding_twelve [AddMonoid K] (χ : K →+ ZMod 2)
    (label : M × W → ZMod 12) (h : K) (q : ExactKey M K W) :
    residueAnswerTwelve χ label (translateKey h q) =
      residueAnswerTwelve χ label q + bridgeTwelve χ h := by
  simp [residueAnswerTwelve, translateKey, keyVertex, map_add, add_assoc]

theorem residue_folding_144 [AddMonoid K] (χ : K →+ ZMod 2)
    (label : M × W → ZMod 144) (h : K) (q : ExactKey M K W) :
    residueAnswer144 χ label (translateKey h q) =
      residueAnswer144 χ label q + bridge144 χ h := by
  simp [residueAnswer144, translateKey, keyVertex, map_add, add_assoc]

end IndependentDuodenary
