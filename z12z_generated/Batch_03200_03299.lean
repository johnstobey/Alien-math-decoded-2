import Mathlib

namespace Z12ZCompilerV4

abbrev Ring12 := ZMod 12
abbrev Constraint := Set Ring12

def anchor : Ring12 := 0
def antipode (k : Ring12) : Ring12 := k + 6

def Antipodal (s : Constraint) : Prop := ∀ k, k ∈ s ↔ antipode k ∈ s

inductive Domain where
  | constraint
  | suppression
  | contamination
  | sabotage
  deriving DecidableEq, Repr

inductive Partition where
  | airWater
  | fireEarth
  deriving DecidableEq, Repr

structure Event where
  k : Ring12
  r : Ring12
  n : Ring12
  constraint : Constraint
  domain : Domain
  partition : Partition

structure State where
  k : Ring12
  r : Ring12
  n : Ring12
  P : Set Constraint
  S : Constraint
  E : List Event

def Coherent (x : State) : Prop := x.k = x.n + x.r
def Consistent (x : State) : Prop := ∀ k, k ∈ x.S ↔ ∀ p ∈ x.P, k ∈ p

def initial : State := ⟨anchor, 0, 0, ∅, Set.univ, []⟩

def delta (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : State :=
  let n' := x.n + 1
  let r' := if lawful then x.r + dr else x.r
  { k := n' + r'
    r := r'
    n := n'
    P := insert e.constraint x.P
    S := x.S ∩ e.constraint
    E := x.E ++ [e] }

def tighten (T : Set (Ring12 × Ring12)) (s : Constraint) : Set (Ring12 × Ring12) :=
  T ∩ Set.prod s s

def anchorReset (x : State) : State :=
  { x with k := anchor, r := 0 }

theorem initial_coherent : Coherent initial := by rfl
theorem initial_consistent : Consistent initial := by intro k; simp [initial]
theorem initial_antipodal : Antipodal initial.S := by intro k; simp [initial]

theorem intersection_antipodal (s p : Constraint) (hs : Antipodal s) (hp : Antipodal p) : Antipodal (s ∩ p) := by
  intro k
  exact and_congr (hs k) (hp k)

theorem delta_consistent (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : Consistent (delta x e dr lawful) := by
  intro k
  change (k ∈ x.S ∧ k ∈ e.constraint) ↔ ∀ p ∈ insert e.constraint x.P, k ∈ p
  rw [hx k]
  constructor
  · rintro ⟨hold, hnew⟩ p hp
    rcases Set.mem_insert_iff.mp hp with heq | hp
    · subst p; exact hnew
    · exact hold p hp
  · intro h
    exact ⟨fun p hp => h p (Set.mem_insert_of_mem _ hp), h e.constraint (Set.mem_insert _ _)⟩
theorem generated_03200 (tag : Fin 10000) (htag : tag.val = 3200) (k : Ring12) : tag.val = 3200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03201 (tag : Fin 10000) (htag : tag.val = 3201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03202 (tag : Fin 10000) (htag : tag.val = 3202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03203 (tag : Fin 10000) (htag : tag.val = 3203) (x : State) (e : Event) (dr : Ring12) : tag.val = 3203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03204 (tag : Fin 10000) (htag : tag.val = 3204) (x : State) (e : Event) (dr : Ring12) : tag.val = 3204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03205 (tag : Fin 10000) (htag : tag.val = 3205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03206 (tag : Fin 10000) (htag : tag.val = 3206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03207 (tag : Fin 10000) (htag : tag.val = 3207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03208 (tag : Fin 10000) (htag : tag.val = 3208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03209 (tag : Fin 10000) (htag : tag.val = 3209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03210 (tag : Fin 10000) (htag : tag.val = 3210) (k : Ring12) : tag.val = 3210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03211 (tag : Fin 10000) (htag : tag.val = 3211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03212 (tag : Fin 10000) (htag : tag.val = 3212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03213 (tag : Fin 10000) (htag : tag.val = 3213) (x : State) (e : Event) (dr : Ring12) : tag.val = 3213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03214 (tag : Fin 10000) (htag : tag.val = 3214) (x : State) (e : Event) (dr : Ring12) : tag.val = 3214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03215 (tag : Fin 10000) (htag : tag.val = 3215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03216 (tag : Fin 10000) (htag : tag.val = 3216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03217 (tag : Fin 10000) (htag : tag.val = 3217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03218 (tag : Fin 10000) (htag : tag.val = 3218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03219 (tag : Fin 10000) (htag : tag.val = 3219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03220 (tag : Fin 10000) (htag : tag.val = 3220) (k : Ring12) : tag.val = 3220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03221 (tag : Fin 10000) (htag : tag.val = 3221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03222 (tag : Fin 10000) (htag : tag.val = 3222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03223 (tag : Fin 10000) (htag : tag.val = 3223) (x : State) (e : Event) (dr : Ring12) : tag.val = 3223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03224 (tag : Fin 10000) (htag : tag.val = 3224) (x : State) (e : Event) (dr : Ring12) : tag.val = 3224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03225 (tag : Fin 10000) (htag : tag.val = 3225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03226 (tag : Fin 10000) (htag : tag.val = 3226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03227 (tag : Fin 10000) (htag : tag.val = 3227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03228 (tag : Fin 10000) (htag : tag.val = 3228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03229 (tag : Fin 10000) (htag : tag.val = 3229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03230 (tag : Fin 10000) (htag : tag.val = 3230) (k : Ring12) : tag.val = 3230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03231 (tag : Fin 10000) (htag : tag.val = 3231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03232 (tag : Fin 10000) (htag : tag.val = 3232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03233 (tag : Fin 10000) (htag : tag.val = 3233) (x : State) (e : Event) (dr : Ring12) : tag.val = 3233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03234 (tag : Fin 10000) (htag : tag.val = 3234) (x : State) (e : Event) (dr : Ring12) : tag.val = 3234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03235 (tag : Fin 10000) (htag : tag.val = 3235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03236 (tag : Fin 10000) (htag : tag.val = 3236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03237 (tag : Fin 10000) (htag : tag.val = 3237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03238 (tag : Fin 10000) (htag : tag.val = 3238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03239 (tag : Fin 10000) (htag : tag.val = 3239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03240 (tag : Fin 10000) (htag : tag.val = 3240) (k : Ring12) : tag.val = 3240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03241 (tag : Fin 10000) (htag : tag.val = 3241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03242 (tag : Fin 10000) (htag : tag.val = 3242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03243 (tag : Fin 10000) (htag : tag.val = 3243) (x : State) (e : Event) (dr : Ring12) : tag.val = 3243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03244 (tag : Fin 10000) (htag : tag.val = 3244) (x : State) (e : Event) (dr : Ring12) : tag.val = 3244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03245 (tag : Fin 10000) (htag : tag.val = 3245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03246 (tag : Fin 10000) (htag : tag.val = 3246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03247 (tag : Fin 10000) (htag : tag.val = 3247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03248 (tag : Fin 10000) (htag : tag.val = 3248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03249 (tag : Fin 10000) (htag : tag.val = 3249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03250 (tag : Fin 10000) (htag : tag.val = 3250) (k : Ring12) : tag.val = 3250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03251 (tag : Fin 10000) (htag : tag.val = 3251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03252 (tag : Fin 10000) (htag : tag.val = 3252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03253 (tag : Fin 10000) (htag : tag.val = 3253) (x : State) (e : Event) (dr : Ring12) : tag.val = 3253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03254 (tag : Fin 10000) (htag : tag.val = 3254) (x : State) (e : Event) (dr : Ring12) : tag.val = 3254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03255 (tag : Fin 10000) (htag : tag.val = 3255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03256 (tag : Fin 10000) (htag : tag.val = 3256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03257 (tag : Fin 10000) (htag : tag.val = 3257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03258 (tag : Fin 10000) (htag : tag.val = 3258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03259 (tag : Fin 10000) (htag : tag.val = 3259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03260 (tag : Fin 10000) (htag : tag.val = 3260) (k : Ring12) : tag.val = 3260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03261 (tag : Fin 10000) (htag : tag.val = 3261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03262 (tag : Fin 10000) (htag : tag.val = 3262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03263 (tag : Fin 10000) (htag : tag.val = 3263) (x : State) (e : Event) (dr : Ring12) : tag.val = 3263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03264 (tag : Fin 10000) (htag : tag.val = 3264) (x : State) (e : Event) (dr : Ring12) : tag.val = 3264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03265 (tag : Fin 10000) (htag : tag.val = 3265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03266 (tag : Fin 10000) (htag : tag.val = 3266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03267 (tag : Fin 10000) (htag : tag.val = 3267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03268 (tag : Fin 10000) (htag : tag.val = 3268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03269 (tag : Fin 10000) (htag : tag.val = 3269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03270 (tag : Fin 10000) (htag : tag.val = 3270) (k : Ring12) : tag.val = 3270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03271 (tag : Fin 10000) (htag : tag.val = 3271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03272 (tag : Fin 10000) (htag : tag.val = 3272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03273 (tag : Fin 10000) (htag : tag.val = 3273) (x : State) (e : Event) (dr : Ring12) : tag.val = 3273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03274 (tag : Fin 10000) (htag : tag.val = 3274) (x : State) (e : Event) (dr : Ring12) : tag.val = 3274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03275 (tag : Fin 10000) (htag : tag.val = 3275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03276 (tag : Fin 10000) (htag : tag.val = 3276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03277 (tag : Fin 10000) (htag : tag.val = 3277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03278 (tag : Fin 10000) (htag : tag.val = 3278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03279 (tag : Fin 10000) (htag : tag.val = 3279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03280 (tag : Fin 10000) (htag : tag.val = 3280) (k : Ring12) : tag.val = 3280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03281 (tag : Fin 10000) (htag : tag.val = 3281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03282 (tag : Fin 10000) (htag : tag.val = 3282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03283 (tag : Fin 10000) (htag : tag.val = 3283) (x : State) (e : Event) (dr : Ring12) : tag.val = 3283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03284 (tag : Fin 10000) (htag : tag.val = 3284) (x : State) (e : Event) (dr : Ring12) : tag.val = 3284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03285 (tag : Fin 10000) (htag : tag.val = 3285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03286 (tag : Fin 10000) (htag : tag.val = 3286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03287 (tag : Fin 10000) (htag : tag.val = 3287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03288 (tag : Fin 10000) (htag : tag.val = 3288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03289 (tag : Fin 10000) (htag : tag.val = 3289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03290 (tag : Fin 10000) (htag : tag.val = 3290) (k : Ring12) : tag.val = 3290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03291 (tag : Fin 10000) (htag : tag.val = 3291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03292 (tag : Fin 10000) (htag : tag.val = 3292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03293 (tag : Fin 10000) (htag : tag.val = 3293) (x : State) (e : Event) (dr : Ring12) : tag.val = 3293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03294 (tag : Fin 10000) (htag : tag.val = 3294) (x : State) (e : Event) (dr : Ring12) : tag.val = 3294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03295 (tag : Fin 10000) (htag : tag.val = 3295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03296 (tag : Fin 10000) (htag : tag.val = 3296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03297 (tag : Fin 10000) (htag : tag.val = 3297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03298 (tag : Fin 10000) (htag : tag.val = 3298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03299 (tag : Fin 10000) (htag : tag.val = 3299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
