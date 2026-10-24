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
theorem generated_07300 (tag : Fin 10000) (htag : tag.val = 7300) (k : Ring12) : tag.val = 7300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07301 (tag : Fin 10000) (htag : tag.val = 7301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07302 (tag : Fin 10000) (htag : tag.val = 7302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07303 (tag : Fin 10000) (htag : tag.val = 7303) (x : State) (e : Event) (dr : Ring12) : tag.val = 7303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07304 (tag : Fin 10000) (htag : tag.val = 7304) (x : State) (e : Event) (dr : Ring12) : tag.val = 7304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07305 (tag : Fin 10000) (htag : tag.val = 7305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07306 (tag : Fin 10000) (htag : tag.val = 7306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07307 (tag : Fin 10000) (htag : tag.val = 7307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07308 (tag : Fin 10000) (htag : tag.val = 7308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07309 (tag : Fin 10000) (htag : tag.val = 7309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07310 (tag : Fin 10000) (htag : tag.val = 7310) (k : Ring12) : tag.val = 7310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07311 (tag : Fin 10000) (htag : tag.val = 7311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07312 (tag : Fin 10000) (htag : tag.val = 7312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07313 (tag : Fin 10000) (htag : tag.val = 7313) (x : State) (e : Event) (dr : Ring12) : tag.val = 7313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07314 (tag : Fin 10000) (htag : tag.val = 7314) (x : State) (e : Event) (dr : Ring12) : tag.val = 7314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07315 (tag : Fin 10000) (htag : tag.val = 7315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07316 (tag : Fin 10000) (htag : tag.val = 7316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07317 (tag : Fin 10000) (htag : tag.val = 7317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07318 (tag : Fin 10000) (htag : tag.val = 7318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07319 (tag : Fin 10000) (htag : tag.val = 7319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07320 (tag : Fin 10000) (htag : tag.val = 7320) (k : Ring12) : tag.val = 7320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07321 (tag : Fin 10000) (htag : tag.val = 7321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07322 (tag : Fin 10000) (htag : tag.val = 7322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07323 (tag : Fin 10000) (htag : tag.val = 7323) (x : State) (e : Event) (dr : Ring12) : tag.val = 7323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07324 (tag : Fin 10000) (htag : tag.val = 7324) (x : State) (e : Event) (dr : Ring12) : tag.val = 7324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07325 (tag : Fin 10000) (htag : tag.val = 7325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07326 (tag : Fin 10000) (htag : tag.val = 7326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07327 (tag : Fin 10000) (htag : tag.val = 7327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07328 (tag : Fin 10000) (htag : tag.val = 7328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07329 (tag : Fin 10000) (htag : tag.val = 7329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07330 (tag : Fin 10000) (htag : tag.val = 7330) (k : Ring12) : tag.val = 7330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07331 (tag : Fin 10000) (htag : tag.val = 7331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07332 (tag : Fin 10000) (htag : tag.val = 7332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07333 (tag : Fin 10000) (htag : tag.val = 7333) (x : State) (e : Event) (dr : Ring12) : tag.val = 7333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07334 (tag : Fin 10000) (htag : tag.val = 7334) (x : State) (e : Event) (dr : Ring12) : tag.val = 7334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07335 (tag : Fin 10000) (htag : tag.val = 7335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07336 (tag : Fin 10000) (htag : tag.val = 7336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07337 (tag : Fin 10000) (htag : tag.val = 7337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07338 (tag : Fin 10000) (htag : tag.val = 7338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07339 (tag : Fin 10000) (htag : tag.val = 7339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07340 (tag : Fin 10000) (htag : tag.val = 7340) (k : Ring12) : tag.val = 7340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07341 (tag : Fin 10000) (htag : tag.val = 7341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07342 (tag : Fin 10000) (htag : tag.val = 7342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07343 (tag : Fin 10000) (htag : tag.val = 7343) (x : State) (e : Event) (dr : Ring12) : tag.val = 7343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07344 (tag : Fin 10000) (htag : tag.val = 7344) (x : State) (e : Event) (dr : Ring12) : tag.val = 7344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07345 (tag : Fin 10000) (htag : tag.val = 7345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07346 (tag : Fin 10000) (htag : tag.val = 7346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07347 (tag : Fin 10000) (htag : tag.val = 7347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07348 (tag : Fin 10000) (htag : tag.val = 7348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07349 (tag : Fin 10000) (htag : tag.val = 7349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07350 (tag : Fin 10000) (htag : tag.val = 7350) (k : Ring12) : tag.val = 7350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07351 (tag : Fin 10000) (htag : tag.val = 7351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07352 (tag : Fin 10000) (htag : tag.val = 7352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07353 (tag : Fin 10000) (htag : tag.val = 7353) (x : State) (e : Event) (dr : Ring12) : tag.val = 7353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07354 (tag : Fin 10000) (htag : tag.val = 7354) (x : State) (e : Event) (dr : Ring12) : tag.val = 7354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07355 (tag : Fin 10000) (htag : tag.val = 7355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07356 (tag : Fin 10000) (htag : tag.val = 7356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07357 (tag : Fin 10000) (htag : tag.val = 7357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07358 (tag : Fin 10000) (htag : tag.val = 7358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07359 (tag : Fin 10000) (htag : tag.val = 7359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07360 (tag : Fin 10000) (htag : tag.val = 7360) (k : Ring12) : tag.val = 7360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07361 (tag : Fin 10000) (htag : tag.val = 7361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07362 (tag : Fin 10000) (htag : tag.val = 7362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07363 (tag : Fin 10000) (htag : tag.val = 7363) (x : State) (e : Event) (dr : Ring12) : tag.val = 7363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07364 (tag : Fin 10000) (htag : tag.val = 7364) (x : State) (e : Event) (dr : Ring12) : tag.val = 7364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07365 (tag : Fin 10000) (htag : tag.val = 7365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07366 (tag : Fin 10000) (htag : tag.val = 7366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07367 (tag : Fin 10000) (htag : tag.val = 7367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07368 (tag : Fin 10000) (htag : tag.val = 7368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07369 (tag : Fin 10000) (htag : tag.val = 7369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07370 (tag : Fin 10000) (htag : tag.val = 7370) (k : Ring12) : tag.val = 7370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07371 (tag : Fin 10000) (htag : tag.val = 7371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07372 (tag : Fin 10000) (htag : tag.val = 7372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07373 (tag : Fin 10000) (htag : tag.val = 7373) (x : State) (e : Event) (dr : Ring12) : tag.val = 7373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07374 (tag : Fin 10000) (htag : tag.val = 7374) (x : State) (e : Event) (dr : Ring12) : tag.val = 7374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07375 (tag : Fin 10000) (htag : tag.val = 7375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07376 (tag : Fin 10000) (htag : tag.val = 7376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07377 (tag : Fin 10000) (htag : tag.val = 7377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07378 (tag : Fin 10000) (htag : tag.val = 7378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07379 (tag : Fin 10000) (htag : tag.val = 7379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07380 (tag : Fin 10000) (htag : tag.val = 7380) (k : Ring12) : tag.val = 7380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07381 (tag : Fin 10000) (htag : tag.val = 7381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07382 (tag : Fin 10000) (htag : tag.val = 7382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07383 (tag : Fin 10000) (htag : tag.val = 7383) (x : State) (e : Event) (dr : Ring12) : tag.val = 7383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07384 (tag : Fin 10000) (htag : tag.val = 7384) (x : State) (e : Event) (dr : Ring12) : tag.val = 7384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07385 (tag : Fin 10000) (htag : tag.val = 7385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07386 (tag : Fin 10000) (htag : tag.val = 7386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07387 (tag : Fin 10000) (htag : tag.val = 7387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07388 (tag : Fin 10000) (htag : tag.val = 7388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07389 (tag : Fin 10000) (htag : tag.val = 7389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07390 (tag : Fin 10000) (htag : tag.val = 7390) (k : Ring12) : tag.val = 7390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07391 (tag : Fin 10000) (htag : tag.val = 7391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07392 (tag : Fin 10000) (htag : tag.val = 7392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07393 (tag : Fin 10000) (htag : tag.val = 7393) (x : State) (e : Event) (dr : Ring12) : tag.val = 7393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07394 (tag : Fin 10000) (htag : tag.val = 7394) (x : State) (e : Event) (dr : Ring12) : tag.val = 7394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07395 (tag : Fin 10000) (htag : tag.val = 7395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07396 (tag : Fin 10000) (htag : tag.val = 7396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07397 (tag : Fin 10000) (htag : tag.val = 7397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07398 (tag : Fin 10000) (htag : tag.val = 7398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07399 (tag : Fin 10000) (htag : tag.val = 7399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
