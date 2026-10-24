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
theorem generated_02300 (tag : Fin 10000) (htag : tag.val = 2300) (k : Ring12) : tag.val = 2300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02301 (tag : Fin 10000) (htag : tag.val = 2301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02302 (tag : Fin 10000) (htag : tag.val = 2302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02303 (tag : Fin 10000) (htag : tag.val = 2303) (x : State) (e : Event) (dr : Ring12) : tag.val = 2303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02304 (tag : Fin 10000) (htag : tag.val = 2304) (x : State) (e : Event) (dr : Ring12) : tag.val = 2304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02305 (tag : Fin 10000) (htag : tag.val = 2305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02306 (tag : Fin 10000) (htag : tag.val = 2306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02307 (tag : Fin 10000) (htag : tag.val = 2307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02308 (tag : Fin 10000) (htag : tag.val = 2308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02309 (tag : Fin 10000) (htag : tag.val = 2309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02310 (tag : Fin 10000) (htag : tag.val = 2310) (k : Ring12) : tag.val = 2310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02311 (tag : Fin 10000) (htag : tag.val = 2311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02312 (tag : Fin 10000) (htag : tag.val = 2312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02313 (tag : Fin 10000) (htag : tag.val = 2313) (x : State) (e : Event) (dr : Ring12) : tag.val = 2313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02314 (tag : Fin 10000) (htag : tag.val = 2314) (x : State) (e : Event) (dr : Ring12) : tag.val = 2314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02315 (tag : Fin 10000) (htag : tag.val = 2315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02316 (tag : Fin 10000) (htag : tag.val = 2316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02317 (tag : Fin 10000) (htag : tag.val = 2317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02318 (tag : Fin 10000) (htag : tag.val = 2318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02319 (tag : Fin 10000) (htag : tag.val = 2319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02320 (tag : Fin 10000) (htag : tag.val = 2320) (k : Ring12) : tag.val = 2320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02321 (tag : Fin 10000) (htag : tag.val = 2321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02322 (tag : Fin 10000) (htag : tag.val = 2322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02323 (tag : Fin 10000) (htag : tag.val = 2323) (x : State) (e : Event) (dr : Ring12) : tag.val = 2323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02324 (tag : Fin 10000) (htag : tag.val = 2324) (x : State) (e : Event) (dr : Ring12) : tag.val = 2324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02325 (tag : Fin 10000) (htag : tag.val = 2325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02326 (tag : Fin 10000) (htag : tag.val = 2326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02327 (tag : Fin 10000) (htag : tag.val = 2327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02328 (tag : Fin 10000) (htag : tag.val = 2328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02329 (tag : Fin 10000) (htag : tag.val = 2329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02330 (tag : Fin 10000) (htag : tag.val = 2330) (k : Ring12) : tag.val = 2330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02331 (tag : Fin 10000) (htag : tag.val = 2331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02332 (tag : Fin 10000) (htag : tag.val = 2332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02333 (tag : Fin 10000) (htag : tag.val = 2333) (x : State) (e : Event) (dr : Ring12) : tag.val = 2333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02334 (tag : Fin 10000) (htag : tag.val = 2334) (x : State) (e : Event) (dr : Ring12) : tag.val = 2334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02335 (tag : Fin 10000) (htag : tag.val = 2335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02336 (tag : Fin 10000) (htag : tag.val = 2336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02337 (tag : Fin 10000) (htag : tag.val = 2337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02338 (tag : Fin 10000) (htag : tag.val = 2338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02339 (tag : Fin 10000) (htag : tag.val = 2339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02340 (tag : Fin 10000) (htag : tag.val = 2340) (k : Ring12) : tag.val = 2340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02341 (tag : Fin 10000) (htag : tag.val = 2341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02342 (tag : Fin 10000) (htag : tag.val = 2342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02343 (tag : Fin 10000) (htag : tag.val = 2343) (x : State) (e : Event) (dr : Ring12) : tag.val = 2343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02344 (tag : Fin 10000) (htag : tag.val = 2344) (x : State) (e : Event) (dr : Ring12) : tag.val = 2344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02345 (tag : Fin 10000) (htag : tag.val = 2345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02346 (tag : Fin 10000) (htag : tag.val = 2346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02347 (tag : Fin 10000) (htag : tag.val = 2347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02348 (tag : Fin 10000) (htag : tag.val = 2348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02349 (tag : Fin 10000) (htag : tag.val = 2349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02350 (tag : Fin 10000) (htag : tag.val = 2350) (k : Ring12) : tag.val = 2350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02351 (tag : Fin 10000) (htag : tag.val = 2351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02352 (tag : Fin 10000) (htag : tag.val = 2352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02353 (tag : Fin 10000) (htag : tag.val = 2353) (x : State) (e : Event) (dr : Ring12) : tag.val = 2353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02354 (tag : Fin 10000) (htag : tag.val = 2354) (x : State) (e : Event) (dr : Ring12) : tag.val = 2354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02355 (tag : Fin 10000) (htag : tag.val = 2355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02356 (tag : Fin 10000) (htag : tag.val = 2356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02357 (tag : Fin 10000) (htag : tag.val = 2357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02358 (tag : Fin 10000) (htag : tag.val = 2358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02359 (tag : Fin 10000) (htag : tag.val = 2359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02360 (tag : Fin 10000) (htag : tag.val = 2360) (k : Ring12) : tag.val = 2360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02361 (tag : Fin 10000) (htag : tag.val = 2361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02362 (tag : Fin 10000) (htag : tag.val = 2362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02363 (tag : Fin 10000) (htag : tag.val = 2363) (x : State) (e : Event) (dr : Ring12) : tag.val = 2363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02364 (tag : Fin 10000) (htag : tag.val = 2364) (x : State) (e : Event) (dr : Ring12) : tag.val = 2364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02365 (tag : Fin 10000) (htag : tag.val = 2365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02366 (tag : Fin 10000) (htag : tag.val = 2366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02367 (tag : Fin 10000) (htag : tag.val = 2367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02368 (tag : Fin 10000) (htag : tag.val = 2368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02369 (tag : Fin 10000) (htag : tag.val = 2369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02370 (tag : Fin 10000) (htag : tag.val = 2370) (k : Ring12) : tag.val = 2370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02371 (tag : Fin 10000) (htag : tag.val = 2371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02372 (tag : Fin 10000) (htag : tag.val = 2372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02373 (tag : Fin 10000) (htag : tag.val = 2373) (x : State) (e : Event) (dr : Ring12) : tag.val = 2373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02374 (tag : Fin 10000) (htag : tag.val = 2374) (x : State) (e : Event) (dr : Ring12) : tag.val = 2374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02375 (tag : Fin 10000) (htag : tag.val = 2375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02376 (tag : Fin 10000) (htag : tag.val = 2376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02377 (tag : Fin 10000) (htag : tag.val = 2377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02378 (tag : Fin 10000) (htag : tag.val = 2378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02379 (tag : Fin 10000) (htag : tag.val = 2379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02380 (tag : Fin 10000) (htag : tag.val = 2380) (k : Ring12) : tag.val = 2380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02381 (tag : Fin 10000) (htag : tag.val = 2381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02382 (tag : Fin 10000) (htag : tag.val = 2382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02383 (tag : Fin 10000) (htag : tag.val = 2383) (x : State) (e : Event) (dr : Ring12) : tag.val = 2383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02384 (tag : Fin 10000) (htag : tag.val = 2384) (x : State) (e : Event) (dr : Ring12) : tag.val = 2384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02385 (tag : Fin 10000) (htag : tag.val = 2385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02386 (tag : Fin 10000) (htag : tag.val = 2386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02387 (tag : Fin 10000) (htag : tag.val = 2387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02388 (tag : Fin 10000) (htag : tag.val = 2388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02389 (tag : Fin 10000) (htag : tag.val = 2389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02390 (tag : Fin 10000) (htag : tag.val = 2390) (k : Ring12) : tag.val = 2390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02391 (tag : Fin 10000) (htag : tag.val = 2391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02392 (tag : Fin 10000) (htag : tag.val = 2392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02393 (tag : Fin 10000) (htag : tag.val = 2393) (x : State) (e : Event) (dr : Ring12) : tag.val = 2393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02394 (tag : Fin 10000) (htag : tag.val = 2394) (x : State) (e : Event) (dr : Ring12) : tag.val = 2394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02395 (tag : Fin 10000) (htag : tag.val = 2395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02396 (tag : Fin 10000) (htag : tag.val = 2396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02397 (tag : Fin 10000) (htag : tag.val = 2397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02398 (tag : Fin 10000) (htag : tag.val = 2398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02399 (tag : Fin 10000) (htag : tag.val = 2399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
