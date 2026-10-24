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
theorem generated_01300 (tag : Fin 10000) (htag : tag.val = 1300) (k : Ring12) : tag.val = 1300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01301 (tag : Fin 10000) (htag : tag.val = 1301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01302 (tag : Fin 10000) (htag : tag.val = 1302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01303 (tag : Fin 10000) (htag : tag.val = 1303) (x : State) (e : Event) (dr : Ring12) : tag.val = 1303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01304 (tag : Fin 10000) (htag : tag.val = 1304) (x : State) (e : Event) (dr : Ring12) : tag.val = 1304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01305 (tag : Fin 10000) (htag : tag.val = 1305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01306 (tag : Fin 10000) (htag : tag.val = 1306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01307 (tag : Fin 10000) (htag : tag.val = 1307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01308 (tag : Fin 10000) (htag : tag.val = 1308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01309 (tag : Fin 10000) (htag : tag.val = 1309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01310 (tag : Fin 10000) (htag : tag.val = 1310) (k : Ring12) : tag.val = 1310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01311 (tag : Fin 10000) (htag : tag.val = 1311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01312 (tag : Fin 10000) (htag : tag.val = 1312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01313 (tag : Fin 10000) (htag : tag.val = 1313) (x : State) (e : Event) (dr : Ring12) : tag.val = 1313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01314 (tag : Fin 10000) (htag : tag.val = 1314) (x : State) (e : Event) (dr : Ring12) : tag.val = 1314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01315 (tag : Fin 10000) (htag : tag.val = 1315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01316 (tag : Fin 10000) (htag : tag.val = 1316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01317 (tag : Fin 10000) (htag : tag.val = 1317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01318 (tag : Fin 10000) (htag : tag.val = 1318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01319 (tag : Fin 10000) (htag : tag.val = 1319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01320 (tag : Fin 10000) (htag : tag.val = 1320) (k : Ring12) : tag.val = 1320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01321 (tag : Fin 10000) (htag : tag.val = 1321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01322 (tag : Fin 10000) (htag : tag.val = 1322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01323 (tag : Fin 10000) (htag : tag.val = 1323) (x : State) (e : Event) (dr : Ring12) : tag.val = 1323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01324 (tag : Fin 10000) (htag : tag.val = 1324) (x : State) (e : Event) (dr : Ring12) : tag.val = 1324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01325 (tag : Fin 10000) (htag : tag.val = 1325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01326 (tag : Fin 10000) (htag : tag.val = 1326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01327 (tag : Fin 10000) (htag : tag.val = 1327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01328 (tag : Fin 10000) (htag : tag.val = 1328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01329 (tag : Fin 10000) (htag : tag.val = 1329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01330 (tag : Fin 10000) (htag : tag.val = 1330) (k : Ring12) : tag.val = 1330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01331 (tag : Fin 10000) (htag : tag.val = 1331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01332 (tag : Fin 10000) (htag : tag.val = 1332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01333 (tag : Fin 10000) (htag : tag.val = 1333) (x : State) (e : Event) (dr : Ring12) : tag.val = 1333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01334 (tag : Fin 10000) (htag : tag.val = 1334) (x : State) (e : Event) (dr : Ring12) : tag.val = 1334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01335 (tag : Fin 10000) (htag : tag.val = 1335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01336 (tag : Fin 10000) (htag : tag.val = 1336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01337 (tag : Fin 10000) (htag : tag.val = 1337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01338 (tag : Fin 10000) (htag : tag.val = 1338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01339 (tag : Fin 10000) (htag : tag.val = 1339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01340 (tag : Fin 10000) (htag : tag.val = 1340) (k : Ring12) : tag.val = 1340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01341 (tag : Fin 10000) (htag : tag.val = 1341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01342 (tag : Fin 10000) (htag : tag.val = 1342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01343 (tag : Fin 10000) (htag : tag.val = 1343) (x : State) (e : Event) (dr : Ring12) : tag.val = 1343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01344 (tag : Fin 10000) (htag : tag.val = 1344) (x : State) (e : Event) (dr : Ring12) : tag.val = 1344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01345 (tag : Fin 10000) (htag : tag.val = 1345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01346 (tag : Fin 10000) (htag : tag.val = 1346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01347 (tag : Fin 10000) (htag : tag.val = 1347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01348 (tag : Fin 10000) (htag : tag.val = 1348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01349 (tag : Fin 10000) (htag : tag.val = 1349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01350 (tag : Fin 10000) (htag : tag.val = 1350) (k : Ring12) : tag.val = 1350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01351 (tag : Fin 10000) (htag : tag.val = 1351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01352 (tag : Fin 10000) (htag : tag.val = 1352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01353 (tag : Fin 10000) (htag : tag.val = 1353) (x : State) (e : Event) (dr : Ring12) : tag.val = 1353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01354 (tag : Fin 10000) (htag : tag.val = 1354) (x : State) (e : Event) (dr : Ring12) : tag.val = 1354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01355 (tag : Fin 10000) (htag : tag.val = 1355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01356 (tag : Fin 10000) (htag : tag.val = 1356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01357 (tag : Fin 10000) (htag : tag.val = 1357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01358 (tag : Fin 10000) (htag : tag.val = 1358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01359 (tag : Fin 10000) (htag : tag.val = 1359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01360 (tag : Fin 10000) (htag : tag.val = 1360) (k : Ring12) : tag.val = 1360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01361 (tag : Fin 10000) (htag : tag.val = 1361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01362 (tag : Fin 10000) (htag : tag.val = 1362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01363 (tag : Fin 10000) (htag : tag.val = 1363) (x : State) (e : Event) (dr : Ring12) : tag.val = 1363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01364 (tag : Fin 10000) (htag : tag.val = 1364) (x : State) (e : Event) (dr : Ring12) : tag.val = 1364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01365 (tag : Fin 10000) (htag : tag.val = 1365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01366 (tag : Fin 10000) (htag : tag.val = 1366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01367 (tag : Fin 10000) (htag : tag.val = 1367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01368 (tag : Fin 10000) (htag : tag.val = 1368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01369 (tag : Fin 10000) (htag : tag.val = 1369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01370 (tag : Fin 10000) (htag : tag.val = 1370) (k : Ring12) : tag.val = 1370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01371 (tag : Fin 10000) (htag : tag.val = 1371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01372 (tag : Fin 10000) (htag : tag.val = 1372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01373 (tag : Fin 10000) (htag : tag.val = 1373) (x : State) (e : Event) (dr : Ring12) : tag.val = 1373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01374 (tag : Fin 10000) (htag : tag.val = 1374) (x : State) (e : Event) (dr : Ring12) : tag.val = 1374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01375 (tag : Fin 10000) (htag : tag.val = 1375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01376 (tag : Fin 10000) (htag : tag.val = 1376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01377 (tag : Fin 10000) (htag : tag.val = 1377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01378 (tag : Fin 10000) (htag : tag.val = 1378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01379 (tag : Fin 10000) (htag : tag.val = 1379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01380 (tag : Fin 10000) (htag : tag.val = 1380) (k : Ring12) : tag.val = 1380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01381 (tag : Fin 10000) (htag : tag.val = 1381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01382 (tag : Fin 10000) (htag : tag.val = 1382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01383 (tag : Fin 10000) (htag : tag.val = 1383) (x : State) (e : Event) (dr : Ring12) : tag.val = 1383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01384 (tag : Fin 10000) (htag : tag.val = 1384) (x : State) (e : Event) (dr : Ring12) : tag.val = 1384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01385 (tag : Fin 10000) (htag : tag.val = 1385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01386 (tag : Fin 10000) (htag : tag.val = 1386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01387 (tag : Fin 10000) (htag : tag.val = 1387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01388 (tag : Fin 10000) (htag : tag.val = 1388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01389 (tag : Fin 10000) (htag : tag.val = 1389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01390 (tag : Fin 10000) (htag : tag.val = 1390) (k : Ring12) : tag.val = 1390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01391 (tag : Fin 10000) (htag : tag.val = 1391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01392 (tag : Fin 10000) (htag : tag.val = 1392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01393 (tag : Fin 10000) (htag : tag.val = 1393) (x : State) (e : Event) (dr : Ring12) : tag.val = 1393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01394 (tag : Fin 10000) (htag : tag.val = 1394) (x : State) (e : Event) (dr : Ring12) : tag.val = 1394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01395 (tag : Fin 10000) (htag : tag.val = 1395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01396 (tag : Fin 10000) (htag : tag.val = 1396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01397 (tag : Fin 10000) (htag : tag.val = 1397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01398 (tag : Fin 10000) (htag : tag.val = 1398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01399 (tag : Fin 10000) (htag : tag.val = 1399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
