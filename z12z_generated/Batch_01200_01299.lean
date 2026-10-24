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
theorem generated_01200 (tag : Fin 10000) (htag : tag.val = 1200) (k : Ring12) : tag.val = 1200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01201 (tag : Fin 10000) (htag : tag.val = 1201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01202 (tag : Fin 10000) (htag : tag.val = 1202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01203 (tag : Fin 10000) (htag : tag.val = 1203) (x : State) (e : Event) (dr : Ring12) : tag.val = 1203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01204 (tag : Fin 10000) (htag : tag.val = 1204) (x : State) (e : Event) (dr : Ring12) : tag.val = 1204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01205 (tag : Fin 10000) (htag : tag.val = 1205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01206 (tag : Fin 10000) (htag : tag.val = 1206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01207 (tag : Fin 10000) (htag : tag.val = 1207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01208 (tag : Fin 10000) (htag : tag.val = 1208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01209 (tag : Fin 10000) (htag : tag.val = 1209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01210 (tag : Fin 10000) (htag : tag.val = 1210) (k : Ring12) : tag.val = 1210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01211 (tag : Fin 10000) (htag : tag.val = 1211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01212 (tag : Fin 10000) (htag : tag.val = 1212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01213 (tag : Fin 10000) (htag : tag.val = 1213) (x : State) (e : Event) (dr : Ring12) : tag.val = 1213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01214 (tag : Fin 10000) (htag : tag.val = 1214) (x : State) (e : Event) (dr : Ring12) : tag.val = 1214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01215 (tag : Fin 10000) (htag : tag.val = 1215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01216 (tag : Fin 10000) (htag : tag.val = 1216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01217 (tag : Fin 10000) (htag : tag.val = 1217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01218 (tag : Fin 10000) (htag : tag.val = 1218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01219 (tag : Fin 10000) (htag : tag.val = 1219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01220 (tag : Fin 10000) (htag : tag.val = 1220) (k : Ring12) : tag.val = 1220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01221 (tag : Fin 10000) (htag : tag.val = 1221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01222 (tag : Fin 10000) (htag : tag.val = 1222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01223 (tag : Fin 10000) (htag : tag.val = 1223) (x : State) (e : Event) (dr : Ring12) : tag.val = 1223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01224 (tag : Fin 10000) (htag : tag.val = 1224) (x : State) (e : Event) (dr : Ring12) : tag.val = 1224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01225 (tag : Fin 10000) (htag : tag.val = 1225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01226 (tag : Fin 10000) (htag : tag.val = 1226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01227 (tag : Fin 10000) (htag : tag.val = 1227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01228 (tag : Fin 10000) (htag : tag.val = 1228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01229 (tag : Fin 10000) (htag : tag.val = 1229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01230 (tag : Fin 10000) (htag : tag.val = 1230) (k : Ring12) : tag.val = 1230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01231 (tag : Fin 10000) (htag : tag.val = 1231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01232 (tag : Fin 10000) (htag : tag.val = 1232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01233 (tag : Fin 10000) (htag : tag.val = 1233) (x : State) (e : Event) (dr : Ring12) : tag.val = 1233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01234 (tag : Fin 10000) (htag : tag.val = 1234) (x : State) (e : Event) (dr : Ring12) : tag.val = 1234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01235 (tag : Fin 10000) (htag : tag.val = 1235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01236 (tag : Fin 10000) (htag : tag.val = 1236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01237 (tag : Fin 10000) (htag : tag.val = 1237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01238 (tag : Fin 10000) (htag : tag.val = 1238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01239 (tag : Fin 10000) (htag : tag.val = 1239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01240 (tag : Fin 10000) (htag : tag.val = 1240) (k : Ring12) : tag.val = 1240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01241 (tag : Fin 10000) (htag : tag.val = 1241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01242 (tag : Fin 10000) (htag : tag.val = 1242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01243 (tag : Fin 10000) (htag : tag.val = 1243) (x : State) (e : Event) (dr : Ring12) : tag.val = 1243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01244 (tag : Fin 10000) (htag : tag.val = 1244) (x : State) (e : Event) (dr : Ring12) : tag.val = 1244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01245 (tag : Fin 10000) (htag : tag.val = 1245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01246 (tag : Fin 10000) (htag : tag.val = 1246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01247 (tag : Fin 10000) (htag : tag.val = 1247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01248 (tag : Fin 10000) (htag : tag.val = 1248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01249 (tag : Fin 10000) (htag : tag.val = 1249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01250 (tag : Fin 10000) (htag : tag.val = 1250) (k : Ring12) : tag.val = 1250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01251 (tag : Fin 10000) (htag : tag.val = 1251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01252 (tag : Fin 10000) (htag : tag.val = 1252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01253 (tag : Fin 10000) (htag : tag.val = 1253) (x : State) (e : Event) (dr : Ring12) : tag.val = 1253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01254 (tag : Fin 10000) (htag : tag.val = 1254) (x : State) (e : Event) (dr : Ring12) : tag.val = 1254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01255 (tag : Fin 10000) (htag : tag.val = 1255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01256 (tag : Fin 10000) (htag : tag.val = 1256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01257 (tag : Fin 10000) (htag : tag.val = 1257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01258 (tag : Fin 10000) (htag : tag.val = 1258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01259 (tag : Fin 10000) (htag : tag.val = 1259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01260 (tag : Fin 10000) (htag : tag.val = 1260) (k : Ring12) : tag.val = 1260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01261 (tag : Fin 10000) (htag : tag.val = 1261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01262 (tag : Fin 10000) (htag : tag.val = 1262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01263 (tag : Fin 10000) (htag : tag.val = 1263) (x : State) (e : Event) (dr : Ring12) : tag.val = 1263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01264 (tag : Fin 10000) (htag : tag.val = 1264) (x : State) (e : Event) (dr : Ring12) : tag.val = 1264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01265 (tag : Fin 10000) (htag : tag.val = 1265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01266 (tag : Fin 10000) (htag : tag.val = 1266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01267 (tag : Fin 10000) (htag : tag.val = 1267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01268 (tag : Fin 10000) (htag : tag.val = 1268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01269 (tag : Fin 10000) (htag : tag.val = 1269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01270 (tag : Fin 10000) (htag : tag.val = 1270) (k : Ring12) : tag.val = 1270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01271 (tag : Fin 10000) (htag : tag.val = 1271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01272 (tag : Fin 10000) (htag : tag.val = 1272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01273 (tag : Fin 10000) (htag : tag.val = 1273) (x : State) (e : Event) (dr : Ring12) : tag.val = 1273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01274 (tag : Fin 10000) (htag : tag.val = 1274) (x : State) (e : Event) (dr : Ring12) : tag.val = 1274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01275 (tag : Fin 10000) (htag : tag.val = 1275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01276 (tag : Fin 10000) (htag : tag.val = 1276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01277 (tag : Fin 10000) (htag : tag.val = 1277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01278 (tag : Fin 10000) (htag : tag.val = 1278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01279 (tag : Fin 10000) (htag : tag.val = 1279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01280 (tag : Fin 10000) (htag : tag.val = 1280) (k : Ring12) : tag.val = 1280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01281 (tag : Fin 10000) (htag : tag.val = 1281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01282 (tag : Fin 10000) (htag : tag.val = 1282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01283 (tag : Fin 10000) (htag : tag.val = 1283) (x : State) (e : Event) (dr : Ring12) : tag.val = 1283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01284 (tag : Fin 10000) (htag : tag.val = 1284) (x : State) (e : Event) (dr : Ring12) : tag.val = 1284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01285 (tag : Fin 10000) (htag : tag.val = 1285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01286 (tag : Fin 10000) (htag : tag.val = 1286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01287 (tag : Fin 10000) (htag : tag.val = 1287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01288 (tag : Fin 10000) (htag : tag.val = 1288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01289 (tag : Fin 10000) (htag : tag.val = 1289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01290 (tag : Fin 10000) (htag : tag.val = 1290) (k : Ring12) : tag.val = 1290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01291 (tag : Fin 10000) (htag : tag.val = 1291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01292 (tag : Fin 10000) (htag : tag.val = 1292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01293 (tag : Fin 10000) (htag : tag.val = 1293) (x : State) (e : Event) (dr : Ring12) : tag.val = 1293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01294 (tag : Fin 10000) (htag : tag.val = 1294) (x : State) (e : Event) (dr : Ring12) : tag.val = 1294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01295 (tag : Fin 10000) (htag : tag.val = 1295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01296 (tag : Fin 10000) (htag : tag.val = 1296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01297 (tag : Fin 10000) (htag : tag.val = 1297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01298 (tag : Fin 10000) (htag : tag.val = 1298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01299 (tag : Fin 10000) (htag : tag.val = 1299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
