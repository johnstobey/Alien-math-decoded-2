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
theorem generated_00200 (tag : Fin 10000) (htag : tag.val = 200) (k : Ring12) : tag.val = 200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00201 (tag : Fin 10000) (htag : tag.val = 201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00202 (tag : Fin 10000) (htag : tag.val = 202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00203 (tag : Fin 10000) (htag : tag.val = 203) (x : State) (e : Event) (dr : Ring12) : tag.val = 203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00204 (tag : Fin 10000) (htag : tag.val = 204) (x : State) (e : Event) (dr : Ring12) : tag.val = 204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00205 (tag : Fin 10000) (htag : tag.val = 205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00206 (tag : Fin 10000) (htag : tag.val = 206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00207 (tag : Fin 10000) (htag : tag.val = 207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00208 (tag : Fin 10000) (htag : tag.val = 208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00209 (tag : Fin 10000) (htag : tag.val = 209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00210 (tag : Fin 10000) (htag : tag.val = 210) (k : Ring12) : tag.val = 210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00211 (tag : Fin 10000) (htag : tag.val = 211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00212 (tag : Fin 10000) (htag : tag.val = 212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00213 (tag : Fin 10000) (htag : tag.val = 213) (x : State) (e : Event) (dr : Ring12) : tag.val = 213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00214 (tag : Fin 10000) (htag : tag.val = 214) (x : State) (e : Event) (dr : Ring12) : tag.val = 214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00215 (tag : Fin 10000) (htag : tag.val = 215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00216 (tag : Fin 10000) (htag : tag.val = 216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00217 (tag : Fin 10000) (htag : tag.val = 217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00218 (tag : Fin 10000) (htag : tag.val = 218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00219 (tag : Fin 10000) (htag : tag.val = 219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00220 (tag : Fin 10000) (htag : tag.val = 220) (k : Ring12) : tag.val = 220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00221 (tag : Fin 10000) (htag : tag.val = 221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00222 (tag : Fin 10000) (htag : tag.val = 222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00223 (tag : Fin 10000) (htag : tag.val = 223) (x : State) (e : Event) (dr : Ring12) : tag.val = 223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00224 (tag : Fin 10000) (htag : tag.val = 224) (x : State) (e : Event) (dr : Ring12) : tag.val = 224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00225 (tag : Fin 10000) (htag : tag.val = 225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00226 (tag : Fin 10000) (htag : tag.val = 226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00227 (tag : Fin 10000) (htag : tag.val = 227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00228 (tag : Fin 10000) (htag : tag.val = 228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00229 (tag : Fin 10000) (htag : tag.val = 229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00230 (tag : Fin 10000) (htag : tag.val = 230) (k : Ring12) : tag.val = 230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00231 (tag : Fin 10000) (htag : tag.val = 231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00232 (tag : Fin 10000) (htag : tag.val = 232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00233 (tag : Fin 10000) (htag : tag.val = 233) (x : State) (e : Event) (dr : Ring12) : tag.val = 233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00234 (tag : Fin 10000) (htag : tag.val = 234) (x : State) (e : Event) (dr : Ring12) : tag.val = 234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00235 (tag : Fin 10000) (htag : tag.val = 235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00236 (tag : Fin 10000) (htag : tag.val = 236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00237 (tag : Fin 10000) (htag : tag.val = 237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00238 (tag : Fin 10000) (htag : tag.val = 238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00239 (tag : Fin 10000) (htag : tag.val = 239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00240 (tag : Fin 10000) (htag : tag.val = 240) (k : Ring12) : tag.val = 240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00241 (tag : Fin 10000) (htag : tag.val = 241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00242 (tag : Fin 10000) (htag : tag.val = 242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00243 (tag : Fin 10000) (htag : tag.val = 243) (x : State) (e : Event) (dr : Ring12) : tag.val = 243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00244 (tag : Fin 10000) (htag : tag.val = 244) (x : State) (e : Event) (dr : Ring12) : tag.val = 244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00245 (tag : Fin 10000) (htag : tag.val = 245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00246 (tag : Fin 10000) (htag : tag.val = 246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00247 (tag : Fin 10000) (htag : tag.val = 247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00248 (tag : Fin 10000) (htag : tag.val = 248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00249 (tag : Fin 10000) (htag : tag.val = 249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00250 (tag : Fin 10000) (htag : tag.val = 250) (k : Ring12) : tag.val = 250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00251 (tag : Fin 10000) (htag : tag.val = 251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00252 (tag : Fin 10000) (htag : tag.val = 252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00253 (tag : Fin 10000) (htag : tag.val = 253) (x : State) (e : Event) (dr : Ring12) : tag.val = 253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00254 (tag : Fin 10000) (htag : tag.val = 254) (x : State) (e : Event) (dr : Ring12) : tag.val = 254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00255 (tag : Fin 10000) (htag : tag.val = 255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00256 (tag : Fin 10000) (htag : tag.val = 256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00257 (tag : Fin 10000) (htag : tag.val = 257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00258 (tag : Fin 10000) (htag : tag.val = 258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00259 (tag : Fin 10000) (htag : tag.val = 259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00260 (tag : Fin 10000) (htag : tag.val = 260) (k : Ring12) : tag.val = 260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00261 (tag : Fin 10000) (htag : tag.val = 261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00262 (tag : Fin 10000) (htag : tag.val = 262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00263 (tag : Fin 10000) (htag : tag.val = 263) (x : State) (e : Event) (dr : Ring12) : tag.val = 263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00264 (tag : Fin 10000) (htag : tag.val = 264) (x : State) (e : Event) (dr : Ring12) : tag.val = 264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00265 (tag : Fin 10000) (htag : tag.val = 265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00266 (tag : Fin 10000) (htag : tag.val = 266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00267 (tag : Fin 10000) (htag : tag.val = 267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00268 (tag : Fin 10000) (htag : tag.val = 268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00269 (tag : Fin 10000) (htag : tag.val = 269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00270 (tag : Fin 10000) (htag : tag.val = 270) (k : Ring12) : tag.val = 270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00271 (tag : Fin 10000) (htag : tag.val = 271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00272 (tag : Fin 10000) (htag : tag.val = 272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00273 (tag : Fin 10000) (htag : tag.val = 273) (x : State) (e : Event) (dr : Ring12) : tag.val = 273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00274 (tag : Fin 10000) (htag : tag.val = 274) (x : State) (e : Event) (dr : Ring12) : tag.val = 274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00275 (tag : Fin 10000) (htag : tag.val = 275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00276 (tag : Fin 10000) (htag : tag.val = 276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00277 (tag : Fin 10000) (htag : tag.val = 277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00278 (tag : Fin 10000) (htag : tag.val = 278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00279 (tag : Fin 10000) (htag : tag.val = 279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00280 (tag : Fin 10000) (htag : tag.val = 280) (k : Ring12) : tag.val = 280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00281 (tag : Fin 10000) (htag : tag.val = 281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00282 (tag : Fin 10000) (htag : tag.val = 282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00283 (tag : Fin 10000) (htag : tag.val = 283) (x : State) (e : Event) (dr : Ring12) : tag.val = 283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00284 (tag : Fin 10000) (htag : tag.val = 284) (x : State) (e : Event) (dr : Ring12) : tag.val = 284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00285 (tag : Fin 10000) (htag : tag.val = 285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00286 (tag : Fin 10000) (htag : tag.val = 286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00287 (tag : Fin 10000) (htag : tag.val = 287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00288 (tag : Fin 10000) (htag : tag.val = 288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00289 (tag : Fin 10000) (htag : tag.val = 289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00290 (tag : Fin 10000) (htag : tag.val = 290) (k : Ring12) : tag.val = 290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00291 (tag : Fin 10000) (htag : tag.val = 291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00292 (tag : Fin 10000) (htag : tag.val = 292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00293 (tag : Fin 10000) (htag : tag.val = 293) (x : State) (e : Event) (dr : Ring12) : tag.val = 293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00294 (tag : Fin 10000) (htag : tag.val = 294) (x : State) (e : Event) (dr : Ring12) : tag.val = 294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00295 (tag : Fin 10000) (htag : tag.val = 295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00296 (tag : Fin 10000) (htag : tag.val = 296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00297 (tag : Fin 10000) (htag : tag.val = 297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00298 (tag : Fin 10000) (htag : tag.val = 298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00299 (tag : Fin 10000) (htag : tag.val = 299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
