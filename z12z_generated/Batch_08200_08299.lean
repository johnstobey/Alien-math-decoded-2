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
theorem generated_08200 (tag : Fin 10000) (htag : tag.val = 8200) (k : Ring12) : tag.val = 8200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08201 (tag : Fin 10000) (htag : tag.val = 8201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08202 (tag : Fin 10000) (htag : tag.val = 8202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08203 (tag : Fin 10000) (htag : tag.val = 8203) (x : State) (e : Event) (dr : Ring12) : tag.val = 8203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08204 (tag : Fin 10000) (htag : tag.val = 8204) (x : State) (e : Event) (dr : Ring12) : tag.val = 8204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08205 (tag : Fin 10000) (htag : tag.val = 8205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08206 (tag : Fin 10000) (htag : tag.val = 8206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08207 (tag : Fin 10000) (htag : tag.val = 8207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08208 (tag : Fin 10000) (htag : tag.val = 8208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08209 (tag : Fin 10000) (htag : tag.val = 8209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08210 (tag : Fin 10000) (htag : tag.val = 8210) (k : Ring12) : tag.val = 8210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08211 (tag : Fin 10000) (htag : tag.val = 8211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08212 (tag : Fin 10000) (htag : tag.val = 8212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08213 (tag : Fin 10000) (htag : tag.val = 8213) (x : State) (e : Event) (dr : Ring12) : tag.val = 8213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08214 (tag : Fin 10000) (htag : tag.val = 8214) (x : State) (e : Event) (dr : Ring12) : tag.val = 8214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08215 (tag : Fin 10000) (htag : tag.val = 8215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08216 (tag : Fin 10000) (htag : tag.val = 8216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08217 (tag : Fin 10000) (htag : tag.val = 8217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08218 (tag : Fin 10000) (htag : tag.val = 8218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08219 (tag : Fin 10000) (htag : tag.val = 8219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08220 (tag : Fin 10000) (htag : tag.val = 8220) (k : Ring12) : tag.val = 8220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08221 (tag : Fin 10000) (htag : tag.val = 8221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08222 (tag : Fin 10000) (htag : tag.val = 8222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08223 (tag : Fin 10000) (htag : tag.val = 8223) (x : State) (e : Event) (dr : Ring12) : tag.val = 8223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08224 (tag : Fin 10000) (htag : tag.val = 8224) (x : State) (e : Event) (dr : Ring12) : tag.val = 8224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08225 (tag : Fin 10000) (htag : tag.val = 8225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08226 (tag : Fin 10000) (htag : tag.val = 8226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08227 (tag : Fin 10000) (htag : tag.val = 8227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08228 (tag : Fin 10000) (htag : tag.val = 8228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08229 (tag : Fin 10000) (htag : tag.val = 8229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08230 (tag : Fin 10000) (htag : tag.val = 8230) (k : Ring12) : tag.val = 8230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08231 (tag : Fin 10000) (htag : tag.val = 8231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08232 (tag : Fin 10000) (htag : tag.val = 8232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08233 (tag : Fin 10000) (htag : tag.val = 8233) (x : State) (e : Event) (dr : Ring12) : tag.val = 8233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08234 (tag : Fin 10000) (htag : tag.val = 8234) (x : State) (e : Event) (dr : Ring12) : tag.val = 8234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08235 (tag : Fin 10000) (htag : tag.val = 8235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08236 (tag : Fin 10000) (htag : tag.val = 8236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08237 (tag : Fin 10000) (htag : tag.val = 8237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08238 (tag : Fin 10000) (htag : tag.val = 8238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08239 (tag : Fin 10000) (htag : tag.val = 8239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08240 (tag : Fin 10000) (htag : tag.val = 8240) (k : Ring12) : tag.val = 8240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08241 (tag : Fin 10000) (htag : tag.val = 8241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08242 (tag : Fin 10000) (htag : tag.val = 8242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08243 (tag : Fin 10000) (htag : tag.val = 8243) (x : State) (e : Event) (dr : Ring12) : tag.val = 8243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08244 (tag : Fin 10000) (htag : tag.val = 8244) (x : State) (e : Event) (dr : Ring12) : tag.val = 8244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08245 (tag : Fin 10000) (htag : tag.val = 8245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08246 (tag : Fin 10000) (htag : tag.val = 8246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08247 (tag : Fin 10000) (htag : tag.val = 8247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08248 (tag : Fin 10000) (htag : tag.val = 8248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08249 (tag : Fin 10000) (htag : tag.val = 8249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08250 (tag : Fin 10000) (htag : tag.val = 8250) (k : Ring12) : tag.val = 8250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08251 (tag : Fin 10000) (htag : tag.val = 8251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08252 (tag : Fin 10000) (htag : tag.val = 8252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08253 (tag : Fin 10000) (htag : tag.val = 8253) (x : State) (e : Event) (dr : Ring12) : tag.val = 8253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08254 (tag : Fin 10000) (htag : tag.val = 8254) (x : State) (e : Event) (dr : Ring12) : tag.val = 8254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08255 (tag : Fin 10000) (htag : tag.val = 8255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08256 (tag : Fin 10000) (htag : tag.val = 8256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08257 (tag : Fin 10000) (htag : tag.val = 8257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08258 (tag : Fin 10000) (htag : tag.val = 8258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08259 (tag : Fin 10000) (htag : tag.val = 8259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08260 (tag : Fin 10000) (htag : tag.val = 8260) (k : Ring12) : tag.val = 8260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08261 (tag : Fin 10000) (htag : tag.val = 8261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08262 (tag : Fin 10000) (htag : tag.val = 8262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08263 (tag : Fin 10000) (htag : tag.val = 8263) (x : State) (e : Event) (dr : Ring12) : tag.val = 8263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08264 (tag : Fin 10000) (htag : tag.val = 8264) (x : State) (e : Event) (dr : Ring12) : tag.val = 8264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08265 (tag : Fin 10000) (htag : tag.val = 8265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08266 (tag : Fin 10000) (htag : tag.val = 8266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08267 (tag : Fin 10000) (htag : tag.val = 8267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08268 (tag : Fin 10000) (htag : tag.val = 8268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08269 (tag : Fin 10000) (htag : tag.val = 8269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08270 (tag : Fin 10000) (htag : tag.val = 8270) (k : Ring12) : tag.val = 8270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08271 (tag : Fin 10000) (htag : tag.val = 8271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08272 (tag : Fin 10000) (htag : tag.val = 8272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08273 (tag : Fin 10000) (htag : tag.val = 8273) (x : State) (e : Event) (dr : Ring12) : tag.val = 8273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08274 (tag : Fin 10000) (htag : tag.val = 8274) (x : State) (e : Event) (dr : Ring12) : tag.val = 8274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08275 (tag : Fin 10000) (htag : tag.val = 8275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08276 (tag : Fin 10000) (htag : tag.val = 8276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08277 (tag : Fin 10000) (htag : tag.val = 8277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08278 (tag : Fin 10000) (htag : tag.val = 8278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08279 (tag : Fin 10000) (htag : tag.val = 8279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08280 (tag : Fin 10000) (htag : tag.val = 8280) (k : Ring12) : tag.val = 8280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08281 (tag : Fin 10000) (htag : tag.val = 8281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08282 (tag : Fin 10000) (htag : tag.val = 8282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08283 (tag : Fin 10000) (htag : tag.val = 8283) (x : State) (e : Event) (dr : Ring12) : tag.val = 8283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08284 (tag : Fin 10000) (htag : tag.val = 8284) (x : State) (e : Event) (dr : Ring12) : tag.val = 8284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08285 (tag : Fin 10000) (htag : tag.val = 8285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08286 (tag : Fin 10000) (htag : tag.val = 8286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08287 (tag : Fin 10000) (htag : tag.val = 8287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08288 (tag : Fin 10000) (htag : tag.val = 8288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08289 (tag : Fin 10000) (htag : tag.val = 8289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08290 (tag : Fin 10000) (htag : tag.val = 8290) (k : Ring12) : tag.val = 8290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08291 (tag : Fin 10000) (htag : tag.val = 8291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08292 (tag : Fin 10000) (htag : tag.val = 8292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08293 (tag : Fin 10000) (htag : tag.val = 8293) (x : State) (e : Event) (dr : Ring12) : tag.val = 8293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08294 (tag : Fin 10000) (htag : tag.val = 8294) (x : State) (e : Event) (dr : Ring12) : tag.val = 8294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08295 (tag : Fin 10000) (htag : tag.val = 8295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08296 (tag : Fin 10000) (htag : tag.val = 8296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08297 (tag : Fin 10000) (htag : tag.val = 8297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08298 (tag : Fin 10000) (htag : tag.val = 8298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08299 (tag : Fin 10000) (htag : tag.val = 8299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
