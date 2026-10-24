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
theorem generated_04200 (tag : Fin 10000) (htag : tag.val = 4200) (k : Ring12) : tag.val = 4200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04201 (tag : Fin 10000) (htag : tag.val = 4201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04202 (tag : Fin 10000) (htag : tag.val = 4202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04203 (tag : Fin 10000) (htag : tag.val = 4203) (x : State) (e : Event) (dr : Ring12) : tag.val = 4203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04204 (tag : Fin 10000) (htag : tag.val = 4204) (x : State) (e : Event) (dr : Ring12) : tag.val = 4204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04205 (tag : Fin 10000) (htag : tag.val = 4205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04206 (tag : Fin 10000) (htag : tag.val = 4206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04207 (tag : Fin 10000) (htag : tag.val = 4207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04208 (tag : Fin 10000) (htag : tag.val = 4208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04209 (tag : Fin 10000) (htag : tag.val = 4209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04210 (tag : Fin 10000) (htag : tag.val = 4210) (k : Ring12) : tag.val = 4210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04211 (tag : Fin 10000) (htag : tag.val = 4211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04212 (tag : Fin 10000) (htag : tag.val = 4212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04213 (tag : Fin 10000) (htag : tag.val = 4213) (x : State) (e : Event) (dr : Ring12) : tag.val = 4213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04214 (tag : Fin 10000) (htag : tag.val = 4214) (x : State) (e : Event) (dr : Ring12) : tag.val = 4214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04215 (tag : Fin 10000) (htag : tag.val = 4215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04216 (tag : Fin 10000) (htag : tag.val = 4216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04217 (tag : Fin 10000) (htag : tag.val = 4217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04218 (tag : Fin 10000) (htag : tag.val = 4218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04219 (tag : Fin 10000) (htag : tag.val = 4219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04220 (tag : Fin 10000) (htag : tag.val = 4220) (k : Ring12) : tag.val = 4220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04221 (tag : Fin 10000) (htag : tag.val = 4221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04222 (tag : Fin 10000) (htag : tag.val = 4222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04223 (tag : Fin 10000) (htag : tag.val = 4223) (x : State) (e : Event) (dr : Ring12) : tag.val = 4223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04224 (tag : Fin 10000) (htag : tag.val = 4224) (x : State) (e : Event) (dr : Ring12) : tag.val = 4224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04225 (tag : Fin 10000) (htag : tag.val = 4225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04226 (tag : Fin 10000) (htag : tag.val = 4226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04227 (tag : Fin 10000) (htag : tag.val = 4227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04228 (tag : Fin 10000) (htag : tag.val = 4228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04229 (tag : Fin 10000) (htag : tag.val = 4229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04230 (tag : Fin 10000) (htag : tag.val = 4230) (k : Ring12) : tag.val = 4230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04231 (tag : Fin 10000) (htag : tag.val = 4231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04232 (tag : Fin 10000) (htag : tag.val = 4232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04233 (tag : Fin 10000) (htag : tag.val = 4233) (x : State) (e : Event) (dr : Ring12) : tag.val = 4233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04234 (tag : Fin 10000) (htag : tag.val = 4234) (x : State) (e : Event) (dr : Ring12) : tag.val = 4234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04235 (tag : Fin 10000) (htag : tag.val = 4235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04236 (tag : Fin 10000) (htag : tag.val = 4236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04237 (tag : Fin 10000) (htag : tag.val = 4237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04238 (tag : Fin 10000) (htag : tag.val = 4238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04239 (tag : Fin 10000) (htag : tag.val = 4239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04240 (tag : Fin 10000) (htag : tag.val = 4240) (k : Ring12) : tag.val = 4240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04241 (tag : Fin 10000) (htag : tag.val = 4241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04242 (tag : Fin 10000) (htag : tag.val = 4242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04243 (tag : Fin 10000) (htag : tag.val = 4243) (x : State) (e : Event) (dr : Ring12) : tag.val = 4243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04244 (tag : Fin 10000) (htag : tag.val = 4244) (x : State) (e : Event) (dr : Ring12) : tag.val = 4244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04245 (tag : Fin 10000) (htag : tag.val = 4245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04246 (tag : Fin 10000) (htag : tag.val = 4246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04247 (tag : Fin 10000) (htag : tag.val = 4247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04248 (tag : Fin 10000) (htag : tag.val = 4248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04249 (tag : Fin 10000) (htag : tag.val = 4249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04250 (tag : Fin 10000) (htag : tag.val = 4250) (k : Ring12) : tag.val = 4250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04251 (tag : Fin 10000) (htag : tag.val = 4251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04252 (tag : Fin 10000) (htag : tag.val = 4252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04253 (tag : Fin 10000) (htag : tag.val = 4253) (x : State) (e : Event) (dr : Ring12) : tag.val = 4253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04254 (tag : Fin 10000) (htag : tag.val = 4254) (x : State) (e : Event) (dr : Ring12) : tag.val = 4254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04255 (tag : Fin 10000) (htag : tag.val = 4255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04256 (tag : Fin 10000) (htag : tag.val = 4256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04257 (tag : Fin 10000) (htag : tag.val = 4257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04258 (tag : Fin 10000) (htag : tag.val = 4258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04259 (tag : Fin 10000) (htag : tag.val = 4259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04260 (tag : Fin 10000) (htag : tag.val = 4260) (k : Ring12) : tag.val = 4260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04261 (tag : Fin 10000) (htag : tag.val = 4261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04262 (tag : Fin 10000) (htag : tag.val = 4262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04263 (tag : Fin 10000) (htag : tag.val = 4263) (x : State) (e : Event) (dr : Ring12) : tag.val = 4263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04264 (tag : Fin 10000) (htag : tag.val = 4264) (x : State) (e : Event) (dr : Ring12) : tag.val = 4264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04265 (tag : Fin 10000) (htag : tag.val = 4265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04266 (tag : Fin 10000) (htag : tag.val = 4266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04267 (tag : Fin 10000) (htag : tag.val = 4267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04268 (tag : Fin 10000) (htag : tag.val = 4268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04269 (tag : Fin 10000) (htag : tag.val = 4269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04270 (tag : Fin 10000) (htag : tag.val = 4270) (k : Ring12) : tag.val = 4270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04271 (tag : Fin 10000) (htag : tag.val = 4271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04272 (tag : Fin 10000) (htag : tag.val = 4272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04273 (tag : Fin 10000) (htag : tag.val = 4273) (x : State) (e : Event) (dr : Ring12) : tag.val = 4273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04274 (tag : Fin 10000) (htag : tag.val = 4274) (x : State) (e : Event) (dr : Ring12) : tag.val = 4274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04275 (tag : Fin 10000) (htag : tag.val = 4275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04276 (tag : Fin 10000) (htag : tag.val = 4276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04277 (tag : Fin 10000) (htag : tag.val = 4277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04278 (tag : Fin 10000) (htag : tag.val = 4278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04279 (tag : Fin 10000) (htag : tag.val = 4279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04280 (tag : Fin 10000) (htag : tag.val = 4280) (k : Ring12) : tag.val = 4280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04281 (tag : Fin 10000) (htag : tag.val = 4281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04282 (tag : Fin 10000) (htag : tag.val = 4282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04283 (tag : Fin 10000) (htag : tag.val = 4283) (x : State) (e : Event) (dr : Ring12) : tag.val = 4283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04284 (tag : Fin 10000) (htag : tag.val = 4284) (x : State) (e : Event) (dr : Ring12) : tag.val = 4284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04285 (tag : Fin 10000) (htag : tag.val = 4285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04286 (tag : Fin 10000) (htag : tag.val = 4286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04287 (tag : Fin 10000) (htag : tag.val = 4287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04288 (tag : Fin 10000) (htag : tag.val = 4288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04289 (tag : Fin 10000) (htag : tag.val = 4289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04290 (tag : Fin 10000) (htag : tag.val = 4290) (k : Ring12) : tag.val = 4290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04291 (tag : Fin 10000) (htag : tag.val = 4291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04292 (tag : Fin 10000) (htag : tag.val = 4292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04293 (tag : Fin 10000) (htag : tag.val = 4293) (x : State) (e : Event) (dr : Ring12) : tag.val = 4293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04294 (tag : Fin 10000) (htag : tag.val = 4294) (x : State) (e : Event) (dr : Ring12) : tag.val = 4294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04295 (tag : Fin 10000) (htag : tag.val = 4295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04296 (tag : Fin 10000) (htag : tag.val = 4296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04297 (tag : Fin 10000) (htag : tag.val = 4297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04298 (tag : Fin 10000) (htag : tag.val = 4298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04299 (tag : Fin 10000) (htag : tag.val = 4299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
