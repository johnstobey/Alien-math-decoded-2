import IndependentDuodenary.MillenniumBridge

open IndependentDuodenary

example (x : PrizeBinaryWord) : (prizeEncodeWord x).length = x.length := by
  simp [prizeEncodeWord]

example (x w : PrizeBinaryWord) :
    (prizeEncodePair x w).length = x.length + w.length + 1 := by
  simp [prizeEncodePair, prizeEncodeWord]
  omega

example (a b : Bool) :
    (if a then (2 : Fin 4) else 1) = (if b then (2 : Fin 4) else 1) → a = b := by
  cases a <;> cases b <;> decide

example (x : PrizeBinaryWord) : (0 : Fin 4) ∉ prizeEncodeWord x := by
  intro hx
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hx
  cases b <;> simp_all

example (x : PrizeBinaryWord) : (3 : Fin 4) ∉ prizeEncodeWord x := by
  intro hx
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hx
  cases b <;> simp_all

#guard prizeEncodeWord [false, true] = [1, 2]
#guard prizeEncodePair [] [] = [3]
