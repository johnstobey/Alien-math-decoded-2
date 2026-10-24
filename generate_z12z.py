#!/usr/bin/env python3
"""Generate exactly 10,000 Lean 4 theorem instances from the supplied specification.
Requires Python 3.10+. Generated Lean files require mathlib and Lean 4.14.0.
Run inside the existing repository: python3 generate_z12z.py --output z12z_generated --check
"""

from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

COUNT = 10_000

PRELUDE = r"""import Mathlib

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
"""

FAMILIES = [
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (k : Ring12) : tag.val = {i} ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = {i} ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = {i} ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) : tag.val = {i} ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) : tag.val = {i} ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = {i} ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = {i} ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = {i} ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = {i} ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩""",
    r"""theorem generated_{i:05d} (tag : Fin 10000) (htag : tag.val = {i}) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = {i} ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩""",
]

def main() -> None:
    parser = argparse.ArgumentParser(description="Generate 10000 Lean theorem files.")
    parser.add_argument("--output", type=Path, default=Path("z12z_generated"))
    parser.add_argument("--batch-size", type=int, default=100)
    parser.add_argument("--check", action="store_true", help="Check generated files using lake.")
    args = parser.parse_args()

    if not 1 <= args.batch_size <= COUNT:
        parser.error("--batch-size must be between 1 and 10000")

    if args.check and shutil.which("lake") is None:
        parser.error("--check requires lake on PATH")

    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    
    files: list[Path] = []
    generated = 0

    for first in range(0, COUNT, args.batch_size):
        stop = min(first + args.batch_size, COUNT)
        path = out / f"Batch_{first:05d}_{stop - 1:05d}.lean"
        declarations = [
            FAMILIES[i % len(FAMILIES)].format(i=i)
            for i in range(first, stop)
        ]
        with path.open("w", encoding="utf-8", newline="\n") as stream:
            stream.write(PRELUDE)
            stream.write("\n\n".join(declarations))
            stream.write("\n\nend Z12ZCompilerV4\n")
        files.append(path)
        generated += len(declarations)

    assert generated == COUNT

    manifest = {
        "protocol": "Z12Z_DETERMINISTIC_COMPILER_V4",
        "ring": "ZMod 12",
        "anchor": 0,
        "generated_theorems": generated,
        "proof_families": len(FAMILIES),
        "lean_checked": False,
        "files": [path.name for path in files],
        "scope": "10000 parameterized instances of 10 proof families, checked independently per file; not 10000 independent mathematical discoveries.",
    }

    manifest_path = out / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    if args.check:
        for path in files:
            result = subprocess.run(["lake", "env", "lean", str(path)], check=False)
            if result.returncode != 0:
                raise SystemExit(result.returncode)
        manifest["lean_checked"] = True
        manifest["checked_files"] = len(files)
        manifest["sha256"] = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in files}
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({"output": str(out), "generated_theorems": generated}))

if __name__ == "__main__":
    main()