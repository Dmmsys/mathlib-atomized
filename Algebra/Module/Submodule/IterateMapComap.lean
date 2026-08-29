/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!

# Iterate maps and comaps of submodules

Some preliminary work for establishing the strong rank condition for Noetherian rings.

Given two linear maps `f i : N →ₗ[R] M` and a submodule `K : Submodule R N`, we can define
`LinearMap.iterateMapComap f i n K : Submodule R N` to be `f⁻¹(i(⋯(f⁻¹(i(K)))))` (`n` times).
If `f(K) ≤ i(K)`, then this sequence is non-decreasing (`LinearMap.iterateMapComap_le_succ`).
On the other hand, if `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComap f i m K = LinearMap.iterateMapComap f i (m + 1) K`,
then for any `n`,
`LinearMap.iterateMapComap f i n K = LinearMap.iterateMapComap f i (n + 1) K`.
In particular, by taking `n = 0`, the kernel of `f` is contained in `K`
(`LinearMap.ker_le_of_iterateMapComap_eq_succ`),
which is a consequence of `LinearMap.ker_le_comap`.
As a special case, if one can take `K` to be zero,
then `f` is injective. This is the key result for establishing the strong rank condition
for Noetherian rings.

The construction here is adapted from the proof in Djoković's paper
*Epimorphisms of modules which must be isomorphisms* [djokovic1973].

-/

@[expose] public section

open Function Submodule

namespace LinearMap

variable {R N M : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] (f i : N ->ₗ[R] M)

/--
Definition of `iterateMapComap` / `iterateMapComap` 的定义

English:
definition iterateMapComap
  signature: (n : Nat)
  body: (fun K : Submodule R N => (K.map i).comap f)^[n]

中文:
定义 iterateMapComap
  签名: (n : 自然数)
  定义体: (fun K : Submodule R N => (K.map i).comap f)^[n]

Depends on / 依赖: K.map, Submodule
-/
def iterateMapComap (n : Nat) := (fun K : Submodule R N => (K.map i).comap f)^[n]

/--
theorem `iterateMapComap_le_succ` / 定理 `iterateMapComap_le_succ`

English:
theorem iterateMapComap_le_succ
  given: (K : Submodule R N) (h : K.map f <= K.map i) (n : Nat)
  proof: by
  nth_rw 2 [iterateMapComap]
  rw [iterate_succ']; rw [Function.comp_apply]; rw [← iterateMapComap]; rw [← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [iterateMapComap, iterate_succ', Function.comp_apply]
    calc
      _ <= (f.iterateMapComap i n K).m

中文:
定理 iterateMapComap_le_succ
  条件: (K : Submodule R N) (h : K.map f <= K.map i) (n : 自然数)
  证明: by
  nth_rw 2 [iterateMapComap]
  rw [iterate_succ']; rw [Function.comp_apply]; rw [← iterateMapComap]; rw [← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [iterateMapComap, iterate_succ', Function.comp_apply]
    calc
      _ <= (f.iterateMapComap i n K).m

Depends on / 依赖: Function, Function.comp_apply, comp_apply, f.iterateMapComap, iterateMapComap, iterate_succ, le_comap_map, map_comap_le, map_le_iff_le_comap, nth_rw, simp_rw
-/
theorem iterateMapComap_le_succ (K : Submodule R N) (h : K.map f <= K.map i) (n : Nat) :
    f.iterateMapComap i n K <= f.iterateMapComap i (n + 1) K := by
  nth_rw 2 [iterateMapComap]
  rw [iterate_succ']; rw [Function.comp_apply]; rw [← iterateMapComap]; rw [← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [iterateMapComap, iterate_succ', Function.comp_apply]
    calc
      _ <= (f.iterateMapComap i n K).map i := map_comap_le _ _
      _ <= (((f.iterateMapComap i n K).map f).comap f).map i := by grw [← le_comap_map]
      _ <= _ := by gcongr; exact ih

/--
theorem `iterateMapComap_eq_succ` / 定理 `iterateMapComap_eq_succ`

English:
theorem iterateMapComap_eq_succ
  statement: (K : Submodule R N)
  proof: by
  induction n with
  | zero =>
    contrapose! heq
    induction m with
    | zero => exact heq
    | succ m ih =>
      rw [iterateMapComap]; rw [iterateMapComap]; rw [iterate_succ']; rw [iterate_succ']
      exact fun H => ih (map_injective_of_injective hi (comap_injective_of_surjective hf H))


中文:
定理 iterateMapComap_eq_succ
  结论: (K : Submodule R N)
  证明: by
  induction n with
  | zero =>
    contrapose! heq
    induction m with
    | zero => exact heq
    | succ m ih =>
      rw [iterateMapComap]; rw [iterateMapComap]; rw [iterate_succ']; rw [iterate_succ']
      exact fun H => ih (map_injective_of_injective hi (comap_injective_of_surjective hf H))


Depends on / 依赖: Function, Function.comp_apply, comap_injective_of_surjective, comp_apply, contrapose, iterateMapComap, iterate_succ, map_injective_of_injective
-/
theorem iterateMapComap_eq_succ (K : Submodule R N)
    (m : Nat) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) (n : Nat) :
    f.iterateMapComap i n K = f.iterateMapComap i (n + 1) K := by
  induction n with
  | zero =>
    contrapose! heq
    induction m with
    | zero => exact heq
    | succ m ih =>
      rw [iterateMapComap]; rw [iterateMapComap]; rw [iterate_succ']; rw [iterate_succ']
      exact fun H => ih (map_injective_of_injective hi (comap_injective_of_surjective hf H))
  | succ n ih =>
    rw [iterateMapComap]; rw [iterateMapComap]; rw [iterate_succ']; rw [iterate_succ']; rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← iterateMapComap]; rw [← iterateMapComap]; rw [ih]

/--
theorem `ker_le_of_iterateMapComap_eq_succ` / 定理 `ker_le_of_iterateMapComap_eq_succ`

English:
theorem ker_le_of_iterateMapComap_eq_succ
  statement: (K : Submodule R N)
  proof: by
  rw [show K = _ from f.iterateMapComap_eq_succ i K m heq hf hi 0]
  exact f.ker_le_comap

中文:
定理 ker_le_of_iterateMapComap_eq_succ
  结论: (K : Submodule R N)
  证明: by
  rw [show K = _ from f.iterateMapComap_eq_succ i K m heq hf hi 0]
  exact f.ker_le_comap

Depends on / 依赖: f.iterateMapComap_eq_succ, f.ker_le_comap, iterateMapComap_eq_succ, ker_le_comap
-/
theorem ker_le_of_iterateMapComap_eq_succ (K : Submodule R N)
    (m : Nat) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) : LinearMap.ker f <= K := by
  rw [show K = _ from f.iterateMapComap_eq_succ i K m heq hf hi 0]
  exact f.ker_le_comap

end LinearMap
