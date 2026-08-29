/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Monoid

/-! # Topological properties of the unitary (sub)group

* In a topological star monoid `R`, `unitary R` is a topological group
* In a topological star monoid `R` which is T1, `unitary R` is closed as a subset of `R`.
-/

public section

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousStar
  signature: R] : ContinuousStar (unitary R) where
  body: continuous_induced_rng.mpr continuous_subtype_val.star

中文:
实例 [余ntinuousStar
  签名: R] : 余ntinuousStar (unitary R) where
  定义体: continuous_induced_rng.mpr continuous_subtype_val.star

Depends on / 依赖: continuous_induced_rng, continuous_induced_rng.mpr, continuous_subtype_val, continuous_subtype_val.star
-/
instance [ContinuousStar R] : ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousStar
  signature: R] : ContinuousInv (unitary R) where
  body: continuous_star

中文:
实例 [余ntinuousStar
  签名: R] : 连续取逆 (unitary R) where
  定义体: continuous_star

Depends on / 依赖: continuous_star
-/
instance [ContinuousStar R] : ContinuousInv (unitary R) where
  continuous_inv := continuous_star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousMul
  signature: R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where

中文:
实例 [连续乘法
  签名: R] [余ntinuousStar R] : 是拓扑群 (unitary R) where
-/
instance [ContinuousMul R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where

/--
lemma `isClosed_unitary` / 引理 `isClosed_unitary`

English:
lemma isClosed_unitary
  given: [T1Space R] [ContinuousStar R] [ContinuousMul R]
  proof: by
  let f (u : R) : R × R := (star u * u, u * star u)
  have hf : f ⁻¹' {(1, 1)} = unitary R := by ext u; simp [f, Unitary.mem_iff]
  rw [← hf]
  exact isClosed_singleton.preimage (by fun_prop)

中文:
引理 isClosed_unitary
  条件: [T1空间 R] [余ntinuousStar R] [连续乘法 R]
  证明: by
  let f (u : R) : R × R := (star u * u, u * star u)
  have hf : f ⁻¹' {(1, 1)} = unitary R := by ext u; simp [f, Unitary.mem_iff]
  rw [← hf]
  exact isClosed_singleton.preimage (by fun_prop)

Depends on / 依赖: Unitary, Unitary.mem_iff, fun_prop, isClosed_singleton, isClosed_singleton.preimage, mem_iff, preimage, unitary
-/
lemma isClosed_unitary [T1Space R] [ContinuousStar R] [ContinuousMul R] :
    IsClosed (unitary R : Set R) := by
  let f (u : R) : R × R := (star u * u, u * star u)
  have hf : f ⁻¹' {(1, 1)} = unitary R := by ext u; simp [f, Unitary.mem_iff]
  rw [← hf]
  exact isClosed_singleton.preimage (by fun_prop)
