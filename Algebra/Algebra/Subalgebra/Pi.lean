/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Pi

/-!
# Products of subalgebras

In this file we define the product of subalgebras as a subalgebra of the product algebra.

## Main definitions

* `Subalgebra.pi`: the product of subalgebras.
-/

@[expose] public section

open Algebra

namespace Subalgebra
variable {ι R : Type*} {S : ι -> Type*} [CommSemiring R] [forall i, Semiring (S i)] [forall i, Algebra R (S i)]
  {s : Set ι} {t t₁ t₂ : forall i, Subalgebra R (S i)} {x : forall i, S i}

/-- The product of subalgebras as a subalgebra. -/
@[simps coe toSubsemiring]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (s : Set ι) (t : forall i, Subalgebra R (S i))
  body: Submodule.pi s fun i => (t i).toSubmodule
  mul_mem' hx hy i hi := (t i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (t i).algebraMap_mem _

中文:
定义 pi
  签名: (s : 集合 ι) (t : 对任意 i, 子代数 R (S i))
  定义体: Submodule.pi s fun i => (t i).toSubmodule
  mul_mem' hx hy i hi := (t i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (t i).algebraMap_mem _

Depends on / 依赖: Submodule, Submodule.pi, toSubmodule
-/
def pi (s : Set ι) (t : forall i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
  __ := Submodule.pi s fun i => (t i).toSubmodule
  mul_mem' hx hy i hi := (t i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (t i).algebraMap_mem _

/--
lemma `mem_pi` / 引理 `mem_pi`

English:
lemma mem_pi
  statement: x in pi s t ↔ forall i in s, x i in t i
  proof: .rfl

中文:
引理 mem_pi
  结论: x in pi s t ↔ 对任意 i in s, x i in t i
  证明: .rfl
-/
@[simp] lemma mem_pi : x in pi s t ↔ forall i in s, x i in t i := .rfl

open Subalgebra in
/--
lemma `pi_toSubmodule` / 引理 `pi_toSubmodule`

English:
lemma pi_toSubmodule
  statement: toSubmodule (pi s t) = .pi s fun i => (t i).toSubmodule
  proof: rfl

@[simp]

中文:
引理 pi_toSubmodule
  结论: toSubmodule (pi s t) = .pi s fun i => (t i).toSubmodule
  证明: rfl

@[simp]
-/
@[simp] lemma pi_toSubmodule : toSubmodule (pi s t) = .pi s fun i => (t i).toSubmodule := rfl

@[simp]
/--
lemma `pi_top` / 引理 `pi_top`

English:
lemma pi_top
  given: (s : Set ι)
  statement: pi s (fun i => (⊤ : Subalgebra R (S i))) = ⊤
  proof: SetLike.coe_injective Set.pi_univ _

中文:
引理 pi_top
  条件: (s : 集合 ι)
  结论: pi s (fun i => (⊤ : 子代数 R (S i))) = ⊤
  证明: SetLike.coe_injective Set.pi_univ _

Depends on / 依赖: Set.pi_univ, SetLike, SetLike.coe_injective, coe_injective, pi_univ
-/
lemma pi_top (s : Set ι) : pi s (fun i => (⊤ : Subalgebra R (S i))) = ⊤ :=
SetLike.coe_injective Set.pi_univ _

/--
lemma `pi_mono` / 引理 `pi_mono`

English:
lemma pi_mono
  given: (h : forall i in s, t₁ i <= t₂ i)
  statement: pi s t₁ <= pi s t₂
  proof: Set.pi_mono h

中文:
引理 pi_mono
  条件: (h : 对任意 i in s, t₁ i <= t₂ i)
  结论: pi s t₁ <= pi s t₂
  证明: Set.pi_mono h
-/
@[gcongr] lemma pi_mono (h : forall i in s, t₁ i <= t₂ i) : pi s t₁ <= pi s t₂ := Set.pi_mono h

/--
theorem `center_pi` / 定理 `center_pi`

English:
theorem center_pi
  statement: center R (Π i, S i) = pi .univ fun i => center R (S i)
  proof: SetLike.coe_injective Set.center_pi

中文:
定理 center_pi
  结论: center R (Π i, S i) = pi .univ fun i => center R (S i)
  证明: SetLike.coe_injective Set.center_pi
-/
protected theorem center_pi : center R (Π i, S i) = pi .univ fun i => center R (S i) :=
  SetLike.coe_injective Set.center_pi

end Subalgebra
