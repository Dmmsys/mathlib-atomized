/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.SetLike.Basic

/-! # Class of grading-preserving functions and isomorphisms

We define `GradedFunLike F 𝒜 ℬ` where `𝒜` and `ℬ` represent some sort of grading. This class
assumes `FunLike A B` where `A` and `B` are the underlying types.

We also define `GradedEquivLike E 𝒜 ℬ`, which is similar to `EquivLike`, where here `e : E` is
required to satisfy `x ∈ 𝒜 i ↔ e x ∈ ℬ i`.
-/

@[expose] public section

/--
Definition of `GradedFunLike` / `GradedFunLike` 的定义

English:
class GradedFunLike
  parameters: (F : Type*) {A B σ τ ι : outParam Type*}
  axioms and operations (1):
    - map_mem((f : F) {i x}) : x in 𝒜 i -> f x in ℬ i

中文:
类 GradedFunLike
  参数: (F : 类型) {A B σ τ ι : outParam 类型}
  公理与运算 (1 个):
    - map_mem((f : F) {i x}) : x in 𝒜 i -> f x in ℬ i
-/
class GradedFunLike (F : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι -> σ) (ℬ : outParam <| ι -> τ)
    [FunLike F A B] where
  map_mem (f : F) {i x} : x in 𝒜 i -> f x in ℬ i

section GradedFunLike

variable {F A B σ τ ι : Type*}
  [SetLike σ A] [SetLike τ B] {𝒜 : ι -> σ} {ℬ : ι -> τ} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]

/--
lemma `Graded.map_mem` / 引理 `Graded.map_mem`

English:
lemma Graded.map_mem
  given: (f : F) {i x} (h : x in 𝒜 i)
  statement: f x in ℬ i
  proof: GradedFunLike.map_mem f h

中文:
引理 Graded.map_mem
  条件: (f : F) {i x} (h : x in 𝒜 i)
  结论: f x in ℬ i
  证明: GradedFunLike.map_mem f h

Depends on / 依赖: GradedFunLike, GradedFunLike.map_mem, map_mem
-/
lemma Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i :=
  GradedFunLike.map_mem f h

/--
Definition of `Graded.subtypeMap` / `Graded.subtypeMap` 的定义

English:
definition Graded.subtypeMap
  signature: (f : F) (i : ι) (x : 𝒜 i)
  body: ⟨f x, map_mem f x.2⟩

中文:
定义 Graded.subtypeMap
  签名: (f : F) (i : ι) (x : 𝒜 i)
  定义体: ⟨f x, map_mem f x.2⟩

Depends on / 依赖: map_mem
-/
def Graded.subtypeMap (f : F) (i : ι) (x : 𝒜 i) : ℬ i :=
  ⟨f x, map_mem f x.2⟩

end GradedFunLike

/--
Definition of `GradedEquivLike` / `GradedEquivLike` 的定义

English:
class GradedEquivLike
  parameters: (E : Type*) {A B σ τ ι : outParam Type*}
  axioms and operations (1):
    - map_mem_iff((e : E) {i x}) : e x in ℬ i ↔ x in 𝒜 i

中文:
类 GradedEquivLike
  参数: (E : 类型) {A B σ τ ι : outParam 类型}
  公理与运算 (1 个):
    - map_mem_iff((e : E) {i x}) : e x in ℬ i ↔ x in 𝒜 i
-/
class GradedEquivLike (E : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι -> σ) (ℬ : outParam <| ι -> τ)
    [EquivLike E A B] where
  map_mem_iff (e : E) {i x} : e x in ℬ i ↔ x in 𝒜 i

section GradedEquivLike

variable (E : Type*) {A B σ τ ι : Type*} [SetLike σ A] [SetLike τ B]
  (𝒜 : ι -> σ) (ℬ : ι -> τ) [EquivLike E A B] [GradedEquivLike E 𝒜 ℬ]

instance (priority := 100) GradedEquivLike.toGradedFunLike : GradedFunLike E 𝒜 ℬ where
  __ := (inferInstance : FunLike E A B)
  map_mem e := (map_mem_iff e).mpr

variable {E 𝒜 ℬ}

/--
lemma `Graded.map_mem_iff` / 引理 `Graded.map_mem_iff`

English:
lemma Graded.map_mem_iff
  given: (e : E) {i x}
  statement: e x in ℬ i ↔ x in 𝒜 i
  proof: GradedEquivLike.map_mem_iff e
alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff

中文:
引理 Graded.map_mem_iff
  条件: (e : E) {i x}
  结论: e x in ℬ i ↔ x in 𝒜 i
  证明: GradedEquivLike.map_mem_iff e
alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff

Depends on / 依赖: Graded, Graded.map_mem_iff, Graded.map_mem_of_mem, Graded.mem_of_map_mem, GradedEquivLike, GradedEquivLike.map_mem_iff, map_mem_iff, map_mem_of_mem, mem_of_map_mem
-/
lemma Graded.map_mem_iff (e : E) {i x} : e x in ℬ i ↔ x in 𝒜 i :=
  GradedEquivLike.map_mem_iff e
alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff

/--
Definition of `Graded.equiv` / `Graded.equiv` 的定义

English:
definition Graded.equiv
  signature: (e : E) (i : ι)
  body: subtypeMap e i
  invFun y := ⟨EquivLike.inv e (y : B),
mem_of_map_mem e by rw [EquivLike.apply_inv_apply]; exact y.2⟩
  left_inv _ := by ext; exact EquivLike.inv_apply_apply e _
  right_inv _ := by ext; exact EquivLike.apply_inv_apply e _

中文:
定义 Graded.equiv
  签名: (e : E) (i : ι)
  定义体: subtypeMap e i
  invFun y := ⟨EquivLike.inv e (y : B),
mem_of_map_mem e by rw [EquivLike.apply_inv_apply]; exact y.2⟩
  left_inv _ := by ext; exact EquivLike.inv_apply_apply e _
  right_inv _ := by ext; exact EquivLike.apply_inv_apply e _
-/
@[simps] def Graded.equiv (e : E) (i : ι) : 𝒜 i ≃ ℬ i where
  toFun := subtypeMap e i
  invFun y := ⟨EquivLike.inv e (y : B),
mem_of_map_mem e by rw [EquivLike.apply_inv_apply]; exact y.2⟩
  left_inv _ := by ext; exact EquivLike.inv_apply_apply e _
  right_inv _ := by ext; exact EquivLike.apply_inv_apply e _

end GradedEquivLike
