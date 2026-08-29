/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Stably free modules

## Main definition
* `IsStablyFree`: A module `M` over a ring `R` is called stably free if there exists a finite free
  `R`-module `N` such that `M ⊕ N` is free.
-/

public section

universe u v w

namespace Module

/-- A module `M` over a ring `R` is called stably free if there exists a finite free `R`-module `N`
such that `M ⊕ N` is free.

The underlying constructor is marked as private. The intended constructor of `IsStablyFree` is
`IsStablyFree.of_free_prod`, and use `IsStablyFree.exist_free_prod` to extract the property from
`IsStablyFree`. -/
@[stacks 0BC3 "(2)"]
/--
Definition of `IsStablyFree` / `IsStablyFree` 的定义

English:
class IsStablyFree
  parameters: (R : Type u) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]
  axioms and operations (1):
    - private(exist_free_prod') : exists (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.Finite R N) (_ : Free R N), Free R (M × N)

中文:
类 是StablyFree
  参数: (R : 类型u) [环 R] (M : 类型) [加法交换群 M] [模 R M]
  公理与运算 (1 个):
    - private(exist_free_prod') : 存在 (N : 类型u) (_ : 加法交换群 N) (_ : 模 R N) (_ : 模.有限 R N) (_ : 自由 R N), 自由 R (M × N)
-/
class IsStablyFree (R : Type u) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] : Prop where
  private exist_free_prod' : exists (N : Type u) (_ : AddCommGroup N) (_ : Module R N)
    (_ : Module.Finite R N) (_ : Free R N), Free R (M × N)

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/--
theorem `IsStablyFree.exist_free_prod` / 定理 `IsStablyFree.exist_free_prod`

English:
theorem IsStablyFree.exist_free_prod
  given: [IsStablyFree R M]
  proof: IsStablyFree.exist_free_prod'

中文:
定理 是StablyFree.exist_free_prod
  条件: [是StablyFree R M]
  证明: IsStablyFree.exist_free_prod'

Depends on / 依赖: IsStablyFree, IsStablyFree.exist_free_prod, exist_free_prod
-/
theorem IsStablyFree.exist_free_prod [IsStablyFree R M] :
    exists (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.Finite R N) (_ : Free R N),
      Free R (M × N) :=
  IsStablyFree.exist_free_prod'

variable {R M N} in
/--
theorem `IsStablyFree.equiv` / 定理 `IsStablyFree.equiv`

English:
theorem IsStablyFree.equiv
  given: (e : M ≃ₗ[R] N) [IsStablyFree R M]
  statement: IsStablyFree R N
  proof: by
  obtain ⟨P, hPc, hPm, hPfin, hPfree, _⟩ := IsStablyFree.exist_free_prod R M
  exact ⟨P, hPc, hPm, hPfin, hPfree, Free.of_equiv (e.prodCongr (LinearEquiv.refl R P))⟩

中文:
定理 是StablyFree.equiv
  条件: (e : M ≃ₗ[R] N) [是StablyFree R M]
  结论: 是StablyFree R N
  证明: by
  obtain ⟨P, hPc, hPm, hPfin, hPfree, _⟩ := IsStablyFree.exist_free_prod R M
  exact ⟨P, hPc, hPm, hPfin, hPfree, Free.of_equiv (e.prodCongr (LinearEquiv.refl R P))⟩

Depends on / 依赖: Free.of_equiv, IsStablyFree, IsStablyFree.exist_free_prod, LinearEquiv, LinearEquiv.refl, e.prodCongr, exist_free_prod, hPfree, of_equiv, prodCongr
-/
theorem IsStablyFree.equiv (e : M ≃ₗ[R] N) [IsStablyFree R M] : IsStablyFree R N := by
  obtain ⟨P, hPc, hPm, hPfin, hPfree, _⟩ := IsStablyFree.exist_free_prod R M
  exact ⟨P, hPc, hPm, hPfin, hPfree, Free.of_equiv (e.prodCongr (LinearEquiv.refl R P))⟩

variable {R M N} in
/--
theorem `IsStablyFree.equiv_iff` / 定理 `IsStablyFree.equiv_iff`

English:
theorem IsStablyFree.equiv_iff
  given: (e : M ≃ₗ[R] N)
  statement: IsStablyFree R M ↔ IsStablyFree R N
  proof: ⟨fun h => h.equiv e, fun h => h.equiv e.symm⟩

中文:
定理 是StablyFree.equiv_iff
  条件: (e : M ≃ₗ[R] N)
  结论: 是StablyFree R M ↔ 是StablyFree R N
  证明: ⟨fun h => h.equiv e, fun h => h.equiv e.symm⟩

Depends on / 依赖: e.symm, h.equiv
-/
theorem IsStablyFree.equiv_iff (e : M ≃ₗ[R] N) : IsStablyFree R M ↔ IsStablyFree R N :=
  ⟨fun h => h.equiv e, fun h => h.equiv e.symm⟩

/--
Instance `IsStablyFree.ulift` / 实例 `IsStablyFree.ulift`

English:
instance IsStablyFree.ulift
  signature: [IsStablyFree R M]
  body: IsStablyFree.equiv ULift.moduleEquiv.symm

中文:
实例 是StablyFree.ulift
  签名: [是StablyFree R M]
  定义体: IsStablyFree.equiv ULift.moduleEquiv.symm

Depends on / 依赖: IsStablyFree, IsStablyFree.equiv, ULift.moduleEquiv.symm, moduleEquiv
-/
instance IsStablyFree.ulift [IsStablyFree R M] : IsStablyFree R (ULift.{w} M) :=
  IsStablyFree.equiv ULift.moduleEquiv.symm

/--
theorem `IsStablyFree.of_ulift` / 定理 `IsStablyFree.of_ulift`

English:
theorem IsStablyFree.of_ulift
  given: [IsStablyFree R (ULift.{w} M)]
  statement: IsStablyFree R M
  proof: IsStablyFree.equiv ULift.moduleEquiv

中文:
定理 是StablyFree.of_ulift
  条件: [是StablyFree R (类型层提升.{w} M)]
  结论: 是StablyFree R M
  证明: IsStablyFree.equiv ULift.moduleEquiv

Depends on / 依赖: IsStablyFree, IsStablyFree.equiv, ULift.moduleEquiv, moduleEquiv
-/
theorem IsStablyFree.of_ulift [IsStablyFree R (ULift.{w} M)] : IsStablyFree R M :=
  IsStablyFree.equiv ULift.moduleEquiv

/--
Instance `IsStablyFree.shrink` / 实例 `IsStablyFree.shrink`

English:
instance IsStablyFree.shrink
  signature: [Small.{w, v} M] [IsStablyFree R M]
  body: IsStablyFree.equiv (Shrink.linearEquiv R M).symm

中文:
实例 是StablyFree.shrink
  签名: [Small.{w, v} M] [是StablyFree R M]
  定义体: IsStablyFree.equiv (Shrink.linearEquiv R M).symm

Depends on / 依赖: IsStablyFree, IsStablyFree.equiv, Shrink, Shrink.linearEquiv, linearEquiv
-/
instance IsStablyFree.shrink [Small.{w, v} M] [IsStablyFree R M] : IsStablyFree R (Shrink.{w} M) :=
  IsStablyFree.equiv (Shrink.linearEquiv R M).symm

/--
theorem `IsStablyFree.of_shrink` / 定理 `IsStablyFree.of_shrink`

English:
theorem IsStablyFree.of_shrink
  given: [Small.{w, v} M] [IsStablyFree R (Shrink.{w} M)]
  proof: IsStablyFree.equiv (Shrink.linearEquiv R M)

中文:
定理 是StablyFree.of_shrink
  条件: [Small.{w, v} M] [是StablyFree R (Shrink.{w} M)]
  证明: IsStablyFree.equiv (Shrink.linearEquiv R M)

Depends on / 依赖: IsStablyFree, IsStablyFree.equiv, Shrink, Shrink.linearEquiv, linearEquiv
-/
theorem IsStablyFree.of_shrink [Small.{w, v} M] [IsStablyFree R (Shrink.{w} M)] :
    IsStablyFree R M :=
  IsStablyFree.equiv (Shrink.linearEquiv R M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Free
  signature: R M] : IsStablyFree R M
  body: ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

中文:
实例 [自由
  签名: R M] : 是StablyFree R M
  定义体: ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
-/
instance [Free R M] : IsStablyFree R M :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/--
theorem `IsStablyFree.of_free_prod` / 定理 `IsStablyFree.of_free_prod`

English:
theorem IsStablyFree.of_free_prod
  given: [Module.Finite R N] [Free R N] [Free R (M × N)]
  proof: have : Small.{u} N := Module.Finite.small.{u} R N
  let +nondep eN : N ≃ₗ[R] Shrink.{u} N := (Shrink.linearEquiv R N).symm
  ⟨Shrink.{u} N, inferInstance, inferInstance, Module.Finite.equiv eN,
    Free.of_equiv eN, Free.of_equiv ((LinearEquiv.refl R M).prodCongr eN)⟩

中文:
定理 是StablyFree.of_free_prod
  条件: [模.有限 R N] [自由 R N] [自由 R (M × N)]
  证明: have : Small.{u} N := Module.Finite.small.{u} R N
  let +nondep eN : N ≃ₗ[R] Shrink.{u} N := (Shrink.linearEquiv R N).symm
  ⟨Shrink.{u} N, inferInstance, inferInstance, Module.Finite.equiv eN,
    Free.of_equiv eN, Free.of_equiv ((LinearEquiv.refl R M).prodCongr eN)⟩

Depends on / 依赖: Finite, Free.of_equiv, LinearEquiv, LinearEquiv.refl, Module, Module.Finite.equiv, Module.Finite.small, Shrink, Shrink.linearEquiv, linearEquiv, nondep, of_equiv, prodCongr
-/
theorem IsStablyFree.of_free_prod [Module.Finite R N] [Free R N] [Free R (M × N)] :
    IsStablyFree R M :=
  have : Small.{u} N := Module.Finite.small.{u} R N
  let +nondep eN : N ≃ₗ[R] Shrink.{u} N := (Shrink.linearEquiv R N).symm
  ⟨Shrink.{u} N, inferInstance, inferInstance, Module.Finite.equiv eN,
    Free.of_equiv eN, Free.of_equiv ((LinearEquiv.refl R M).prodCongr eN)⟩

/--
theorem `IsStablyFree.of_free_prod'` / 定理 `IsStablyFree.of_free_prod'`

English:
theorem IsStablyFree.of_free_prod'
  given: [Module.Finite R N] [Free R N] [Free R (N × M)]
  proof: have : Free R (M × N) := Free.of_equiv (LinearEquiv.prodComm R N M)
  .of_free_prod R M N

中文:
定理 是StablyFree.of_free_prod'
  条件: [模.有限 R N] [自由 R N] [自由 R (N × M)]
  证明: have : Free R (M × N) := Free.of_equiv (LinearEquiv.prodComm R N M)
  .of_free_prod R M N

Depends on / 依赖: Free.of_equiv, LinearEquiv, LinearEquiv.prodComm, of_equiv, of_free_prod, prodComm
-/
theorem IsStablyFree.of_free_prod' [Module.Finite R N] [Free R N] [Free R (N × M)] :
    IsStablyFree R M :=
  have : Free R (M × N) := Free.of_equiv (LinearEquiv.prodComm R N M)
  .of_free_prod R M N

instance (priority := low) [IsStablyFree R M] : Projective R M := by
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  exact Projective.of_split (LinearMap.inl R M N) (LinearMap.fst R M N) (LinearMap.ext fun _ => rfl)

end Module
