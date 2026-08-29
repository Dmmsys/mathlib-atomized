/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# Finiteness and infiniteness of the `DFinsupp` type

## Main results

* `DFinsupp.fintype`: if the domain and codomain are finite, then `DFinsupp` is finite
* `DFinsupp.infinite_of_left`: if the domain is infinite, then `DFinsupp` is infinite
* `DFinsupp.infinite_of_exists_right`: if one fiber of the codomain is infinite,
  then `DFinsupp` is infinite
-/

public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

section FiniteInfinite

/--
Instance `DFinsupp.fintype` / 实例 `DFinsupp.fintype`

English:
instance DFinsupp.fintype
  signature: {ι : Sort _} {π : ι -> Sort _} [DecidableEq ι] [forall i, Zero (π i)]
  body: Fintype.ofEquiv (forall i, π i) DFinsupp.equivFunOnFintype.symm

中文:
实例 直和有限支撑.fintype
  签名: {ι : 类型层 _} {π : ι -> 类型层 _} [DecidableEq ι] [对任意 i, 零 (π i)]
  定义体: Fintype.ofEquiv (forall i, π i) DFinsupp.equivFunOnFintype.symm

Depends on / 依赖: DFinsupp, DFinsupp.equivFunOnFintype.symm, Fintype, Fintype.ofEquiv, equivFunOnFintype, ofEquiv
-/
instance DFinsupp.fintype {ι : Sort _} {π : ι -> Sort _} [DecidableEq ι] [forall i, Zero (π i)]
    [Fintype ι] [forall i, Fintype (π i)] : Fintype (Π₀ i, π i) :=
  Fintype.ofEquiv (forall i, π i) DFinsupp.equivFunOnFintype.symm

/--
Instance `DFinsupp.infinite_of_left` / 实例 `DFinsupp.infinite_of_left`

English:
instance DFinsupp.infinite_of_left
  signature: {ι : Sort _} {π : ι -> Sort _} [forall i, Nontrivial (π i)]
  body: by
  let := Classical.decEq ι; choose m hm using fun i => exists_ne (0 : π i)
  exact Infinite.of_injective _ (DFinsupp.single_left_injective hm)

中文:
实例 直和有限支撑.infinite_of_left
  签名: {ι : 类型层 _} {π : ι -> 类型层 _} [对任意 i, 非平凡 (π i)]
  定义体: by
  let := Classical.decEq ι; choose m hm using fun i => exists_ne (0 : π i)
  exact Infinite.of_injective _ (DFinsupp.single_left_injective hm)

Depends on / 依赖: Classical, Classical.decEq, DFinsupp, DFinsupp.single_left_injective, Infinite, Infinite.of_injective, exists_ne, of_injective, single_left_injective
-/
instance DFinsupp.infinite_of_left {ι : Sort _} {π : ι -> Sort _} [forall i, Nontrivial (π i)]
    [forall i, Zero (π i)] [Infinite ι] : Infinite (Π₀ i, π i) := by
  let := Classical.decEq ι; choose m hm using fun i => exists_ne (0 : π i)
  exact Infinite.of_injective _ (DFinsupp.single_left_injective hm)

/--
theorem `DFinsupp.infinite_of_exists_right` / 定理 `DFinsupp.infinite_of_exists_right`

English:
theorem DFinsupp.infinite_of_exists_right
  statement: {ι : Sort _} {π : ι -> Sort _} (i : ι) [Infinite (π i)]
  proof: letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective

中文:
定理 直和有限支撑.infinite_of_存在_right
  结论: {ι : 类型层 _} {π : ι -> 类型层 _} (i : ι) [无限 (π i)]
  证明: letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective

Depends on / 依赖: Classical, Classical.decEq, DFinsupp, DFinsupp.single, DFinsupp.single_injective, Infinite, Infinite.of_injective, of_injective, single, single_injective
-/
theorem DFinsupp.infinite_of_exists_right {ι : Sort _} {π : ι -> Sort _} (i : ι) [Infinite (π i)]
    [forall i, Zero (π i)] : Infinite (Π₀ i, π i) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective

/--
Instance `DFinsupp.infinite_of_right` / 实例 `DFinsupp.infinite_of_right`

English:
instance DFinsupp.infinite_of_right
  signature: {ι : Sort _} {π : ι -> Sort _} [forall i, Infinite (π i)]
  body: DFinsupp.infinite_of_exists_right (Classical.arbitrary ι)

中文:
实例 直和有限支撑.infinite_of_right
  签名: {ι : 类型层 _} {π : ι -> 类型层 _} [对任意 i, 无限 (π i)]
  定义体: DFinsupp.infinite_of_exists_right (Classical.arbitrary ι)

Depends on / 依赖: Classical, Classical.arbitrary, DFinsupp, DFinsupp.infinite_of_exists_right, arbitrary, infinite_of_exists_right
-/
instance DFinsupp.infinite_of_right {ι : Sort _} {π : ι -> Sort _} [forall i, Infinite (π i)]
    [forall i, Zero (π i)] [Nonempty ι] : Infinite (Π₀ i, π i) :=
  DFinsupp.infinite_of_exists_right (Classical.arbitrary ι)

end FiniteInfinite
