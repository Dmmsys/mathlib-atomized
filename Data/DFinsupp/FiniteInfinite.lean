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

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

section FiniteInfinite

/-
**DFinsupp.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.fintype {ι : Sort _} {π : ι -> Sort _} [DecidableEq ι] [forall i,
 Zero (π i)] [Fintype ι] [forall i, Fintype (π i)] : Fintype (Π₀ i, π i)
参数：π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance DFinsupp.fintype {ι : Sort _} {π : ι → Sort _} [DecidableEq ι] [∀ i, Zero (π i)]
    [Fintype ι] [∀ i, Fintype (π i)] : Fintype (Π₀ i, π i) :=
  Fintype.ofEquiv (∀ i, π i) DFinsupp.equivFunOnFintype.symm
/-
**DFinsupp.infinite_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.infinite_of_left {ι : Sort _} {π : ι -> Sort _} [forall i, Nontri
vial (π i)] [forall i, Zero (π i)] [Infinite ι] : Infinite (Π₀ i, π i)
参数：π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `DFinsupp.single_left_injective`：single_left_injective {b : forall i : ι,
 β i} (h : forall i, b i != 0) : Function.Injective (fun i => single i (b i) : ι
 -> Π₀ i, β i)
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance DFinsupp.infinite_of_left {ι : Sort _} {π : ι → Sort _} [∀ i, Nontrivial (π i)]
    [∀ i, Zero (π i)] [Infinite ι] : Infinite (Π₀ i, π i) := by
  let := Classical.decEq ι; choose m hm using fun i => exists_ne (0 : π i)
  exact Infinite.of_injective _ (DFinsupp.single_left_injective hm)

/-- See `DFinsupp.infinite_of_right` for this in instance form, with the drawback that
it needs all `π i` to be infinite. -/
/-
**DFinsupp.infinite_of_exists_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFinsupp.infinite_of_exists_right {ι : Sort _} {π : ι -> Sort _} (i : ι) [
Infinite (π i)] [forall i, Zero (π i)] : Infinite (Π₀ i, π i)
参数：i : ι；π i；π i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `DFinsupp.single_injective`：single_injective {i} : Function.Injective (si
ngle i : β i -> Π₀ i, β i)

--- 原说明 ---
See `DFinsupp.infinite_of_right` for this in instance form, with the drawback th
at
it needs all `π i` to be infinite.
-/
theorem DFinsupp.infinite_of_exists_right {ι : Sort _} {π : ι → Sort _} (i : ι) [Infinite (π i)]
    [∀ i, Zero (π i)] : Infinite (Π₀ i, π i) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective

/-- See `DFinsupp.infinite_of_exists_right` for the case that only one `π ι` is infinite. -/
/-
**DFinsupp.infinite_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.infinite_of_right {ι : Sort _} {π : ι -> Sort _} [forall i, Infin
ite (π i)] [forall i, Zero (π i)] [Nonempty ι] : Infinite (Π₀ i, π i)
参数：π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.infinite_of_exists_right`：DFinsupp.infinite_of_exists_right {ι 
: Sort _} {π : ι -> Sort _} (i : ι) [Infinite (π i)] [forall i, Zero (π i)] : In
finite (Π₀ i, π i)

--- 原说明 ---
See `DFinsupp.infinite_of_exists_right` for the case that only one `π ι` is infi
nite.
-/
instance DFinsupp.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite (π i)]
    [∀ i, Zero (π i)] [Nonempty ι] : Infinite (Π₀ i, π i) :=
  DFinsupp.infinite_of_exists_right (Classical.arbitrary ι)

end FiniteInfinite

