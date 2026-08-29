/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Bases.Finite

/-!
# Convergence of intervals

## Motivation

If a function tends to infinity somewhere, then its derivative is not integrable around this place.
One should be careful about this statement: "somewhere" could mean a point, but also convergence
from the left or from the right, or it could also be infinity, and "around this place" will refer
to these directed neighborhoods. Therefore, the above theorem has many variants. Instead of stating
all these variants, one can look for the common abstraction and have a single version. One has to
be careful: if one considers convergence along a sequence, then the function may tend to infinity
but have a derivative which is small along the sequence (with big jumps in between), so in the end
the derivative may be integrable on a neighborhood of the sequence. What really matters for such
calculus issues in terms of derivatives is that whole intervals are included in the sets we
consider.

The right common abstraction is provided in this file, as the `TendstoIxxClass` typeclass.
It takes as parameters a class of bounded intervals and two real filters `l₁` and `l₂`.
An instance `TendstoIxxClass Icc l₁ l₂` registers that, if `aₙ` and `bₙ` are converging towards
the filter `l₁`, then the intervals `Icc aₙ bₙ` are eventually contained in any given set
belonging to `l₂`. For instance, for `l₁ = 𝓝[>] x` and `l₂ = 𝓝[≥] x`, the strict and large right
neighborhoods of `x` respectively, then given any large right neighborhood `s ∈ 𝓝[≥] x` and any two
sequences `xₙ` and `yₙ` converging strictly to the right of `x`,
then the interval `[xₙ, yₙ]` is eventually contained in `s`. Therefore, the instance
`TendstoIxxClass Icc (𝓝[>] x) (𝓝[≥] x)` holds. Note that one could have taken as
well `l₂ = 𝓝[>] x`, but that `l₁ = 𝓝[≥] x` and `l₂ = 𝓝[>] x` wouldn't work.

With this formalism, the above theorem would read: if `TendstoIxxClass Icc l l` and `f` tends
to infinity along `l`, then its derivative is not integrable on any element of `l`.
Beyond this simple example, this typeclass plays a prominent role in generic formulations of
the fundamental theorem of calculus.

## Main definition

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.smallSets`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`. Here and below
`Ixx` is one of `Set.Icc`, `Set.Ico`, `Set.Ioc`, and `Set.Ioo`.
We define `Filter.TendstoIxxClass Ixx l₁ l₂` to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove
`Filter.TendstoIxxClass Set.Ico (𝓟 (Set.Iic a)) (𝓟 (Set.Iio a))`, i.e., if `u₁ n` and `u₂ n` belong
eventually to `Set.Iic a`, then the interval `Set.Ico (u₁ n) (u₂ n)` is eventually included in
`Set.Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `Mathlib/Topology/Algebra/Ordered`.

| Input filter | `Ixx = Set.Icc` | `Ixx = Set.Ico` | `Ixx = Set.Ioc` | `Ixx = Set.Ioo` |
|-----------------:|:----------------:|:----------------:|:----------------:|:----------------:|
| `Filter.atTop` | `Filter.atTop` | `Filter.atTop` | `Filter.atTop` | `Filter.atTop` |
| `Filter.atBot` | `Filter.atBot` | `Filter.atBot` | `Filter.atBot` | `Filter.atBot` |
| `pure a` | `pure a` | `⊥` | `⊥` | `⊥` |
| `𝓟 (Set.Iic a)` | `𝓟 (Set.Iic a)` | `𝓟 (Set.Iio a)` | `𝓟 (Set.Iic a)` | `𝓟 (Set.Iio a)` |
| `𝓟 (Set.Ici a)` | `𝓟 (Set.Ici a)` | `𝓟 (Set.Ici a)` | `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)` |
| `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)` |
| `𝓟 (Set.Iio a)` | `𝓟 (Set.Iio a)` | `𝓟 (Set.Iio a)` | `𝓟 (Set.Iio a)` | `𝓟 (Set.Iio a)` |
| `𝓝 a` | `𝓝 a` | `𝓝 a` | `𝓝 a` | `𝓝 a` |
| `𝓝[Set.Iic a] b` | `𝓝[Set.Iic a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iic a] b` | `𝓝[Set.Iio a] b` |
| `𝓝[Set.Ici a] b` | `𝓝[Set.Ici a] b` | `𝓝[Set.Ici a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` |
| `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` |
| `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` |

-/

public section


variable {α β : Type*}

open Filter Set Function

namespace Filter

section Preorder

/--
Definition of `TendstoIxxClass` / `TendstoIxxClass` 的定义

English:
class TendstoIxxClass
  parameters: (Ixx : α -> α -> Set α) (l₁ : Filter α) (l₂ : outParam <| Filter α)
  axioms and operations (1):
    - tendsto_Ixx : Tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ˢ l₁) l₂.smallSets

中文:
类 TendstoIxx类
  参数: (Ixx : α -> α -> 集合 α) (l₁ : 滤子 α) (l₂ : outParam <| 滤子 α)
  公理与运算 (1 个):
    - tendsto_Ixx : 收敛 (fun p : α × α => Ixx p.1 p.2) (l₁ ×ˢ l₁) l₂.smallSets
-/
class TendstoIxxClass (Ixx : α -> α -> Set α) (l₁ : Filter α) (l₂ : outParam <| Filter α) : Prop where
  /-- `Function.uncurry Ixx` tends to `l₂.smallSets` along `l₁ ×ˢ l₁`. In other words, for any
  `s ∈ l₂` there exists `t ∈ l₁` such that `Ixx x y ⊆ s` whenever `x ∈ t` and `y ∈ t`.

  Use lemmas like `Filter.Tendsto.Icc` instead. -/
  tendsto_Ixx : Tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ˢ l₁) l₂.smallSets

/--
theorem `tendstoIxxClass_principal` / 定理 `tendstoIxxClass_principal`

English:
theorem tendstoIxxClass_principal
  given: {s t : Set α} {Ixx : α -> α -> Set α}
  proof: Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ by
    simp only [smallSets_principal, prod_principal_principal, tendsto_principal_principal,
      forall_prod_set, mem_powerset_iff]

中文:
定理 tendstoIxxClass_principal
  条件: {s t : 集合 α} {Ixx : α -> α -> 集合 α}
  证明: Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ by
    simp only [smallSets_principal, prod_principal_principal, tendsto_principal_principal,
      forall_prod_set, mem_powerset_iff]

Depends on / 依赖: Iff.trans, forall_prod_set, mem_powerset_iff, prod_principal_principal, smallSets_principal, tendsto_principal_principal
-/
theorem tendstoIxxClass_principal {s t : Set α} {Ixx : α -> α -> Set α} :
    TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (y in s), Ixx x y subseteq t :=
Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ by
    simp only [smallSets_principal, prod_principal_principal, tendsto_principal_principal,
      forall_prod_set, mem_powerset_iff]

/--
theorem `tendstoIxxClass_inf` / 定理 `tendstoIxxClass_inf`

English:
theorem tendstoIxxClass_inf
  statement: {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass Ixx l₁ l₂]
  proof: ⟨by simpa only [prod_inf_prod, smallSets_inf] using h.1.inf h'.1⟩

中文:
定理 tendstoIxxClass_inf
  结论: {l₁ l₁' l₂ l₂' : 滤子 α} {Ixx} [h : TendstoIxx类 Ixx l₁ l₂]
  证明: ⟨by simpa only [prod_inf_prod, smallSets_inf] using h.1.inf h'.1⟩

Depends on / 依赖: prod_inf_prod, smallSets_inf
-/
theorem tendstoIxxClass_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass Ixx l₁ l₂]
    [h' : TendstoIxxClass Ixx l₁' l₂'] : TendstoIxxClass Ixx (l₁ ⊓ l₁') (l₂ ⊓ l₂') :=
  ⟨by simpa only [prod_inf_prod, smallSets_inf] using h.1.inf h'.1⟩

/--
theorem `tendstoIxxClass_of_subset` / 定理 `tendstoIxxClass_of_subset`

English:
theorem tendstoIxxClass_of_subset
  statement: {l₁ l₂ : Filter α} {Ixx Ixx' : α -> α -> Set α}
  proof: ⟨h'.1.smallSets_mono Eventually.of_forall Prod.forall.2 h⟩

中文:
定理 tendstoIxxClass_of_subset
  结论: {l₁ l₂ : 滤子 α} {Ixx Ixx' : α -> α -> 集合 α}
  证明: ⟨h'.1.smallSets_mono Eventually.of_forall Prod.forall.2 h⟩

Depends on / 依赖: Eventually, Eventually.of_forall, Prod.forall, of_forall, smallSets_mono
-/
theorem tendstoIxxClass_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α -> α -> Set α}
    (h : forall a b, Ixx a b subseteq Ixx' a b) [h' : TendstoIxxClass Ixx' l₁ l₂] : TendstoIxxClass Ixx l₁ l₂ :=
⟨h'.1.smallSets_mono Eventually.of_forall Prod.forall.2 h⟩

/--
theorem `HasBasis.tendstoIxxClass` / 定理 `HasBasis.tendstoIxxClass`

English:
theorem HasBasis.tendstoIxxClass
  statement: {ι : Type*} {p : ι -> Prop} {s} {l : Filter α}
  proof: ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun _ h => H i hi _ h.1 _ h.2⟩⟩

中文:
定理 有基.tendstoIxxClass
  结论: {ι : 类型} {p : ι -> 命题} {s} {l : 滤子 α}
  证明: ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun _ h => H i hi _ h.1 _ h.2⟩⟩

Depends on / 依赖: hl.prod_self.tendsto_iff, hl.smallSets, prod_self, smallSets, tendsto_iff
-/
theorem HasBasis.tendstoIxxClass {ι : Type*} {p : ι -> Prop} {s} {l : Filter α}
    (hl : l.HasBasis p s) {Ixx : α -> α -> Set α}
    (H : forall i, p i -> forall x in s i, forall y in s i, Ixx x y subseteq s i) : TendstoIxxClass Ixx l l :=
  ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun _ h => H i hi _ h.1 _ h.2⟩⟩

variable [Preorder α]

/--
theorem `Tendsto.Icc` / 定理 `Tendsto.Icc`

English:
theorem Tendsto.Icc
  statement: {l₁ l₂ : Filter α} [TendstoIxxClass Icc l₁ l₂] {lb : Filter β}
  proof: (@TendstoIxxClass.tendsto_Ixx α Set.Icc _ _ _).comp h₁.prodMk h₂

中文:
定理 收敛.闭区间
  结论: {l₁ l₂ : 滤子 α} [TendstoIxx类 闭区间 l₁ l₂] {lb : 滤子 β}
  证明: (@TendstoIxxClass.tendsto_Ixx α Set.Icc _ _ _).comp h₁.prodMk h₂
-/
protected theorem Tendsto.Icc {l₁ l₂ : Filter α} [TendstoIxxClass Icc l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β -> α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Icc (u₁ x) (u₂ x)) lb l₂.smallSets :=
(@TendstoIxxClass.tendsto_Ixx α Set.Icc _ _ _).comp h₁.prodMk h₂

/--
theorem `Tendsto.Ioc` / 定理 `Tendsto.Ioc`

English:
theorem Tendsto.Ioc
  statement: {l₁ l₂ : Filter α} [TendstoIxxClass Ioc l₁ l₂] {lb : Filter β}
  proof: (@TendstoIxxClass.tendsto_Ixx α Set.Ioc _ _ _).comp h₁.prodMk h₂

中文:
定理 收敛.左开右闭区间
  结论: {l₁ l₂ : 滤子 α} [TendstoIxx类 左开右闭区间 l₁ l₂] {lb : 滤子 β}
  证明: (@TendstoIxxClass.tendsto_Ixx α Set.Ioc _ _ _).comp h₁.prodMk h₂
-/
protected theorem Tendsto.Ioc {l₁ l₂ : Filter α} [TendstoIxxClass Ioc l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β -> α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioc (u₁ x) (u₂ x)) lb l₂.smallSets :=
(@TendstoIxxClass.tendsto_Ixx α Set.Ioc _ _ _).comp h₁.prodMk h₂

/--
theorem `Tendsto.Ico` / 定理 `Tendsto.Ico`

English:
theorem Tendsto.Ico
  statement: {l₁ l₂ : Filter α} [TendstoIxxClass Ico l₁ l₂] {lb : Filter β}
  proof: (@TendstoIxxClass.tendsto_Ixx α Set.Ico _ _ _).comp h₁.prodMk h₂

中文:
定理 收敛.左闭右开区间
  结论: {l₁ l₂ : 滤子 α} [TendstoIxx类 左闭右开区间 l₁ l₂] {lb : 滤子 β}
  证明: (@TendstoIxxClass.tendsto_Ixx α Set.Ico _ _ _).comp h₁.prodMk h₂
-/
protected theorem Tendsto.Ico {l₁ l₂ : Filter α} [TendstoIxxClass Ico l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β -> α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ico (u₁ x) (u₂ x)) lb l₂.smallSets :=
(@TendstoIxxClass.tendsto_Ixx α Set.Ico _ _ _).comp h₁.prodMk h₂

/--
theorem `Tendsto.Ioo` / 定理 `Tendsto.Ioo`

English:
theorem Tendsto.Ioo
  statement: {l₁ l₂ : Filter α} [TendstoIxxClass Ioo l₁ l₂] {lb : Filter β}
  proof: (@TendstoIxxClass.tendsto_Ixx α Set.Ioo _ _ _).comp h₁.prodMk h₂

中文:
定理 收敛.开区间
  结论: {l₁ l₂ : 滤子 α} [TendstoIxx类 开区间 l₁ l₂] {lb : 滤子 β}
  证明: (@TendstoIxxClass.tendsto_Ixx α Set.Ioo _ _ _).comp h₁.prodMk h₂
-/
protected theorem Tendsto.Ioo {l₁ l₂ : Filter α} [TendstoIxxClass Ioo l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β -> α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioo (u₁ x) (u₂ x)) lb l₂.smallSets :=
(@TendstoIxxClass.tendsto_Ixx α Set.Ioo _ _ _).comp h₁.prodMk h₂


/--
Instance `tendsto_Icc_atTop_atTop` / 实例 `tendsto_Icc_atTop_atTop`

English:
instance tendsto_Icc_atTop_atTop
  signature: : TendstoIxxClass Icc (atTop : Filter α) atTop
  body: (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
Set.OrdConnected.out ordConnected_biInter fun _ _ => ordConnected_Ici

中文:
实例 tendsto_Icc_atTop_atTop
  签名: : TendstoIxx类 闭区间 (atTop : 滤子 α) atTop
  定义体: (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
Set.OrdConnected.out ordConnected_biInter fun _ _ => ordConnected_Ici

Depends on / 依赖: OrdConnected, Set.OrdConnected.out, hasBasis_iInf_principal_finite, ordConnected_Ici, ordConnected_biInter, tendstoIxxClass
-/
instance tendsto_Icc_atTop_atTop : TendstoIxxClass Icc (atTop : Filter α) atTop :=
  (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
Set.OrdConnected.out ordConnected_biInter fun _ _ => ordConnected_Ici

/--
Instance `tendsto_Ico_atTop_atTop` / 实例 `tendsto_Ico_atTop_atTop`

English:
instance tendsto_Ico_atTop_atTop
  signature: : TendstoIxxClass Ico (atTop : Filter α) atTop
  body: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

中文:
实例 tendsto_Ico_atTop_atTop
  签名: : TendstoIxx类 左闭右开区间 (atTop : 滤子 α) atTop
  定义体: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ico_atTop_atTop : TendstoIxxClass Ico (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

/--
Instance `tendsto_Ioc_atTop_atTop` / 实例 `tendsto_Ioc_atTop_atTop`

English:
instance tendsto_Ioc_atTop_atTop
  signature: : TendstoIxxClass Ioc (atTop : Filter α) atTop
  body: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

中文:
实例 tendsto_Ioc_atTop_atTop
  签名: : TendstoIxx类 左开右闭区间 (atTop : 滤子 α) atTop
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioc_atTop_atTop : TendstoIxxClass Ioc (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

/--
Instance `tendsto_Ioo_atTop_atTop` / 实例 `tendsto_Ioo_atTop_atTop`

English:
instance tendsto_Ioo_atTop_atTop
  signature: : TendstoIxxClass Ioo (atTop : Filter α) atTop
  body: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

中文:
实例 tendsto_Ioo_atTop_atTop
  签名: : TendstoIxx类 开区间 (atTop : 滤子 α) atTop
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

Depends on / 依赖: Ioo_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioo_atTop_atTop : TendstoIxxClass Ioo (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

/--
Instance `tendsto_Icc_atBot_atBot` / 实例 `tendsto_Icc_atBot_atBot`

English:
instance tendsto_Icc_atBot_atBot
  signature: : TendstoIxxClass Icc (atBot : Filter α) atBot
  body: (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
Set.OrdConnected.out ordConnected_biInter fun _ _ => ordConnected_Iic

中文:
实例 tendsto_Icc_atBot_atBot
  签名: : TendstoIxx类 闭区间 (atBot : 滤子 α) atBot
  定义体: (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
Set.OrdConnected.out ordConnected_biInter fun _ _ => ordConnected_Iic

Depends on / 依赖: OrdConnected, Set.OrdConnected.out, hasBasis_iInf_principal_finite, ordConnected_Iic, ordConnected_biInter, tendstoIxxClass
-/
instance tendsto_Icc_atBot_atBot : TendstoIxxClass Icc (atBot : Filter α) atBot :=
  (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
Set.OrdConnected.out ordConnected_biInter fun _ _ => ordConnected_Iic

/--
Instance `tendsto_Ico_atBot_atBot` / 实例 `tendsto_Ico_atBot_atBot`

English:
instance tendsto_Ico_atBot_atBot
  signature: : TendstoIxxClass Ico (atBot : Filter α) atBot
  body: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

中文:
实例 tendsto_Ico_atBot_atBot
  签名: : TendstoIxx类 左闭右开区间 (atBot : 滤子 α) atBot
  定义体: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ico_atBot_atBot : TendstoIxxClass Ico (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

/--
Instance `tendsto_Ioc_atBot_atBot` / 实例 `tendsto_Ioc_atBot_atBot`

English:
instance tendsto_Ioc_atBot_atBot
  signature: : TendstoIxxClass Ioc (atBot : Filter α) atBot
  body: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

中文:
实例 tendsto_Ioc_atBot_atBot
  签名: : TendstoIxx类 左开右闭区间 (atBot : 滤子 α) atBot
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioc_atBot_atBot : TendstoIxxClass Ioc (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

/--
Instance `tendsto_Ioo_atBot_atBot` / 实例 `tendsto_Ioo_atBot_atBot`

English:
instance tendsto_Ioo_atBot_atBot
  signature: : TendstoIxxClass Ioo (atBot : Filter α) atBot
  body: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

中文:
实例 tendsto_Ioo_atBot_atBot
  签名: : TendstoIxx类 开区间 (atBot : 滤子 α) atBot
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

Depends on / 依赖: Ioo_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioo_atBot_atBot : TendstoIxxClass Ioo (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

/--
Instance `OrdConnected.tendsto_Icc` / 实例 `OrdConnected.tendsto_Icc`

English:
instance OrdConnected.tendsto_Icc
  signature: {s : Set α} [hs : OrdConnected s]
  body: tendstoIxxClass_principal.2 hs.out

中文:
实例 序连通.tendsto_Icc
  签名: {s : 集合 α} [hs : 序连通 s]
  定义体: tendstoIxxClass_principal.2 hs.out

Depends on / 依赖: hs.out, tendstoIxxClass_principal
-/
instance OrdConnected.tendsto_Icc {s : Set α} [hs : OrdConnected s] :
    TendstoIxxClass Icc (𝓟 s) (𝓟 s) :=
  tendstoIxxClass_principal.2 hs.out

/--
Instance `tendsto_Ico_Ici_Ici` / 实例 `tendsto_Ico_Ici_Ici`

English:
instance tendsto_Ico_Ici_Ici
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

中文:
实例 tendsto_Ico_Ici_Ici
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ico_Ici_Ici {a : α} : TendstoIxxClass Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

/--
Instance `tendsto_Ico_Ioi_Ioi` / 实例 `tendsto_Ico_Ioi_Ioi`

English:
instance tendsto_Ico_Ioi_Ioi
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

中文:
实例 tendsto_Ico_Ioi_Ioi
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ico_Ioi_Ioi {a : α} : TendstoIxxClass Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

/--
Instance `tendsto_Ico_Iic_Iio` / 实例 `tendsto_Ico_Iic_Iio`

English:
instance tendsto_Ico_Iic_Iio
  signature: {a : α}
  body: tendstoIxxClass_principal.2 fun _ _ _ h₁ _ h₂ => lt_of_lt_of_le h₂.2 h₁

中文:
实例 tendsto_Ico_Iic_Iio
  签名: {a : α}
  定义体: tendstoIxxClass_principal.2 fun _ _ _ h₁ _ h₂ => lt_of_lt_of_le h₂.2 h₁

Depends on / 依赖: lt_of_lt_of_le, tendstoIxxClass_principal
-/
instance tendsto_Ico_Iic_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_principal.2 fun _ _ _ h₁ _ h₂ => lt_of_lt_of_le h₂.2 h₁

/--
Instance `tendsto_Ico_Iio_Iio` / 实例 `tendsto_Ico_Iio_Iio`

English:
instance tendsto_Ico_Iio_Iio
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

中文:
实例 tendsto_Ico_Iio_Iio
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ico_Iio_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

/--
Instance `tendsto_Ioc_Ici_Ioi` / 实例 `tendsto_Ioc_Ici_Ioi`

English:
instance tendsto_Ioc_Ici_Ioi
  signature: {a : α}
  body: tendstoIxxClass_principal.2 fun _ h₁ _ _ _ h₂ => lt_of_le_of_lt h₁ h₂.1

中文:
实例 tendsto_Ioc_Ici_Ioi
  签名: {a : α}
  定义体: tendstoIxxClass_principal.2 fun _ h₁ _ _ _ h₂ => lt_of_le_of_lt h₁ h₂.1

Depends on / 依赖: lt_of_le_of_lt, tendstoIxxClass_principal
-/
instance tendsto_Ioc_Ici_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_principal.2 fun _ h₁ _ _ _ h₂ => lt_of_le_of_lt h₁ h₂.1

/--
Instance `tendsto_Ioc_Iic_Iic` / 实例 `tendsto_Ioc_Iic_Iic`

English:
instance tendsto_Ioc_Iic_Iic
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

中文:
实例 tendsto_Ioc_Iic_Iic
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioc_Iic_Iic {a : α} : TendstoIxxClass Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

/--
Instance `tendsto_Ioc_Iio_Iio` / 实例 `tendsto_Ioc_Iio_Iio`

English:
instance tendsto_Ioc_Iio_Iio
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

中文:
实例 tendsto_Ioc_Iio_Iio
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioc_Iio_Iio {a : α} : TendstoIxxClass Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

/--
Instance `tendsto_Ioc_Ioi_Ioi` / 实例 `tendsto_Ioc_Ioi_Ioi`

English:
instance tendsto_Ioc_Ioi_Ioi
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

中文:
实例 tendsto_Ioc_Ioi_Ioi
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioc_Ioi_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

/--
Instance `tendsto_Ioo_Ici_Ioi` / 实例 `tendsto_Ioo_Ici_Ioi`

English:
instance tendsto_Ioo_Ici_Ioi
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

中文:
实例 tendsto_Ioo_Ici_Ioi
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

Depends on / 依赖: Ioo_subset_Ioc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioo_Ici_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

/--
Instance `tendsto_Ioo_Iic_Iio` / 实例 `tendsto_Ioo_Iic_Iio`

English:
instance tendsto_Ioo_Iic_Iio
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ico_self

中文:
实例 tendsto_Ioo_Iic_Iio
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ico_self

Depends on / 依赖: Ioo_subset_Ico_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioo_Iic_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ico_self

/--
Instance `tendsto_Ioo_Ioi_Ioi` / 实例 `tendsto_Ioo_Ioi_Ioi`

English:
instance tendsto_Ioo_Ioi_Ioi
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

中文:
实例 tendsto_Ioo_Ioi_Ioi
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

Depends on / 依赖: Ioo_subset_Ioc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioo_Ioi_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

/--
Instance `tendsto_Ioo_Iio_Iio` / 实例 `tendsto_Ioo_Iio_Iio`

English:
instance tendsto_Ioo_Iio_Iio
  signature: {a : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

中文:
实例 tendsto_Ioo_Iio_Iio
  签名: {a : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

Depends on / 依赖: Ioo_subset_Ioc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioo_Iio_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

/--
Instance `tendsto_Icc_Icc_Icc` / 实例 `tendsto_Icc_Icc_Icc`

English:
instance tendsto_Icc_Icc_Icc
  signature: {a b : α}
  body: tendstoIxxClass_principal.mpr fun _x hx _y hy => Icc_subset_Icc hx.1 hy.2

中文:
实例 tendsto_Icc_Icc_Icc
  签名: {a b : α}
  定义体: tendstoIxxClass_principal.mpr fun _x hx _y hy => Icc_subset_Icc hx.1 hy.2

Depends on / 依赖: Icc_subset_Icc, tendstoIxxClass_principal, tendstoIxxClass_principal.mpr
-/
instance tendsto_Icc_Icc_Icc {a b : α} : TendstoIxxClass Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_principal.mpr fun _x hx _y hy => Icc_subset_Icc hx.1 hy.2

/--
Instance `tendsto_Ioc_Icc_Icc` / 实例 `tendsto_Ioc_Icc_Icc`

English:
instance tendsto_Ioc_Icc_Icc
  signature: {a b : α}
  body: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

中文:
实例 tendsto_Ioc_Icc_Icc
  签名: {a b : α}
  定义体: tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, tendstoIxxClass_of_subset
-/
instance tendsto_Ioc_Icc_Icc {a b : α} : TendstoIxxClass Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

end Preorder

section PartialOrder

variable [PartialOrder α]

/--
Instance `tendsto_Icc_pure_pure` / 实例 `tendsto_Icc_pure_pure`

English:
instance tendsto_Icc_pure_pure
  signature: {a : α}
  body: by
  rw [← principal_singleton]
  exact tendstoIxxClass_principal.2 ordConnected_singleton.out

中文:
实例 tendsto_Icc_pure_pure
  签名: {a : α}
  定义体: by
  rw [← principal_singleton]
  exact tendstoIxxClass_principal.2 ordConnected_singleton.out

Depends on / 依赖: ordConnected_singleton, ordConnected_singleton.out, principal_singleton, tendstoIxxClass_principal
-/
instance tendsto_Icc_pure_pure {a : α} : TendstoIxxClass Icc (pure a) (pure a : Filter α) := by
  rw [← principal_singleton]
  exact tendstoIxxClass_principal.2 ordConnected_singleton.out

/--
Instance `tendsto_Ico_pure_bot` / 实例 `tendsto_Ico_pure_bot`

English:
instance tendsto_Ico_pure_bot
  signature: {a : α}
  body: ⟨by simp⟩

中文:
实例 tendsto_Ico_pure_bot
  签名: {a : α}
  定义体: ⟨by simp⟩
-/
instance tendsto_Ico_pure_bot {a : α} : TendstoIxxClass Ico (pure a) ⊥ :=
  ⟨by simp⟩

/--
Instance `tendsto_Ioc_pure_bot` / 实例 `tendsto_Ioc_pure_bot`

English:
instance tendsto_Ioc_pure_bot
  signature: {a : α}
  body: ⟨by simp⟩

中文:
实例 tendsto_Ioc_pure_bot
  签名: {a : α}
  定义体: ⟨by simp⟩
-/
instance tendsto_Ioc_pure_bot {a : α} : TendstoIxxClass Ioc (pure a) ⊥ :=
  ⟨by simp⟩

/--
Instance `tendsto_Ioo_pure_bot` / 实例 `tendsto_Ioo_pure_bot`

English:
instance tendsto_Ioo_pure_bot
  signature: {a : α}
  body: ⟨by simp⟩

中文:
实例 tendsto_Ioo_pure_bot
  签名: {a : α}
  定义体: ⟨by simp⟩
-/
instance tendsto_Ioo_pure_bot {a : α} : TendstoIxxClass Ioo (pure a) ⊥ :=
  ⟨by simp⟩

end PartialOrder

section LinearOrder

open Interval

variable [LinearOrder α]

/--
Instance `tendsto_Icc_uIcc_uIcc` / 实例 `tendsto_Icc_uIcc_uIcc`

English:
instance tendsto_Icc_uIcc_uIcc
  signature: {a b : α}
  body: Filter.tendsto_Icc_Icc_Icc

中文:
实例 tendsto_Icc_uIcc_uIcc
  签名: {a b : α}
  定义体: Filter.tendsto_Icc_Icc_Icc

Depends on / 依赖: Filter, Filter.tendsto_Icc_Icc_Icc, tendsto_Icc_Icc_Icc
-/
instance tendsto_Icc_uIcc_uIcc {a b : α} : TendstoIxxClass Icc (𝓟 [[a, b]]) (𝓟 [[a, b]]) :=
  Filter.tendsto_Icc_Icc_Icc

/--
Instance `tendsto_Ioc_uIcc_uIcc` / 实例 `tendsto_Ioc_uIcc_uIcc`

English:
instance tendsto_Ioc_uIcc_uIcc
  signature: {a b : α}
  body: Filter.tendsto_Ioc_Icc_Icc

中文:
实例 tendsto_Ioc_uIcc_uIcc
  签名: {a b : α}
  定义体: Filter.tendsto_Ioc_Icc_Icc

Depends on / 依赖: Filter, Filter.tendsto_Ioc_Icc_Icc, tendsto_Ioc_Icc_Icc
-/
instance tendsto_Ioc_uIcc_uIcc {a b : α} : TendstoIxxClass Ioc (𝓟 [[a, b]]) (𝓟 [[a, b]]) :=
  Filter.tendsto_Ioc_Icc_Icc

/--
Instance `tendsto_uIcc_of_Icc` / 实例 `tendsto_uIcc_of_Icc`

English:
instance tendsto_uIcc_of_Icc
  signature: {l : Filter α} [TendstoIxxClass Icc l l]
  body: by
refine ⟨fun s hs => mem_map.2 mem_prod_self_iff.2 ?_⟩
  obtain ⟨t, htl, hts⟩ : exists t in l, forall p in (t : Set α) ×ˢ t, Icc (p : α × α).1 p.2 in s :=
    mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine ⟨t, htl, fun p hp => ?_⟩
  rcases le_total p.1 p.2 with h | h
  · rw [mem_preimage, uIcc_of_le h]
    exact hts p hp
  · rw [mem_preimage, uIcc_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩

中文:
实例 tendsto_uIcc_of_Icc
  签名: {l : 滤子 α} [TendstoIxx类 闭区间 l l]
  定义体: by
refine ⟨fun s hs => mem_map.2 mem_prod_self_iff.2 ?_⟩
  obtain ⟨t, htl, hts⟩ : exists t in l, forall p in (t : Set α) ×ˢ t, Icc (p : α × α).1 p.2 in s :=
    mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine ⟨t, htl, fun p hp => ?_⟩
  rcases le_total p.1 p.2 with h | h
  · rw [mem_preimage, uIcc_of_le h]
    exact hts p hp
  · rw [mem_preimage, uIcc_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩

Depends on / 依赖: le_total, mem_map, mem_preimage, mem_prod_self_iff, tendsto_fst, tendsto_fst.Icc, tendsto_snd, uIcc_of_ge, uIcc_of_le
-/
instance tendsto_uIcc_of_Icc {l : Filter α} [TendstoIxxClass Icc l l] :
    TendstoIxxClass uIcc l l := by
refine ⟨fun s hs => mem_map.2 mem_prod_self_iff.2 ?_⟩
  obtain ⟨t, htl, hts⟩ : exists t in l, forall p in (t : Set α) ×ˢ t, Icc (p : α × α).1 p.2 in s :=
    mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine ⟨t, htl, fun p hp => ?_⟩
  rcases le_total p.1 p.2 with h | h
  · rw [mem_preimage, uIcc_of_le h]
    exact hts p hp
  · rw [mem_preimage, uIcc_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩

/--
theorem `Tendsto.uIcc` / 定理 `Tendsto.uIcc`

English:
theorem Tendsto.uIcc
  statement: {l : Filter α} [TendstoIxxClass Icc l l] {f g : β -> α}
  proof: (@TendstoIxxClass.tendsto_Ixx α Set.uIcc _ _ _).comp hf.prodMk hg

中文:
定理 收敛.uIcc
  结论: {l : 滤子 α} [TendstoIxx类 闭区间 l l] {f g : β -> α}
  证明: (@TendstoIxxClass.tendsto_Ixx α Set.uIcc _ _ _).comp hf.prodMk hg
-/
protected theorem Tendsto.uIcc {l : Filter α} [TendstoIxxClass Icc l l] {f g : β -> α}
    {lb : Filter β} (hf : Tendsto f lb l) (hg : Tendsto g lb l) :
    Tendsto (fun x => [[f x, g x]]) lb l.smallSets :=
(@TendstoIxxClass.tendsto_Ixx α Set.uIcc _ _ _).comp hf.prodMk hg

end LinearOrder

end Filter
