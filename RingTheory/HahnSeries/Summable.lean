/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Summable families of Hahn Series

We introduce a notion of formal summability for families of Hahn series, and define a formal sum
function. This theory is applied to characterize invertible Hahn series whose coefficients are in a
commutative domain.

## Main Definitions
* `HahnSeries.SummableFamily` is a family of Hahn series such that the union of the supports
  is partially well-ordered and only finitely many are nonzero at any given coefficient. Note that
  this is different from `Summable` in the valuation topology, because there are topologically
  summable families that do not satisfy the axioms of `HahnSeries.SummableFamily`, and formally
  summable families whose sums do not converge topologically.
* `HahnSeries.SummableFamily.hsum` is the formal sum of a summable family.
* `HahnSeries.SummableFamily.lsum` is the formal sum bundled as a `LinearMap`.
* `HahnSeries.SummableFamily.smul` is the summable family given by pointwise scalar multiplication
  of component Hahn series.
* `HahnSeries.SummableFamily.mul` is the summable family given by pointwise multiplication.
* `HahnSeries.SummableFamily.powers` is the summable family given by non-negative powers of a
  Hahn series, if the series has strictly positive order. If the series has non-positive order, then
  the summable family takes the junk value of zero.

## Main results
* `HahnSeries.isUnit_iff`: If `R` is a commutative domain, and `Γ` is a linearly ordered additive
  commutative group, then a Hahn series is a unit if and only if its leading term is a unit in `R`.
* `HahnSeries.SummableFamily.hsum_smul`: `smul` is compatible with `hsum`.
* `HahnSeries.SummableFamily.hsum_mul`: `mul` is compatible with `hsum`. That is, the product of
  sums is equal to the sum of pointwise products.

## TODO
* Summable Pi families

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

open scoped Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

namespace HahnSeries

section

/--
Definition of `SummableFamily` / `SummableFamily` 的定义

English:
structure SummableFamily
  parameters: (Γ R) [PartialOrder Γ] [AddCommMonoid R] (α : Type*)
  axioms and operations (3):
    - toFun : α -> R⟦Γ⟧
    - isPWO_iUnion_support' : Set.IsPWO (⋃ a : α, (toFun a).support)
    - finite_co_support' : forall g : Γ, { a | (toFun a).coeff g != 0 }.Finite

中文:
结构 SummableFamily
  参数: (Γ R) [偏序 Γ] [加法交换幺半群 R] (α : 类型)
  公理与运算 (3 个):
    - toFun : α -> R⟦Γ⟧
    - isPWO_iUnion_support' : 集合.IsPWO (⋃ a : α, (toFun a).support)
    - finite_co_support' : 对任意 g : Γ, { a | (toFun a).coeff g != 0 }.有限
-/
structure SummableFamily (Γ R) [PartialOrder Γ] [AddCommMonoid R] (α : Type*) where
  /-- A parametrized family of Hahn series. -/
  toFun : α -> R⟦Γ⟧
  isPWO_iUnion_support' : Set.IsPWO (⋃ a : α, (toFun a).support)
  finite_co_support' : forall g : Γ, { a | (toFun a).coeff g != 0 }.Finite

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (SummableFamily Γ R α) α R⟦Γ⟧
  body: toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

@[simp]

中文:
实例 :
  签名: 函数状 (SummableFamily Γ R α) α R⟦Γ⟧
  定义体: toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

@[simp]

Depends on / 依赖: max_comm
-/
instance : FunLike (SummableFamily Γ R α) α R⟦Γ⟧ where
  coe := toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (toFun : α -> R⟦Γ⟧) (h1 h2)
  proof: rfl

中文:
定理 coe_mk
  条件: (toFun : α -> R⟦Γ⟧) (h1 h2)
  证明: rfl
-/
theorem coe_mk (toFun : α -> R⟦Γ⟧) (h1 h2) :
    (⟨toFun, h1, h2⟩ : SummableFamily Γ R α) = toFun :=
  rfl

/--
theorem `isPWO_iUnion_support` / 定理 `isPWO_iUnion_support`

English:
theorem isPWO_iUnion_support
  given: (s : SummableFamily Γ R α)
  statement: Set.IsPWO (⋃ a : α, (s a).support)
  proof: s.isPWO_iUnion_support'

中文:
定理 isPWO_iUnion_support
  条件: (s : SummableFamily Γ R α)
  结论: 集合.IsPWO (⋃ a : α, (s a).support)
  证明: s.isPWO_iUnion_support'

Depends on / 依赖: isPWO_iUnion_support, max_comm, s.isPWO_iUnion_support
-/
theorem isPWO_iUnion_support (s : SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support) :=
  s.isPWO_iUnion_support'

/--
theorem `finite_co_support` / 定理 `finite_co_support`

English:
theorem finite_co_support
  given: (s : SummableFamily Γ R α) (g : Γ)
  proof: s.finite_co_support' g

中文:
定理 finite_co_support
  条件: (s : SummableFamily Γ R α) (g : Γ)
  证明: s.finite_co_support' g

Depends on / 依赖: finite_co_support, s.finite_co_support
-/
theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (fun a => (s a).coeff g).HasFiniteSupport :=
  s.finite_co_support' g

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (SummableFamily Γ R α) (α -> R⟦Γ⟧) (⇑)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  结论: @函数.单射 (SummableFamily Γ R α) (α -> R⟦Γ⟧) (⇑)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α -> R⟦Γ⟧) (⇑) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : SummableFamily Γ R α} (h : forall a : α, s a = t a)
  statement: s = t
  proof: DFunLike.ext s t h

中文:
定理 ext
  条件: {s t : SummableFamily Γ R α} (h : 对任意 a : α, s a = t a)
  结论: s = t
  证明: DFunLike.ext s t h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {s t : SummableFamily Γ R α} (h : forall a : α, s a = t a) : s = t :=
  DFunLike.ext s t h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (SummableFamily Γ R α)
  body: ⟨fun x y =>
    { toFun := x + y
      isPWO_iUnion_support' :=
        (x.isPWO_iUnion_support.union y.isPWO_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset ..)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g != 0 at ha
            rw [Set.mem_union]; rw [Function.mem_support]; rw [Function.mem_support]
            contrapose! ha
            rw [ha.1]; rw [ha.2]; rw [add_zero]) }⟩

中文:
实例 :
  签名: 加法 (SummableFamily Γ R α)
  定义体: ⟨fun x y =>
    { toFun := x + y
      isPWO_iUnion_support' :=
        (x.isPWO_iUnion_support.union y.isPWO_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset ..)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g != 0 at ha
            rw [Set.mem_union]; rw [Function.mem_support]; rw [Function.mem_support]
            contrapose! ha
            rw [ha.1]; rw [ha.2]; rw [add_zero]) }⟩

Depends on / 依赖: Function, Function.mem_support, Set.iUnion_mono, Set.iUnion_union_distrib, Set.mem_union, add_zero, contrapose, finite_co_support, iUnion_mono, iUnion_union_distrib, isPWO_iUnion_support, mem_support, mem_union, subset, support_add_subset, x.finite_co_support, x.isPWO_iUnion_support.union, y.finite_co_support, y.isPWO_iUnion_support
-/
instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y
      isPWO_iUnion_support' :=
        (x.isPWO_iUnion_support.union y.isPWO_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset ..)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g != 0 at ha
            rw [Set.mem_union]; rw [Function.mem_support]; rw [Function.mem_support]
            contrapose! ha
            rw [ha.1]; rw [ha.2]; rw [add_zero]) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (SummableFamily Γ R α)
  body: ⟨⟨0, by simp, by simp⟩⟩

中文:
实例 :
  签名: 零 (SummableFamily Γ R α)
  定义体: ⟨⟨0, by simp, by simp⟩⟩
-/
instance : Zero (SummableFamily Γ R α) :=
  ⟨⟨0, by simp, by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SummableFamily Γ R α)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 (SummableFamily Γ R α)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (SummableFamily Γ R α) :=
  ⟨0⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (s t : SummableFamily Γ R α)
  statement: ⇑(s + t) = s + t
  proof: rfl

中文:
定理 coe_add
  条件: (s t : SummableFamily Γ R α)
  结论: ⇑(s + t) = s + t
  证明: rfl
-/
theorem coe_add (s t : SummableFamily Γ R α) : ⇑(s + t) = s + t :=
  rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: {s t : SummableFamily Γ R α} {a : α}
  statement: (s + t) a = s a + t a
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: {s t : SummableFamily Γ R α} {a : α}
  结论: (s + t) a = s a + t a
  证明: rfl

@[simp]
-/
theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
  rfl

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : SummableFamily Γ R α) : α -> R⟦Γ⟧) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : SummableFamily Γ R α) : α -> R⟦Γ⟧) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : SummableFamily Γ R α) : α -> R⟦Γ⟧) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: {a : α}
  statement: (0 : SummableFamily Γ R α) a = 0
  proof: rfl

中文:
定理 zero_apply
  条件: {a : α}
  结论: (0 : SummableFamily Γ R α) a = 0
  证明: rfl
-/
theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
  rfl


section SMul

variable {M} [SMulZeroClass M R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul M (SummableFamily Γ R β)
  body: ⟨fun r t =>
    { toFun := r • t
      isPWO_iUnion_support' := t.isPWO_iUnion_support.mono (Set.iUnion_mono fun i =>
        Pi.smul_apply r t i ▸ Function.support_const_smul_subset r _)
      finite_co_support' := by
        intro g
        refine (t.finite_co_support g).subset ?_
        intro i hi
        simp only [Pi.smul_apply, coeff_smul, ne_eq, Set.mem_ofPred_eq] at hi
        simp only [Function.mem_support, ne_eq]
        exact right_ne_zero_of_smul hi } ⟩

@[simp]

中文:
实例 :
  签名: 标量乘法 M (SummableFamily Γ R β)
  定义体: ⟨fun r t =>
    { toFun := r • t
      isPWO_iUnion_support' := t.isPWO_iUnion_support.mono (Set.iUnion_mono fun i =>
        Pi.smul_apply r t i ▸ Function.support_const_smul_subset r _)
      finite_co_support' := by
        intro g
        refine (t.finite_co_support g).subset ?_
        intro i hi
        simp only [Pi.smul_apply, coeff_smul, ne_eq, Set.mem_ofPred_eq] at hi
        simp only [Function.mem_support, ne_eq]
        exact right_ne_zero_of_smul hi } ⟩

@[simp]

Depends on / 依赖: Function, Function.mem_support, Function.support_const_smul_subset, Pi.smul_apply, Set.iUnion_mono, Set.mem_ofPred_eq, coeff_smul, finite_co_support, iUnion_mono, isPWO_iUnion_support, mem_ofPred_eq, mem_support, ne_eq, right_ne_zero_of_smul, smul_apply, subset, support_const_smul_subset, t.finite_co_support, t.isPWO_iUnion_support.mono
-/
instance : SMul M (SummableFamily Γ R β) :=
  ⟨fun r t =>
    { toFun := r • t
      isPWO_iUnion_support' := t.isPWO_iUnion_support.mono (Set.iUnion_mono fun i =>
        Pi.smul_apply r t i ▸ Function.support_const_smul_subset r _)
      finite_co_support' := by
        intro g
        refine (t.finite_co_support g).subset ?_
        intro i hi
        simp only [Pi.smul_apply, coeff_smul, ne_eq, Set.mem_ofPred_eq] at hi
        simp only [Function.mem_support, ne_eq]
        exact right_ne_zero_of_smul hi } ⟩

@[simp]
/--
theorem `coe_smul'` / 定理 `coe_smul'`

English:
theorem coe_smul'
  given: (m : M) (s : SummableFamily Γ R α)
  statement: ⇑(m • s) = m • s
  proof: rfl

中文:
定理 coe_smul'
  条件: (m : M) (s : SummableFamily Γ R α)
  结论: ⇑(m • s) = m • s
  证明: rfl
-/
theorem coe_smul' (m : M) (s : SummableFamily Γ R α) : ⇑(m • s) = m • s :=
  rfl

/--
theorem `smul_apply'` / 定理 `smul_apply'`

English:
theorem smul_apply'
  given: (m : M) (s : SummableFamily Γ R α) (a : α)
  statement: (m • s) a = m • s a
  proof: rfl

中文:
定理 smul_apply'
  条件: (m : M) (s : SummableFamily Γ R α) (a : α)
  结论: (m • s) a = m • s a
  证明: rfl
-/
theorem smul_apply' (m : M) (s : SummableFamily Γ R α) (a : α) : (m • s) a = m • s a :=
  rfl

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (SummableFamily Γ R α)
  body: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add (fun _ _ => coe_smul' _ _)

中文:
实例 :
  签名: 加法交换幺半群 (SummableFamily Γ R α)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add (fun _ _ => coe_smul' _ _)

Depends on / 依赖: fast_instance
-/
instance : AddCommMonoid (SummableFamily Γ R α) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add (fun _ _ => coe_smul' _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient function of a summable family, as a finsupp on the parameter type. -/
@[simps]
/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (s : SummableFamily Γ R α) (g : Γ)
  body: (s.finite_co_support g).toFinset
  toFun a := (s a).coeff g
  mem_support_toFun a := by simp

@[simp]

中文:
定义 coeff
  签名: (s : SummableFamily Γ R α) (g : Γ)
  定义体: (s.finite_co_support g).toFinset
  toFun a := (s a).coeff g
  mem_support_toFun a := by simp

@[simp]

Depends on / 依赖: finite_co_support, s.finite_co_support, toFinset
-/
def coeff (s : SummableFamily Γ R α) (g : Γ) : α ->₀ R where
  support := (s.finite_co_support g).toFinset
  toFun a := (s a).coeff g
  mem_support_toFun a := by simp

@[simp]
/--
theorem `coeff_def` / 定理 `coeff_def`

English:
theorem coeff_def
  given: (s : SummableFamily Γ R α) (a : α) (g : Γ)
  statement: s.coeff g a = (s a).coeff g
  proof: rfl

中文:
定理 coeff_def
  条件: (s : SummableFamily Γ R α) (a : α) (g : Γ)
  结论: s.coeff g a = (s a).coeff g
  证明: rfl
-/
theorem coeff_def (s : SummableFamily Γ R α) (a : α) (g : Γ) : s.coeff g a = (s a).coeff g :=
  rfl

/--
Definition of `hsum` / `hsum` 的定义

English:
definition hsum
  signature: (s : SummableFamily Γ R α)
  body: ∑ᶠ i, (s i).coeff g
  isPWO_support' :=
    s.isPWO_iUnion_support.mono fun g => by
      contrapose
      rw [Set.mem_iUnion]; rw [not_exists]; rw [Function.mem_support]; rw [Classical.not_not]
      simp_rw [mem_support, Classical.not_not]
      intro h
      rw [finsum_congr h]; rw [finsum_zero]

@[simp]

中文:
定义 hsum
  签名: (s : SummableFamily Γ R α)
  定义体: ∑ᶠ i, (s i).coeff g
  isPWO_support' :=
    s.isPWO_iUnion_support.mono fun g => by
      contrapose
      rw [Set.mem_iUnion]; rw [not_exists]; rw [Function.mem_support]; rw [Classical.not_not]
      simp_rw [mem_support, Classical.not_not]
      intro h
      rw [finsum_congr h]; rw [finsum_zero]

@[simp]
-/
def hsum (s : SummableFamily Γ R α) : R⟦Γ⟧ where
  coeff g := ∑ᶠ i, (s i).coeff g
  isPWO_support' :=
    s.isPWO_iUnion_support.mono fun g => by
      contrapose
      rw [Set.mem_iUnion]; rw [not_exists]; rw [Function.mem_support]; rw [Classical.not_not]
      simp_rw [mem_support, Classical.not_not]
      intro h
      rw [finsum_congr h]; rw [finsum_zero]

@[simp]
/--
theorem `coeff_hsum` / 定理 `coeff_hsum`

English:
theorem coeff_hsum
  given: {s : SummableFamily Γ R α} {g : Γ}
  statement: s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
  proof: rfl

@[simp]

中文:
定理 coeff_hsum
  条件: {s : SummableFamily Γ R α} {g : Γ}
  结论: s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
  证明: rfl

@[simp]
-/
theorem coeff_hsum {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl

@[simp]
/--
theorem `hsum_zero` / 定理 `hsum_zero`

English:
theorem hsum_zero
  statement: (0 : SummableFamily Γ R α).hsum = 0
  proof: by
  ext
  simp

中文:
定理 hsum_zero
  结论: (0 : SummableFamily Γ R α).hsum = 0
  证明: by
  ext
  simp
-/
theorem hsum_zero : (0 : SummableFamily Γ R α).hsum = 0 := by
  ext
  simp

/--
theorem `support_hsum_subset` / 定理 `support_hsum_subset`

English:
theorem support_hsum_subset
  given: {s : SummableFamily Γ R α}
  statement: s.hsum.support subseteq ⋃ a : α, (s a).support
  proof: fun g hg => by
  rw [mem_support]; rw [coeff_hsum]; rw [finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩

@[simp]

中文:
定理 support_hsum_subset
  条件: {s : SummableFamily Γ R α}
  结论: s.hsum.support subseteq ⋃ a : α, (s a).support
  证明: fun g hg => by
  rw [mem_support]; rw [coeff_hsum]; rw [finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩

@[simp]

Depends on / 依赖: Set.mem_iUnion, coeff_hsum, exists_ne_zero_of_sum_ne_zero, finite_co_support, finsum_eq_sum, mem_iUnion, mem_support, s.finite_co_support
-/
theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support subseteq ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support]; rw [coeff_hsum]; rw [finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩

@[simp]
/--
theorem `hsum_add` / 定理 `hsum_add`

English:
theorem hsum_add
  given: {s t : SummableFamily Γ R α}
  statement: (s + t).hsum = s.hsum + t.hsum
  proof: by
  ext g
  simp only [coeff_hsum, coeff_add, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

中文:
定理 hsum_add
  条件: {s t : SummableFamily Γ R α}
  结论: (s + t).hsum = s.hsum + t.hsum
  证明: by
  ext g
  simp only [coeff_hsum, coeff_add, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

Depends on / 依赖: add_apply, coeff_add, coeff_hsum, finite_co_support, finsum_add_distrib, s.finite_co_support, t.finite_co_support
-/
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [coeff_hsum, coeff_add, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_hsum_eq_sum_of_subset` / 定理 `coeff_hsum_eq_sum_of_subset`

English:
theorem coeff_hsum_eq_sum_of_subset
  statement: {s : SummableFamily Γ R α} {g : Γ} {t : Finset α}
  proof: by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)]
  exact sum_subset (Set.Finite.toFinset_subset.mpr h) (by simp)

中文:
定理 coeff_hsum_eq_sum_of_subset
  结论: {s : SummableFamily Γ R α} {g : Γ} {t : 有限集 α}
  证明: by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)]
  exact sum_subset (Set.Finite.toFinset_subset.mpr h) (by simp)

Depends on / 依赖: Finite, Set.Finite.toFinset_subset.mpr, coeff_hsum, finite_co_support, finsum_eq_sum, s.finite_co_support, sum_subset, toFinset_subset
-/
theorem coeff_hsum_eq_sum_of_subset {s : SummableFamily Γ R α} {g : Γ} {t : Finset α}
    (h : { a | (s a).coeff g != 0 } subseteq t) : s.hsum.coeff g = ∑ i in t, (s i).coeff g := by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)]
  exact sum_subset (Set.Finite.toFinset_subset.mpr h) (by simp)

/--
theorem `coeff_hsum_eq_sum` / 定理 `coeff_hsum_eq_sum`

English:
theorem coeff_hsum_eq_sum
  given: {s : SummableFamily Γ R α} {g : Γ}
  proof: by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _), coeff_support]

中文:
定理 coeff_hsum_eq_sum
  条件: {s : SummableFamily Γ R α} {g : Γ}
  证明: by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _), coeff_support]

Depends on / 依赖: coeff_hsum, coeff_support, finite_co_support, finsum_eq_sum, s.finite_co_support
-/
theorem coeff_hsum_eq_sum {s : SummableFamily Γ R α} {g : Γ} :
    s.hsum.coeff g = ∑ i in (s.coeff g).support, (s i).coeff g := by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _), coeff_support]

/-- The summable family made of a single Hahn series. -/
@[simps]
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧)
  body: Pi.single i x
  isPWO_iUnion_support' := by
    have : (Pi.single (M := fun _ => R⟦Γ⟧) i x i).support.IsPWO := by simp
refine this.mono Set.iUnion_subset fun a => ?_
    obtain rfl | ha := eq_or_ne a i
    · rfl
    · simp [ha]
  finite_co_support' g := (Set.finite_singleton i).subset fun j => by
    obtain rfl | ha := eq_or_ne j i <;> simp [*]

@[simp]

中文:
定义 single
  签名: {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧)
  定义体: Pi.single i x
  isPWO_iUnion_support' := by
    have : (Pi.single (M := fun _ => R⟦Γ⟧) i x i).support.IsPWO := by simp
refine this.mono Set.iUnion_subset fun a => ?_
    obtain rfl | ha := eq_or_ne a i
    · rfl
    · simp [ha]
  finite_co_support' g := (Set.finite_singleton i).subset fun j => by
    obtain rfl | ha := eq_or_ne j i <;> simp [*]

@[simp]

Depends on / 依赖: Pi.single, single
-/
def single {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧) : SummableFamily Γ R ι where
  toFun := Pi.single i x
  isPWO_iUnion_support' := by
    have : (Pi.single (M := fun _ => R⟦Γ⟧) i x i).support.IsPWO := by simp
refine this.mono Set.iUnion_subset fun a => ?_
    obtain rfl | ha := eq_or_ne a i
    · rfl
    · simp [ha]
  finite_co_support' g := (Set.finite_singleton i).subset fun j => by
    obtain rfl | ha := eq_or_ne j i <;> simp [*]

@[simp]
/--
theorem `hsum_single` / 定理 `hsum_single`

English:
theorem hsum_single
  given: {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧)
  statement: (single i x).hsum = x
  proof: by
  ext g
  rw [coeff_hsum]; rw [finsum_eq_single _ i]; rw [single_toFun]; rw [Pi.single_eq_same]
  simp +contextual

中文:
定理 hsum_single
  条件: {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧)
  结论: (single i x).hsum = x
  证明: by
  ext g
  rw [coeff_hsum]; rw [finsum_eq_single _ i]; rw [single_toFun]; rw [Pi.single_eq_same]
  simp +contextual

Depends on / 依赖: Pi.single_eq_same, coeff_hsum, contextual, finsum_eq_single, single_eq_same, single_toFun
-/
theorem hsum_single {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧) : (single i x).hsum = x := by
  ext g
  rw [coeff_hsum]; rw [finsum_eq_single _ i]; rw [single_toFun]; rw [Pi.single_eq_same]
  simp +contextual

/-- The summable family made of a constant Hahn series. -/
@[simps]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (ι) [Finite ι] (x : R⟦Γ⟧)
  body: x
  isPWO_iUnion_support' := by
    cases isEmpty_or_nonempty ι
    · simp
    · exact Eq.mpr (congrArg (fun s => s.IsPWO) (Set.iUnion_const x.support)) x.isPWO_support
  finite_co_support' g := Set.toFinite {a | ((fun _ => x) a).coeff g != 0}

@[simp]

中文:
定义 const
  签名: (ι) [有限 ι] (x : R⟦Γ⟧)
  定义体: x
  isPWO_iUnion_support' := by
    cases isEmpty_or_nonempty ι
    · simp
    · exact Eq.mpr (congrArg (fun s => s.IsPWO) (Set.iUnion_const x.support)) x.isPWO_support
  finite_co_support' g := Set.toFinite {a | ((fun _ => x) a).coeff g != 0}

@[simp]
-/
def const (ι) [Finite ι] (x : R⟦Γ⟧) : SummableFamily Γ R ι where
  toFun _ := x
  isPWO_iUnion_support' := by
    cases isEmpty_or_nonempty ι
    · simp
    · exact Eq.mpr (congrArg (fun s => s.IsPWO) (Set.iUnion_const x.support)) x.isPWO_support
  finite_co_support' g := Set.toFinite {a | ((fun _ => x) a).coeff g != 0}

@[simp]
/--
theorem `hsum_unique` / 定理 `hsum_unique`

English:
theorem hsum_unique
  given: {ι} [Unique ι] (x : SummableFamily Γ R ι)
  statement: x.hsum = x default
  proof: by
  ext g
  simp only [coeff_hsum, finsum_unique]

中文:
定理 hsum_unique
  条件: {ι} [唯一 ι] (x : SummableFamily Γ R ι)
  结论: x.hsum = x default
  证明: by
  ext g
  simp only [coeff_hsum, finsum_unique]

Depends on / 依赖: coeff_hsum, finsum_unique
-/
theorem hsum_unique {ι} [Unique ι] (x : SummableFamily Γ R ι) : x.hsum = x default := by
  ext g
  simp only [coeff_hsum, finsum_unique]

/-- A summable family induced by an equivalence of the parametrizing type. -/
@[simps]
/--
Definition of `Equiv` / `Equiv` 的定义

English:
definition Equiv
  signature: (e : α ≃ β) (s : SummableFamily Γ R α)
  body: s (e.symm b)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g => ?_
    simp only [Set.mem_iUnion, mem_support, ne_eq, forall_exists_index]
    exact fun b hg => Exists.intro (e.symm b) hg
  finite_co_support' g :=
(Equiv.set_finite_iff e.subtypeEquivOfSubtype').mp s.finite_co_support' g

@[simp]

中文:
定义 等价
  签名: (e : α ≃ β) (s : SummableFamily Γ R α)
  定义体: s (e.symm b)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g => ?_
    simp only [Set.mem_iUnion, mem_support, ne_eq, forall_exists_index]
    exact fun b hg => Exists.intro (e.symm b) hg
  finite_co_support' g :=
(Equiv.set_finite_iff e.subtypeEquivOfSubtype').mp s.finite_co_support' g

@[simp]

Depends on / 依赖: e.symm
-/
def Equiv (e : α ≃ β) (s : SummableFamily Γ R α) : SummableFamily Γ R β where
  toFun b := s (e.symm b)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g => ?_
    simp only [Set.mem_iUnion, mem_support, ne_eq, forall_exists_index]
    exact fun b hg => Exists.intro (e.symm b) hg
  finite_co_support' g :=
(Equiv.set_finite_iff e.subtypeEquivOfSubtype').mp s.finite_co_support' g

@[simp]
/--
theorem `hsum_equiv` / 定理 `hsum_equiv`

English:
theorem hsum_equiv
  given: (e : α ≃ β) (s : SummableFamily Γ R α)
  statement: (Equiv e s).hsum = s.hsum
  proof: by
  ext g
  simp only [coeff_hsum, Equiv_toFun]
  exact finsum_eq_of_bijective e.symm (Equiv.bijective e.symm) fun x => rfl

中文:
定理 hsum_equiv
  条件: (e : α ≃ β) (s : SummableFamily Γ R α)
  结论: (等价 e s).hsum = s.hsum
  证明: by
  ext g
  simp only [coeff_hsum, Equiv_toFun]
  exact finsum_eq_of_bijective e.symm (Equiv.bijective e.symm) fun x => rfl

Depends on / 依赖: Equiv.bijective, Equiv_toFun, bijective, coeff_hsum, e.symm, finsum_eq_of_bijective
-/
theorem hsum_equiv (e : α ≃ β) (s : SummableFamily Γ R α) : (Equiv e s).hsum = s.hsum := by
  ext g
  simp only [coeff_hsum, Equiv_toFun]
  exact finsum_eq_of_bijective e.symm (Equiv.bijective e.symm) fun x => rfl

/-- The summable family given by multiplying every series in a summable family by a scalar. -/
@[simps]
/--
Definition of `smulFamily` / `smulFamily` 的定义

English:
definition smulFamily
  signature: [AddCommMonoid V] [SMulWithZero R V] (f : α -> R) (s : SummableFamily Γ V α)
  body: (f a) • s a
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g hg => ?_
    simp_all only [Set.mem_iUnion, mem_support, coeff_smul, ne_eq]
    obtain ⟨i, hi⟩ := hg
exact Exists.intro i right_ne_zero_of_smul hi
  finite_co_support' g := by
    refine Set.Finite.subset (s.finite_co_support g) fun i hi => ?_
    simp_all only [coeff_smul, ne_eq, Set.mem_ofPred_eq, Function.mem_support]
    exact right_ne_zero_of_smul hi

中文:
定义 smulFamily
  签名: [加法交换幺半群 V] [带零标量乘法 R V] (f : α -> R) (s : SummableFamily Γ V α)
  定义体: (f a) • s a
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g hg => ?_
    simp_all only [Set.mem_iUnion, mem_support, coeff_smul, ne_eq]
    obtain ⟨i, hi⟩ := hg
exact Exists.intro i right_ne_zero_of_smul hi
  finite_co_support' g := by
    refine Set.Finite.subset (s.finite_co_support g) fun i hi => ?_
    simp_all only [coeff_smul, ne_eq, Set.mem_ofPred_eq, Function.mem_support]
    exact right_ne_zero_of_smul hi
-/
def smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α -> R) (s : SummableFamily Γ V α) :
    SummableFamily Γ V α where
  toFun a := (f a) • s a
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g hg => ?_
    simp_all only [Set.mem_iUnion, mem_support, coeff_smul, ne_eq]
    obtain ⟨i, hi⟩ := hg
exact Exists.intro i right_ne_zero_of_smul hi
  finite_co_support' g := by
    refine Set.Finite.subset (s.finite_co_support g) fun i hi => ?_
    simp_all only [coeff_smul, ne_eq, Set.mem_ofPred_eq, Function.mem_support]
    exact right_ne_zero_of_smul hi

/--
theorem `hsum_smulFamily` / 定理 `hsum_smulFamily`

English:
theorem hsum_smulFamily
  statement: [AddCommMonoid V] [SMulWithZero R V] (f : α -> R)
  proof: rfl

中文:
定理 hsum_smulFamily
  结论: [加法交换幺半群 V] [带零标量乘法 R V] (f : α -> R)
  证明: rfl
-/
theorem hsum_smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α -> R)
    (s : SummableFamily Γ V α) (g : Γ) :
    (smulFamily f s).hsum.coeff g = ∑ᶠ i, (f i) • ((s i).coeff g) :=
  rfl

/--
theorem `le_hsum_support_mem` / 定理 `le_hsum_support_mem`

English:
theorem le_hsum_support_mem
  statement: {s : SummableFamily Γ R α} {g g' : Γ}
  proof: by
  rw [mem_support]; rw [coeff_hsum_eq_sum] at hg'
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg'
  exact hg i g' hi

中文:
定理 le_hsum_support_mem
  结论: {s : SummableFamily Γ R α} {g g' : Γ}
  证明: by
  rw [mem_support]; rw [coeff_hsum_eq_sum] at hg'
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg'
  exact hg i g' hi

Depends on / 依赖: Finset, Finset.exists_ne_zero_of_sum_ne_zero, coeff_hsum_eq_sum, exists_ne_zero_of_sum_ne_zero, mem_support
-/
theorem le_hsum_support_mem {s : SummableFamily Γ R α} {g g' : Γ}
    (hg : forall b : α, forall g' in (s b).support, g <= g') (hg' : g' in s.hsum.support) : g <= g' := by
  rw [mem_support]; rw [coeff_hsum_eq_sum] at hg'
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg'
  exact hg i g' hi

/--
theorem `hsum_orderTop_of_le` / 定理 `hsum_orderTop_of_le`

English:
theorem hsum_orderTop_of_le
  statement: {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
  proof: orderTop_eq_of_le (ne_of_eq_of_ne (by rw [coeff_hsum, finsum_eq_single (fun i => (s i).coeff g) a
    hna]) (coeff_orderTop_ne ha.symm)) fun _ hg' => le_hsum_support_mem hg hg'

中文:
定理 hsum_orderTop_of_le
  结论: {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
  证明: orderTop_eq_of_le (ne_of_eq_of_ne (by rw [coeff_hsum, finsum_eq_single (fun i => (s i).coeff g) a
    hna]) (coeff_orderTop_ne ha.symm)) fun _ hg' => le_hsum_support_mem hg hg'

Depends on / 依赖: coeff_hsum, coeff_orderTop_ne, finsum_eq_single, ha.symm, le_hsum_support_mem, ne_of_eq_of_ne, orderTop_eq_of_le
-/
theorem hsum_orderTop_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
    (hg : forall b : α, forall g' in (s b).support, g <= g') (hna : forall b : α, b != a -> (s b).coeff g = 0) :
    s.hsum.orderTop = g :=
  orderTop_eq_of_le (ne_of_eq_of_ne (by rw [coeff_hsum, finsum_eq_single (fun i => (s i).coeff g) a
    hna]) (coeff_orderTop_ne ha.symm)) fun _ hg' => le_hsum_support_mem hg hg'

/--
theorem `hsum_leadingCoeff_of_le` / 定理 `hsum_leadingCoeff_of_le`

English:
theorem hsum_leadingCoeff_of_le
  statement: {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
  proof: by
  have := hsum_orderTop_of_le ha hg hna
  rw [orderTop] at this
  have hs : s.hsum != 0 := by
    by_contra h
    simp [h] at this
  simp only [hs, ↓reduceDIte, WithTop.coe_eq_coe] at this
  simp only [leadingCoeff_of_ne_zero hs, coeff_hsum, untop_orderTop_of_ne_zero hs, this]
  rw [finsum_eq_single (fun i => (s i).coeff g) a hna]

中文:
定理 hsum_leadingCoeff_of_le
  结论: {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
  证明: by
  have := hsum_orderTop_of_le ha hg hna
  rw [orderTop] at this
  have hs : s.hsum != 0 := by
    by_contra h
    simp [h] at this
  simp only [hs, ↓reduceDIte, WithTop.coe_eq_coe] at this
  simp only [leadingCoeff_of_ne_zero hs, coeff_hsum, untop_orderTop_of_ne_zero hs, this]
  rw [finsum_eq_single (fun i => (s i).coeff g) a hna]

Depends on / 依赖: WithTop, WithTop.coe_eq_coe, coe_eq_coe, coeff_hsum, finsum_eq_single, hsum_orderTop_of_le, leadingCoeff_of_ne_zero, orderTop, reduceDIte, s.hsum, untop_orderTop_of_ne_zero
-/
theorem hsum_leadingCoeff_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
    (hg : forall b : α, forall g' in (s b).support, g <= g') (hna : forall b : α, b != a -> (s b).coeff g = 0) :
    s.hsum.leadingCoeff = (s a).coeff g := by
  have := hsum_orderTop_of_le ha hg hna
  rw [orderTop] at this
  have hs : s.hsum != 0 := by
    by_contra h
    simp [h] at this
  simp only [hs, ↓reduceDIte, WithTop.coe_eq_coe] at this
  simp only [leadingCoeff_of_ne_zero hs, coeff_hsum, untop_orderTop_of_ne_zero hs, this]
  rw [finsum_eq_single (fun i => (s i).coeff g) a hna]

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {s t : SummableFamily Γ R α} {a : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (SummableFamily Γ R α)
  body: { toFun := fun a => -s a
      isPWO_iUnion_support' := by
        simp_rw [support_neg]
        exact s.isPWO_iUnion_support
      finite_co_support' := fun g => by
        simp only [coeff_neg', Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }

@[simp]

中文:
实例 :
  签名: 取负 (SummableFamily Γ R α)
  定义体: { toFun := fun a => -s a
      isPWO_iUnion_support' := by
        simp_rw [support_neg]
        exact s.isPWO_iUnion_support
      finite_co_support' := fun g => by
        simp only [coeff_neg', Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }

@[simp]

Depends on / 依赖: Pi.neg_apply, coeff_neg, finite_co_support, isPWO_iUnion_support, neg_apply, neg_eq_zero, s.finite_co_support, s.isPWO_iUnion_support, simp_rw, support_neg
-/
instance : Neg (SummableFamily Γ R α) where
  neg s :=
    { toFun := fun a => -s a
      isPWO_iUnion_support' := by
        simp_rw [support_neg]
        exact s.isPWO_iUnion_support
      finite_co_support' := fun g => by
        simp only [coeff_neg', Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (s : SummableFamily Γ R α)
  statement: ⇑(-s) = -s
  proof: rfl

中文:
定理 coe_neg
  条件: (s : SummableFamily Γ R α)
  结论: ⇑(-s) = -s
  证明: rfl
-/
theorem coe_neg (s : SummableFamily Γ R α) : ⇑(-s) = -s :=
  rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  statement: (-s) a = -s a
  proof: rfl

中文:
定理 neg_apply
  结论: (-s) a = -s a
  证明: rfl
-/
theorem neg_apply : (-s) a = -s a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (SummableFamily Γ R α)
  body: { toFun := s - s'
      isPWO_iUnion_support' := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').isPWO_iUnion_support
      finite_co_support' g := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').finite_co_support' _ }

@[simp]

中文:
实例 :
  签名: 减法 (SummableFamily Γ R α)
  定义体: { toFun := s - s'
      isPWO_iUnion_support' := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').isPWO_iUnion_support
      finite_co_support' g := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').finite_co_support' _ }

@[simp]

Depends on / 依赖: finite_co_support, isPWO_iUnion_support, simp_rw, sub_eq_add_neg
-/
instance : Sub (SummableFamily Γ R α) where
  sub s s' :=
    { toFun := s - s'
      isPWO_iUnion_support' := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').isPWO_iUnion_support
      finite_co_support' g := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').finite_co_support' _ }

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (s t : SummableFamily Γ R α)
  statement: ⇑(s - t) = s - t
  proof: rfl

中文:
定理 coe_sub
  条件: (s t : SummableFamily Γ R α)
  结论: ⇑(s - t) = s - t
  证明: rfl
-/
theorem coe_sub (s t : SummableFamily Γ R α) : ⇑(s - t) = s - t :=
  rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  statement: (s - t) a = s a - t a
  proof: rfl

中文:
定理 sub_apply
  结论: (s - t) a = s a - t a
  证明: rfl
-/
theorem sub_apply : (s - t) a = s a - t a :=
  rfl


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (SummableFamily Γ R α)
  body: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul' _ _) (fun _ _ => coe_smul' _ _)

中文:
实例 :
  签名: 加法交换群 (SummableFamily Γ R α)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul' _ _) (fun _ _ => coe_smul' _ _)

Depends on / 依赖: fast_instance
-/
instance : AddCommGroup (SummableFamily Γ R α) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul' _ _) (fun _ _ => coe_smul' _ _)

end AddCommGroup

section SMul

variable [PartialOrder Γ] [PartialOrder Γ'] [AddCommMonoid V]

variable [AddCommMonoid R] [SMulWithZero R V]

/--
theorem `smul_support_subset_prod` / 定理 `smul_support_subset_prod`

English:
theorem smul_support_subset_prod
  statement: (s : SummableFamily Γ R α)
  proof: by
  intro _ hab
  simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
    Set.mem_ofPred_eq]
  exact ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩

中文:
定理 smul_support_subset_prod
  结论: (s : SummableFamily Γ R α)
  证明: by
  intro _ hab
  simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
    Set.mem_ofPred_eq]
  exact ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩

Depends on / 依赖: Finite, Function, Function.mem_support, Set.Finite.coe_toFinset, Set.mem_ofPred_eq, Set.mem_prod, coe_toFinset, left_ne_zero_of_smul, mem_ofPred_eq, mem_prod, mem_support, ne_eq, right_ne_zero_of_smul
-/
theorem smul_support_subset_prod (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) => (s i.1).coeff gh.1 • (t i.2).coeff gh.2) subseteq
    ((s.finite_co_support' gh.1).prod (t.finite_co_support' gh.2)).toFinset := by
  intro _ hab
  simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
    Set.mem_ofPred_eq]
  exact ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩

/--
theorem `hasFiniteSupport_smul` / 定理 `hasFiniteSupport_smul`

English:
theorem hasFiniteSupport_smul
  statement: (s : SummableFamily Γ R α)
  proof: Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

@[deprecated (since := "2026-03-03")] alias smul_support_finite := hasFiniteSupport_smul

中文:
定理 hasFiniteSupport_smul
  结论: (s : SummableFamily Γ R α)
  证明: Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

@[deprecated (since := "2026-03-03")] alias smul_support_finite := hasFiniteSupport_smul

Depends on / 依赖: Finite, Set.Finite.subset, Set.toFinite, finite_co_support, s.finite_co_support, smul_support_subset_prod, subset, t.finite_co_support, toFinite, toFinset
-/
theorem hasFiniteSupport_smul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (fun (i : α × β) => (s i.1).coeff gh.1 • (t i.2).coeff gh.2).HasFiniteSupport :=
  Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

@[deprecated (since := "2026-03-03")] alias smul_support_finite := hasFiniteSupport_smul

variable [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']

open HahnModule

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isPWO_iUnion_support_prod_smul` / 定理 `isPWO_iUnion_support_prod_smul`

English:
theorem isPWO_iUnion_support_prod_smul
  statement: {s : α -> R⟦Γ⟧} {t : β -> V⟦Γ'⟧}
  proof: by
  apply (hs.vadd ht).mono
  have hsupp : forall ab : α × β, support ((fun ab => (of R).symm (s ab.1 • (of R) (t ab.2))) ab) subseteq
      (s ab.1).support +ᵥ (t ab.2).support := by
    intro ab
    refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd fun a =>
      Set.VAddAntidiagonal.finite_of_isPWO (s ab.1).isPWO_support (t ab.2).isPWO_support a)
    simp only [Set.mem_ofPred_eq]
    contrapose! hx
    rw [mem_support]; rw [not_not]; rw [HahnModule.coeff_smul]; rw [hx]; rw [sum_empty]
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y => y)
    (Set.subset_iUnion_of_subset b fun x y => y)

中文:
定理 isPWO_iUnion_support_prod_smul
  结论: {s : α -> R⟦Γ⟧} {t : β -> V⟦Γ'⟧}
  证明: by
  apply (hs.vadd ht).mono
  have hsupp : forall ab : α × β, support ((fun ab => (of R).symm (s ab.1 • (of R) (t ab.2))) ab) subseteq
      (s ab.1).support +ᵥ (t ab.2).support := by
    intro ab
    refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd fun a =>
      Set.VAddAntidiagonal.finite_of_isPWO (s ab.1).isPWO_support (t ab.2).isPWO_support a)
    simp only [Set.mem_ofPred_eq]
    contrapose! hx
    rw [mem_support]; rw [not_not]; rw [HahnModule.coeff_smul]; rw [hx]; rw [sum_empty]
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y => y)
    (Set.subset_iUnion_of_subset b fun x y => y)

Depends on / 依赖: HahnModule, HahnModule.coeff_smul, Set.Su, Set.Subset.trans, Set.VAddAntidiagonal.finite_of_isPWO, Set.mem_ofPred_eq, Subset, VAddAntidiagonal, coeff_smul, contrapose, finite_of_isPWO, hs.vadd, isPWO_support, mem_ofPred_eq, mem_support, not_not, subseteq, sum_empty, support, support_vaddAntidiagonal_subset_vadd
-/
theorem isPWO_iUnion_support_prod_smul {s : α -> R⟦Γ⟧} {t : β -> V⟦Γ'⟧}
    (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a => (of R).symm
      ((s a.1) • (of R) (t a.2))) a).support).IsPWO := by
  apply (hs.vadd ht).mono
  have hsupp : forall ab : α × β, support ((fun ab => (of R).symm (s ab.1 • (of R) (t ab.2))) ab) subseteq
      (s ab.1).support +ᵥ (t ab.2).support := by
    intro ab
    refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd fun a =>
      Set.VAddAntidiagonal.finite_of_isPWO (s ab.1).isPWO_support (t ab.2).isPWO_support a)
    simp only [Set.mem_ofPred_eq]
    contrapose! hx
    rw [mem_support]; rw [not_not]; rw [HahnModule.coeff_smul]; rw [hx]; rw [sum_empty]
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y => y)
    (Set.subset_iUnion_of_subset b fun x y => y)

/--
theorem `finite_co_support_prod_smul` / 定理 `finite_co_support_prod_smul`

English:
theorem finite_co_support_prod_smul
  statement: (s : SummableFamily Γ R α)
  proof: by
  apply ((VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
    t.isPWO_iUnion_support g)).finite_toSet.biUnion'
    (fun gh _ => hasFiniteSupport_smul s t gh)).subset _
  exact fun ab hab => by
    simp only [ne_eq, Set.mem_ofPred_eq] at hab
    obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    simp only [mem_coe, mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
      Function.mem_support, exists_prop, Prod.exists]
    exact ⟨ij.1, ij.2, ⟨⟨ab.1, left_ne_zero_of_smul hij.2⟩, ⟨ab.2, right_ne_zero_of_smul hij.2⟩,
      ((mem_vaddAntidiagonal _ _).mp hij.1).2.2⟩, hij.2⟩

中文:
定理 finite_co_support_prod_smul
  结论: (s : SummableFamily Γ R α)
  证明: by
  apply ((VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
    t.isPWO_iUnion_support g)).finite_toSet.biUnion'
    (fun gh _ => hasFiniteSupport_smul s t gh)).subset _
  exact fun ab hab => by
    simp only [ne_eq, Set.mem_ofPred_eq] at hab
    obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    simp only [mem_coe, mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
      Function.mem_support, exists_prop, Prod.exists]
    exact ⟨ij.1, ij.2, ⟨⟨ab.1, left_ne_zero_of_smul hij.2⟩, ⟨ab.2, right_ne_zero_of_smul hij.2⟩,
      ((mem_vaddAntidiagonal _ _).mp hij.1).2.2⟩, hij.2⟩

Depends on / 依赖: Finset, Finset.exists_ne_zero_of_sum_ne_zero, Function, Function.mem_support, Prod.exists, Set.VAddAntidiagonal.finite_of_isPWO, Set.mem_iUnion, Set.mem_ofPred_eq, VAddAntidiagonal, biUnion, exists_ne_zero_of_sum_ne_zero, exists_prop, finite_of_isPWO, finite_toSet, finite_toSet.biUnion, hasFiniteSupport_smul, isPWO_iUnion_support, left_ne_zero_of_smul, mem_coe, mem_iUnion
-/
theorem finite_co_support_prod_smul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') :
    Finite {(ab : α × β) |
      ((fun (ab : α × β) => (of R).symm (s ab.1 • (of R) (t ab.2))) ab).coeff g != 0} := by
  apply ((VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
    t.isPWO_iUnion_support g)).finite_toSet.biUnion'
    (fun gh _ => hasFiniteSupport_smul s t gh)).subset _
  exact fun ab hab => by
    simp only [ne_eq, Set.mem_ofPred_eq] at hab
    obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    simp only [mem_coe, mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
      Function.mem_support, exists_prop, Prod.exists]
    exact ⟨ij.1, ij.2, ⟨⟨ab.1, left_ne_zero_of_smul hij.2⟩, ⟨ab.2, right_ne_zero_of_smul hij.2⟩,
      ((mem_vaddAntidiagonal _ _).mp hij.1).2.2⟩, hij.2⟩

/-- An elementwise scalar multiplication of one summable family on another. -/
@[simps]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β)
  body: (of R).symm (s (ab.1) • ((of R) (t (ab.2))))
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_smul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_smul s t g

中文:
定义 smul
  签名: (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β)
  定义体: (of R).symm (s (ab.1) • ((of R) (t (ab.2))))
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_smul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_smul s t g
-/
def smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) : SummableFamily Γ' V (α × β) where
  toFun ab := (of R).symm (s (ab.1) • ((of R) (t (ab.2))))
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_smul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_smul s t g

/--
theorem `sum_vAddAntidiagonal_eq` / 定理 `sum_vAddAntidiagonal_eq`

English:
theorem sum_vAddAntidiagonal_eq
  statement: (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ')
  proof: by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vaddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    exact ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

中文:
定理 sum_vAddAntidiagonal_eq
  结论: (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ')
  证明: by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vaddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    exact ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

Depends on / 依赖: Exists, Exists.intro, Function, Function.mem_support, Set.mem_iUnion, mem_iUnion, mem_support, mem_vaddAntidiagonal, smul_eq_zero_of_left, sum_subset
-/
theorem sum_vAddAntidiagonal_eq (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ')
    (a : α × β) :
    ∑ x in VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO (s a.1).isPWO_support'
      (t a.2).isPWO_support' g), (s a.1).coeff x.1 • (t a.2).coeff x.2 =
    ∑ x in VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support'
      t.isPWO_iUnion_support' g), (s a.1).coeff x.1 • (t a.2).coeff x.2 := by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vaddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    exact ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  statement: {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
  proof: by
  rw [coeff_hsum]
  simp only [coeff_hsum_eq_sum, smul_toFun, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  simp_rw [sum_vAddAntidiagonal_eq, Finset.smul_sum, Finset.sum_smul]
  rw [← sum_finsum_comm _ _ <| fun gh _ => hasFiniteSupport_smul s t gh]
  refine sum_congr rfl fun gh _ => ?_
  rw [finsum_eq_sum _ (hasFiniteSupport_smul s t gh)]; rw [← sum_product_right']
  refine sum_subset (fun ab hab => ?_) (fun ab _ hab => by simp_all)
  have hsupp := smul_support_subset_prod s t gh
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, Set.Finite.coe_toFinset, support_subset_iff, Set.mem_prod,
    Set.mem_ofPred_eq, Prod.forall, coeff_support, mem_product]
  exact hsupp ab.1 ab.2 hab

中文:
定理 coeff_smul
  结论: {R} {V} [半环 R] [加法交换幺半群 V] [模 R V]
  证明: by
  rw [coeff_hsum]
  simp only [coeff_hsum_eq_sum, smul_toFun, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  simp_rw [sum_vAddAntidiagonal_eq, Finset.smul_sum, Finset.sum_smul]
  rw [← sum_finsum_comm _ _ <| fun gh _ => hasFiniteSupport_smul s t gh]
  refine sum_congr rfl fun gh _ => ?_
  rw [finsum_eq_sum _ (hasFiniteSupport_smul s t gh)]; rw [← sum_product_right']
  refine sum_subset (fun ab hab => ?_) (fun ab _ hab => by simp_all)
  have hsupp := smul_support_subset_prod s t gh
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, Set.Finite.coe_toFinset, support_subset_iff, Set.mem_prod,
    Set.mem_ofPred_eq, Prod.forall, coeff_support, mem_product]
  exact hsupp ab.1 ab.2 hab

Depends on / 依赖: Equiv.symm_apply_apply, Finset, Finset.smul_sum, Finset.sum_smul, HahnModule, HahnModule.coeff_smul, coeff_hsum, coeff_hsum_eq_sum, coeff_smul, finsum_eq_sum, hasFiniteSupport_smul, mem_vaddAn, simp_rw, smul_sum, smul_support_subset_prod, smul_toFun, sum_congr, sum_finsum_comm, sum_product_right, sum_smul
-/
theorem coeff_smul {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') :
    (smul s t).hsum.coeff g =
    ∑ gh in VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
      t.isPWO_iUnion_support g), (s.hsum.coeff gh.1) • (t.hsum.coeff gh.2) := by
  rw [coeff_hsum]
  simp only [coeff_hsum_eq_sum, smul_toFun, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  simp_rw [sum_vAddAntidiagonal_eq, Finset.smul_sum, Finset.sum_smul]
  rw [← sum_finsum_comm _ _ <| fun gh _ => hasFiniteSupport_smul s t gh]
  refine sum_congr rfl fun gh _ => ?_
  rw [finsum_eq_sum _ (hasFiniteSupport_smul s t gh)]; rw [← sum_product_right']
  refine sum_subset (fun ab hab => ?_) (fun ab _ hab => by simp_all)
  have hsupp := smul_support_subset_prod s t gh
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, Set.Finite.coe_toFinset, support_subset_iff, Set.mem_prod,
    Set.mem_ofPred_eq, Prod.forall, coeff_support, mem_product]
  exact hsupp ab.1 ab.2 hab

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smul_hsum` / 定理 `smul_hsum`

English:
theorem smul_hsum
  statement: {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
  proof: by
  ext g
  rw [coeff_smul s t g]; rw [HahnModule.coeff_smul]; rw [Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a => a) (fun _ _ _ _ h => h) (fun _ hgh => ?_)
    (fun gh _ hgh => ?_) fun _ _ => by simp)
  · simp_all only [mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [coeff_hsum_eq_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simpa using h'
    · by_contra hi
      simp_all
  · simp only [Set.image_id', mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, not_and] at hgh
    by_cases h : s.hsum.coeff gh.1 = 0
    · exact smul_eq_zero_of_left h (t.hsum.coeff gh.2)
    · simp_all

中文:
定理 smul_hsum
  结论: {R} {V} [半环 R] [加法交换幺半群 V] [模 R V]
  证明: by
  ext g
  rw [coeff_smul s t g]; rw [HahnModule.coeff_smul]; rw [Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a => a) (fun _ _ _ _ h => h) (fun _ hgh => ?_)
    (fun gh _ hgh => ?_) fun _ _ => by simp)
  · simp_all only [mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [coeff_hsum_eq_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simpa using h'
    · by_contra hi
      simp_all
  · simp only [Set.image_id', mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, not_and] at hgh
    by_cases h : s.hsum.coeff gh.1 = 0
    · exact smul_eq_zero_of_left h (t.hsum.coeff gh.2)
    · simp_all

Depends on / 依赖: Eq.symm, Equiv.symm_apply_apply, Finset, Finset.exists_ne_zero_of_sum_ne_zero, HahnModule, HahnModule.coeff_smul, Set.image_id, Set.mem_iUnion, and_true, coeff_hsum_eq_sum, coeff_smul, exists_ne_zero_of_sum_ne_zero, image_id, mem_coe, mem_iUnion, mem_support, mem_vaddAntidiagonal, ne_eq, sum_of_injOn, symm_apply_apply
-/
theorem smul_hsum {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (smul s t).hsum = (of R).symm (s.hsum • (of R) (t.hsum)) := by
  ext g
  rw [coeff_smul s t g]; rw [HahnModule.coeff_smul]; rw [Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a => a) (fun _ _ _ _ h => h) (fun _ hgh => ?_)
    (fun gh _ hgh => ?_) fun _ _ => by simp)
  · simp_all only [mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [coeff_hsum_eq_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simpa using h'
    · by_contra hi
      simp_all
  · simp only [Set.image_id', mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, not_and] at hgh
    by_cases h : s.hsum.coeff gh.1 = 0
    · exact smul_eq_zero_of_left h (t.hsum.coeff gh.2)
    · simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R⟦Γ⟧ (SummableFamily Γ' V β)
  body: Equiv (Equiv.punitProd β) smul (const Unit x) t

中文:
实例 :
  签名: 标量乘法 R⟦Γ⟧ (SummableFamily Γ' V β)
  定义体: Equiv (Equiv.punitProd β) smul (const Unit x) t

Depends on / 依赖: Equiv.punitProd, punitProd
-/
instance : SMul R⟦Γ⟧ (SummableFamily Γ' V β) where
smul x t := Equiv (Equiv.punitProd β) smul (const Unit x) t

/--
theorem `smul_eq` / 定理 `smul_eq`

English:
theorem smul_eq
  given: {x : R⟦Γ⟧} {t : SummableFamily Γ' V β}
  proof: rfl

@[simp]

中文:
定理 smul_eq
  条件: {x : R⟦Γ⟧} {t : SummableFamily Γ' V β}
  证明: rfl

@[simp]
-/
theorem smul_eq {x : R⟦Γ⟧} {t : SummableFamily Γ' V β} :
    x • t = Equiv (Equiv.punitProd β) (smul (const Unit x) t) :=
  rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α}
  proof: rfl

@[simp]

中文:
定理 smul_apply
  条件: {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α}
  证明: rfl

@[simp]
-/
theorem smul_apply {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α} :
    (x • s) a = (of R).symm (x • of R (s a)) :=
  rfl

@[simp]
/--
theorem `hsum_smul_module` / 定理 `hsum_smul_module`

English:
theorem hsum_smul_module
  statement: {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] {x : R⟦Γ⟧}
  proof: by
  rw [smul_eq]; rw [hsum_equiv]; rw [smul_hsum]; rw [hsum_unique]; rw [const_toFun]

中文:
定理 hsum_smul_module
  结论: {R} {V} [半环 R] [加法交换幺半群 V] [模 R V] {x : R⟦Γ⟧}
  证明: by
  rw [smul_eq]; rw [hsum_equiv]; rw [smul_hsum]; rw [hsum_unique]; rw [const_toFun]

Depends on / 依赖: const_toFun, hsum_equiv, hsum_unique, smul_eq, smul_hsum
-/
theorem hsum_smul_module {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] {x : R⟦Γ⟧}
    {s : SummableFamily Γ' V α} :
    (x • s).hsum = (of R).symm (x • of R s.hsum) := by
  rw [smul_eq]; rw [hsum_equiv]; rw [smul_hsum]; rw [hsum_unique]; rw [const_toFun]

end SMul

section Semiring

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [PartialOrder Γ'] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [Semiring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: V] [Module R V] : Module R⟦Γ⟧ (SummableFamily Γ' V α) where
  body: ext fun _ => by simp
  zero_smul _ := ext fun _ => by simp
  one_smul _ := ext fun _ => by rw [smul_apply, HahnModule.one_smul', Equiv.symm_apply_apply]
  add_smul _ _ _ := ext fun _ => by simp [add_smul]
  smul_add _ _ _ := ext fun _ => by simp
  mul_smul _ _ _ := ext fun _ => by simp [HahnModule.instModule.mul_smul]

中文:
实例 [加法交换幺半群
  签名: V] [模 R V] : 模 R⟦Γ⟧ (SummableFamily Γ' V α) where
  定义体: ext fun _ => by simp
  zero_smul _ := ext fun _ => by simp
  one_smul _ := ext fun _ => by rw [smul_apply, HahnModule.one_smul', Equiv.symm_apply_apply]
  add_smul _ _ _ := ext fun _ => by simp [add_smul]
  smul_add _ _ _ := ext fun _ => by simp
  mul_smul _ _ _ := ext fun _ => by simp [HahnModule.instModule.mul_smul]
-/
instance [AddCommMonoid V] [Module R V] : Module R⟦Γ⟧ (SummableFamily Γ' V α) where
  smul_zero _ := ext fun _ => by simp
  zero_smul _ := ext fun _ => by simp
  one_smul _ := ext fun _ => by rw [smul_apply, HahnModule.one_smul', Equiv.symm_apply_apply]
  add_smul _ _ _ := ext fun _ => by simp [add_smul]
  smul_add _ _ _ := ext fun _ => by simp
  mul_smul _ _ _ := ext fun _ => by simp [HahnModule.instModule.mul_smul]

/--
theorem `hsum_smul` / 定理 `hsum_smul`

English:
theorem hsum_smul
  given: {x : R⟦Γ⟧} {s : SummableFamily Γ R α}
  proof: by
  rw [hsum_smul_module]; rw [of_symm_smul_of_eq_mul]

中文:
定理 hsum_smul
  条件: {x : R⟦Γ⟧} {s : SummableFamily Γ R α}
  证明: by
  rw [hsum_smul_module]; rw [of_symm_smul_of_eq_mul]

Depends on / 依赖: hsum_smul_module, of_symm_smul_of_eq_mul
-/
theorem hsum_smul {x : R⟦Γ⟧} {s : SummableFamily Γ R α} :
    (x • s).hsum = x * s.hsum := by
  rw [hsum_smul_module]; rw [of_symm_smul_of_eq_mul]

/-- The summation of a `summable_family` as a `LinearMap`. -/
@[simps]
/--
Definition of `lsum` / `lsum` 的定义

English:
definition lsum
  signature: : SummableFamily Γ R α ->ₗ[R⟦Γ⟧] R⟦Γ⟧ where
  body: hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul

@[simp]

中文:
定义 lsum
  签名: : SummableFamily Γ R α ->ₗ[R⟦Γ⟧] R⟦Γ⟧ where
  定义体: hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul

@[simp]
-/
def lsum : SummableFamily Γ R α ->ₗ[R⟦Γ⟧] R⟦Γ⟧ where
  toFun := hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul

@[simp]
/--
theorem `hsum_sub` / 定理 `hsum_sub`

English:
theorem hsum_sub
  given: {R : Type*} [Ring R] {s t : SummableFamily Γ R α}
  proof: by
  rw [← lsum_apply]; rw [map_sub]; rw [lsum_apply]; rw [lsum_apply]

中文:
定理 hsum_sub
  条件: {R : 类型} [环 R] {s t : SummableFamily Γ R α}
  证明: by
  rw [← lsum_apply]; rw [map_sub]; rw [lsum_apply]; rw [lsum_apply]

Depends on / 依赖: lsum_apply, map_sub
-/
theorem hsum_sub {R : Type*} [Ring R] {s t : SummableFamily Γ R α} :
    (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply]; rw [map_sub]; rw [lsum_apply]; rw [lsum_apply]

/--
theorem `isPWO_iUnion_support_prod_mul` / 定理 `isPWO_iUnion_support_prod_mul`

English:
theorem isPWO_iUnion_support_prod_mul
  statement: {s : α -> R⟦Γ⟧} {t : β -> R⟦Γ⟧}
  proof: isPWO_iUnion_support_prod_smul hs ht

中文:
定理 isPWO_iUnion_support_prod_mul
  结论: {s : α -> R⟦Γ⟧} {t : β -> R⟦Γ⟧}
  证明: isPWO_iUnion_support_prod_smul hs ht

Depends on / 依赖: isPWO_iUnion_support_prod_smul
-/
theorem isPWO_iUnion_support_prod_mul {s : α -> R⟦Γ⟧} {t : β -> R⟦Γ⟧}
    (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a => ((s a.1) * (t a.2))) a).support).IsPWO :=
  isPWO_iUnion_support_prod_smul hs ht

/--
theorem `finite_co_support_prod_mul` / 定理 `finite_co_support_prod_mul`

English:
theorem finite_co_support_prod_mul
  statement: (s : SummableFamily Γ R α)
  proof: finite_co_support_prod_smul s t g

中文:
定理 finite_co_support_prod_mul
  结论: (s : SummableFamily Γ R α)
  证明: finite_co_support_prod_smul s t g

Depends on / 依赖: finite_co_support_prod_smul
-/
theorem finite_co_support_prod_mul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ R β) (g : Γ) :
    Finite {(a : α × β) | ((fun (a : α × β) => (s a.1 * t a.2)) a).coeff g != 0} :=
  finite_co_support_prod_smul s t g

/-- A summable family given by pointwise multiplication of a pair of summable families. -/
@[simps]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β)
  body: s (a.1) * t (a.2)
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_mul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_mul s t g

中文:
定义 mul
  签名: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β)
  定义体: s (a.1) * t (a.2)
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_mul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_mul s t g
-/
def mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (SummableFamily Γ R (α × β)) where
  toFun a := s (a.1) * t (a.2)
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_mul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_mul s t g

/--
theorem `mul_eq_smul` / 定理 `mul_eq_smul`

English:
theorem mul_eq_smul
  given: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β)
  proof: rfl

中文:
定理 mul_eq_smul
  条件: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β)
  证明: rfl
-/
theorem mul_eq_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    mul s t = smul s t :=
  rfl

/--
theorem `coeff_hsum_mul` / 定理 `coeff_hsum_mul`

English:
theorem coeff_hsum_mul
  given: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ)
  proof: by
  simp_rw [← smul_eq_mul, mul_eq_smul]
  exact coeff_smul s t g

中文:
定理 coeff_hsum_mul
  条件: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ)
  证明: by
  simp_rw [← smul_eq_mul, mul_eq_smul]
  exact coeff_smul s t g

Depends on / 依赖: coeff_smul, mul_eq_smul, simp_rw, smul_eq_mul
-/
theorem coeff_hsum_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ) :
    (mul s t).hsum.coeff g = ∑ gh in antidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) * (t.hsum.coeff gh.2) := by
  simp_rw [← smul_eq_mul, mul_eq_smul]
  exact coeff_smul s t g

/--
theorem `hsum_mul` / 定理 `hsum_mul`

English:
theorem hsum_mul
  given: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β)
  proof: by
  rw [← smul_eq_mul]; rw [mul_eq_smul]
  exact smul_hsum s t

中文:
定理 hsum_mul
  条件: (s : SummableFamily Γ R α) (t : SummableFamily Γ R β)
  证明: by
  rw [← smul_eq_mul]; rw [mul_eq_smul]
  exact smul_hsum s t

Depends on / 依赖: mul_eq_smul, smul_eq_mul, smul_hsum
-/
theorem hsum_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (mul s t).hsum = s.hsum * t.hsum := by
  rw [← smul_eq_mul]; rw [mul_eq_smul]
  exact smul_hsum s t

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R]

/--
Definition of `ofFinsupp` / `ofFinsupp` 的定义

English:
definition ofFinsupp
  signature: (f : α ->₀ R⟦Γ⟧)
  body: f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine Set.iUnion_subset_iff.2 fun a g hg => ?_
    have haf : a in f.support := by
      rw [Finsupp.mem_support_iff]; rw [← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine f.support.finite_toSet.subset fun a ha => ?_
    simp only [mem_coe, Finsupp.mem_support_iff, Ne]
    contrapose ha
    simp [ha]

@[simp]

中文:
定义 ofFinsupp
  签名: (f : α ->₀ R⟦Γ⟧)
  定义体: f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine Set.iUnion_subset_iff.2 fun a g hg => ?_
    have haf : a in f.support := by
      rw [Finsupp.mem_support_iff]; rw [← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine f.support.finite_toSet.subset fun a ha => ?_
    simp only [mem_coe, Finsupp.mem_support_iff, Ne]
    contrapose ha
    simp [ha]

@[simp]
-/
def ofFinsupp (f : α ->₀ R⟦Γ⟧) : SummableFamily Γ R α where
  toFun := f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine Set.iUnion_subset_iff.2 fun a g hg => ?_
    have haf : a in f.support := by
      rw [Finsupp.mem_support_iff]; rw [← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine f.support.finite_toSet.subset fun a ha => ?_
    simp only [mem_coe, Finsupp.mem_support_iff, Ne]
    contrapose ha
    simp [ha]

@[simp]
/--
theorem `coe_ofFinsupp` / 定理 `coe_ofFinsupp`

English:
theorem coe_ofFinsupp
  given: {f : α ->₀ R⟦Γ⟧}
  statement: ⇑(SummableFamily.ofFinsupp f) = f
  proof: rfl

@[simp]

中文:
定理 coe_ofFinsupp
  条件: {f : α ->₀ R⟦Γ⟧}
  结论: ⇑(SummableFamily.ofFinsupp f) = f
  证明: rfl

@[simp]
-/
theorem coe_ofFinsupp {f : α ->₀ R⟦Γ⟧} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl

@[simp]
/--
theorem `hsum_ofFinsupp` / 定理 `hsum_ofFinsupp`

English:
theorem hsum_ofFinsupp
  given: {f : α ->₀ R⟦Γ⟧}
  statement: (ofFinsupp f).hsum = f.sum fun _ => id
  proof: by
  ext g
  simp only [coeff_hsum, coe_ofFinsupp, Finsupp.sum]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum]; rw [finsum_eq_sum_of_support_subset]
  intro x h
  simp only [mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose h
  simp [h]

中文:
定理 hsum_ofFinsupp
  条件: {f : α ->₀ R⟦Γ⟧}
  结论: (ofFinsupp f).hsum = f.求和 fun _ => id
  证明: by
  ext g
  simp only [coeff_hsum, coe_ofFinsupp, Finsupp.sum]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum]; rw [finsum_eq_sum_of_support_subset]
  intro x h
  simp only [mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose h
  simp [h]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Finsupp.sum, addMonoidHom_apply, coe_ofFinsupp, coeff.addMonoidHom_apply, coeff_hsum, contrapose, finsum_eq_sum_of_support_subset, map_sum, mem_coe, mem_support_iff, simp_rw
-/
theorem hsum_ofFinsupp {f : α ->₀ R⟦Γ⟧} : (ofFinsupp f).hsum = f.sum fun _ => id := by
  ext g
  simp only [coeff_hsum, coe_ofFinsupp, Finsupp.sum]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum]; rw [finsum_eq_sum_of_support_subset]
  intro x h
  simp only [mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose h
  simp [h]

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R]

open scoped Classical in
/--
Definition of `embDomain` / `embDomain` 的定义

English:
definition embDomain
  signature: (s : SummableFamily Γ R α) (f : α ↪ β)
  body: if h : b in Set.range f then s (Classical.choose h) else 0
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => ?_)
    by_cases hb : b in Set.range f
    · rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · simp [-Set.mem_range, dif_neg hb] at h
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        by_cases hb : b in Set.range f
        · simp only [Ne, Set.mem_ofPred_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne, Set.mem_ofPred_eq, dif_neg hb, coeff_zero, not_true_eq_false] at h)

中文:
定义 embDomain
  签名: (s : SummableFamily Γ R α) (f : α ↪ β)
  定义体: if h : b in Set.range f then s (Classical.choose h) else 0
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => ?_)
    by_cases hb : b in Set.range f
    · rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · simp [-Set.mem_range, dif_neg hb] at h
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        by_cases hb : b in Set.range f
        · simp only [Ne, Set.mem_ofPred_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne, Set.mem_ofPred_eq, dif_neg hb, coeff_zero, not_true_eq_false] at h)

Depends on / 依赖: Classical, Classical.choose, Set.range
-/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β where
  toFun b := if h : b in Set.range f then s (Classical.choose h) else 0
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => ?_)
    by_cases hb : b in Set.range f
    · rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · simp [-Set.mem_range, dif_neg hb] at h
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        by_cases hb : b in Set.range f
        · simp only [Ne, Set.mem_ofPred_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne, Set.mem_ofPred_eq, dif_neg hb, coeff_zero, not_true_eq_false] at h)

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

open scoped Classical in
/--
theorem `embDomain_apply` / 定理 `embDomain_apply`

English:
theorem embDomain_apply
  proof: rfl

@[simp]

中文:
定理 embDomain_apply
  证明: rfl

@[simp]
-/
theorem embDomain_apply :
    s.embDomain f b = if h : b in Set.range f then s (Classical.choose h) else 0 :=
  rfl

@[simp]
/--
theorem `embDomain_image` / 定理 `embDomain_image`

English:
theorem embDomain_image
  statement: s.embDomain f (f a) = s a
  proof: by
  rw [embDomain_apply]; rw [dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))

@[simp]

中文:
定理 embDomain_image
  结论: s.embDomain f (f a) = s a
  证明: by
  rw [embDomain_apply]; rw [dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, Set.mem_range_self, choose_spec, dif_pos, embDomain_apply, f.injective, injective, mem_range_self
-/
theorem embDomain_image : s.embDomain f (f a) = s a := by
  rw [embDomain_apply]; rw [dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))

@[simp]
/--
theorem `embDomain_of_notMem_range` / 定理 `embDomain_of_notMem_range`

English:
theorem embDomain_of_notMem_range
  given: (h : b ∉ Set.range f)
  statement: s.embDomain f b = 0
  proof: by
  rw [embDomain_apply]; rw [dif_neg h]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]

中文:
定理 embDomain_of_notMem_range
  条件: (h : b ∉ 集合.range f)
  结论: s.embDomain f b = 0
  证明: by
  rw [embDomain_apply]; rw [dif_neg h]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]

Depends on / 依赖: dif_neg, embDomain_apply
-/
theorem embDomain_of_notMem_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [embDomain_apply]; rw [dif_neg h]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]
/--
theorem `hsum_embDomain` / 定理 `hsum_embDomain`

English:
theorem hsum_embDomain
  statement: (s.embDomain f).hsum = s.hsum
  proof: by
  classical
  ext g
  simp only [coeff_hsum, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, coeff_zero]
  exact finsum_emb_domain f fun a => (s a).coeff g

中文:
定理 hsum_embDomain
  结论: (s.embDomain f).hsum = s.hsum
  证明: by
  classical
  ext g
  simp only [coeff_hsum, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, coeff_zero]
  exact finsum_emb_domain f fun a => (s a).coeff g

Depends on / 依赖: HahnSeries, HahnSeries.coeff, apply_dite, classical, coeff_hsum, coeff_zero, dite_apply, embDomain_apply, finsum_emb_domain
-/
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum := by
  classical
  ext g
  simp only [coeff_hsum, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, coeff_zero]
  exact finsum_emb_domain f fun a => (s a).coeff g

end EmbDomain

section powers

/--
theorem `support_pow_subset_closure` / 定理 `support_pow_subset_closure`

English:
theorem support_pow_subset_closure
  statement: [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  proof: by
  intro g hn
  induction n generalizing g with
  | zero =>
    simp only [pow_zero, mem_support, coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    simp only [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  | succ n ih =>
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

中文:
定理 support_pow_subset_closure
  结论: [加法交换幺半群 Γ] [偏序 Γ] [是OrderedCancelAdd幺半群 Γ]
  证明: by
  intro g hn
  induction n generalizing g with
  | zero =>
    simp only [pow_zero, mem_support, coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    simp only [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  | succ n ih =>
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

Depends on / 依赖: AddSubmonoid, AddSubmonoid.add_mem, AddSubmonoid.subset_closure, AddSubmonoid.zero_mem, Classical, Classical.not_imp, SetLike, SetLike.mem_coe, add_mem, coeff_one, generalizing, ite_eq_right_iff, mem_coe, mem_support, ne_eq, not_imp, pow_zero, subset_closure, support_mul_subset, zero_mem
-/
theorem support_pow_subset_closure [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] (x : R⟦Γ⟧)
    (n : Nat) : support (x ^ n) subseteq AddSubmonoid.closure (support x) := by
  intro g hn
  induction n generalizing g with
  | zero =>
    simp only [pow_zero, mem_support, coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    simp only [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  | succ n ih =>
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

/--
theorem `isPWO_iUnion_support_powers` / 定理 `isPWO_iUnion_support_powers`

English:
theorem isPWO_iUnion_support_powers
  statement: [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  proof: (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)

中文:
定理 isPWO_iUnion_support_powers
  结论: [加法交换幺半群 Γ] [线性序 Γ] [是OrderedCancelAdd幺半群 Γ]
  证明: (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)

Depends on / 依赖: Function, Function.mem_support.mp, Set.iUnion_subset, addSubmonoid_closure, iUnion_subset, isPWO_support, le_trans, mem_support, order_le_of_coeff_ne_zero, support_pow_subset_closure, x.isPWO_support
-/
theorem isPWO_iUnion_support_powers [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R]
    {x : R⟦Γ⟧} (hx : 0 <= x.order) :
    (⋃ n : Nat, (x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)

/--
theorem `co_support_zero` / 定理 `co_support_zero`

English:
theorem co_support_zero
  statement: [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  proof: by
  simp only [Set.subset_singleton_iff, Set.mem_ofPred_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, coeff_zero, not_true_eq_false]

中文:
定理 co_support_zero
  结论: [加法交换幺半群 Γ] [偏序 Γ] [是OrderedCancelAdd幺半群 Γ]
  证明: by
  simp only [Set.subset_singleton_iff, Set.mem_ofPred_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, coeff_zero, not_true_eq_false]

Depends on / 依赖: Set.mem_ofPred_eq, Set.subset_singleton_iff, coeff_zero, mem_ofPred_eq, ne_eq, not_false_eq_true, not_true_eq_false, subset_singleton_iff, zero_pow
-/
theorem co_support_zero [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] (g : Γ) :
    {a | ¬((0 : R⟦Γ⟧) ^ a).coeff g = 0} subseteq {0} := by
  simp only [Set.subset_singleton_iff, Set.mem_ofPred_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, coeff_zero, not_true_eq_false]

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

/--
theorem `pow_finite_co_support` / 定理 `pow_finite_co_support`

English:
theorem pow_finite_co_support
  given: {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ)
  proof: by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g in ⋃ n : Nat, { g | (x ^ n).coeff g != 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((antidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (mem_antidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := mem_antidiagonal.1 (mem_coe.1 hij)
exact lt_add_of_pos_left ij.2 lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx)
order_le_of_coeff_ne_zero Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_antidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

中文:
定理 pow_finite_co_support
  条件: {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ)
  证明: by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g in ⋃ n : Nat, { g | (x ^ n).coeff g != 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((antidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (mem_antidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := mem_antidiagonal.1 (mem_coe.1 hij)
exact lt_add_of_pos_left ij.2 lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx)
order_le_of_coeff_ne_zero Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_antidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

Depends on / 依赖: Finite, Set.Finite.subset, Set.IsPWO, Set.finite_empty.subset, Set.finite_singleton, Set.mem_iUnion, antidiagonal, biUnion, co_support_zero, finite_empty, finite_singleton, finite_toSet, finite_toSet.biUnion, hpwo.isWF.induction, ij.snd, isPWO_iUnion_support_powers, isPWO_support, le_of_lt, mem_ant, mem_iUnion
-/
theorem pow_finite_co_support {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n => x ^ n) a).coeff g != 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g in ⋃ n : Nat, { g | (x ^ n).coeff g != 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((antidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (mem_antidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := mem_antidiagonal.1 (mem_coe.1 hij)
exact lt_add_of_pos_left ij.2 lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx)
order_le_of_coeff_ne_zero Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_antidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

/-- A summable family of powers of a Hahn series `x`. If `x` has non-positive `orderTop`, then
return a junk value given by pretending `x = 0`. -/
@[simps]
/--
Definition of `powers` / `powers` 的定义

English:
definition powers
  signature: (x : R⟦Γ⟧)
  body: (if 0 < x.orderTop then x else 0) ^ n
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp only [h, ↓reduceIte]
      apply isPWO_iUnion_support_powers
      rw [order_zero]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support h g
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support (orderTop_zero (R := R) (Γ := Γ) ▸ WithTop.top_pos) g

中文:
定义 powers
  签名: (x : R⟦Γ⟧)
  定义体: (if 0 < x.orderTop then x else 0) ^ n
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp only [h, ↓reduceIte]
      apply isPWO_iUnion_support_powers
      rw [order_zero]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support h g
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support (orderTop_zero (R := R) (Γ := Γ) ▸ WithTop.top_pos) g

Depends on / 依赖: orderTop, x.orderTop
-/
def powers (x : R⟦Γ⟧) : SummableFamily Γ R Nat where
  toFun n := (if 0 < x.orderTop then x else 0) ^ n
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp only [h, ↓reduceIte]
      apply isPWO_iUnion_support_powers
      rw [order_zero]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support h g
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support (orderTop_zero (R := R) (Γ := Γ) ▸ WithTop.top_pos) g

/--
theorem `powers_of_orderTop_pos` / 定理 `powers_of_orderTop_pos`

English:
theorem powers_of_orderTop_pos
  given: {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : Nat)
  proof: by
  simp [hx]

中文:
定理 powers_of_orderTop_pos
  条件: {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : 自然数)
  证明: by
  simp [hx]
-/
theorem powers_of_orderTop_pos {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : Nat) :
    powers x n = x ^ n := by
  simp [hx]

/--
theorem `powers_of_not_orderTop_pos` / 定理 `powers_of_not_orderTop_pos`

English:
theorem powers_of_not_orderTop_pos
  given: {x : R⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
  proof: by
  ext a
  obtain rfl | ha := eq_or_ne a 0 <;> simp [powers, *]

@[simp]

中文:
定理 powers_of_not_orderTop_pos
  条件: {x : R⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
  证明: by
  ext a
  obtain rfl | ha := eq_or_ne a 0 <;> simp [powers, *]

@[simp]

Depends on / 依赖: eq_or_ne, powers
-/
theorem powers_of_not_orderTop_pos {x : R⟦Γ⟧} (hx : ¬ 0 < x.orderTop) :
    powers x = .single 0 1 := by
  ext a
  obtain rfl | ha := eq_or_ne a 0 <;> simp [powers, *]

@[simp]
/--
theorem `powers_zero` / 定理 `powers_zero`

English:
theorem powers_zero
  statement: powers (0 : R⟦Γ⟧) = .single 0 1
  proof: by
  ext n
  rw [powers_of_orderTop_pos (by simp)]
  obtain rfl | ha := eq_or_ne n 0 <;> simp [*]

中文:
定理 powers_zero
  结论: powers (0 : R⟦Γ⟧) = .single 0 1
  证明: by
  ext n
  rw [powers_of_orderTop_pos (by simp)]
  obtain rfl | ha := eq_or_ne n 0 <;> simp [*]

Depends on / 依赖: eq_or_ne, powers_of_orderTop_pos
-/
theorem powers_zero : powers (0 : R⟦Γ⟧) = .single 0 1 := by
  ext n
  rw [powers_of_orderTop_pos (by simp)]
  obtain rfl | ha := eq_or_ne n 0 <;> simp [*]

variable {x : R⟦Γ⟧} (hx : 0 < x.orderTop)

include hx in
@[simp]
/--
theorem `coe_powers` / 定理 `coe_powers`

English:
theorem coe_powers
  statement: ⇑(powers x) = HPow.hPow x
  proof: by
  ext1 n
  simp [hx]

include hx in

中文:
定理 coe_powers
  结论: ⇑(powers x) = 异质幂.hPow x
  证明: by
  ext1 n
  simp [hx]

include hx in
-/
theorem coe_powers : ⇑(powers x) = HPow.hPow x := by
  ext1 n
  simp [hx]

include hx in
/--
theorem `embDomain_succ_smul_powers` / 定理 `embDomain_succ_smul_powers`

English:
theorem embDomain_succ_smul_powers
  proof: by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · -- FIXME: smul_eq_mul introduces type confusion between HahnModule and HahnSeries.
    simp [embDomain_apply, of_symm_smul_of_eq_mul, powers_of_orderTop_pos hx, pow_succ',
      -smul_eq_mul]

include hx in

中文:
定理 embDomain_succ_smul_powers
  证明: by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · -- FIXME: smul_eq_mul introduces type confusion between HahnModule and HahnSeries.
    simp [embDomain_apply, of_symm_smul_of_eq_mul, powers_of_orderTop_pos hx, pow_succ',
      -smul_eq_mul]

include hx in

Depends on / 依赖: HahnModule, HahnSeries, SummableFamily, SummableFamily.ext, between, confusion, embDomain_apply, introduces, of_symm_smul_of_eq_mul, pow_succ, powers_of_orderTop_pos, smul_eq_mul
-/
theorem embDomain_succ_smul_powers :
    (x • powers x).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · -- FIXME: smul_eq_mul introduces type confusion between HahnModule and HahnSeries.
    simp [embDomain_apply, of_symm_smul_of_eq_mul, powers_of_orderTop_pos hx, pow_succ',
      -smul_eq_mul]

include hx in
/--
theorem `one_sub_self_mul_hsum_powers` / 定理 `one_sub_self_mul_hsum_powers`

English:
theorem one_sub_self_mul_hsum_powers
  statement: (1 - x) * (powers x).hsum = 1
  proof: by
  rw [← hsum_smul]; rw [sub_smul 1 x (powers x)]; rw [one_smul]; rw [hsum_sub]; rw [←
    hsum_embDomain (x • powers x) ⟨Nat.succ]; rw [Nat.succ_injective⟩]; rw [embDomain_succ_smul_powers hx]
  simp

中文:
定理 one_sub_self_mul_hsum_powers
  结论: (1 - x) * (powers x).hsum = 1
  证明: by
  rw [← hsum_smul]; rw [sub_smul 1 x (powers x)]; rw [one_smul]; rw [hsum_sub]; rw [←
    hsum_embDomain (x • powers x) ⟨Nat.succ]; rw [Nat.succ_injective⟩]; rw [embDomain_succ_smul_powers hx]
  simp

Depends on / 依赖: Nat.succ, Nat.succ_injective, embDomain_succ_smul_powers, hsum_embDomain, hsum_smul, hsum_sub, one_smul, powers, sub_smul, succ_injective
-/
theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x).hsum = 1 := by
  rw [← hsum_smul]; rw [sub_smul 1 x (powers x)]; rw [one_smul]; rw [hsum_sub]; rw [←
    hsum_embDomain (x • powers x) ⟨Nat.succ]; rw [Nat.succ_injective⟩]; rw [embDomain_succ_smul_powers hx]
  simp

end powers

end SummableFamily

section Inversion

section CommRing

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

/--
theorem `one_minus_single_neg_mul` / 定理 `one_minus_single_neg_mul`

English:
theorem one_minus_single_neg_mul
  statement: {x y : R⟦Γ⟧} {r : R} (hr : r * x.leadingCoeff = 1)
  proof: by
  nth_rw 1 [hxy]
  rw [mul_add]; rw [single_mul_single]; rw [hr]; rw [hxo]; rw [sub_add_eq_sub_sub_swap]; rw [sub_eq_neg_self]; rw [sub_eq_zero_of_eq single_zero_one.symm]

中文:
定理 one_minus_single_neg_mul
  结论: {x y : R⟦Γ⟧} {r : R} (hr : r * x.leadingCoeff = 1)
  证明: by
  nth_rw 1 [hxy]
  rw [mul_add]; rw [single_mul_single]; rw [hr]; rw [hxo]; rw [sub_add_eq_sub_sub_swap]; rw [sub_eq_neg_self]; rw [sub_eq_zero_of_eq single_zero_one.symm]

Depends on / 依赖: mul_add, nth_rw, single_mul_single, single_zero_one, single_zero_one.symm, sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq
-/
theorem one_minus_single_neg_mul {x y : R⟦Γ⟧} {r : R} (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + single x.order x.leadingCoeff) (oinv : Γ) (hxo : oinv + x.order = 0) :
    1 - single oinv r * x = -(single oinv r * y) := by
  nth_rw 1 [hxy]
  rw [mul_add]; rw [single_mul_single]; rw [hr]; rw [hxo]; rw [sub_add_eq_sub_sub_swap]; rw [sub_eq_neg_self]; rw [sub_eq_zero_of_eq single_zero_one.symm]

/--
theorem `unit_aux` / 定理 `unit_aux`

English:
theorem unit_aux
  statement: (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoeff = 1)
  proof: by
  let y := (x - single x.order x.leadingCoeff)
  by_cases hy : y = 0
  · have hrx : (single oinv) r * x = 1 := by
      rw [eq_of_sub_eq_zero hy]; rw [single_mul_single]; rw [hxo]; rw [hr]; rw [single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.top_pos]
· have hr' : IsRegular r := IsUnit.isRegular .of_mul_eq_one x.leadingCoeff hr
    have hy' : 0 < (single oinv r * y).order := by
      rw [(order_single_mul_of_isRegular hr' hy)]
      refine pos_of_lt_add_right (a := x.order) ?_
      rw [← add_assoc]; rw [add_comm x.order]; rw [hxo]; rw [zero_add]
      exact order_lt_order_of_eq_add_single (sub_add_cancel x _).symm hy
    rw [one_minus_single_neg_mul hr (sub_add_cancel x _).symm _ hxo]; rw [orderTop_neg]
    exact zero_lt_orderTop_of_order hy'

中文:
定理 unit_aux
  结论: (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoeff = 1)
  证明: by
  let y := (x - single x.order x.leadingCoeff)
  by_cases hy : y = 0
  · have hrx : (single oinv) r * x = 1 := by
      rw [eq_of_sub_eq_zero hy]; rw [single_mul_single]; rw [hxo]; rw [hr]; rw [single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.top_pos]
· have hr' : IsRegular r := IsUnit.isRegular .of_mul_eq_one x.leadingCoeff hr
    have hy' : 0 < (single oinv r * y).order := by
      rw [(order_single_mul_of_isRegular hr' hy)]
      refine pos_of_lt_add_right (a := x.order) ?_
      rw [← add_assoc]; rw [add_comm x.order]; rw [hxo]; rw [zero_add]
      exact order_lt_order_of_eq_add_single (sub_add_cancel x _).symm hy
    rw [one_minus_single_neg_mul hr (sub_add_cancel x _).symm _ hxo]; rw [orderTop_neg]
    exact zero_lt_orderTop_of_order hy'

Depends on / 依赖: IsRegular, IsUnit, IsUnit.isRegular, WithTop, WithTop.top_pos, add_, add_assoc, eq_of_sub_eq_zero, isRegular, leadingCoeff, of_mul_eq_one, orderTop_zero, order_single_mul_of_isRegular, pos_of_lt_add_right, single, single_mul_single, single_zero_one, sub_self, top_pos, x.leadingCoeff
-/
theorem unit_aux (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoeff = 1)
    (oinv : Γ) (hxo : oinv + x.order = 0) :
    0 < (1 - single oinv r * x).orderTop := by
  let y := (x - single x.order x.leadingCoeff)
  by_cases hy : y = 0
  · have hrx : (single oinv) r * x = 1 := by
      rw [eq_of_sub_eq_zero hy]; rw [single_mul_single]; rw [hxo]; rw [hr]; rw [single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.top_pos]
· have hr' : IsRegular r := IsUnit.isRegular .of_mul_eq_one x.leadingCoeff hr
    have hy' : 0 < (single oinv r * y).order := by
      rw [(order_single_mul_of_isRegular hr' hy)]
      refine pos_of_lt_add_right (a := x.order) ?_
      rw [← add_assoc]; rw [add_comm x.order]; rw [hxo]; rw [zero_add]
      exact order_lt_order_of_eq_add_single (sub_add_cancel x _).symm hy
    rw [one_minus_single_neg_mul hr (sub_add_cancel x _).symm _ hxo]; rw [orderTop_neg]
    exact zero_lt_orderTop_of_order hy'

/--
theorem `isUnit_of_isUnit_leadingCoeff_AddUnitOrder` / 定理 `isUnit_of_isUnit_leadingCoeff_AddUnitOrder`

English:
theorem isUnit_of_isUnit_leadingCoeff_AddUnitOrder
  statement: {x : R⟦Γ⟧} (hx : IsUnit x.leadingCoeff)
  proof: by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ hxo.addUnit.neg_add)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h')

中文:
定理 isUnit_of_isUnit_leadingCoeff_AddUnitOrder
  结论: {x : R⟦Γ⟧} (hx : 是单位 x.leadingCoeff)
  证明: by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ hxo.addUnit.neg_add)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h')

Depends on / 依赖: SummableFamily, SummableFamily.one_sub_self_mul_hsum_powers, Units.val_mk, addUnit, hxo.addUnit.neg_add, isUnit_of_mul_isUnit_right, neg_add, of_mul_eq_one, one_sub_self_mul_hsum_powers, sub_sub_cancel, unit_aux, val_mk
-/
theorem isUnit_of_isUnit_leadingCoeff_AddUnitOrder {x : R⟦Γ⟧} (hx : IsUnit x.leadingCoeff)
    (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ hxo.addUnit.neg_add)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h')

/--
theorem `isUnit_of_orderTop_pos` / 定理 `isUnit_of_orderTop_pos`

English:
theorem isUnit_of_orderTop_pos
  given: {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop)
  proof: by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton x
  · refine isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [(x.orderTop_self_sub_one_pos_iff.mp h).2]
      exact isUnit_one
    · have := (x.orderTop_self_sub_one_pos_iff.mp h).1
      rw [← order_eq_orderTop_of_ne_zero
        (fun h => WithTop.top_ne_zero (orderTop_eq_top.mpr h ▸ this))]; rw [WithTop.coe_eq_zero] at this
      rw [this]
      exact isAddUnit_zero

中文:
定理 isUnit_of_orderTop_pos
  条件: {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop)
  证明: by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton x
  · refine isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [(x.orderTop_self_sub_one_pos_iff.mp h).2]
      exact isUnit_one
    · have := (x.orderTop_self_sub_one_pos_iff.mp h).1
      rw [← order_eq_orderTop_of_ne_zero
        (fun h => WithTop.top_ne_zero (orderTop_eq_top.mpr h ▸ this))]; rw [WithTop.coe_eq_zero] at this
      rw [this]
      exact isAddUnit_zero

Depends on / 依赖: WithTop, WithTop.coe_eq_zero, WithTop.top_ne_zero, coe_eq_zero, isAddUnit_zero, isUnit_of_isUnit_leadingCoeff_AddUnitOrder, isUnit_of_subsingleton, isUnit_one, orderTop_eq_top, orderTop_eq_top.mpr, orderTop_self_sub_one_pos_iff, order_eq_orderTop_of_ne_zero, subsingleton_or_nontrivial, top_ne_zero, x.orderTop_self_sub_one_pos_iff.mp
-/
theorem isUnit_of_orderTop_pos {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop) :
    IsUnit x := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton x
  · refine isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [(x.orderTop_self_sub_one_pos_iff.mp h).2]
      exact isUnit_one
    · have := (x.orderTop_self_sub_one_pos_iff.mp h).1
      rw [← order_eq_orderTop_of_ne_zero
        (fun h => WithTop.top_ne_zero (orderTop_eq_top.mpr h ▸ this))]; rw [WithTop.coe_eq_zero] at this
      rw [this]
      exact isAddUnit_zero

/-- Make an element of `orderTopSubOnePos` -/
@[simps]
/--
Definition of `toOrderTopSubOnePos` / `toOrderTopSubOnePos` 的定义

English:
definition toOrderTopSubOnePos
  signature: {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop)
  body: ⟨x, (isUnit_of_orderTop_pos h).unit.inv, IsUnit.mul_val_inv (isUnit_of_orderTop_pos h),
    IsUnit.val_inv_mul (isUnit_of_orderTop_pos h)⟩
  property := h

中文:
定义 toOrderTopSubOnePos
  签名: {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop)
  定义体: ⟨x, (isUnit_of_orderTop_pos h).unit.inv, IsUnit.mul_val_inv (isUnit_of_orderTop_pos h),
    IsUnit.val_inv_mul (isUnit_of_orderTop_pos h)⟩
  property := h

Depends on / 依赖: IsUnit, IsUnit.mul_val_inv, isUnit_of_orderTop_pos, mul_val_inv, unit.inv
-/
def toOrderTopSubOnePos {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop) :
    orderTopSubOnePos Γ R where
  val := ⟨x, (isUnit_of_orderTop_pos h).unit.inv, IsUnit.mul_val_inv (isUnit_of_orderTop_pos h),
    IsUnit.val_inv_mul (isUnit_of_orderTop_pos h)⟩
  property := h

end CommRing

section IsDomain

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R] [IsDomain R]

/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  given: {x : R⟦Γ⟧}
  statement: IsUnit x ↔ IsUnit (x.leadingCoeff)
  proof: by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      .of_mul_eq_one (i.leadingCoeff)
        ((coeff_mul_order_add_order u i).symm.trans ?_)
    rw [ui]; rw [coeff_one]; rw [if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui)]; rw [ui]; rw [order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, hx⟩
    rw [Units.val_mk] at hx
    rw [hx] at iu
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h)

中文:
定理 isUnit_iff
  条件: {x : R⟦Γ⟧}
  结论: 是单位 x ↔ 是单位 (x.leadingCoeff)
  证明: by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      .of_mul_eq_one (i.leadingCoeff)
        ((coeff_mul_order_add_order u i).symm.trans ?_)
    rw [ui]; rw [coeff_one]; rw [if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui)]; rw [ui]; rw [order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, hx⟩
    rw [Units.val_mk] at hx
    rw [hx] at iu
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h)

Depends on / 依赖: InjectiveFunction, InjectiveFunction.repr, SummableFamily, SummableFamily.one_sub_self_mul_hsum_powers, Units.val_mk, coeff_mul_order_add_order, coeff_one, i.leadingCoeff, if_pos, isUnit_of_mul_isUnit_right, leadingCoeff, left_ne_zero_of_mul_eq_one, neg_add_cancel, of_mul_eq_one, one_sub_self_mul_hsum_powers, order_mul, order_one, right_ne_zero_of_mul_eq_one, sub_sub_cancel, symm.trans
-/
theorem isUnit_iff {x : R⟦Γ⟧} : IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      .of_mul_eq_one (i.leadingCoeff)
        ((coeff_mul_order_add_order u i).symm.trans ?_)
    rw [ui]; rw [coeff_one]; rw [if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui)]; rw [ui]; rw [order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, hx⟩
    rw [Units.val_mk] at hx
    rw [hx] at iu
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h)

end IsDomain

section Field

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

@[simps -isSimp inv]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivInvMonoid R⟦Γ⟧
  body: single (-x.order) (x.leadingCoeff)⁻¹ *
      (SummableFamily.powers <| 1 - single (-x.order) (x.leadingCoeff)⁻¹ * x).hsum

@[simp]

中文:
实例 :
  签名: 除逆幺半群 R⟦Γ⟧
  定义体: single (-x.order) (x.leadingCoeff)⁻¹ *
      (SummableFamily.powers <| 1 - single (-x.order) (x.leadingCoeff)⁻¹ * x).hsum

@[simp]

Depends on / 依赖: SummableFamily, SummableFamily.powers, leadingCoeff, powers, single, x.leadingCoeff, x.order
-/
instance : DivInvMonoid R⟦Γ⟧ where
  inv x :=
    single (-x.order) (x.leadingCoeff)⁻¹ *
      (SummableFamily.powers <| 1 - single (-x.order) (x.leadingCoeff)⁻¹ * x).hsum

@[simp]
/--
theorem `inv_single` / 定理 `inv_single`

English:
theorem inv_single
  given: (a : Γ) (r : R)
  statement: (single a r)⁻¹ = single (-a) r⁻¹
  proof: by
  obtain rfl | hr := eq_or_ne r 0
  · simp [inv_def]
  · simp [inv_def, hr]

@[simp]

中文:
定理 inv_single
  条件: (a : Γ) (r : R)
  结论: (single a r)⁻¹ = single (-a) r⁻¹
  证明: by
  obtain rfl | hr := eq_or_ne r 0
  · simp [inv_def]
  · simp [inv_def, hr]

@[simp]

Depends on / 依赖: eq_or_ne, inv_def
-/
theorem inv_single (a : Γ) (r : R) : (single a r)⁻¹ = single (-a) r⁻¹ := by
  obtain rfl | hr := eq_or_ne r 0
  · simp [inv_def]
  · simp [inv_def, hr]

@[simp]
/--
theorem `single_div_single` / 定理 `single_div_single`

English:
theorem single_div_single
  given: (a b : Γ) (r s : R)
  proof: by
  rw [div_eq_mul_inv]; rw [sub_eq_add_neg]; rw [div_eq_mul_inv]; rw [inv_single]; rw [single_mul_single]

中文:
定理 single_div_single
  条件: (a b : Γ) (r s : R)
  证明: by
  rw [div_eq_mul_inv]; rw [sub_eq_add_neg]; rw [div_eq_mul_inv]; rw [inv_single]; rw [single_mul_single]

Depends on / 依赖: div_eq_mul_inv, inv_single, single_mul_single, sub_eq_add_neg
-/
theorem single_div_single (a b : Γ) (r s : R) :
    single a r / single b s = single (a - b) (r / s) := by
  rw [div_eq_mul_inv]; rw [sub_eq_add_neg]; rw [div_eq_mul_inv]; rw [inv_single]; rw [single_mul_single]

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field R⟦Γ⟧ where
  body: by simp [inv_def]
  mul_inv_cancel x x0 := by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr x0)) _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    rw [inv_def]; rw [← mul_assoc]; rw [mul_comm x]; rw [h]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext; simp [← single_zero_nnratCast, NNRat.smul_def]
  qsmul_def q x := by ext; simp [← single_zero_ratCast, Rat.smul_def]
  nnratCast_def q := by
    simp [← single_zero_nnratCast, ← single_zero_natCast, NNRat.cast_def]
  ratCast_def q := by
    simp [← single_zero_ratCast, ← single_zero_intCast, ← single_zero_natCast, Rat.cast_def]

example : (instSMul : SMul NNRat R⟦Γ⟧) = NNRat.smulDivisionSemiring := rfl
example : (instSMul : SMul Rat R⟦Γ⟧) = Rat.smulDivisionRing := rfl

中文:
实例 instField
  签名: : 域 R⟦Γ⟧ where
  定义体: by simp [inv_def]
  mul_inv_cancel x x0 := by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr x0)) _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    rw [inv_def]; rw [← mul_assoc]; rw [mul_comm x]; rw [h]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext; simp [← single_zero_nnratCast, NNRat.smul_def]
  qsmul_def q x := by ext; simp [← single_zero_ratCast, Rat.smul_def]
  nnratCast_def q := by
    simp [← single_zero_nnratCast, ← single_zero_natCast, NNRat.cast_def]
  ratCast_def q := by
    simp [← single_zero_ratCast, ← single_zero_intCast, ← single_zero_natCast, Rat.cast_def]

example : (instSMul : SMul NNRat R⟦Γ⟧) = NNRat.smulDivisionSemiring := rfl
example : (instSMul : SMul Rat R⟦Γ⟧) = Rat.smulDivisionRing := rfl

Depends on / 依赖: NNRat.smul_def, Rat.smul_def, SummableFamily, SummableFamily.one_sub_self_mul_hsum_powers, inv_def, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, mul_assoc, mul_comm, mul_inv_cancel, neg_add_cancel, nnqsmul, nnqsmul_def, nnratCast_def, one_sub_self_mul_hsum_powers, qsmul_def, single_zero_nnratCast, single_zero_ratCast, smul_def, sub_sub_cancel
-/
instance instField : Field R⟦Γ⟧ where
  inv_zero := by simp [inv_def]
  mul_inv_cancel x x0 := by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr x0)) _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    rw [inv_def]; rw [← mul_assoc]; rw [mul_comm x]; rw [h]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext; simp [← single_zero_nnratCast, NNRat.smul_def]
  qsmul_def q x := by ext; simp [← single_zero_ratCast, Rat.smul_def]
  nnratCast_def q := by
    simp [← single_zero_nnratCast, ← single_zero_natCast, NNRat.cast_def]
  ratCast_def q := by
    simp [← single_zero_ratCast, ← single_zero_intCast, ← single_zero_natCast, Rat.cast_def]

example : (instSMul : SMul NNRat R⟦Γ⟧) = NNRat.smulDivisionSemiring := rfl
example : (instSMul : SMul Rat R⟦Γ⟧) = Rat.smulDivisionRing := rfl

/--
theorem `single_zero_ofScientific` / 定理 `single_zero_ofScientific`

English:
theorem single_zero_ofScientific
  given: (m e s)
  proof: by
  simpa using single_zero_ratCast (Γ := Γ) (R := R) (OfScientific.ofScientific m e s)

中文:
定理 single_zero_ofScientific
  条件: (m e s)
  证明: by
  simpa using single_zero_ratCast (Γ := Γ) (R := R) (OfScientific.ofScientific m e s)

Depends on / 依赖: OfScientific, OfScientific.ofScientific, ofScientific, single_zero_ratCast
-/
theorem single_zero_ofScientific (m e s) :
    single (0 : Γ) (OfScientific.ofScientific m e s : R) = OfScientific.ofScientific m e s := by
  simpa using single_zero_ratCast (Γ := Γ) (R := R) (OfScientific.ofScientific m e s)

end Field

end Inversion

end HahnSeries
