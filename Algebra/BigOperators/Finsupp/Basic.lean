/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.Data.Finsupp.Indicator

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/

@[expose] public section

assert_not_exists Field

noncomputable section

open Finset Function

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
variable {t : ι -> A -> C}
variable {s : Finset α} {f : α -> ι ->₀ A} (i : ι)
variable (g : ι ->₀ A) (k : ι -> A -> γ -> B) (x : γ)
variable {β M M' N P G H R S : Type*}

namespace Finsupp

/-!
### Declarations about `Finsupp.sum` and `Finsupp.prod`

In most of this section, the domain `β` is assumed to be an `AddMonoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive /-- `sum f g` is the sum of `g a (f a)` over the support of `f`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: [Zero M] [CommMonoid N] (f : α ->₀ M) (g : α -> M -> N)
  body: ∏ a in f.support, g a (f a)

中文:
定义 乘积
  签名: [零 M] [交换幺半群 N] (f : α ->₀ M) (g : α -> M -> N)
  定义体: ∏ a in f.support, g a (f a)

Depends on / 依赖: f.support, support
-/
def prod [Zero M] [CommMonoid N] (f : α ->₀ M) (g : α -> M -> N) : N :=
  ∏ a in f.support, g a (f a)

variable [Zero M] [Zero M'] [CommMonoid N]

@[to_additive (attr := simp)]
/--
lemma `prod_fun_one` / 引理 `prod_fun_one`

English:
lemma prod_fun_one
  given: (f : α ->₀ M)
  statement: f.prod (fun _ _ => (1 : N)) = 1
  proof: by simp [prod]

@[to_additive]

中文:
引理 prod_fun_one
  条件: (f : α ->₀ M)
  结论: f.乘积 (fun _ _ => (1 : N)) = 1
  证明: by simp [prod]

@[to_additive]
-/
lemma prod_fun_one (f : α ->₀ M) : f.prod (fun _ _ => (1 : N)) = 1 := by simp [prod]

@[to_additive]
/--
theorem `prod_of_support_subset` / 定理 `prod_of_support_subset`

English:
theorem prod_of_support_subset
  statement: (f : α ->₀ M) {s : Finset α} (hs : f.support subseteq s) (g : α -> M -> N)
  proof: by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact notMem_support_iff.1 hx

@[to_additive]

中文:
定理 prod_of_support_subset
  结论: (f : α ->₀ M) {s : 有限集 α} (hs : f.support subseteq s) (g : α -> M -> N)
  证明: by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact notMem_support_iff.1 hx

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_subset, congr_arg, notMem_support_iff, prod_subset
-/
theorem prod_of_support_subset (f : α ->₀ M) {s : Finset α} (hs : f.support subseteq s) (g : α -> M -> N)
    (h : forall i in s, g i 0 = 1) : f.prod g = ∏ x in s, g x (f x) := by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact notMem_support_iff.1 hx

@[to_additive]
/--
theorem `prod_fintype` / 定理 `prod_fintype`

English:
theorem prod_fintype
  given: [Fintype α] (f : α ->₀ M) (g : α -> M -> N) (h : forall i, g i 0 = 1)
  proof: f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[to_additive (attr := simp)]

中文:
定理 prod_fintype
  条件: [有限类型 α] (f : α ->₀ M) (g : α -> M -> N) (h : 对任意 i, g i 0 = 1)
  证明: f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[to_additive (attr := simp)]

Depends on / 依赖: f.prod_of_support_subset, prod_of_support_subset, subset_univ
-/
theorem prod_fintype [Fintype α] (f : α ->₀ M) (g : α -> M -> N) (h : forall i, g i 0 = 1) :
    f.prod g = ∏ i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[to_additive (attr := simp)]
/--
theorem `prod_single_index` / 定理 `prod_single_index`

English:
theorem prod_single_index
  given: {a : α} {b : M} {h : α -> M -> N} (h_zero : h a 0 = 1)
  proof: calc
    (single a b).prod h = ∏ x in {a}, h x (single a b x) :=
      prod_of_support_subset _ support_single_subset h fun _ hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp

@[to_additive]

中文:
定理 prod_single_index
  条件: {a : α} {b : M} {h : α -> M -> N} (h_zero : h a 0 = 1)
  证明: calc
    (single a b).prod h = ∏ x in {a}, h x (single a b x) :=
      prod_of_support_subset _ support_single_subset h fun _ hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp

@[to_additive]

Depends on / 依赖: h_zero, mem_singleton, prod_of_support_subset, single, support_single_subset
-/
theorem prod_single_index {a : α} {b : M} {h : α -> M -> N} (h_zero : h a 0 = 1) :
    (single a b).prod h = h a b :=
  calc
    (single a b).prod h = ∏ x in {a}, h x (single a b x) :=
      prod_of_support_subset _ support_single_subset h fun _ hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp

@[to_additive]
/--
theorem `prod_mapRange_index` / 定理 `prod_mapRange_index`

English:
theorem prod_mapRange_index
  statement: {f : M -> M'} {hf : f 0 = 0} {g : α ->₀ M} {h : α -> M' -> N}
  proof: Finset.prod_subset support_mapRange fun _ _ H => by rw [notMem_support_iff.1 H, h0]

@[to_additive (attr := simp)]

中文:
定理 prod_mapRange_index
  结论: {f : M -> M'} {hf : f 0 = 0} {g : α ->₀ M} {h : α -> M' -> N}
  证明: Finset.prod_subset support_mapRange fun _ _ H => by rw [notMem_support_iff.1 H, h0]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_subset, notMem_support_iff, prod_subset, support_mapRange
-/
theorem prod_mapRange_index {f : M -> M'} {hf : f 0 = 0} {g : α ->₀ M} {h : α -> M' -> N}
    (h0 : forall a, h a 0 = 1) : (mapRange f hf g).prod h = g.prod fun a b => h a (f b) :=
  Finset.prod_subset support_mapRange fun _ _ H => by rw [notMem_support_iff.1 H, h0]

@[to_additive (attr := simp)]
/--
lemma `prod_onFinset` / 引理 `prod_onFinset`

English:
lemma prod_onFinset
  given: (s : Finset α) (f : α -> M) (hf) (g : α -> M -> N) (hg : forall i in s, g i 0 = 1)
  proof: prod_of_support_subset _ support_onFinset_subset _ hg

@[to_additive (attr := simp)]

中文:
引理 prod_onFinset
  条件: (s : 有限集 α) (f : α -> M) (hf) (g : α -> M -> N) (hg : 对任意 i in s, g i 0 = 1)
  证明: prod_of_support_subset _ support_onFinset_subset _ hg

@[to_additive (attr := simp)]

Depends on / 依赖: CanLift, Subalgebra, prod_of_support_subset, support_onFinset_subset
-/
lemma prod_onFinset (s : Finset α) (f : α -> M) (hf) (g : α -> M -> N) (hg : forall i in s, g i 0 = 1) :
    (onFinset s f hf).prod g = ∏ a in s, g a (f a) :=
  prod_of_support_subset _ support_onFinset_subset _ hg

@[to_additive (attr := simp)]
/--
theorem `prod_zero_index` / 定理 `prod_zero_index`

English:
theorem prod_zero_index
  given: {h : α -> M -> N}
  statement: (0 : α ->₀ M).prod h = 1
  proof: rfl

@[to_additive]

中文:
定理 prod_zero_index
  条件: {h : α -> M -> N}
  结论: (0 : α ->₀ M).乘积 h = 1
  证明: rfl

@[to_additive]
-/
theorem prod_zero_index {h : α -> M -> N} : (0 : α ->₀ M).prod h = 1 :=
  rfl

@[to_additive]
/--
theorem `prod_comm` / 定理 `prod_comm`

English:
theorem prod_comm
  given: (f : α ->₀ M) (g : β ->₀ M') (h : α -> M -> β -> M' -> N)
  proof: Finset.prod_comm

@[to_additive]

中文:
定理 prod_comm
  条件: (f : α ->₀ M) (g : β ->₀ M') (h : α -> M -> β -> M' -> N)
  证明: Finset.prod_comm

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_comm, prod_comm
-/
theorem prod_comm (f : α ->₀ M) (g : β ->₀ M') (h : α -> M -> β -> M' -> N) :
    (f.prod fun x v => g.prod fun x' v' => h x v x' v') =
      g.prod fun x' v' => f.prod fun x v => h x v x' v' :=
  Finset.prod_comm

@[to_additive]
/--
theorem `prod_finsetProd_comm` / 定理 `prod_finsetProd_comm`

English:
theorem prod_finsetProd_comm
  given: {s : Finset β} (f : α ->₀ M) (h : α -> M -> β -> N)
  proof: Finset.prod_comm

@[to_additive (attr := simp)]

中文:
定理 prod_finsetProd_comm
  条件: {s : 有限集 β} (f : α ->₀ M) (h : α -> M -> β -> N)
  证明: Finset.prod_comm

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_comm, prod_comm
-/
theorem prod_finsetProd_comm {s : Finset β} (f : α ->₀ M) (h : α -> M -> β -> N) :
    (f.prod fun a m => ∏ b in s, h a m b) = ∏ b in s, f.prod fun a m => h a m b := Finset.prod_comm

@[to_additive (attr := simp)]
/--
theorem `prod_ite_eq` / 定理 `prod_ite_eq`

English:
theorem prod_ite_eq
  given: [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N)
  proof: by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]

中文:
定理 prod_ite_eq
  条件: [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N)
  证明: by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]

Depends on / 依赖: Finsupp, Finsupp.prod, f.support.prod_ite_eq, prod_ite_eq, support
-/
theorem prod_ite_eq [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N) :
    (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a in f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]

/--
theorem `sum_ite_self_eq` / 定理 `sum_ite_self_eq`

English:
theorem sum_ite_self_eq
  given: [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α ->₀ N) (a : α)
  proof: by
  simp_all

中文:
定理 sum_ite_self_eq
  条件: [DecidableEq α] {N : 类型} [加法交换幺半群 N] (f : α ->₀ N) (a : α)
  证明: by
  simp_all
-/
theorem sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α ->₀ N) (a : α) :
    (f.sum fun x v => ite (a = x) v 0) = f a := by
  simp_all

/--
The left-hand side of `sum_ite_self_eq` simplifies; this is the variant that is useful for `simp`.
-/
@[simp]
/--
theorem `if_mem_support` / 定理 `if_mem_support`

English:
theorem if_mem_support
  given: [DecidableEq α] {N : Type*} [Zero N] (f : α ->₀ N) (a : α)
  proof: by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h => h.symm

中文:
定理 if_mem_support
  条件: [DecidableEq α] {N : 类型} [零 N] (f : α ->₀ N) (a : α)
  证明: by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h => h.symm

Depends on / 依赖: h.symm, ite_eq_left_iff, mem_support_iff, ne_eq, not_not
-/
theorem if_mem_support [DecidableEq α] {N : Type*} [Zero N] (f : α ->₀ N) (a : α) :
    (if a in f.support then f a else 0) = f a := by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h => h.symm

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[to_additive (attr := simp) /-- A restatement of `sum_ite_eq` with the equality test reversed. -/]
/--
theorem `prod_ite_eq'` / 定理 `prod_ite_eq'`

English:
theorem prod_ite_eq'
  given: [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N)
  proof: by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']

中文:
定理 prod_ite_eq'
  条件: [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N)
  证明: by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']

Depends on / 依赖: Finsupp, Finsupp.prod, f.support.prod_ite_eq, prod_ite_eq, support
-/
theorem prod_ite_eq' [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N) :
    (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a in f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']

/--
theorem `sum_ite_self_eq'` / 定理 `sum_ite_self_eq'`

English:
theorem sum_ite_self_eq'
  given: [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α ->₀ N) (a : α)
  proof: by
  simp

@[to_additive (attr := simp)]

中文:
定理 sum_ite_self_eq'
  条件: [DecidableEq α] {N : 类型} [加法交换幺半群 N] (f : α ->₀ N) (a : α)
  证明: by
  simp

@[to_additive (attr := simp)]
-/
theorem sum_ite_self_eq' [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α ->₀ N) (a : α) :
    (f.sum fun x v => ite (x = a) v 0) = f a := by
  simp

@[to_additive (attr := simp)]
/--
theorem `prod_pow` / 定理 `prod_pow`

English:
theorem prod_pow
  given: [Fintype α] (f : α ->₀ Nat) (g : α -> N)
  proof: f.prod_fintype _ fun _ => pow_zero _

@[to_additive (attr := simp)]

中文:
定理 prod_pow
  条件: [有限类型 α] (f : α ->₀ 自然数) (g : α -> N)
  证明: f.prod_fintype _ fun _ => pow_zero _

@[to_additive (attr := simp)]

Depends on / 依赖: f.prod_fintype, pow_zero, prod_fintype
-/
theorem prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ => pow_zero _

@[to_additive (attr := simp)]
/--
theorem `prod_zpow` / 定理 `prod_zpow`

English:
theorem prod_zpow
  given: {N} [DivisionCommMonoid N] [Fintype α] (f : α ->₀ Int) (g : α -> N)
  proof: f.prod_fintype _ fun _ => zpow_zero _

中文:
定理 prod_zpow
  条件: {N} [DivisionComm幺半群 N] [有限类型 α] (f : α ->₀ 整数) (g : α -> N)
  证明: f.prod_fintype _ fun _ => zpow_zero _

Depends on / 依赖: f.prod_fintype, prod_fintype, zpow_zero
-/
theorem prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α ->₀ Int) (g : α -> N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ => zpow_zero _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `onFinset` is the same as multiplying it over the original `Finset`. -/
@[to_additive
      /-- If `g` maps a second argument of 0 to 0, summing it over the
      result of `onFinset` is the same as summing it over the original `Finset`. -/]
/--
theorem `onFinset_prod` / 定理 `onFinset_prod`

English:
theorem onFinset_prod
  statement: {s : Finset α} {f : α -> M} {g : α -> M -> N} (hf : forall a, f a != 0 -> a in s)
  proof: Finset.prod_subset support_onFinset_subset by simp +contextual [*]

中文:
定理 onFinset_prod
  结论: {s : 有限集 α} {f : α -> M} {g : α -> M -> N} (hf : 对任意 a, f a != 0 -> a in s)
  证明: Finset.prod_subset support_onFinset_subset by simp +contextual [*]

Depends on / 依赖: Finset, Finset.prod_subset, contextual, prod_subset, support_onFinset_subset
-/
theorem onFinset_prod {s : Finset α} {f : α -> M} {g : α -> M -> N} (hf : forall a, f a != 0 -> a in s)
    (hg : forall a, g a 0 = 1) : (onFinset s f hf).prod g = ∏ a in s, g a (f a) :=
Finset.prod_subset support_onFinset_subset by simp +contextual [*]

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      /-- Taking a sum over `f : α →₀ M` is the same as adding the value on a
      single element `y ∈ f.support` to the sum over `erase y f`. -/]
/--
theorem `mul_prod_erase` / 定理 `mul_prod_erase`

English:
theorem mul_prod_erase
  given: (f : α ->₀ M) (y : α) (g : α -> M -> N) (hyf : y in f.support)
  proof: by
  classical
    rw [Finsupp.prod]; rw [Finsupp.prod]; rw [← Finset.mul_prod_erase _ _ hyf]; rw [Finsupp.support_erase]; rw [Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

中文:
定理 mul_prod_erase
  条件: (f : α ->₀ M) (y : α) (g : α -> M -> N) (hyf : y in f.support)
  证明: by
  classical
    rw [Finsupp.prod]; rw [Finsupp.prod]; rw [← Finset.mul_prod_erase _ _ hyf]; rw [Finsupp.support_erase]; rw [Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

Depends on / 依赖: Finset, Finset.mul_prod_erase, Finset.prod_congr, Finsupp, Finsupp.erase_ne, Finsupp.prod, Finsupp.support_erase, classical, erase_ne, mul_prod_erase, ne_of_mem_erase, prod_congr, support_erase
-/
theorem mul_prod_erase (f : α ->₀ M) (y : α) (g : α -> M -> N) (hyf : y in f.support) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    rw [Finsupp.prod]; rw [Finsupp.prod]; rw [← Finset.mul_prod_erase _ _ hyf]; rw [Finsupp.support_erase]; rw [Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

/-- Generalization of `Finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      /-- Generalization of `Finsupp.add_sum_erase`: if `g` maps a second argument of 0
      to 0, then its sum over `f : α →₀ M` is the same as adding the value on any element
      `y : α` to the sum over `erase y f`. -/]
/--
theorem `mul_prod_erase'` / 定理 `mul_prod_erase'`

English:
theorem mul_prod_erase'
  given: (f : α ->₀ M) (y : α) (g : α -> M -> N) (hg : forall i : α, g i 0 = 1)
  proof: by
  by_cases hyf : y in f.support
  · exact Finsupp.mul_prod_erase f y g hyf
  · rw [notMem_support_iff.mp hyf, hg y, erase_of_notMem_support hyf, one_mul]

@[to_additive]

中文:
定理 mul_prod_erase'
  条件: (f : α ->₀ M) (y : α) (g : α -> M -> N) (hg : 对任意 i : α, g i 0 = 1)
  证明: by
  by_cases hyf : y in f.support
  · exact Finsupp.mul_prod_erase f y g hyf
  · rw [notMem_support_iff.mp hyf, hg y, erase_of_notMem_support hyf, one_mul]

@[to_additive]

Depends on / 依赖: Finsupp, Finsupp.mul_prod_erase, erase_of_notMem_support, f.support, mul_prod_erase, notMem_support_iff, notMem_support_iff.mp, one_mul, support
-/
theorem mul_prod_erase' (f : α ->₀ M) (y : α) (g : α -> M -> N) (hg : forall i : α, g i 0 = 1) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  by_cases hyf : y in f.support
  · exact Finsupp.mul_prod_erase f y g hyf
  · rw [notMem_support_iff.mp hyf, hg y, erase_of_notMem_support hyf, one_mul]

@[to_additive]
/--
theorem `_root_.SubmonoidClass.finsuppProd_mem` / 定理 `_root_.SubmonoidClass.finsuppProd_mem`

English:
theorem _root_.SubmonoidClass.finsuppProd_mem
  statement: {S : Type*} [SetLike S N] [SubmonoidClass S N]
  proof: prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)

中文:
定理 _root_.子幺半群类.finsuppProd_mem
  结论: {S : 类型} [集合状 S N] [子幺半群类 S N]
  证明: prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff.mp, mem_support_iff, prod_mem
-/
theorem _root_.SubmonoidClass.finsuppProd_mem {S : Type*} [SetLike S N] [SubmonoidClass S N]
    (s : S) (f : α ->₀ M) (g : α -> M -> N) (h : forall c, f c != 0 -> g c (f c) in s) : f.prod g in s :=
  prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)

-- Note: Using `gcongr only` since `congr` doesn't accept this lemma.
@[to_additive (attr := gcongr only)]
/--
theorem `prod_congr` / 定理 `prod_congr`

English:
theorem prod_congr
  given: {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : forall x in f.support, g1 x (f x) = g2 x (f x))
  proof: Finset.prod_congr rfl h

中文:
定理 prod_congr
  条件: {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : 对任意 x in f.support, g1 x (f x) = g2 x (f x))
  证明: Finset.prod_congr rfl h

Depends on / 依赖: Finset, Finset.prod_congr, prod_congr
-/
theorem prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : forall x in f.support, g1 x (f x) = g2 x (f x)) :
    f.prod g1 = f.prod g2 :=
  Finset.prod_congr rfl h

/-- The product over two finsupps agree if the functions agree and are well-behaved within the
shared support. -/
@[to_additive (attr := gcongr only)
/-- The sum over two finsupps agree if the functions agree and are well-behaved within the
shared support. -/]
/--
theorem `prod_congr_of_eq_on_union` / 定理 `prod_congr_of_eq_on_union`

English:
theorem prod_congr_of_eq_on_union
  statement: [DecidableEq α] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N}
  proof: by
  rw [Finsupp.prod_of_support_subset f1 Finset.subset_union_left _ h1]; rw [Finsupp.prod_of_support_subset f2 Finset.subset_union_right _ h2]
  exact Finset.prod_congr rfl h

@[to_additive]

中文:
定理 prod_congr_of_eq_on_union
  结论: [DecidableEq α] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N}
  证明: by
  rw [Finsupp.prod_of_support_subset f1 Finset.subset_union_left _ h1]; rw [Finsupp.prod_of_support_subset f2 Finset.subset_union_right _ h2]
  exact Finset.prod_congr rfl h

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_congr, Finset.subset_union_left, Finset.subset_union_right, Finsupp, Finsupp.prod_of_support_subset, prod_congr, prod_of_support_subset, subset_union_left, subset_union_right
-/
theorem prod_congr_of_eq_on_union [DecidableEq α] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N}
    (h : forall x in f1.support union f2.support, g1 x (f1 x) = g2 x (f2 x))
    (h1 : forall x in f1.support union f2.support, g1 x 0 = 1)
    (h2 : forall x in f1.support union f2.support, g2 x 0 = 1) :
    f1.prod g1 = f2.prod g2 := by
  rw [Finsupp.prod_of_support_subset f1 Finset.subset_union_left _ h1]; rw [Finsupp.prod_of_support_subset f2 Finset.subset_union_right _ h2]
  exact Finset.prod_congr rfl h

@[to_additive]
/--
theorem `prod_eq_single` / 定理 `prod_eq_single`

English:
theorem prod_eq_single
  statement: {f : α ->₀ M} (a : α) {g : α -> M -> N}
  proof: by
  refine Finset.prod_eq_single a (fun b hb₁ hb₂ => ?_) (fun h => ?_)
  · exact h₀ b (mem_support_iff.mp hb₁) hb₂
  · simp only [notMem_support_iff] at h
    rw [h]
    exact h₁ h

@[to_additive]

中文:
定理 prod_eq_single
  结论: {f : α ->₀ M} (a : α) {g : α -> M -> N}
  证明: by
  refine Finset.prod_eq_single a (fun b hb₁ hb₂ => ?_) (fun h => ?_)
  · exact h₀ b (mem_support_iff.mp hb₁) hb₂
  · simp only [notMem_support_iff] at h
    rw [h]
    exact h₁ h

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_single, mem_support_iff, mem_support_iff.mp, notMem_support_iff, prod_eq_single
-/
theorem prod_eq_single {f : α ->₀ M} (a : α) {g : α -> M -> N}
    (h₀ : forall b, f b != 0 -> b != a -> g b (f b) = 1) (h₁ : f a = 0 -> g a 0 = 1) :
    f.prod g = g a (f a) := by
  refine Finset.prod_eq_single a (fun b hb₁ hb₂ => ?_) (fun h => ?_)
  · exact h₀ b (mem_support_iff.mp hb₁) hb₂
  · simp only [notMem_support_iff] at h
    rw [h]
    exact h₁ h

@[to_additive]
/--
lemma `prod_unique` / 引理 `prod_unique`

English:
lemma prod_unique
  given: [Unique α] {f : α ->₀ M} {g : α -> M -> N} (h₁ : f default = 0 -> g default 0 = 1)
  proof: prod_eq_single _ (fun a => by simp [Subsingleton.elim a default]) h₁

中文:
引理 prod_unique
  条件: [唯一 α] {f : α ->₀ M} {g : α -> M -> N} (h₁ : f default = 0 -> g default 0 = 1)
  证明: prod_eq_single _ (fun a => by simp [Subsingleton.elim a default]) h₁

Depends on / 依赖: Subsingleton, Subsingleton.elim, prod_eq_single
-/
lemma prod_unique [Unique α] {f : α ->₀ M} {g : α -> M -> N} (h₁ : f default = 0 -> g default 0 = 1) :
    f.prod g = g default (f default) :=
  prod_eq_single _ (fun a => by simp [Subsingleton.elim a default]) h₁

end SumProd

section CommMonoidWithZero
variable [Zero α] [CommMonoidWithZero β] [Nontrivial β] [NoZeroDivisors β]
  {f : ι ->₀ α} (a : α) {g : ι -> α -> β}

@[simp]
/--
lemma `prod_eq_zero_iff` / 引理 `prod_eq_zero_iff`

English:
lemma prod_eq_zero_iff
  statement: f.prod g = 0 ↔ exists i in f.support, g i (f i) = 0
  proof: Finset.prod_eq_zero_iff

中文:
引理 prod_eq_zero_iff
  结论: f.乘积 g = 0 ↔ 存在 i in f.support, g i (f i) = 0
  证明: Finset.prod_eq_zero_iff

Depends on / 依赖: Finset, Finset.prod_eq_zero_iff, prod_eq_zero_iff
-/
lemma prod_eq_zero_iff : f.prod g = 0 ↔ exists i in f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
/--
lemma `prod_ne_zero_iff` / 引理 `prod_ne_zero_iff`

English:
lemma prod_ne_zero_iff
  statement: f.prod g != 0 ↔ forall i in f.support, g i (f i) != 0
  proof: Finset.prod_ne_zero_iff

中文:
引理 prod_ne_zero_iff
  结论: f.乘积 g != 0 ↔ 对任意 i in f.support, g i (f i) != 0
  证明: Finset.prod_ne_zero_iff

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff, S.smul_mem, Subalgebra, Subalgebra.instSubsemiringClass, instSubsemiringClass, neg_mem, neg_one_smul, prod_ne_zero_iff, smul_mem
-/
lemma prod_ne_zero_iff : f.prod g != 0 ↔ forall i in f.support, g i (f i) != 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero
end Finsupp

@[to_additive]
/--
theorem `map_finsuppProd` / 定理 `map_finsuppProd`

English:
theorem map_finsuppProd
  statement: [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*}
  proof: map_prod h _ _

@[to_additive]

中文:
定理 map_finsuppProd
  结论: [零 M] [交换幺半群 N] [交换幺半群 P] {H : 类型}
  证明: map_prod h _ _

@[to_additive]

Depends on / 依赖: map_prod
-/
theorem map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*}
    [FunLike H N P] [MonoidHomClass H N P]
    (h : H) (f : α ->₀ M) (g : α -> M -> N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod h _ _

@[to_additive]
/--
theorem `MonoidHom.coe_finsuppProd` / 定理 `MonoidHom.coe_finsuppProd`

English:
theorem MonoidHom.coe_finsuppProd
  statement: [Zero β] [MulOneClass N] [CommMonoid P] (f : α ->₀ β)
  proof: MonoidHom.coe_finsetProd _ _

@[to_additive (attr := simp)]

中文:
定理 幺半群态射.coe_finsuppProd
  结论: [零 β] [MulOne类 N] [交换幺半群 P] (f : α ->₀ β)
  证明: MonoidHom.coe_finsetProd _ _

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.coe_finsetProd, coe_finsetProd
-/
theorem MonoidHom.coe_finsuppProd [Zero β] [MulOneClass N] [CommMonoid P] (f : α ->₀ β)
    (g : α -> β -> N ->* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi) :=
  MonoidHom.coe_finsetProd _ _

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.finsuppProd_apply` / 定理 `MonoidHom.finsuppProd_apply`

English:
theorem MonoidHom.finsuppProd_apply
  statement: [Zero β] [MulOneClass N] [CommMonoid P] (f : α ->₀ β)
  proof: MonoidHom.finsetProd_apply _ _ _

中文:
定理 幺半群态射.finsuppProd_apply
  结论: [零 β] [MulOne类 N] [交换幺半群 P] (f : α ->₀ β)
  证明: MonoidHom.finsetProd_apply _ _ _

Depends on / 依赖: MonoidHom, MonoidHom.finsetProd_apply, finsetProd_apply
-/
theorem MonoidHom.finsuppProd_apply [Zero β] [MulOneClass N] [CommMonoid P] (f : α ->₀ β)
    (g : α -> β -> N ->* P) (x : N) : f.prod g x = f.prod fun i fi => g i fi x :=
  MonoidHom.finsetProd_apply _ _ _

namespace Finsupp

/--
theorem `single_multiset_sum` / 定理 `single_multiset_sum`

English:
theorem single_multiset_sum
  given: [AddCommMonoid M] (s : Multiset M) (a : α)
  proof: Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons]; rw [single_add]; rw [ih]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]

中文:
定理 single_multiset_sum
  条件: [加法交换幺半群 M] (s : Multiset M) (a : α)
  证明: Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons]; rw [single_add]; rw [ih]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.sum_cons, induction_on, map_cons, single_add, single_zero, sum_cons
-/
theorem single_multiset_sum [AddCommMonoid M] (s : Multiset M) (a : α) :
    single a s.sum = (s.map (single a)).sum :=
  Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons]; rw [single_add]; rw [ih]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]

/--
theorem `single_finsetSum` / 定理 `single_finsetSum`

English:
theorem single_finsetSum
  given: [AddCommMonoid M] (s : Finset ι) (f : ι -> M) (a : α)
  proof: by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl

@[deprecated (since := "2026-04-08")] alias single_finset_sum := single_finsetSum

中文:
定理 single_finsetSum
  条件: [加法交换幺半群 M] (s : 有限集 ι) (f : ι -> M) (a : α)
  证明: by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl

@[deprecated (since := "2026-04-08")] alias single_finset_sum := single_finsetSum

Depends on / 依赖: Multiset, Multiset.map_map, map_map, single_multiset_sum
-/
theorem single_finsetSum [AddCommMonoid M] (s : Finset ι) (f : ι -> M) (a : α) :
    single a (∑ b in s, f b) = ∑ b in s, single a (f b) := by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl

@[deprecated (since := "2026-04-08")] alias single_finset_sum := single_finsetSum

/--
theorem `single_sum` / 定理 `single_sum`

English:
theorem single_sum
  given: [Zero M] [AddCommMonoid N] (s : ι ->₀ M) (f : ι -> M -> N) (a : α)
  proof: single_finsetSum _ _ _

@[to_additive]

中文:
定理 single_sum
  条件: [零 M] [加法交换幺半群 N] (s : ι ->₀ M) (f : ι -> M -> N) (a : α)
  证明: single_finsetSum _ _ _

@[to_additive]

Depends on / 依赖: single_finsetSum
-/
theorem single_sum [Zero M] [AddCommMonoid N] (s : ι ->₀ M) (f : ι -> M -> N) (a : α) :
    single a (s.sum f) = s.sum fun d c => single a (f d c) :=
  single_finsetSum _ _ _

@[to_additive]
/--
theorem `prod_neg_index` / 定理 `prod_neg_index`

English:
theorem prod_neg_index
  statement: [SubtractionMonoid G] [CommMonoid M] {g : α ->₀ G} {h : α -> G -> M}
  proof: prod_mapRange_index h0

中文:
定理 prod_neg_index
  结论: [Subtraction幺半群 G] [交换幺半群 M] {g : α ->₀ G} {h : α -> G -> M}
  证明: prod_mapRange_index h0

Depends on / 依赖: prod_mapRange_index
-/
theorem prod_neg_index [SubtractionMonoid G] [CommMonoid M] {g : α ->₀ G} {h : α -> G -> M}
    (h0 : forall a, h a 0 = 1) : (-g).prod h = g.prod fun a b => h a (-b) :=
  prod_mapRange_index h0

/--
theorem `finsetSum_apply` / 定理 `finsetSum_apply`

English:
theorem finsetSum_apply
  given: [AddCommMonoid N] (S : Finset ι) (f : ι -> α ->₀ N) (a : α)
  proof: map_sum (applyAddHom a) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

@[simp]

中文:
定理 finsetSum_apply
  条件: [加法交换幺半群 N] (S : 有限集 ι) (f : ι -> α ->₀ N) (a : α)
  证明: map_sum (applyAddHom a) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

@[simp]

Depends on / 依赖: applyAddHom, map_sum
-/
theorem finsetSum_apply [AddCommMonoid N] (S : Finset ι) (f : ι -> α ->₀ N) (a : α) :
    (∑ i in S, f i) a = ∑ i in S, f i a :=
  map_sum (applyAddHom a) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

@[simp]
/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} {a₂ : β}
  proof: finsetSum_apply _ _ _

中文:
定理 sum_apply
  条件: [零 M] [加法交换幺半群 N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} {a₂ : β}
  证明: finsetSum_apply _ _ _

Depends on / 依赖: finsetSum_apply
-/
theorem sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} {a₂ : β} :
    (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ :=
  finsetSum_apply _ _ _

/--
theorem `coe_finsetSum` / 定理 `coe_finsetSum`

English:
theorem coe_finsetSum
  given: [AddCommMonoid N] (S : Finset ι) (f : ι -> α ->₀ N)
  proof: map_sum (coeFnAddHom : (α ->₀ N) ->+ _) _ _

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

中文:
定理 coe_finsetSum
  条件: [加法交换幺半群 N] (S : 有限集 ι) (f : ι -> α ->₀ N)
  证明: map_sum (coeFnAddHom : (α ->₀ N) ->+ _) _ _

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum
-/
@[simp, norm_cast] theorem coe_finsetSum [AddCommMonoid N] (S : Finset ι) (f : ι -> α ->₀ N) :
    ⇑(∑ i in S, f i) = ∑ i in S, ⇑(f i) :=
  map_sum (coeFnAddHom : (α ->₀ N) ->+ _) _ _

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: [Zero M] [AddCommMonoid N] (f : α ->₀ M) (g : α -> M -> β ->₀ N)
  proof: coe_finsetSum _ _

中文:
定理 coe_sum
  条件: [零 M] [加法交换幺半群 N] (f : α ->₀ M) (g : α -> M -> β ->₀ N)
  证明: coe_finsetSum _ _
-/
@[simp, norm_cast] theorem coe_sum [Zero M] [AddCommMonoid N] (f : α ->₀ M) (g : α -> M -> β ->₀ N) :
    ⇑(f.sum g) = f.sum fun a₁ b => ⇑(g a₁ b) :=
  coe_finsetSum _ _

/--
theorem `support_sum` / 定理 `support_sum`

English:
theorem support_sum
  given: [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g : α -> M -> β ->₀ N}
  proof: by
  have : forall c, (f.sum fun a b => g a b c) != 0 -> exists a, f a != 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]

中文:
定理 support_sum
  条件: [DecidableEq β] [零 M] [加法交换幺半群 N] {f : α ->₀ M} {g : α -> M -> β ->₀ N}
  证明: by
  have : forall c, (f.sum fun a b => g a b c) != 0 -> exists a, f a != 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]

Depends on / 依赖: Finset, Finset.exists_ne_zero_of_sum_ne_zero, Finset.mem_biUnion, Finset.subset_iff, exists_ne_zero_of_sum_ne_zero, exists_prop, f.sum, mem_biUnion, mem_support_iff, mem_support_iff.mp, subset_iff, sum_apply
-/
theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} :
    (f.sum g).support subseteq f.support.biUnion fun a => (g a (f a)).support := by
  have : forall c, (f.sum fun a b => g a b c) != 0 -> exists a, f a != 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]

/--
theorem `support_finsetSum` / 定理 `support_finsetSum`

English:
theorem support_finsetSum
  given: [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α -> β ->₀ M}
  proof: by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons _ _ _ ih =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

@[deprecated (since := "2026-04-08")] alias support_finset_sum := support_finsetSum

中文:
定理 support_finsetSum
  条件: [DecidableEq β] [加法交换幺半群 M] {s : 有限集 α} {f : α -> β ->₀ M}
  证明: by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons _ _ _ ih =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

@[deprecated (since := "2026-04-08")] alias support_finset_sum := support_finsetSum

Depends on / 依赖: Finset, Finset.Subset.refl, Finset.cons_induction_on, Finset.sum_cons, Finset.sup_cons, Finset.sup_eq_biUnion, Finset.union_subset_union, Subset, cons_induction_on, sum_cons, sup_cons, sup_eq_biUnion, support_add, support_add.trans, union_subset_union
-/
theorem support_finsetSum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α -> β ->₀ M} :
    (Finset.sum s f).support subseteq s.biUnion fun x => (f x).support := by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons _ _ _ ih =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

@[deprecated (since := "2026-04-08")] alias support_finset_sum := support_finsetSum

/--
theorem `sum_eq_one_iff` / 定理 `sum_eq_one_iff`

English:
theorem sum_eq_one_iff
  given: (d : α ->₀ Nat)
  statement: sum d (fun _ n => n) = 1 ↔ exists a, d = single a 1
  proof: by
  classical
  refine ⟨fun h1 => ?_, ?_⟩
  · have hd0 : d != 0 := (by simp [·] at h1)
    obtain ⟨a, ha⟩ := ne_iff.mp hd0
    obtain ⟨hda, hda'⟩ : d a = 1 ∧ forall i != a, d i = 0 := by
      rw [← add_sum_erase' _ a _ (fun _ => rfl)]; rw [Nat.add_eq_one_iff]; rw [or_iff_not_imp_left] at h1
      simp_all +contextual [sum, support_erase, sum_eq_zero_iff, mem_erase, erase_ne]
    use a
    ext b
    by_cases hb : b = a
    · rw [hb, single_eq_same, hda]
    · simpa only [single_eq_of_ne hb] using hda' b hb
  · rintro ⟨a, rfl⟩
    rw [sum_eq_single a ?_ (fun _ => rfl)]; rw [single_eq_same]
    exact fun _ _ hba => single_eq_of_ne hba

@[to_additive (attr := simp)]

中文:
定理 sum_eq_one_iff
  条件: (d : α ->₀ 自然数)
  结论: 求和 d (fun _ n => n) = 1 ↔ 存在 a, d = single a 1
  证明: by
  classical
  refine ⟨fun h1 => ?_, ?_⟩
  · have hd0 : d != 0 := (by simp [·] at h1)
    obtain ⟨a, ha⟩ := ne_iff.mp hd0
    obtain ⟨hda, hda'⟩ : d a = 1 ∧ forall i != a, d i = 0 := by
      rw [← add_sum_erase' _ a _ (fun _ => rfl)]; rw [Nat.add_eq_one_iff]; rw [or_iff_not_imp_left] at h1
      simp_all +contextual [sum, support_erase, sum_eq_zero_iff, mem_erase, erase_ne]
    use a
    ext b
    by_cases hb : b = a
    · rw [hb, single_eq_same, hda]
    · simpa only [single_eq_of_ne hb] using hda' b hb
  · rintro ⟨a, rfl⟩
    rw [sum_eq_single a ?_ (fun _ => rfl)]; rw [single_eq_same]
    exact fun _ _ hba => single_eq_of_ne hba

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.add_eq_one_iff, add_eq_one_iff, add_sum_erase, classical, contextual, erase_ne, mem_erase, ne_iff, ne_iff.mp, or_iff_not_imp_left, single_eq_of_ne, single_eq_same, sum_eq_sing, sum_eq_zero_iff, support_erase
-/
theorem sum_eq_one_iff (d : α ->₀ Nat) : sum d (fun _ n => n) = 1 ↔ exists a, d = single a 1 := by
  classical
  refine ⟨fun h1 => ?_, ?_⟩
  · have hd0 : d != 0 := (by simp [·] at h1)
    obtain ⟨a, ha⟩ := ne_iff.mp hd0
    obtain ⟨hda, hda'⟩ : d a = 1 ∧ forall i != a, d i = 0 := by
      rw [← add_sum_erase' _ a _ (fun _ => rfl)]; rw [Nat.add_eq_one_iff]; rw [or_iff_not_imp_left] at h1
      simp_all +contextual [sum, support_erase, sum_eq_zero_iff, mem_erase, erase_ne]
    use a
    ext b
    by_cases hb : b = a
    · rw [hb, single_eq_same, hda]
    · simpa only [single_eq_of_ne hb] using hda' b hb
  · rintro ⟨a, rfl⟩
    rw [sum_eq_single a ?_ (fun _ => rfl)]; rw [single_eq_same]
    exact fun _ _ hba => single_eq_of_ne hba

@[to_additive (attr := simp)]
/--
theorem `prod_mul` / 定理 `prod_mul`

English:
theorem prod_mul
  given: [Zero M] [CommMonoid N] {f : α ->₀ M} {h₁ h₂ : α -> M -> N}
  proof: Finset.prod_mul_distrib

@[to_additive (attr := simp)]

中文:
定理 prod_mul
  条件: [零 M] [交换幺半群 N] {f : α ->₀ M} {h₁ h₂ : α -> M -> N}
  证明: Finset.prod_mul_distrib

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_mul_distrib, prod_mul_distrib
-/
theorem prod_mul [Zero M] [CommMonoid N] {f : α ->₀ M} {h₁ h₂ : α -> M -> N} :
    (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
/--
theorem `prod_inv` / 定理 `prod_inv`

English:
theorem prod_inv
  given: [Zero M] [CommGroup G] {f : α ->₀ M} {h : α -> M -> G}
  proof: (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]

中文:
定理 prod_inv
  条件: [零 M] [交换群 G] {f : α ->₀ M} {h : α -> M -> G}
  证明: (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]

Depends on / 依赖: IsScalarTower, Module, MonoidHom, MonoidHom.id, Semiring, map_prod, module
-/
theorem prod_inv [Zero M] [CommGroup G] {f : α ->₀ M} {h : α -> M -> G} :
    (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]
/--
theorem `sum_sub` / 定理 `sum_sub`

English:
theorem sum_sub
  given: [Zero M] [SubtractionCommMonoid G] {f : α ->₀ M} {h₁ h₂ : α -> M -> G}
  proof: Finset.sum_sub_distrib ..

中文:
定理 sum_sub
  条件: [零 M] [SubtractionComm幺半群 G] {f : α ->₀ M} {h₁ h₂ : α -> M -> G}
  证明: Finset.sum_sub_distrib ..

Depends on / 依赖: Finset, Finset.sum_sub_distrib, sum_sub_distrib
-/
theorem sum_sub [Zero M] [SubtractionCommMonoid G] {f : α ->₀ M} {h₁ h₂ : α -> M -> G} :
    (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
  Finset.sum_sub_distrib ..

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `Finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive
      /-- Taking the product under `h` is an additive homomorphism of finsupps, if `h` is an
      additive homomorphism on the support. This is a more general version of
      `Finsupp.sum_add_index'`; the latter has simpler hypotheses. -/]
/--
theorem `prod_add_index` / 定理 `prod_add_index`

English:
theorem prod_add_index
  statement: [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M}
  proof: by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero]; rw [Finsupp.prod_of_support_subset g subset_union_right h h_zero]; rw [←
    Finset.prod_mul_distrib]; rw [Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

中文:
定理 prod_add_index
  结论: [DecidableEq α] [加法零类 M] [交换幺半群 N] {f g : α ->₀ M}
  证明: by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero]; rw [Finsupp.prod_of_support_subset g subset_union_right h h_zero]; rw [←
    Finset.prod_mul_distrib]; rw [Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_mul_distrib, Finsupp, Finsupp.prod_of_support_subset, Finsupp.support_add, h_add, h_zero, prod_congr, prod_mul_distrib, prod_of_support_subset, subset_union_left, subset_union_right, support_add
-/
theorem prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M}
    {h : α -> M -> N} (h_zero : forall a in f.support union g.support, h a 0 = 1)
    (h_add : forall a in f.support union g.support, forall (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero]; rw [Finsupp.prod_of_support_subset g subset_union_right h h_zero]; rw [←
    Finset.prod_mul_distrib]; rw [Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `Finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      /-- Taking the sum under `h` is an additive homomorphism of finsupps,if `h` is an additive
      homomorphism. This is a more specific version of `Finsupp.sum_add_index` with simpler
      hypotheses. -/]
/--
theorem `prod_add_index'` / 定理 `prod_add_index'`

English:
theorem prod_add_index'
  statement: [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M} {h : α -> M -> N}
  proof: by
  classical exact prod_add_index (fun a _ => h_zero a) fun a _ => h_add a

@[simp]

中文:
定理 prod_add_index'
  结论: [加法零类 M] [交换幺半群 N] {f g : α ->₀ M} {h : α -> M -> N}
  证明: by
  classical exact prod_add_index (fun a _ => h_zero a) fun a _ => h_add a

@[simp]

Depends on / 依赖: Algebra, CommSemiring, algebra, classical, h_add, h_zero, prod_add_index
-/
theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M} {h : α -> M -> N}
    (h_zero : forall a, h a 0 = 1) (h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  classical exact prod_add_index (fun a _ => h_zero a) fun a _ => h_add a

@[simp]
/--
theorem `sum_hom_add_index` / 定理 `sum_hom_add_index`

English:
theorem sum_hom_add_index
  given: [AddZeroClass M] [AddCommMonoid N] {f g : α ->₀ M} (h : α -> M ->+ N)
  proof: sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]

中文:
定理 sum_hom_add_index
  条件: [加法零类 M] [加法交换幺半群 N] {f g : α ->₀ M} (h : α -> M ->+ N)
  证明: sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]

Depends on / 依赖: map_add, map_zero, sum_add_index
-/
theorem sum_hom_add_index [AddZeroClass M] [AddCommMonoid N] {f g : α ->₀ M} (h : α -> M ->+ N) :
    ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]
/--
theorem `prod_hom_add_index` / 定理 `prod_hom_add_index`

English:
theorem prod_hom_add_index
  statement: [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M}
  proof: prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

中文:
定理 prod_hom_add_index
  结论: [加法零类 M] [交换幺半群 N] {f g : α ->₀ M}
  证明: prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

Depends on / 依赖: map_mul, map_one, prod_add_index
-/
theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M}
    (h : α -> Multiplicative M ->* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

/--
Definition of `liftAddHom` / `liftAddHom` 的定义

English:
definition liftAddHom
  signature: [AddZeroClass M] [AddCommMonoid N]
  body: { toFun f := f.sum (F ·)
      map_zero' := Finsupp.sum_zero_index
      map_add' f g := Finsupp.sum_hom_add_index F }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by ext; simp
  right_inv F := by ext; simp
  map_add' F G := by ext; simp

@[simp]

中文:
定义 liftAddHom
  签名: [加法零类 M] [加法交换幺半群 N]
  定义体: { toFun f := f.sum (F ·)
      map_zero' := Finsupp.sum_zero_index
      map_add' f g := Finsupp.sum_hom_add_index F }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by ext; simp
  right_inv F := by ext; simp
  map_add' F G := by ext; simp

@[simp]

Depends on / 依赖: F.comp, Finsupp, Finsupp.sum_hom_add_index, Finsupp.sum_zero_index, f.sum, invFun, left_inv, map_add, map_zero, right_inv, singleAddHom, sum_hom_add_index, sum_zero_index
-/
def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α -> M ->+ N) ≃+ ((α ->₀ M) ->+ N) where
  toFun F :=
    { toFun f := f.sum (F ·)
      map_zero' := Finsupp.sum_zero_index
      map_add' f g := Finsupp.sum_hom_add_index F }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by ext; simp
  right_inv F := by ext; simp
  map_add' F G := by ext; simp

@[simp]
/--
theorem `liftAddHom_apply` / 定理 `liftAddHom_apply`

English:
theorem liftAddHom_apply
  given: [AddZeroClass M] [AddCommMonoid N] (F : α -> M ->+ N) (f : α ->₀ M)
  proof: rfl

@[simp]

中文:
定理 liftAddHom_apply
  条件: [加法零类 M] [加法交换幺半群 N] (F : α -> M ->+ N) (f : α ->₀ M)
  证明: rfl

@[simp]

Depends on / 依赖: f.sum
-/
theorem liftAddHom_apply [AddZeroClass M] [AddCommMonoid N] (F : α -> M ->+ N) (f : α ->₀ M) :
    (liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x :=
  rfl

@[simp]
/--
theorem `liftAddHom_symm_apply` / 定理 `liftAddHom_symm_apply`

English:
theorem liftAddHom_symm_apply
  given: [AddZeroClass M] [AddCommMonoid N] (F : (α ->₀ M) ->+ N) (x : α)
  proof: rfl

中文:
定理 liftAddHom_symm_apply
  条件: [加法零类 M] [加法交换幺半群 N] (F : (α ->₀ M) ->+ N) (x : α)
  证明: rfl

Depends on / 依赖: F.comp, singleAddHom
-/
theorem liftAddHom_symm_apply [AddZeroClass M] [AddCommMonoid N] (F : (α ->₀ M) ->+ N) (x : α) :
    (liftAddHom (α := α) (M := M) (N := N)).symm F x = F.comp (singleAddHom x) :=
  rfl

/--
theorem `liftAddHom_symm_apply_apply` / 定理 `liftAddHom_symm_apply_apply`

English:
theorem liftAddHom_symm_apply_apply
  statement: [AddZeroClass M] [AddCommMonoid N] (F : (α ->₀ M) ->+ N) (x : α)
  proof: rfl

@[simp]

中文:
定理 liftAddHom_symm_apply_apply
  结论: [加法零类 M] [加法交换幺半群 N] (F : (α ->₀ M) ->+ N) (x : α)
  证明: rfl

@[simp]

Depends on / 依赖: single
-/
theorem liftAddHom_symm_apply_apply [AddZeroClass M] [AddCommMonoid N] (F : (α ->₀ M) ->+ N) (x : α)
    (y : M) : (liftAddHom (α := α) (M := M) (N := N)).symm F x y = F (single x y) :=
  rfl

@[simp]
/--
theorem `liftAddHom_singleAddHom` / 定理 `liftAddHom_singleAddHom`

English:
theorem liftAddHom_singleAddHom
  given: [AddCommMonoid M]
  proof: liftAddHom.toEquiv.eq_symm_apply.1 rfl

@[simp]

中文:
定理 liftAddHom_singleAddHom
  条件: [加法交换幺半群 M]
  证明: liftAddHom.toEquiv.eq_symm_apply.1 rfl

@[simp]

Depends on / 依赖: singleAddHom
-/
theorem liftAddHom_singleAddHom [AddCommMonoid M] :
    (liftAddHom (α := α) (M := M) (N := α ->₀ M)) (singleAddHom : α -> M ->+ α ->₀ M) =
      AddMonoidHom.id _ :=
  liftAddHom.toEquiv.eq_symm_apply.1 rfl

@[simp]
/--
theorem `sum_single` / 定理 `sum_single`

English:
theorem sum_single
  given: [AddCommMonoid M] (f : α ->₀ M)
  statement: f.sum single = f
  proof: DFunLike.congr_fun liftAddHom_singleAddHom f

中文:
定理 sum_single
  条件: [加法交换幺半群 M] (f : α ->₀ M)
  结论: f.求和 single = f
  证明: DFunLike.congr_fun liftAddHom_singleAddHom f

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, liftAddHom_singleAddHom
-/
theorem sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum single = f :=
  DFunLike.congr_fun liftAddHom_singleAddHom f

/-- The `Finsupp` version of `Finset.univ_sum_single` -/
@[simp]
/--
theorem `univ_sum_single` / 定理 `univ_sum_single`

English:
theorem univ_sum_single
  given: [Fintype α] [AddCommMonoid M] (f : α ->₀ M)
  proof: by
  classical
  refine DFunLike.coe_injective ?_
  simp_rw [coe_finsetSum, single_eq_pi_single, Finset.univ_sum_single]

@[simp]

中文:
定理 univ_sum_single
  条件: [有限类型 α] [加法交换幺半群 M] (f : α ->₀ M)
  证明: by
  classical
  refine DFunLike.coe_injective ?_
  simp_rw [coe_finsetSum, single_eq_pi_single, Finset.univ_sum_single]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finset, Finset.univ_sum_single, classical, coe_finsetSum, coe_injective, simp_rw, single_eq_pi_single, univ_sum_single
-/
theorem univ_sum_single [Fintype α] [AddCommMonoid M] (f : α ->₀ M) :
    ∑ a : α, single a (f a) = f := by
  classical
  refine DFunLike.coe_injective ?_
  simp_rw [coe_finsetSum, single_eq_pi_single, Finset.univ_sum_single]

@[simp]
/--
theorem `univ_sum_single_apply` / 定理 `univ_sum_single_apply`

English:
theorem univ_sum_single_apply
  given: [AddCommMonoid M] [Fintype α] (i : α) (m : M)
  proof: by
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp

@[simp]

中文:
定理 univ_sum_single_apply
  条件: [加法交换幺半群 M] [有限类型 α] (i : α) (m : M)
  证明: by
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp

@[simp]

Depends on / 依赖: Finset, Finset.sum_pi_single, classical, coe_mk, single, sum_pi_single
-/
theorem univ_sum_single_apply [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single i m j = m := by
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp

@[simp]
/--
theorem `univ_sum_single_apply'` / 定理 `univ_sum_single_apply'`

English:
theorem univ_sum_single_apply'
  given: [AddCommMonoid M] [Fintype α] (i : α) (m : M)
  proof: by
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp

中文:
定理 univ_sum_single_apply'
  条件: [加法交换幺半群 M] [有限类型 α] (i : α) (m : M)
  证明: by
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp

Depends on / 依赖: Finset, Finset.sum_pi_single, classical, coe_mk, simp_rw, single, sum_pi_single
-/
theorem univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single j m i = m := by
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp

/--
lemma `sum_single_add_single` / 引理 `sum_single_add_single`

English:
lemma sum_single_add_single
  statement: (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι -> A -> B) (H : f₁ != f₂)
  proof: by
  classical
  simp [sum_of_support_subset _ support_single_add_single_subset, single_apply, H, HF, H.symm]

中文:
引理 sum_single_add_single
  结论: (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι -> A -> B) (H : f₁ != f₂)
  证明: by
  classical
  simp [sum_of_support_subset _ support_single_add_single_subset, single_apply, H, HF, H.symm]

Depends on / 依赖: H.symm, classical, single_apply, sum_of_support_subset, support_single_add_single_subset
-/
lemma sum_single_add_single (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι -> A -> B) (H : f₁ != f₂)
    (HF : forall f, F f 0 = 0) :
    sum (single f₁ g₁ + single f₂ g₂) F = F f₁ g₁ + F f₂ g₂ := by
  classical
  simp [sum_of_support_subset _ support_single_add_single_subset, single_apply, H, HF, H.symm]

/--
theorem `equivFunOnFinite_symm_eq_sum` / 定理 `equivFunOnFinite_symm_eq_sum`

English:
theorem equivFunOnFinite_symm_eq_sum
  given: [Fintype α] [AddCommMonoid M] (f : α -> M)
  proof: (univ_sum_single _).symm

中文:
定理 equivFunOnFinite_symm_eq_sum
  条件: [有限类型 α] [加法交换幺半群 M] (f : α -> M)
  证明: (univ_sum_single _).symm

Depends on / 依赖: univ_sum_single
-/
theorem equivFunOnFinite_symm_eq_sum [Fintype α] [AddCommMonoid M] (f : α -> M) :
    equivFunOnFinite.symm f = ∑ a, single a (f a) :=
  (univ_sum_single _).symm

/--
theorem `coe_univ_sum_single` / 定理 `coe_univ_sum_single`

English:
theorem coe_univ_sum_single
  given: [Fintype α] [AddCommMonoid M] (f : α -> M)
  proof: congrArg _ (equivFunOnFinite_symm_eq_sum f).symm

中文:
定理 coe_univ_sum_single
  条件: [有限类型 α] [加法交换幺半群 M] (f : α -> M)
  证明: congrArg _ (equivFunOnFinite_symm_eq_sum f).symm

Depends on / 依赖: equivFunOnFinite_symm_eq_sum
-/
theorem coe_univ_sum_single [Fintype α] [AddCommMonoid M] (f : α -> M) :
    ⇑(∑ a : α, single a (f a)) = f :=
  congrArg _ (equivFunOnFinite_symm_eq_sum f).symm

/--
theorem `equivFunOnFinite_symm_sum` / 定理 `equivFunOnFinite_symm_sum`

English:
theorem equivFunOnFinite_symm_sum
  given: [Fintype α] [AddCommMonoid M] (f : α -> M)
  proof: by
  rw [equivFunOnFinite_symm_eq_sum]; rw [sum_fintype _ _ fun _ => rfl]; rw [coe_univ_sum_single]

中文:
定理 equivFunOnFinite_symm_sum
  条件: [有限类型 α] [加法交换幺半群 M] (f : α -> M)
  证明: by
  rw [equivFunOnFinite_symm_eq_sum]; rw [sum_fintype _ _ fun _ => rfl]; rw [coe_univ_sum_single]

Depends on / 依赖: coe_univ_sum_single, equivFunOnFinite_symm_eq_sum, sum_fintype
-/
theorem equivFunOnFinite_symm_sum [Fintype α] [AddCommMonoid M] (f : α -> M) :
    ((equivFunOnFinite.symm f).sum fun _ n => n) = ∑ a, f a := by
  rw [equivFunOnFinite_symm_eq_sum]; rw [sum_fintype _ _ fun _ => rfl]; rw [coe_univ_sum_single]

/--
theorem `liftAddHom_apply_single` / 定理 `liftAddHom_apply_single`

English:
theorem liftAddHom_apply_single
  statement: [AddZeroClass M] [AddCommMonoid N] (f : α -> M ->+ N) (a : α)
  proof: sum_single_index (f a).map_zero

@[simp]

中文:
定理 liftAddHom_apply_single
  结论: [加法零类 M] [加法交换幺半群 N] (f : α -> M ->+ N) (a : α)
  证明: sum_single_index (f a).map_zero

@[simp]

Depends on / 依赖: single
-/
theorem liftAddHom_apply_single [AddZeroClass M] [AddCommMonoid N] (f : α -> M ->+ N) (a : α)
    (b : M) : (liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
/--
theorem `liftAddHom_comp_single` / 定理 `liftAddHom_comp_single`

English:
theorem liftAddHom_comp_single
  given: [AddZeroClass M] [AddCommMonoid N] (f : α -> M ->+ N) (a : α)
  proof: AddMonoidHom.ext fun b => liftAddHom_apply_single f a b

中文:
定理 liftAddHom_comp_single
  条件: [加法零类 M] [加法交换幺半群 N] (f : α -> M ->+ N) (a : α)
  证明: AddMonoidHom.ext fun b => liftAddHom_apply_single f a b

Depends on / 依赖: singleAddHom
-/
theorem liftAddHom_comp_single [AddZeroClass M] [AddCommMonoid N] (f : α -> M ->+ N) (a : α) :
    ((liftAddHom (α := α) (M := M) (N := N)) f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => liftAddHom_apply_single f a b

/--
theorem `comp_liftAddHom` / 定理 `comp_liftAddHom`

English:
theorem comp_liftAddHom
  statement: [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : N ->+ P)
  proof: liftAddHom.symm_apply_eq.1
    funext fun a => by
      rw [liftAddHom_symm_apply]; rw [AddMonoidHom.comp_assoc]; rw [liftAddHom_comp_single]

中文:
定理 comp_liftAddHom
  结论: [加法零类 M] [加法交换幺半群 N] [加法交换幺半群 P] (g : N ->+ P)
  证明: liftAddHom.symm_apply_eq.1
    funext fun a => by
      rw [liftAddHom_symm_apply]; rw [AddMonoidHom.comp_assoc]; rw [liftAddHom_comp_single]
-/
theorem comp_liftAddHom [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : N ->+ P)
    (f : α -> M ->+ N) :
    g.comp ((liftAddHom (α := α) (M := M) (N := N)) f) =
      (liftAddHom (α := α) (M := M) (N := P)) fun a => g.comp (f a) :=
liftAddHom.symm_apply_eq.1
    funext fun a => by
      rw [liftAddHom_symm_apply]; rw [AddMonoidHom.comp_assoc]; rw [liftAddHom_comp_single]

/--
theorem `sum_sub_index` / 定理 `sum_sub_index`

English:
theorem sum_sub_index
  statement: [AddGroup β] [AddCommGroup γ] {f g : α ->₀ β} {h : α -> β -> γ}
  proof: ((liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]

中文:
定理 sum_sub_index
  结论: [加法群 β] [加法交换群 γ] {f g : α ->₀ β} {h : α -> β -> γ}
  证明: ((liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ofMapSub, h_sub, liftAddHom, map_sub, ofMapSub
-/
theorem sum_sub_index [AddGroup β] [AddCommGroup γ] {f g : α ->₀ β} {h : α -> β -> γ}
    (h_sub : forall a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h :=
  ((liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]
/--
theorem `prod_embDomain` / 定理 `prod_embDomain`

English:
theorem prod_embDomain
  given: [Zero M] [CommMonoid N] {v : α ->₀ M} {f : α ↪ β} {g : β -> M -> N}
  proof: by
  rw [prod]; rw [prod]; rw [support_embDomain]; rw [Finset.prod_map]
  simp_rw [embDomain_apply_self]

@[to_additive]

中文:
定理 prod_embDomain
  条件: [零 M] [交换幺半群 N] {v : α ->₀ M} {f : α ↪ β} {g : β -> M -> N}
  证明: by
  rw [prod]; rw [prod]; rw [support_embDomain]; rw [Finset.prod_map]
  simp_rw [embDomain_apply_self]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_map, embDomain_apply_self, prod_map, simp_rw, support_embDomain
-/
theorem prod_embDomain [Zero M] [CommMonoid N] {v : α ->₀ M} {f : α ↪ β} {g : β -> M -> N} :
    (v.embDomain f).prod g = v.prod fun a b => g (f a) b := by
  rw [prod]; rw [prod]; rw [support_embDomain]; rw [Finset.prod_map]
  simp_rw [embDomain_apply_self]

@[to_additive]
/--
theorem `prod_finsetSum_index` / 定理 `prod_finsetSum_index`

English:
theorem prod_finsetSum_index
  statement: [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι -> α ->₀ M}
  proof: Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons]; rw [ih]; rw [sum_cons]; rw [prod_add_index' h_zero h_add]

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]

中文:
定理 prod_finsetSum_index
  结论: [加法交换幺半群 M] [交换幺半群 N] {s : 有限集 ι} {g : ι -> α ->₀ M}
  证明: Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons]; rw [ih]; rw [sum_cons]; rw [prod_add_index' h_zero h_add]

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction_on, cons_induction_on, h_add, h_zero, prod_add_index, prod_cons, sum_cons
-/
theorem prod_finsetSum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι -> α ->₀ M}
    {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i in s, (g i).prod h) = (∑ i in s, g i).prod h :=
  Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons]; rw [ih]; rw [sum_cons]; rw [prod_add_index' h_zero h_add]

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]
/--
theorem `prod_sum_index` / 定理 `prod_sum_index`

English:
theorem prod_sum_index
  statement: [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α ->₀ M}
  proof: (prod_finsetSum_index h_zero h_add).symm

中文:
定理 prod_sum_index
  结论: [零 M] [加法交换幺半群 N] [交换幺半群 P] {f : α ->₀ M}
  证明: (prod_finsetSum_index h_zero h_add).symm

Depends on / 依赖: h_add, h_zero, prod_finsetSum_index
-/
theorem prod_sum_index [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α ->₀ M}
    {g : α -> M -> β ->₀ N} {h : β -> N -> P} (h_zero : forall a, h a 0 = 1)
    (h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h :=
  (prod_finsetSum_index h_zero h_add).symm

/--
theorem `multiset_sum_sum_index` / 定理 `multiset_sum_sum_index`

English:
theorem multiset_sum_sum_index
  statement: [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (α ->₀ M))
  proof: Multiset.induction_on f rfl fun a s ih => by
    rw [Multiset.sum_cons]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]; rw [sum_add_index' h₀ h₁]; rw [ih]

中文:
定理 multiset_sum_sum_index
  结论: [加法交换幺半群 M] [加法交换幺半群 N] (f : Multiset (α ->₀ M))
  证明: Multiset.induction_on f rfl fun a s ih => by
    rw [Multiset.sum_cons]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]; rw [sum_add_index' h₀ h₁]; rw [ih]

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_cons, Multiset.sum_cons, induction_on, map_cons, sum_add_index, sum_cons
-/
theorem multiset_sum_sum_index [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (α ->₀ M))
    (h : α -> M -> N) (h₀ : forall a, h a 0 = 0)
    (h₁ : forall (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.sum.sum h = (f.map fun g : α ->₀ M => g.sum h).sum :=
  Multiset.induction_on f rfl fun a s ih => by
    rw [Multiset.sum_cons]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]; rw [sum_add_index' h₀ h₁]; rw [ih]

/--
theorem `support_sum_eq_biUnion` / 定理 `support_sum_eq_biUnion`

English:
theorem support_sum_eq_biUnion
  statement: {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
  proof: by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq]; rw [hs]
    rw [hs]; rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm

中文:
定理 support_sum_eq_biUnion
  结论: {α : 类型} {ι : 类型} {M : 类型} [DecidableEq α]
  证明: by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq]; rw [hs]
    rw [hs]; rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm

Depends on / 依赖: Finset, Finset.disjoint_biUnion_right, Finset.induction_on, Finsupp, Finsupp.support_add_eq, biUnion_insert, classical, disjoint_biUnion_right, induction_on, ne_of_mem_of_not_mem, not_false_iff, sum_insert, support_add_eq
-/
theorem support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
    [AddCommMonoid M] {g : ι -> α ->₀ M} (s : Finset ι)
    (h : forall i₁ i₂, i₁ != i₂ -> Disjoint (g i₁).support (g i₂).support) :
    (∑ i in s, g i).support = s.biUnion fun i => (g i).support := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq]; rw [hs]
    rw [hs]; rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm

/--
theorem `multiset_map_sum` / 定理 `multiset_map_sum`

English:
theorem multiset_map_sum
  given: [Zero M] {f : α ->₀ M} {m : β -> γ} {h : α -> M -> Multiset β}
  proof: map_sum (Multiset.mapAddMonoidHom m) _ f.support

中文:
定理 multiset_map_sum
  条件: [零 M] {f : α ->₀ M} {m : β -> γ} {h : α -> M -> Multiset β}
  证明: map_sum (Multiset.mapAddMonoidHom m) _ f.support

Depends on / 依赖: Algebra, Multiset, Multiset.mapAddMonoidHom, f.support, mapAddMonoidHom, map_sum, support, toAlgebra
-/
theorem multiset_map_sum [Zero M] {f : α ->₀ M} {m : β -> γ} {h : α -> M -> Multiset β} :
    Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m :=
  map_sum (Multiset.mapAddMonoidHom m) _ f.support

/--
theorem `multiset_sum_sum` / 定理 `multiset_sum_sum`

English:
theorem multiset_sum_sum
  given: [Zero M] [AddCommMonoid N] {f : α ->₀ M} {h : α -> M -> Multiset N}
  proof: map_sum Multiset.sumAddMonoidHom _ f.support

中文:
定理 multiset_sum_sum
  条件: [零 M] [加法交换幺半群 N] {f : α ->₀ M} {h : α -> M -> Multiset N}
  证明: map_sum Multiset.sumAddMonoidHom _ f.support

Depends on / 依赖: Multiset, Multiset.sumAddMonoidHom, f.support, map_sum, sumAddMonoidHom, support
-/
theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α ->₀ M} {h : α -> M -> Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) :=
  map_sum Multiset.sumAddMonoidHom _ f.support

/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive
      /-- For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`
      over `f1` and `f2` equals the sum of `g` over `f1 + f2` -/]
/--
theorem `prod_add_index_of_disjoint` / 定理 `prod_add_index_of_disjoint`

English:
theorem prod_add_index_of_disjoint
  statement: [AddCommMonoid M] {f1 f2 : α ->₀ M}
  proof: by
  have :
    forall {f1 f2 : α ->₀ M},
      Disjoint f1.support f2.support -> (∏ x in f1.support, g x (f1 x + f2 x)) = f1.prod g :=
    fun hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [notMem_support_iff.mp (disjoint_left.mp hd hx), add_zero]
  classical simp_rw [← this hd, ← this hd.symm, add_comm (f2 _), Finsupp.prod, support_add_eq hd,
      prod_union hd, add_apply]

中文:
定理 prod_add_index_of_disjoint
  结论: [加法交换幺半群 M] {f1 f2 : α ->₀ M}
  证明: by
  have :
    forall {f1 f2 : α ->₀ M},
      Disjoint f1.support f2.support -> (∏ x in f1.support, g x (f1 x + f2 x)) = f1.prod g :=
    fun hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [notMem_support_iff.mp (disjoint_left.mp hd hx), add_zero]
  classical simp_rw [← this hd, ← this hd.symm, add_comm (f2 _), Finsupp.prod, support_add_eq hd,
      prod_union hd, add_apply]

Depends on / 依赖: Disjoint, Finset, Finset.prod_congr, Finsupp, Finsupp.prod, add_apply, add_comm, add_zero, classical, disjoint_left, disjoint_left.mp, f1.prod, f1.support, f2.support, hd.symm, notMem_support_iff, notMem_support_iff.mp, prod_congr, prod_union, simp_rw
-/
theorem prod_add_index_of_disjoint [AddCommMonoid M] {f1 f2 : α ->₀ M}
    (hd : Disjoint f1.support f2.support) {β : Type*} [CommMonoid β] (g : α -> M -> β) :
    (f1 + f2).prod g = f1.prod g * f2.prod g := by
  have :
    forall {f1 f2 : α ->₀ M},
      Disjoint f1.support f2.support -> (∏ x in f1.support, g x (f1 x + f2 x)) = f1.prod g :=
    fun hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [notMem_support_iff.mp (disjoint_left.mp hd hx), add_zero]
  classical simp_rw [← this hd, ← this hd.symm, add_comm (f2 _), Finsupp.prod, support_add_eq hd,
      prod_union hd, add_apply]

/--
theorem `prod_dvd_prod_of_subset_of_dvd` / 定理 `prod_dvd_prod_of_subset_of_dvd`

English:
theorem prod_dvd_prod_of_subset_of_dvd
  statement: [Zero M] [CommMonoid N] {f1 f2 : α ->₀ M}
  proof: by
  classical
    simp only [Finsupp.prod]
    rw [← sdiff_union_of_subset h1]; rw [prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2

中文:
定理 prod_dvd_prod_of_subset_of_dvd
  结论: [零 M] [交换幺半群 N] {f1 f2 : α ->₀ M}
  证明: by
  classical
    simp only [Finsupp.prod]
    rw [← sdiff_union_of_subset h1]; rw [prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2

Depends on / 依赖: Finsupp, Finsupp.prod, classical, dvd_mul_of_dvd_right, prod_dvd_prod_of_dvd, prod_union, sdiff_disjoint, sdiff_union_of_subset
-/
theorem prod_dvd_prod_of_subset_of_dvd [Zero M] [CommMonoid N] {f1 f2 : α ->₀ M}
    {g1 g2 : α -> M -> N} (h1 : f1.support subseteq f2.support)
    (h2 : forall a : α, a in f1.support -> g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2 := by
  classical
    simp only [Finsupp.prod]
    rw [← sdiff_union_of_subset h1]; rw [prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2

/--
lemma `indicator_eq_sum_attach_single` / 引理 `indicator_eq_sum_attach_single`

English:
lemma indicator_eq_sum_attach_single
  given: [AddCommMonoid M] {s : Finset α} (f : forall a in s, M)
  proof: by
  rw [← sum_single (indicator s f)]; rw [sum]; rw [sum_subset (support_indicator_subset _ _)]; rw [← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [notMem_support_iff.mp hi]; rw [single_zero]

中文:
引理 indicator_eq_sum_attach_single
  条件: [加法交换幺半群 M] {s : 有限集 α} (f : 对任意 a in s, M)
  证明: by
  rw [← sum_single (indicator s f)]; rw [sum]; rw [sum_subset (support_indicator_subset _ _)]; rw [← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [notMem_support_iff.mp hi]; rw [single_zero]

Depends on / 依赖: Finset, Finset.sum_congr, indicator, indicator_of_mem, notMem_support_iff, notMem_support_iff.mp, single_zero, sum_attach, sum_congr, sum_single, sum_subset, support_indicator_subset
-/
lemma indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : forall a in s, M) :
    indicator s f = ∑ x in s.attach, single ↑x (f x x.2) := by
  rw [← sum_single (indicator s f)]; rw [sum]; rw [sum_subset (support_indicator_subset _ _)]; rw [← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [notMem_support_iff.mp hi]; rw [single_zero]

/--
lemma `indicator_eq_sum_single` / 引理 `indicator_eq_sum_single`

English:
lemma indicator_eq_sum_single
  given: [AddCommMonoid M] (s : Finset α) (f : α -> M)
  proof: (indicator_eq_sum_attach_single _).trans sum_attach _ fun x => single x (f x)

@[to_additive (attr := simp)]

中文:
引理 indicator_eq_sum_single
  条件: [加法交换幺半群 M] (s : 有限集 α) (f : α -> M)
  证明: (indicator_eq_sum_attach_single _).trans sum_attach _ fun x => single x (f x)

@[to_additive (attr := simp)]

Depends on / 依赖: indicator_eq_sum_attach_single, single, sum_attach
-/
lemma indicator_eq_sum_single [AddCommMonoid M] (s : Finset α) (f : α -> M) :
    indicator s (fun x _ => f x) = ∑ x in s, single x (f x) :=
(indicator_eq_sum_attach_single _).trans sum_attach _ fun x => single x (f x)

@[to_additive (attr := simp)]
/--
lemma `prod_indicator_index_eq_prod_attach` / 引理 `prod_indicator_index_eq_prod_attach`

English:
lemma prod_indicator_index_eq_prod_attach
  statement: [Zero M] [CommMonoid N]
  proof: by
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero]; rw [← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]

@[to_additive (attr := simp)]

中文:
引理 prod_indicator_index_eq_prod_attach
  结论: [零 M] [交换幺半群 N]
  证明: by
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero]; rw [← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_congr, h_zero, indicator_of_mem, prod_attach, prod_congr, prod_of_support_subset, support_indicator_subset
-/
lemma prod_indicator_index_eq_prod_attach [Zero M] [CommMonoid N]
    {s : Finset α} (f : forall a in s, M) {h : α -> M -> N} (h_zero : forall a in s, h a 0 = 1) :
    (indicator s f).prod h = ∏ x in s.attach, h ↑x (f x x.2) := by
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero]; rw [← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]

@[to_additive (attr := simp)]
/--
lemma `prod_attach_index` / 引理 `prod_attach_index`

English:
lemma prod_attach_index
  given: [CommMonoid N] {s : Finset α} (f : α -> M) {h : α -> M -> N}
  proof: prod_attach _ fun x => h x (f x)

@[to_additive]

中文:
引理 prod_attach_index
  条件: [交换幺半群 N] {s : 有限集 α} (f : α -> M) {h : α -> M -> N}
  证明: prod_attach _ fun x => h x (f x)

@[to_additive]

Depends on / 依赖: prod_attach
-/
lemma prod_attach_index [CommMonoid N] {s : Finset α} (f : α -> M) {h : α -> M -> N} :
    ∏ x in s.attach, h x (f x) = ∏ x in s, h x (f x) :=
  prod_attach _ fun x => h x (f x)

@[to_additive]
/--
lemma `prod_indicator_index` / 引理 `prod_indicator_index`

English:
lemma prod_indicator_index
  statement: [Zero M] [CommMonoid N]
  proof: by
  simp +contextual [h_zero]

@[to_additive]

中文:
引理 prod_indicator_index
  结论: [零 M] [交换幺半群 N]
  证明: by
  simp +contextual [h_zero]

@[to_additive]

Depends on / 依赖: contextual, h_zero
-/
lemma prod_indicator_index [Zero M] [CommMonoid N]
    {s : Finset α} (f : α -> M) {h : α -> M -> N} (h_zero : forall a in s, h a 0 = 1) :
    (indicator s (fun x _ => f x)).prod h = ∏ x in s, h x (f x) := by
  simp +contextual [h_zero]

@[to_additive]
/--
lemma `prod_mul_eq_prod_mul_of_exists` / 引理 `prod_mul_eq_prod_mul_of_exists`

English:
lemma prod_mul_eq_prod_mul_of_exists
  statement: [Zero M] [CommMonoid N]
  proof: by
  exact Finset.prod_mul_eq_prod_mul_of_exists a ha h

中文:
引理 prod_mul_eq_prod_mul_of_存在
  结论: [零 M] [交换幺半群 N]
  证明: by
  exact Finset.prod_mul_eq_prod_mul_of_exists a ha h

Depends on / 依赖: Finset, Finset.prod_mul_eq_prod_mul_of_exists, prod_mul_eq_prod_mul_of_exists
-/
lemma prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N]
    {f : α ->₀ M} {g : α -> M -> N} {n₁ n₂ : N}
    (a : α) (ha : a in f.support)
    (h : g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ := by
  exact Finset.prod_mul_eq_prod_mul_of_exists a ha h

end Finsupp

/--
theorem `Finset.sum_apply'` / 定理 `Finset.sum_apply'`

English:
theorem Finset.sum_apply'
  statement: (∑ k in s, f k) i = ∑ k in s, f k i
  proof: map_sum (Finsupp.applyAddHom i) f s

中文:
定理 有限集.sum_apply'
  结论: (∑ k in s, f k) i = ∑ k in s, f k i
  证明: map_sum (Finsupp.applyAddHom i) f s

Depends on / 依赖: Finsupp, Finsupp.applyAddHom, applyAddHom, map_sum
-/
theorem Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k i :=
  map_sum (Finsupp.applyAddHom i) f s

/--
theorem `Finsupp.sum_apply'` / 定理 `Finsupp.sum_apply'`

English:
theorem Finsupp.sum_apply'
  statement: g.sum k x = g.sum fun i b => k i b x
  proof: Finset.sum_apply _ _ _

中文:
定理 有限支撑.sum_apply'
  结论: g.求和 k x = g.求和 fun i b => k i b x
  证明: Finset.sum_apply _ _ _

Depends on / 依赖: Finset, Finset.sum_apply, sum_apply
-/
theorem Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

/--
theorem `Finsupp.sum_apply''` / 定理 `Finsupp.sum_apply''`

English:
theorem Finsupp.sum_apply''
  statement: {A F : Type*} [AddZeroClass A] [AddCommMonoid F] [FunLike F γ B]
  proof: by
  classical
  unfold Finsupp.sum
  induction g.support using Finset.induction with
  | empty => simp [h0]
  | insert i s hi ih => simp [sum_insert hi, hadd, ih]

中文:
定理 有限支撑.sum_apply''
  结论: {A F : 类型} [加法零类 A] [加法交换幺半群 F] [函数状 F γ B]
  证明: by
  classical
  unfold Finsupp.sum
  induction g.support using Finset.induction with
  | empty => simp [h0]
  | insert i s hi ih => simp [sum_insert hi, hadd, ih]

Depends on / 依赖: Finset, Finset.induction, Finsupp, Finsupp.sum, classical, g.support, insert, sum_insert, support
-/
theorem Finsupp.sum_apply'' {A F : Type*} [AddZeroClass A] [AddCommMonoid F] [FunLike F γ B]
    (g : ι ->₀ A) (k : ι -> A -> F) (x : γ)
    (h0 : (0 : F) x = 0) (hadd : forall (f g : F), (f + g : F) x = f x + g x) :
    g.sum k x = g.sum (fun i a => k i a x) := by
  classical
  unfold Finsupp.sum
  induction g.support using Finset.induction with
  | empty => simp [h0]
  | insert i s hi ih => simp [sum_insert hi, hadd, ih]

section

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/--
theorem `Finsupp.sum_mul` / 定理 `Finsupp.sum_mul`

English:
theorem Finsupp.sum_mul
  given: (b : S) (s : α ->₀ R) {f : α -> R -> S}
  proof: by simp only [Finsupp.sum, Finset.sum_mul]

中文:
定理 有限支撑.sum_mul
  条件: (b : S) (s : α ->₀ R) {f : α -> R -> S}
  证明: by simp only [Finsupp.sum, Finset.sum_mul]

Depends on / 依赖: Finset, Finset.sum_mul, Finsupp, Finsupp.sum, sum_mul
-/
theorem Finsupp.sum_mul (b : S) (s : α ->₀ R) {f : α -> R -> S} :
    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]

/--
theorem `Finsupp.mul_sum` / 定理 `Finsupp.mul_sum`

English:
theorem Finsupp.mul_sum
  given: (b : S) (s : α ->₀ R) {f : α -> R -> S}
  proof: by simp only [Finsupp.sum, Finset.mul_sum]

中文:
定理 有限支撑.mul_sum
  条件: (b : S) (s : α ->₀ R) {f : α -> R -> S}
  证明: by simp only [Finsupp.sum, Finset.mul_sum]

Depends on / 依赖: Finset, Finset.mul_sum, Finsupp, Finsupp.sum, mul_sum
-/
theorem Finsupp.mul_sum (b : S) (s : α ->₀ R) {f : α -> R -> S} :
    b * s.sum f = s.sum fun a c => b * f a c := by simp only [Finsupp.sum, Finset.mul_sum]

end

/--
lemma `Multiset.card_finsuppSum` / 引理 `Multiset.card_finsuppSum`

English:
lemma Multiset.card_finsuppSum
  given: [Zero M] (f : ι ->₀ M) (g : ι -> M -> Multiset α)
  proof: map_finsuppSum cardHom ..

中文:
引理 Multiset.card_finsuppSum
  条件: [零 M] (f : ι ->₀ M) (g : ι -> M -> Multiset α)
  证明: map_finsuppSum cardHom ..
-/
@[simp] lemma Multiset.card_finsuppSum [Zero M] (f : ι ->₀ M) (g : ι -> M -> Multiset α) :
    card (f.sum g) = f.sum fun i m => card (g i m) := map_finsuppSum cardHom ..

namespace Nat

/--
theorem `prod_pow_pos_of_zero_notMem_support` / 定理 `prod_pow_pos_of_zero_notMem_support`

English:
theorem prod_pow_pos_of_zero_notMem_support
  given: {f : Nat ->₀ Nat} (nhf : 0 ∉ f.support)
  proof: Nat.pos_iff_ne_zero.mpr Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

中文:
定理 prod_pow_pos_of_zero_notMem_support
  条件: {f : 自然数 ->₀ 自然数} (nhf : 0 ∉ f.support)
  证明: Nat.pos_iff_ne_zero.mpr Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff.mpr, Nat.pos_iff_ne_zero.mpr, pos_iff_ne_zero, pow_ne_zero, prod_ne_zero_iff
-/
theorem prod_pow_pos_of_zero_notMem_support {f : Nat ->₀ Nat} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) :=
Nat.pos_iff_ne_zero.mpr Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

end Nat

namespace MulOpposite
variable {ι M N : Type*} [AddCommMonoid M] [Zero N]

/--
lemma `op_finsuppSum` / 引理 `op_finsuppSum`

English:
lemma op_finsuppSum
  given: (f : ι ->₀ N) (g : ι -> N -> M)
  proof: op_sum ..

中文:
引理 op_finsuppSum
  条件: (f : ι ->₀ N) (g : ι -> N -> M)
  证明: op_sum ..

Depends on / 依赖: op_sum
-/
lemma op_finsuppSum (f : ι ->₀ N) (g : ι -> N -> M) :
    op (f.sum g) = f.sum fun i n => op (g i n) := op_sum ..

/--
lemma `unop_finsuppSum` / 引理 `unop_finsuppSum`

English:
lemma unop_finsuppSum
  given: (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ)
  proof: unop_sum ..

中文:
引理 unop_finsuppSum
  条件: (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ)
  证明: unop_sum ..

Depends on / 依赖: unop_sum
-/
lemma unop_finsuppSum (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ) :
    unop (f.sum g) = f.sum fun i n => unop (g i n) := unop_sum ..

end MulOpposite

namespace AddOpposite
variable {ι M N : Type*} [CommMonoid M] [Zero N]

/--
lemma `op_finsuppProd` / 引理 `op_finsuppProd`

English:
lemma op_finsuppProd
  given: (f : ι ->₀ N) (g : ι -> N -> M)
  proof: op_prod ..

中文:
引理 op_finsuppProd
  条件: (f : ι ->₀ N) (g : ι -> N -> M)
  证明: op_prod ..
-/
@[simp] lemma op_finsuppProd (f : ι ->₀ N) (g : ι -> N -> M) :
    op (f.prod g) = f.prod fun i n => op (g i n) := op_prod ..

/--
lemma `unop_finsuppProd` / 引理 `unop_finsuppProd`

English:
lemma unop_finsuppProd
  given: (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ)
  proof: unop_prod ..

中文:
引理 unop_finsuppProd
  条件: (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ)
  证明: unop_prod ..
-/
@[simp] lemma unop_finsuppProd (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ) :
    unop (f.prod g) = f.prod fun i n => unop (g i n) := unop_prod ..

end AddOpposite
