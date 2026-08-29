/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Order.Preorder.Finsupp

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `Finsupp.toMultiset` the equivalence between `α →₀ ℕ` and `Multiset α`, along
with `Multiset.toFinsupp` the reverse equivalence and `Finsupp.orderIsoMultiset` (the equivalence
promoted to an order isomorphism).

-/

@[expose] public section

open Finset

variable {α β ι : Type*}

namespace Finsupp

/--
Definition of `toMultiset` / `toMultiset` 的定义

English:
definition toMultiset
  signature: : (α ->₀ Nat) ->+ Multiset α where
  body: Finsupp.sum f fun a n => n • {a}
  -- Porting note: have to specify `h` or add a `dsimp only` before `sum_add_index'`.
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' _f _g := sum_add_index' (h := fun _ n => n • _)
    (fun _ => zero_nsmul _) (fun _ => add_nsm

中文:
定义 toMultiset
  签名: : (α ->₀ 自然数) ->+ Multiset α where
  定义体: Finsupp.sum f fun a n => n • {a}
  -- Porting note: have to specify `h` or add a `dsimp only` before `sum_add_index'`.
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' _f _g := sum_add_index' (h := fun _ n => n • _)
    (fun _ => zero_nsmul _) (fun _ => add_nsm

Depends on / 依赖: Finsupp, Finsupp.sum
-/
def toMultiset : (α ->₀ Nat) ->+ Multiset α where
  toFun f := Finsupp.sum f fun a n => n • {a}
  -- Porting note: have to specify `h` or add a `dsimp only` before `sum_add_index'`.
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' _f _g := sum_add_index' (h := fun _ n => n • _)
    (fun _ => zero_nsmul _) (fun _ => add_nsmul _)
  map_zero' := sum_zero_index

/--
theorem `toMultiset_zero` / 定理 `toMultiset_zero`

English:
theorem toMultiset_zero
  statement: toMultiset (0 : α ->₀ Nat) = 0
  proof: rfl

中文:
定理 toMultiset_zero
  结论: toMultiset (0 : α ->₀ 自然数) = 0
  证明: rfl
-/
theorem toMultiset_zero : toMultiset (0 : α ->₀ Nat) = 0 :=
  rfl

/--
theorem `toMultiset_add` / 定理 `toMultiset_add`

English:
theorem toMultiset_add
  given: (m n : α ->₀ Nat)
  statement: toMultiset (m + n) = toMultiset m + toMultiset n
  proof: toMultiset.map_add m n

中文:
定理 toMultiset_add
  条件: (m n : α ->₀ 自然数)
  结论: toMultiset (m + n) = toMultiset m + toMultiset n
  证明: toMultiset.map_add m n

Depends on / 依赖: ListShape, actual, map_add, notation, toMultiset, toMultiset.map_add
-/
theorem toMultiset_add (m n : α ->₀ Nat) : toMultiset (m + n) = toMultiset m + toMultiset n :=
  toMultiset.map_add m n

/--
theorem `toMultiset_apply` / 定理 `toMultiset_apply`

English:
theorem toMultiset_apply
  given: (f : α ->₀ Nat)
  statement: toMultiset f = f.sum fun a n => n • {a}
  proof: rfl

@[simp]

中文:
定理 toMultiset_apply
  条件: (f : α ->₀ 自然数)
  结论: toMultiset f = f.sum fun a n => n • {a}
  证明: rfl

@[simp]

Depends on / 依赖: List.perm, QPF.quot, actual, notion
-/
theorem toMultiset_apply (f : α ->₀ Nat) : toMultiset f = f.sum fun a n => n • {a} :=
  rfl

@[simp]
/--
theorem `toMultiset_single` / 定理 `toMultiset_single`

English:
theorem toMultiset_single
  given: (a : α) (n : Nat)
  statement: toMultiset (single a n) = n • {a}
  proof: by
  rw [toMultiset_apply]; rw [sum_single_index]; apply zero_nsmul

中文:
定理 toMultiset_single
  条件: (a : α) (n : 自然数)
  结论: toMultiset (single a n) = n • {a}
  证明: by
  rw [toMultiset_apply]; rw [sum_single_index]; apply zero_nsmul

Depends on / 依赖: sum_single_index, toMultiset_apply, zero_nsmul
-/
theorem toMultiset_single (a : α) (n : Nat) : toMultiset (single a n) = n • {a} := by
  rw [toMultiset_apply]; rw [sum_single_index]; apply zero_nsmul

/--
theorem `toMultiset_sum` / 定理 `toMultiset_sum`

English:
theorem toMultiset_sum
  given: {f : ι -> α ->₀ Nat} (s : Finset ι)
  proof: map_sum Finsupp.toMultiset _ _

中文:
定理 toMultiset_sum
  条件: {f : ι -> α ->₀ 自然数} (s : Finset ι)
  证明: map_sum Finsupp.toMultiset _ _

Depends on / 依赖: Finsupp, Finsupp.toMultiset, LawfulMvFunctor, lawfulMvFunctor, map_sum, toMultiset
-/
theorem toMultiset_sum {f : ι -> α ->₀ Nat} (s : Finset ι) :
    Finsupp.toMultiset (∑ i in s, f i) = ∑ i in s, Finsupp.toMultiset (f i) :=
  map_sum Finsupp.toMultiset _ _

/--
theorem `toMultiset_sum_single` / 定理 `toMultiset_sum_single`

English:
theorem toMultiset_sum_single
  given: (s : Finset ι) (n : Nat)
  proof: by
  simp_rw [toMultiset_sum, Finsupp.toMultiset_single, Finset.sum_nsmul, sum_multiset_singleton]

@[simp]

中文:
定理 toMultiset_sum_single
  条件: (s : Finset ι) (n : 自然数)
  证明: by
  simp_rw [toMultiset_sum, Finsupp.toMultiset_single, Finset.sum_nsmul, sum_multiset_singleton]

@[simp]

Depends on / 依赖: Finset, Finset.sum_nsmul, Finsupp, Finsupp.toMultiset_single, simp_rw, sum_multiset_singleton, sum_nsmul, toMultiset_single, toMultiset_sum
-/
theorem toMultiset_sum_single (s : Finset ι) (n : Nat) :
    Finsupp.toMultiset (∑ i in s, single i n) = n • s.val := by
  simp_rw [toMultiset_sum, Finsupp.toMultiset_single, Finset.sum_nsmul, sum_multiset_singleton]

@[simp]
/--
theorem `card_toMultiset` / 定理 `card_toMultiset`

English:
theorem card_toMultiset
  given: (f : α ->₀ Nat)
  statement: Multiset.card (toMultiset f) = f.sum fun _ => id
  proof: by
  simp [toMultiset_apply, Function.id_def]

中文:
定理 card_toMultiset
  条件: (f : α ->₀ 自然数)
  结论: Multiset.card (toMultiset f) = f.sum fun _ => id
  证明: by
  simp [toMultiset_apply, Function.id_def]

Depends on / 依赖: Function, Function.id_def, id_def, toMultiset_apply
-/
theorem card_toMultiset (f : α ->₀ Nat) : Multiset.card (toMultiset f) = f.sum fun _ => id := by
  simp [toMultiset_apply, Function.id_def]

/--
theorem `toMultiset_map` / 定理 `toMultiset_map`

English:
theorem toMultiset_map
  given: (f : α ->₀ Nat) (g : α -> β)
  proof: by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.map_zero, mapDomain_zero, toMultiset_zero]
  · intro a n f _ _ ih
    rw [toMultiset_add]; rw [Multiset.map_add]; rw [ih]; rw [mapDomain_add]; rw [mapDomain_single]; rw [toMultiset_single]; rw [toMultiset_add]; rw [toMultiset_single]; r

中文:
定理 toMultiset_map
  条件: (f : α ->₀ 自然数) (g : α -> β)
  证明: by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.map_zero, mapDomain_zero, toMultiset_zero]
  · intro a n f _ _ ih
    rw [toMultiset_add]; rw [Multiset.map_add]; rw [ih]; rw [mapDomain_add]; rw [mapDomain_single]; rw [toMultiset_single]; rw [toMultiset_add]; rw [toMultiset_single]; r

Depends on / 依赖: Multiset, Multiset.coe_mapAddMonoidHom, Multiset.mapAddMonoidHom, Multiset.map_add, Multiset.map_zero, coe_mapAddMonoidHom, f.induction, mapAddMonoidHom, mapDomain_add, mapDomain_single, mapDomain_zero, map_add, map_nsmul, map_zero, toMultiset_add, toMultiset_single, toMultiset_zero
-/
theorem toMultiset_map (f : α ->₀ Nat) (g : α -> β) :
    f.toMultiset.map g = toMultiset (f.mapDomain g) := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.map_zero, mapDomain_zero, toMultiset_zero]
  · intro a n f _ _ ih
    rw [toMultiset_add]; rw [Multiset.map_add]; rw [ih]; rw [mapDomain_add]; rw [mapDomain_single]; rw [toMultiset_single]; rw [toMultiset_add]; rw [toMultiset_single]; rw [← Multiset.coe_mapAddMonoidHom]; rw [(Multiset.mapAddMonoidHom g).map_nsmul]
    rfl

@[to_additive (attr := simp)]
/--
theorem `prod_toMultiset` / 定理 `prod_toMultiset`

English:
theorem prod_toMultiset
  given: [CommMonoid α] (f : α ->₀ Nat)
  proof: by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
  · intro a n f _ _ ih
    rw [toMultiset_add]; rw [Multiset.prod_add]; rw [ih]; rw [toMultiset_single]; rw [Multiset.prod_nsmul]; rw [Finsupp.prod_add_index' pow_zero pow_add]; rw [Finsupp.prod_singl

中文:
定理 prod_toMultiset
  条件: [CommMonoid α] (f : α ->₀ 自然数)
  证明: by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
  · intro a n f _ _ ih
    rw [toMultiset_add]; rw [Multiset.prod_add]; rw [ih]; rw [toMultiset_single]; rw [Multiset.prod_nsmul]; rw [Finsupp.prod_add_index' pow_zero pow_add]; rw [Finsupp.prod_singl

Depends on / 依赖: Finsupp, Finsupp.prod_add_index, Finsupp.prod_single_index, Finsupp.prod_zero_index, Multiset, Multiset.prod_add, Multiset.prod_nsmul, Multiset.prod_singleton, Multiset.prod_zero, f.induction, pow_add, pow_zero, prod_add, prod_add_index, prod_nsmul, prod_single_index, prod_singleton, prod_zero, prod_zero_index, toMultiset_add
-/
theorem prod_toMultiset [CommMonoid α] (f : α ->₀ Nat) :
    f.toMultiset.prod = f.prod fun a n => a ^ n := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
  · intro a n f _ _ ih
    rw [toMultiset_add]; rw [Multiset.prod_add]; rw [ih]; rw [toMultiset_single]; rw [Multiset.prod_nsmul]; rw [Finsupp.prod_add_index' pow_zero pow_add]; rw [Finsupp.prod_single_index]; rw [Multiset.prod_singleton]
    exact pow_zero a

@[simp]
/--
theorem `toFinset_toMultiset` / 定理 `toFinset_toMultiset`

English:
theorem toFinset_toMultiset
  given: [DecidableEq α] (f : α ->₀ Nat)
  statement: f.toMultiset.toFinset = f.support
  proof: by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.toFinset_zero, support_zero]
  · intro a n f ha hn ih
    rw [toMultiset_add]; rw [Multiset.toFinset_add]; rw [ih]; rw [toMultiset_single]; rw [support_add_eq]; rw [support_single _ hn]; rw [Multiset.toFinset_nsmul _ _ hn]; rw [Multiset

中文:
定理 toFinset_toMultiset
  条件: [DecidableEq α] (f : α ->₀ 自然数)
  结论: f.toMultiset.toFinset = f.support
  证明: by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.toFinset_zero, support_zero]
  · intro a n f ha hn ih
    rw [toMultiset_add]; rw [Multiset.toFinset_add]; rw [ih]; rw [toMultiset_single]; rw [support_add_eq]; rw [support_single _ hn]; rw [Multiset.toFinset_nsmul _ _ hn]; rw [Multiset

Depends on / 依赖: Disjoint, Disjoint.mono_left, Finset, Finset.disjoint_singleton_left, Multiset, Multiset.toFinset_add, Multiset.toFinset_nsmul, Multiset.toFinset_singleton, Multiset.toFinset_zero, disjoint_singleton_left, f.induction, mono_left, support_add_eq, support_single, support_single_subset, support_zero, toFinset_add, toFinset_nsmul, toFinset_singleton, toFinset_zero
-/
theorem toFinset_toMultiset [DecidableEq α] (f : α ->₀ Nat) : f.toMultiset.toFinset = f.support := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.toFinset_zero, support_zero]
  · intro a n f ha hn ih
    rw [toMultiset_add]; rw [Multiset.toFinset_add]; rw [ih]; rw [toMultiset_single]; rw [support_add_eq]; rw [support_single _ hn]; rw [Multiset.toFinset_nsmul _ _ hn]; rw [Multiset.toFinset_singleton]
    refine Disjoint.mono_left support_single_subset ?_
    rwa [Finset.disjoint_singleton_left]

@[simp]
/--
theorem `count_toMultiset` / 定理 `count_toMultiset`

English:
theorem count_toMultiset
  given: [DecidableEq α] (f : α ->₀ Nat) (a : α)
  statement: (toMultiset f).count a = f a
  proof: calc
    (toMultiset f).count a = Finsupp.sum f (fun x n => (n • {x} : Multiset α).count a) := by
      rw [toMultiset_apply]; exact map_sum (Multiset.countAddMonoidHom a) _ f.support
    _ = f.sum fun x n => n * ({x} : Multiset α).count a := by simp only [Multiset.count_nsmul]
    _ = f a * ({a} : 

中文:
定理 count_toMultiset
  条件: [DecidableEq α] (f : α ->₀ 自然数) (a : α)
  结论: (toMultiset f).count a = f a
  证明: calc
    (toMultiset f).count a = Finsupp.sum f (fun x n => (n • {x} : Multiset α).count a) := by
      rw [toMultiset_apply]; exact map_sum (Multiset.countAddMonoidHom a) _ f.support
    _ = f.sum fun x n => n * ({x} : Multiset α).count a := by simp only [Multiset.count_nsmul]
    _ = f a * ({a} : 

Depends on / 依赖: Finsupp, Finsupp.sum, H.symm, Multiset, Multiset.countAddMonoidHom, Multiset.count_nsmul, Multiset.count_singleton, Multiset.count_singleton_self, countAddMonoidHom, count_nsmul, count_singleton, count_singleton_self, f.sum, f.support, if_false, map_sum, mul_one, mul_zero, sum_eq_single, support
-/
theorem count_toMultiset [DecidableEq α] (f : α ->₀ Nat) (a : α) : (toMultiset f).count a = f a :=
  calc
    (toMultiset f).count a = Finsupp.sum f (fun x n => (n • {x} : Multiset α).count a) := by
      rw [toMultiset_apply]; exact map_sum (Multiset.countAddMonoidHom a) _ f.support
    _ = f.sum fun x n => n * ({x} : Multiset α).count a := by simp only [Multiset.count_nsmul]
    _ = f a * ({a} : Multiset α).count a :=
      sum_eq_single _
        (fun a' _ H => by simp only [Multiset.count_singleton, if_false, H.symm, mul_zero])
        (fun _ => zero_mul _)
    _ = f a := by rw [Multiset.count_singleton_self, mul_one]

/--
theorem `toMultiset_sup` / 定理 `toMultiset_sup`

English:
theorem toMultiset_sup
  given: [DecidableEq α] (f g : α ->₀ Nat)
  proof: by
  ext
  simp_rw [Multiset.count_union, Finsupp.count_toMultiset, Finsupp.sup_apply]

中文:
定理 toMultiset_sup
  条件: [DecidableEq α] (f g : α ->₀ 自然数)
  证明: by
  ext
  simp_rw [Multiset.count_union, Finsupp.count_toMultiset, Finsupp.sup_apply]

Depends on / 依赖: Finsupp, Finsupp.count_toMultiset, Finsupp.sup_apply, Multiset, Multiset.count_union, count_toMultiset, count_union, simp_rw, sup_apply
-/
theorem toMultiset_sup [DecidableEq α] (f g : α ->₀ Nat) :
    toMultiset (f ⊔ g) = toMultiset f union toMultiset g := by
  ext
  simp_rw [Multiset.count_union, Finsupp.count_toMultiset, Finsupp.sup_apply]

/--
theorem `toMultiset_inf` / 定理 `toMultiset_inf`

English:
theorem toMultiset_inf
  given: [DecidableEq α] (f g : α ->₀ Nat)
  proof: by
  ext
  simp_rw [Multiset.count_inter, Finsupp.count_toMultiset, Finsupp.inf_apply]

@[simp]

中文:
定理 toMultiset_inf
  条件: [DecidableEq α] (f g : α ->₀ 自然数)
  证明: by
  ext
  simp_rw [Multiset.count_inter, Finsupp.count_toMultiset, Finsupp.inf_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.count_toMultiset, Finsupp.inf_apply, Multiset, Multiset.count_inter, count_inter, count_toMultiset, inf_apply, simp_rw
-/
theorem toMultiset_inf [DecidableEq α] (f g : α ->₀ Nat) :
    toMultiset (f ⊓ g) = toMultiset f inter toMultiset g := by
  ext
  simp_rw [Multiset.count_inter, Finsupp.count_toMultiset, Finsupp.inf_apply]

@[simp]
/--
theorem `mem_toMultiset` / 定理 `mem_toMultiset`

English:
theorem mem_toMultiset
  given: (f : α ->₀ Nat) (i : α)
  statement: i in toMultiset f ↔ i in f.support
  proof: by
  classical
  rw [← Multiset.count_ne_zero]; rw [Finsupp.count_toMultiset]; rw [Finsupp.mem_support_iff]

中文:
定理 mem_toMultiset
  条件: (f : α ->₀ 自然数) (i : α)
  结论: i in toMultiset f ↔ i in f.support
  证明: by
  classical
  rw [← Multiset.count_ne_zero]; rw [Finsupp.count_toMultiset]; rw [Finsupp.mem_support_iff]

Depends on / 依赖: Finsupp, Finsupp.count_toMultiset, Finsupp.mem_support_iff, Multiset, Multiset.count_ne_zero, classical, count_ne_zero, count_toMultiset, mem_support_iff
-/
theorem mem_toMultiset (f : α ->₀ Nat) (i : α) : i in toMultiset f ↔ i in f.support := by
  classical
  rw [← Multiset.count_ne_zero]; rw [Finsupp.count_toMultiset]; rw [Finsupp.mem_support_iff]

end Finsupp

namespace Multiset

variable [DecidableEq α]

/-- Given a multiset `s`, `s.toFinsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
@[simps symm_apply]
/--
Definition of `toFinsupp` / `toFinsupp` 的定义

English:
definition toFinsupp
  signature: : Multiset α ≃+ (α ->₀ Nat) where
  body: ⟨s.toFinset, fun a => s.count a, fun a => by simp⟩
  invFun f := Finsupp.toMultiset f
  map_add' _ _ := Finsupp.ext fun _ => count_add _ _ _
  right_inv f :=
    Finsupp.ext fun a => by
      simp only [Finsupp.toMultiset_apply, Finsupp.sum, Multiset.count_sum',
        Multiset.count_singleton, mul

中文:
定义 toFinsupp
  签名: : Multiset α ≃+ (α ->₀ 自然数) where
  定义体: ⟨s.toFinset, fun a => s.count a, fun a => by simp⟩
  invFun f := Finsupp.toMultiset f
  map_add' _ _ := Finsupp.ext fun _ => count_add _ _ _
  right_inv f :=
    Finsupp.ext fun a => by
      simp only [Finsupp.toMultiset_apply, Finsupp.sum, Multiset.count_sum',
        Multiset.count_singleton, mul

Depends on / 依赖: s.count, s.toFinset, toFinset
-/
noncomputable def toFinsupp : Multiset α ≃+ (α ->₀ Nat) where
  toFun s := ⟨s.toFinset, fun a => s.count a, fun a => by simp⟩
  invFun f := Finsupp.toMultiset f
  map_add' _ _ := Finsupp.ext fun _ => count_add _ _ _
  right_inv f :=
    Finsupp.ext fun a => by
      simp only [Finsupp.toMultiset_apply, Finsupp.sum, Multiset.count_sum',
        Multiset.count_singleton, mul_boole, Finsupp.coe_mk, Finsupp.mem_support_iff,
        Multiset.count_nsmul, Finset.sum_ite_eq, ite_not, ite_eq_right_iff]
      exact Eq.symm
  left_inv s := by simp only [Finsupp.toMultiset_apply, Finsupp.sum, Finsupp.coe_mk,
    Multiset.toFinset_sum_count_nsmul_eq]

@[simp]
/--
theorem `toFinsupp_support` / 定理 `toFinsupp_support`

English:
theorem toFinsupp_support
  given: (s : Multiset α)
  statement: s.toFinsupp.support = s.toFinset
  proof: rfl

@[simp]

中文:
定理 toFinsupp_support
  条件: (s : Multiset α)
  结论: s.toFinsupp.support = s.toFinset
  证明: rfl

@[simp]
-/
theorem toFinsupp_support (s : Multiset α) : s.toFinsupp.support = s.toFinset := rfl

@[simp]
/--
theorem `toFinsupp_apply` / 定理 `toFinsupp_apply`

English:
theorem toFinsupp_apply
  given: (s : Multiset α) (a : α)
  statement: toFinsupp s a = s.count a
  proof: rfl

中文:
定理 toFinsupp_apply
  条件: (s : Multiset α) (a : α)
  结论: toFinsupp s a = s.count a
  证明: rfl
-/
theorem toFinsupp_apply (s : Multiset α) (a : α) : toFinsupp s a = s.count a := rfl

/--
theorem `toFinsupp_zero` / 定理 `toFinsupp_zero`

English:
theorem toFinsupp_zero
  statement: toFinsupp (0 : Multiset α) = 0
  proof: _root_.map_zero _

中文:
定理 toFinsupp_zero
  结论: toFinsupp (0 : Multiset α) = 0
  证明: _root_.map_zero _

Depends on / 依赖: _root_, _root_.map_zero, map_zero
-/
theorem toFinsupp_zero : toFinsupp (0 : Multiset α) = 0 := _root_.map_zero _

/--
theorem `toFinsupp_add` / 定理 `toFinsupp_add`

English:
theorem toFinsupp_add
  given: (s t : Multiset α)
  statement: toFinsupp (s + t) = toFinsupp s + toFinsupp t
  proof: _root_.map_add toFinsupp s t

@[simp]

中文:
定理 toFinsupp_add
  条件: (s t : Multiset α)
  结论: toFinsupp (s + t) = toFinsupp s + toFinsupp t
  证明: _root_.map_add toFinsupp s t

@[simp]

Depends on / 依赖: _root_, _root_.map_add, map_add, toFinsupp
-/
theorem toFinsupp_add (s t : Multiset α) : toFinsupp (s + t) = toFinsupp s + toFinsupp t :=
  _root_.map_add toFinsupp s t

@[simp]
/--
theorem `toFinsupp_singleton` / 定理 `toFinsupp_singleton`

English:
theorem toFinsupp_singleton
  given: (a : α)
  statement: toFinsupp ({a} : Multiset α) = Finsupp.single a 1
  proof: by
  ext; rw [toFinsupp_apply, count_singleton, Finsupp.single_eq_pi_single, Pi.single_apply]

@[simp]

中文:
定理 toFinsupp_singleton
  条件: (a : α)
  结论: toFinsupp ({a} : Multiset α) = Finsupp.single a 1
  证明: by
  ext; rw [toFinsupp_apply, count_singleton, Finsupp.single_eq_pi_single, Pi.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_eq_pi_single, Pi.single_apply, count_singleton, single_apply, single_eq_pi_single, toFinsupp_apply
-/
theorem toFinsupp_singleton (a : α) : toFinsupp ({a} : Multiset α) = Finsupp.single a 1 := by
  ext; rw [toFinsupp_apply, count_singleton, Finsupp.single_eq_pi_single, Pi.single_apply]

@[simp]
/--
theorem `toFinsupp_toMultiset` / 定理 `toFinsupp_toMultiset`

English:
theorem toFinsupp_toMultiset
  given: (s : Multiset α)
  statement: Finsupp.toMultiset (toFinsupp s) = s
  proof: Multiset.toFinsupp.symm_apply_apply s

中文:
定理 toFinsupp_toMultiset
  条件: (s : Multiset α)
  结论: Finsupp.toMultiset (toFinsupp s) = s
  证明: Multiset.toFinsupp.symm_apply_apply s

Depends on / 依赖: Multiset, Multiset.toFinsupp.symm_apply_apply, symm_apply_apply, toFinsupp
-/
theorem toFinsupp_toMultiset (s : Multiset α) : Finsupp.toMultiset (toFinsupp s) = s :=
  Multiset.toFinsupp.symm_apply_apply s

/--
theorem `toFinsupp_eq_iff` / 定理 `toFinsupp_eq_iff`

English:
theorem toFinsupp_eq_iff
  given: {s : Multiset α} {f : α ->₀ Nat}
  proof: Multiset.toFinsupp.eq_symm_apply.symm

中文:
定理 toFinsupp_eq_iff
  条件: {s : Multiset α} {f : α ->₀ 自然数}
  证明: Multiset.toFinsupp.eq_symm_apply.symm

Depends on / 依赖: Multiset, Multiset.toFinsupp.eq_symm_apply.symm, eq_symm_apply, toFinsupp
-/
theorem toFinsupp_eq_iff {s : Multiset α} {f : α ->₀ Nat} :
    toFinsupp s = f ↔ s = Finsupp.toMultiset f :=
  Multiset.toFinsupp.eq_symm_apply.symm

/--
theorem `toFinsupp_union` / 定理 `toFinsupp_union`

English:
theorem toFinsupp_union
  given: (s t : Multiset α)
  statement: toFinsupp (s union t) = toFinsupp s ⊔ toFinsupp t
  proof: by
  ext
  simp

中文:
定理 toFinsupp_union
  条件: (s t : Multiset α)
  结论: toFinsupp (s union t) = toFinsupp s ⊔ toFinsupp t
  证明: by
  ext
  simp
-/
theorem toFinsupp_union (s t : Multiset α) : toFinsupp (s union t) = toFinsupp s ⊔ toFinsupp t := by
  ext
  simp

/--
theorem `toFinsupp_inter` / 定理 `toFinsupp_inter`

English:
theorem toFinsupp_inter
  given: (s t : Multiset α)
  statement: toFinsupp (s inter t) = toFinsupp s ⊓ toFinsupp t
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinsupp_inter
  条件: (s t : Multiset α)
  结论: toFinsupp (s inter t) = toFinsupp s ⊓ toFinsupp t
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinsupp_inter (s t : Multiset α) : toFinsupp (s inter t) = toFinsupp s ⊓ toFinsupp t := by
  ext
  simp

@[simp]
/--
theorem `toFinsupp_sum_eq` / 定理 `toFinsupp_sum_eq`

English:
theorem toFinsupp_sum_eq
  given: (s : Multiset α)
  statement: s.toFinsupp.sum (fun _ => id) = Multiset.card s
  proof: by
  rw [← Finsupp.card_toMultiset]; rw [toFinsupp_toMultiset]

中文:
定理 toFinsupp_sum_eq
  条件: (s : Multiset α)
  结论: s.toFinsupp.sum (fun _ => id) = Multiset.card s
  证明: by
  rw [← Finsupp.card_toMultiset]; rw [toFinsupp_toMultiset]

Depends on / 依赖: Finsupp, Finsupp.card_toMultiset, card_toMultiset, toFinsupp_toMultiset
-/
theorem toFinsupp_sum_eq (s : Multiset α) : s.toFinsupp.sum (fun _ => id) = Multiset.card s := by
  rw [← Finsupp.card_toMultiset]; rw [toFinsupp_toMultiset]

end Multiset

@[simp]
/--
theorem `Finsupp.toMultiset_toFinsupp` / 定理 `Finsupp.toMultiset_toFinsupp`

English:
theorem Finsupp.toMultiset_toFinsupp
  given: [DecidableEq α] (f : α ->₀ Nat)
  proof: Multiset.toFinsupp.apply_symm_apply _

中文:
定理 Finsupp.toMultiset_toFinsupp
  条件: [DecidableEq α] (f : α ->₀ 自然数)
  证明: Multiset.toFinsupp.apply_symm_apply _

Depends on / 依赖: Multiset, Multiset.toFinsupp.apply_symm_apply, apply_symm_apply, toFinsupp
-/
theorem Finsupp.toMultiset_toFinsupp [DecidableEq α] (f : α ->₀ Nat) :
    Multiset.toFinsupp (Finsupp.toMultiset f) = f :=
  Multiset.toFinsupp.apply_symm_apply _

/--
theorem `Finsupp.toMultiset_eq_iff` / 定理 `Finsupp.toMultiset_eq_iff`

English:
theorem Finsupp.toMultiset_eq_iff
  given: [DecidableEq α] {f : α ->₀ Nat} {s : Multiset α}
  proof: Multiset.toFinsupp.symm_apply_eq

中文:
定理 Finsupp.toMultiset_eq_iff
  条件: [DecidableEq α] {f : α ->₀ 自然数} {s : Multiset α}
  证明: Multiset.toFinsupp.symm_apply_eq

Depends on / 依赖: Multiset, Multiset.toFinsupp.symm_apply_eq, Quot.mk, symm_apply_eq, toFinsupp
-/
theorem Finsupp.toMultiset_eq_iff [DecidableEq α] {f : α ->₀ Nat} {s : Multiset α} :
    Finsupp.toMultiset f = s ↔ f = Multiset.toFinsupp s :=
  Multiset.toFinsupp.symm_apply_eq

/-! ### As an order isomorphism -/

namespace Finsupp
/--
Definition of `orderIsoMultiset` / `orderIsoMultiset` 的定义

English:
definition orderIsoMultiset
  signature: [DecidableEq ι]
  body: Multiset.toFinsupp.symm.toEquiv
  map_rel_iff' {f g} := by simp [le_def, Multiset.le_iff_count]

@[simp]

中文:
定义 orderIsoMultiset
  签名: [DecidableEq ι]
  定义体: Multiset.toFinsupp.symm.toEquiv
  map_rel_iff' {f g} := by simp [le_def, Multiset.le_iff_count]

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinsupp.symm.toEquiv, toEquiv, toFinsupp
-/
noncomputable def orderIsoMultiset [DecidableEq ι] : (ι ->₀ Nat) ≃o Multiset ι where
  toEquiv := Multiset.toFinsupp.symm.toEquiv
  map_rel_iff' {f g} := by simp [le_def, Multiset.le_iff_count]

@[simp]
/--
theorem `coe_orderIsoMultiset` / 定理 `coe_orderIsoMultiset`

English:
theorem coe_orderIsoMultiset
  given: [DecidableEq ι]
  statement: ⇑(@orderIsoMultiset ι _) = toMultiset
  proof: rfl

@[simp]

中文:
定理 coe_orderIsoMultiset
  条件: [DecidableEq ι]
  结论: ⇑(@orderIsoMultiset ι _) = toMultiset
  证明: rfl

@[simp]
-/
theorem coe_orderIsoMultiset [DecidableEq ι] : ⇑(@orderIsoMultiset ι _) = toMultiset :=
  rfl

@[simp]
/--
theorem `coe_orderIsoMultiset_symm` / 定理 `coe_orderIsoMultiset_symm`

English:
theorem coe_orderIsoMultiset_symm
  given: [DecidableEq ι]
  proof: rfl

中文:
定理 coe_orderIsoMultiset_symm
  条件: [DecidableEq ι]
  证明: rfl
-/
theorem coe_orderIsoMultiset_symm [DecidableEq ι] :
    ⇑(@orderIsoMultiset ι).symm = Multiset.toFinsupp :=
  rfl

/--
theorem `toMultiset_strictMono` / 定理 `toMultiset_strictMono`

English:
theorem toMultiset_strictMono
  statement: StrictMono (@toMultiset ι)
  proof: by
  classical exact (@orderIsoMultiset ι _).strictMono

中文:
定理 toMultiset_strictMono
  结论: StrictMono (@toMultiset ι)
  证明: by
  classical exact (@orderIsoMultiset ι _).strictMono

Depends on / 依赖: classical, orderIsoMultiset, strictMono
-/
theorem toMultiset_strictMono : StrictMono (@toMultiset ι) := by
  classical exact (@orderIsoMultiset ι _).strictMono

/--
theorem `sum_id_lt_of_lt` / 定理 `sum_id_lt_of_lt`

English:
theorem sum_id_lt_of_lt
  given: (m n : ι ->₀ Nat) (h : m < n)
  statement: (m.sum fun _ => id) < n.sum fun _ => id
  proof: by
  rw [← card_toMultiset]; rw [← card_toMultiset]
  apply Multiset.card_lt_card
  exact toMultiset_strictMono h

中文:
定理 sum_id_lt_of_lt
  条件: (m n : ι ->₀ 自然数) (h : m < n)
  结论: (m.sum fun _ => id) < n.sum fun _ => id
  证明: by
  rw [← card_toMultiset]; rw [← card_toMultiset]
  apply Multiset.card_lt_card
  exact toMultiset_strictMono h

Depends on / 依赖: Multiset, Multiset.card_lt_card, card_lt_card, card_toMultiset, toMultiset_strictMono
-/
theorem sum_id_lt_of_lt (m n : ι ->₀ Nat) (h : m < n) : (m.sum fun _ => id) < n.sum fun _ => id := by
  rw [← card_toMultiset]; rw [← card_toMultiset]
  apply Multiset.card_lt_card
  exact toMultiset_strictMono h

variable (ι)

/--
theorem `lt_wf` / 定理 `lt_wf`

English:
theorem lt_wf
  statement: WellFounded (@LT.lt (ι ->₀ Nat) _)
  proof: Subrelation.wf (sum_id_lt_of_lt _ _) InvImage.wf _ Nat.lt_wfRel.2

中文:
定理 lt_wf
  结论: WellFounded (@LT.lt (ι ->₀ 自然数) _)
  证明: Subrelation.wf (sum_id_lt_of_lt _ _) InvImage.wf _ Nat.lt_wfRel.2

Depends on / 依赖: InvImage, InvImage.wf, Nat.lt_wfRel, Subrelation, Subrelation.wf, lt_wfRel, sum_id_lt_of_lt
-/
theorem lt_wf : WellFounded (@LT.lt (ι ->₀ Nat) _) :=
Subrelation.wf (sum_id_lt_of_lt _ _) InvImage.wf _ Nat.lt_wfRel.2

-- TODO: generalize to `[WellFoundedRelation α] → WellFoundedRelation (ι →₀ α)`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation (ι ->₀ Nat)
  body: (· < ·)
  wf := lt_wf _

中文:
实例 :
  签名: WellFoundedRelation (ι ->₀ 自然数)
  定义体: (· < ·)
  wf := lt_wf _
-/
instance : WellFoundedRelation (ι ->₀ Nat) where
  rel := (· < ·)
  wf := lt_wf _

end Finsupp

/--
theorem `Multiset.toFinsupp_strictMono` / 定理 `Multiset.toFinsupp_strictMono`

English:
theorem Multiset.toFinsupp_strictMono
  given: [DecidableEq ι]
  statement: StrictMono (@Multiset.toFinsupp ι _)
  proof: (@Finsupp.orderIsoMultiset ι).symm.strictMono

中文:
定理 Multiset.toFinsupp_strictMono
  条件: [DecidableEq ι]
  结论: StrictMono (@Multiset.toFinsupp ι _)
  证明: (@Finsupp.orderIsoMultiset ι).symm.strictMono

Depends on / 依赖: Finsupp, Finsupp.orderIsoMultiset, orderIsoMultiset, strictMono, symm.strictMono
-/
theorem Multiset.toFinsupp_strictMono [DecidableEq ι] : StrictMono (@Multiset.toFinsupp ι _) :=
  (@Finsupp.orderIsoMultiset ι).symm.strictMono

namespace Sym

variable (α)
variable [DecidableEq α] (n : Nat)

/--
Definition of `equivNatSum` / `equivNatSum` 的定义

English:
definition equivNatSum
  signature: :
  body: Multiset.toFinsupp.toEquiv.subtypeEquiv by simp

中文:
定义 equivNatSum
  签名: :
  定义体: Multiset.toFinsupp.toEquiv.subtypeEquiv by simp

Depends on / 依赖: Cofix.corec, Cofix.dest, Multiset, Multiset.toFinsupp.toEquiv.subtypeEquiv, MvFunctor, MvFunctor.map, Sum.elim, Sum.inl, Sum.inr, subtypeEquiv, toEquiv, toFinsupp
-/
noncomputable def equivNatSum :
    Sym α n ≃ {P : α ->₀ Nat // P.sum (fun _ => id) = n} :=
Multiset.toFinsupp.toEquiv.subtypeEquiv by simp

/--
lemma `coe_equivNatSum_apply_apply` / 引理 `coe_equivNatSum_apply_apply`

English:
lemma coe_equivNatSum_apply_apply
  given: (s : Sym α n) (a : α)
  proof: rfl

中文:
引理 coe_equivNatSum_apply_apply
  条件: (s : Sym α n) (a : α)
  证明: rfl
-/
@[simp] lemma coe_equivNatSum_apply_apply (s : Sym α n) (a : α) :
    (equivNatSum α n s : α ->₀ Nat) a = (s : Multiset α).count a :=
  rfl

/--
lemma `coe_equivNatSum_symm_apply` / 引理 `coe_equivNatSum_symm_apply`

English:
lemma coe_equivNatSum_symm_apply
  given: (P : {P : α ->₀ Nat // P.sum (fun _ => id) = n})
  proof: rfl

中文:
引理 coe_equivNatSum_symm_apply
  条件: (P : {P : α ->₀ 自然数 // P.sum (fun _ => id) = n})
  证明: rfl
-/
@[simp] lemma coe_equivNatSum_symm_apply (P : {P : α ->₀ Nat // P.sum (fun _ => id) = n}) :
    ((equivNatSum α n).symm P : Multiset α) = Finsupp.toMultiset P :=
  rfl

/--
Definition of `equivNatSumOfFintype` / `equivNatSumOfFintype` 的定义

English:
definition equivNatSumOfFintype
  signature: [Fintype α]
  body: (equivNatSum α n).trans Finsupp.equivFunOnFinite.subtypeEquiv by simp [Finsupp.sum_fintype]

中文:
定义 equivNatSumOfFintype
  签名: [Fintype α]
  定义体: (equivNatSum α n).trans Finsupp.equivFunOnFinite.subtypeEquiv by simp [Finsupp.sum_fintype]

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.subtypeEquiv, Finsupp.sum_fintype, equivFunOnFinite, equivNatSum, subtypeEquiv, sum_fintype
-/
noncomputable def equivNatSumOfFintype [Fintype α] :
    Sym α n ≃ {P : α -> Nat // ∑ i, P i = n} :=
(equivNatSum α n).trans Finsupp.equivFunOnFinite.subtypeEquiv by simp [Finsupp.sum_fintype]

/--
lemma `coe_equivNatSumOfFintype_apply_apply` / 引理 `coe_equivNatSumOfFintype_apply_apply`

English:
lemma coe_equivNatSumOfFintype_apply_apply
  given: [Fintype α] (s : Sym α n) (a : α)
  proof: rfl

中文:
引理 coe_equivNatSumOfFintype_apply_apply
  条件: [Fintype α] (s : Sym α n) (a : α)
  证明: rfl
-/
@[simp] lemma coe_equivNatSumOfFintype_apply_apply [Fintype α] (s : Sym α n) (a : α) :
    (equivNatSumOfFintype α n s : α -> Nat) a = (s : Multiset α).count a :=
  rfl

/--
lemma `coe_equivNatSumOfFintype_symm_apply` / 引理 `coe_equivNatSumOfFintype_symm_apply`

English:
lemma coe_equivNatSumOfFintype_symm_apply
  given: [Fintype α] (P : {P : α -> Nat // ∑ i, P i = n})
  proof: by
  obtain ⟨P, hP⟩ := P
  change Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm P) = Multiset.sum _
  ext a
  rw [Multiset.count_sum]
  simp [Multiset.count_singleton]

中文:
引理 coe_equivNatSumOfFintype_symm_apply
  条件: [Fintype α] (P : {P : α -> 自然数 // ∑ i, P i = n})
  证明: by
  obtain ⟨P, hP⟩ := P
  change Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm P) = Multiset.sum _
  ext a
  rw [Multiset.count_sum]
  simp [Multiset.count_singleton]
-/
@[simp] lemma coe_equivNatSumOfFintype_symm_apply [Fintype α] (P : {P : α -> Nat // ∑ i, P i = n}) :
    ((equivNatSumOfFintype α n).symm P : Multiset α) = ∑ a, ((P : α -> Nat) a) • {a} := by
  obtain ⟨P, hP⟩ := P
  change Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm P) = Multiset.sum _
  ext a
  rw [Multiset.count_sum]
  simp [Multiset.count_singleton]

end Sym
