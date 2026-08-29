/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.DFinsupp.Ext
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib/Data/Finsupp/Defs.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/

@[expose] public section

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

namespace DFinsupp

section Algebra

/--
Definition of `evalAddMonoidHom` / `evalAddMonoidHom` 的定义

English:
definition evalAddMonoidHom
  signature: [forall i, AddZeroClass (β i)] (i : ι)
  body: (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom

@[simp, norm_cast]

中文:
定义 evalAddMonoidHom
  签名: [对任意 i, 加法零类 (β i)] (i : ι)
  定义体: (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom

@[simp, norm_cast]

Depends on / 依赖: Pi.evalAddMonoidHom, coeFnAddMonoidHom, evalAddMonoidHom
-/
def evalAddMonoidHom [forall i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) ->+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom

@[simp, norm_cast]
/--
theorem `coe_finsetSum` / 定理 `coe_finsetSum`

English:
theorem coe_finsetSum
  given: {α} [forall i, AddCommMonoid (β i)] (s : Finset α) (g : α -> Π₀ i, β i)
  proof: map_sum coeFnAddMonoidHom g s

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

@[simp]

中文:
定理 coe_finsetSum
  条件: {α} [对任意 i, 加法交换幺半群 (β i)] (s : 有限集 α) (g : α -> Π₀ i, β i)
  证明: map_sum coeFnAddMonoidHom g s

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

@[simp]

Depends on / 依赖: coeFnAddMonoidHom, map_sum
-/
theorem coe_finsetSum {α} [forall i, AddCommMonoid (β i)] (s : Finset α) (g : α -> Π₀ i, β i) :
    ⇑(∑ a in s, g a) = ∑ a in s, ⇑(g a) :=
  map_sum coeFnAddMonoidHom g s

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

@[simp]
/--
theorem `finsetSum_apply` / 定理 `finsetSum_apply`

English:
theorem finsetSum_apply
  given: {α} [forall i, AddCommMonoid (β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι)
  proof: map_sum (evalAddMonoidHom i) g s

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

中文:
定理 finsetSum_apply
  条件: {α} [对任意 i, 加法交换幺半群 (β i)] (s : 有限集 α) (g : α -> Π₀ i, β i) (i : ι)
  证明: map_sum (evalAddMonoidHom i) g s

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

Depends on / 依赖: evalAddMonoidHom, map_sum
-/
theorem finsetSum_apply {α} [forall i, AddCommMonoid (β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) :
    (∑ a in s, g a) i = ∑ a in s, g a i :=
  map_sum (evalAddMonoidHom i) g s

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

end Algebra

section ProdAndSum

variable [DecidableEq ι]

/-- `DFinsupp.prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive /-- `sum f g` is the sum of `g i (f i)` over the support of `f`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] (f : Π₀ i, β i)
  body: ∏ i in f.support, g i (f i)

@[to_additive]

中文:
定义 乘积
  签名: [对任意 i, 零 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [交换幺半群 γ] (f : Π₀ i, β i)
  定义体: ∏ i in f.support, g i (f i)

@[to_additive]

Depends on / 依赖: f.support, support
-/
def prod [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] (f : Π₀ i, β i)
    (g : forall i, β i -> γ) : γ :=
  ∏ i in f.support, g i (f i)

@[to_additive]
/--
theorem `prod_of_support_subset` / 定理 `prod_of_support_subset`

English:
theorem prod_of_support_subset
  statement: [forall i, Zero (β i)]
  proof: by
  simp only [DFinsupp.prod]
  apply Finset.prod_subset hs
  intro i hi hi'
  simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
  rw [hi']; rw [map_zero]
  exact hi

中文:
定理 prod_of_support_subset
  结论: [对任意 i, 零 (β i)]
  证明: by
  simp only [DFinsupp.prod]
  apply Finset.prod_subset hs
  intro i hi hi'
  simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
  rw [hi']; rw [map_zero]
  exact hi

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_toFun, DFinsupp.prod, Finset, Finset.prod_subset, map_zero, mem_support_toFun, ne_eq, not_not, prod_subset
-/
theorem prod_of_support_subset [forall i, Zero (β i)]
    [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {g : (i : ι) -> β i -> γ} {s : Finset ι}
    (hs : f.support subseteq s) (map_zero : forall i in s, g i 0 = 1) :
    f.prod g = ∏ i in s, g i (f i) := by
  simp only [DFinsupp.prod]
  apply Finset.prod_subset hs
  intro i hi hi'
  simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
  rw [hi']; rw [map_zero]
  exact hi

/-- The product over two dfinsupps agree if the functions agree and are well-behaved within the
shared support. -/
@[to_additive (attr := gcongr only)
/-- The sum over two dfinsupps agree if the functions agree and are well-behaved within the
shared support. -/]
/--
theorem `prod_congr_of_eq_on_union` / 定理 `prod_congr_of_eq_on_union`

English:
theorem prod_congr_of_eq_on_union
  proof: by
  rw [prod_of_support_subset Finset.subset_union_left h1]; rw [prod_of_support_subset Finset.subset_union_right h2]
  exact Finset.prod_congr rfl h

@[to_additive (attr := simp)]

中文:
定理 prod_congr_of_eq_on_union
  证明: by
  rw [prod_of_support_subset Finset.subset_union_left h1]; rw [prod_of_support_subset Finset.subset_union_right h2]
  exact Finset.prod_congr rfl h

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_congr, Finset.subset_union_left, Finset.subset_union_right, prod_congr, prod_of_support_subset, subset_union_left, subset_union_right
-/
theorem prod_congr_of_eq_on_union
    [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {f1 f2 : Π₀ i, β i} {g1 g2 : (i : ι) -> β i -> γ}
    (h : forall x in f1.support union f2.support, g1 x (f1 x) = g2 x (f2 x))
    (h1 : forall x in f1.support union f2.support, g1 x 0 = 1)
    (h2 : forall x in f1.support union f2.support, g2 x 0 = 1) :
    f1.prod g1 = f2.prod g2 := by
  rw [prod_of_support_subset Finset.subset_union_left h1]; rw [prod_of_support_subset Finset.subset_union_right h2]
  exact Finset.prod_congr rfl h

@[to_additive (attr := simp)]
/--
theorem `_root_.map_dfinsuppProd` / 定理 `_root_.map_dfinsuppProd`

English:
theorem _root_.map_dfinsuppProd
  proof: map_prod _ _ _

@[to_additive]

中文:
定理 _root_.map_dfinsuppProd
  证明: map_prod _ _ _

@[to_additive]

Depends on / 依赖: map_prod
-/
theorem _root_.map_dfinsuppProd
    {R S H : Type*} [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [CommMonoid R] [CommMonoid S] [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀ i, β i)
    (g : forall i, β i -> R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

@[to_additive]
/--
theorem `prod_mapRange_index` / 定理 `prod_mapRange_index`

English:
theorem prod_mapRange_index
  statement: {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂} [forall i, Zero (β₁ i)]
  proof: by
  rw [mapRange_def]
  refine (Finset.prod_subset support_mk_subset ?_).trans ?_
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine Finset.prod_congr rfl ?_
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]

@[to_additive]

中文:
定理 prod_mapRange_index
  结论: {β₁ : ι -> 类型v₁} {β₂ : ι -> 类型v₂} [对任意 i, 零 (β₁ i)]
  证明: by
  rw [mapRange_def]
  refine (Finset.prod_subset support_mk_subset ?_).trans ?_
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine Finset.prod_congr rfl ?_
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]

@[to_additive]

Depends on / 依赖: Finset, Finset.coe_sort_coe, Finset.prod_congr, Finset.prod_subset, coe_sort_coe, dite_eq_ite, ite_true, mapRange_def, mem_support_toFun, mk_apply, ne_eq, not_false_iff, not_not, prod_congr, prod_subset, support_mk_subset
-/
theorem prod_mapRange_index {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂} [forall i, Zero (β₁ i)]
    [forall i, Zero (β₂ i)] [forall (i) (x : β₁ i), Decidable (x != 0)] [forall (i) (x : β₂ i), Decidable (x != 0)]
    [CommMonoid γ] {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : forall i, β₂ i -> γ}
    (h0 : forall i, h i 0 = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b) := by
  rw [mapRange_def]
  refine (Finset.prod_subset support_mk_subset ?_).trans ?_
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine Finset.prod_congr rfl ?_
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]

@[to_additive]
/--
theorem `prod_zero_index` / 定理 `prod_zero_index`

English:
theorem prod_zero_index
  statement: [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: rfl

@[to_additive]

中文:
定理 prod_zero_index
  结论: [对任意 i, 加法交换幺半群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: rfl

@[to_additive]
-/
theorem prod_zero_index [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [CommMonoid γ] {h : forall i, β i -> γ} : (0 : Π₀ i, β i).prod h = 1 :=
  rfl

@[to_additive]
/--
theorem `prod_single_index` / 定理 `prod_single_index`

English:
theorem prod_single_index
  statement: [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
  proof: by
  by_cases h : b != 0
  · simp [DFinsupp.prod, support_single h]
  · rw [not_not] at h
    simp [h, h_zero]
    rfl

@[to_additive]

中文:
定理 prod_single_index
  结论: [对任意 i, 零 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [交换幺半群 γ]
  证明: by
  by_cases h : b != 0
  · simp [DFinsupp.prod, support_single h]
  · rw [not_not] at h
    simp [h, h_zero]
    rfl

@[to_additive]

Depends on / 依赖: DFinsupp, DFinsupp.prod, h_zero, not_not, support_single
-/
theorem prod_single_index [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {i : ι} {b : β i} {h : forall i, β i -> γ} (h_zero : h i 0 = 1) : (single i b).prod h = h i b := by
  by_cases h : b != 0
  · simp [DFinsupp.prod, support_single h]
  · rw [not_not] at h
    simp [h, h_zero]
    rfl

@[to_additive]
/--
theorem `prod_neg_index` / 定理 `prod_neg_index`

English:
theorem prod_neg_index
  statement: [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
  proof: prod_mapRange_index h0

@[to_additive]

中文:
定理 prod_neg_index
  结论: [对任意 i, 加法群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [交换幺半群 γ]
  证明: prod_mapRange_index h0

@[to_additive]

Depends on / 依赖: prod_mapRange_index
-/
theorem prod_neg_index [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {g : Π₀ i, β i} {h : forall i, β i -> γ} (h0 : forall i, h i 0 = 1) :
    (-g).prod h = g.prod fun i b => h i (-b) :=
  prod_mapRange_index h0

@[to_additive]
/--
theorem `prod_comm` / 定理 `prod_comm`

English:
theorem prod_comm
  statement: {ι₁ ι₂ : Sort _} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} [DecidableEq ι₁]
  proof: Finset.prod_comm

@[simp]

中文:
定理 prod_comm
  结论: {ι₁ ι₂ : 类型层 _} {β₁ : ι₁ -> 类型} {β₂ : ι₂ -> 类型} [DecidableEq ι₁]
  证明: Finset.prod_comm

@[simp]

Depends on / 依赖: Finset, Finset.prod_comm, prod_comm
-/
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] [forall i, Zero (β₁ i)] [forall i, Zero (β₂ i)] [forall (i) (x : β₁ i), Decidable (x != 0)]
    [forall (i) (x : β₂ i), Decidable (x != 0)] [CommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i)
    (h : forall i, β₁ i -> forall i, β₂ i -> γ) :
    (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm

@[simp]
/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  statement: {ι} {β : ι -> Type v} {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁}
  proof: map_sum (evalAddMonoidHom i₂) _ f.support

中文:
定理 sum_apply
  结论: {ι} {β : ι -> 类型v} {ι₁ : 类型u₁} [DecidableEq ι₁] {β₁ : ι₁ -> 类型v₁}
  证明: map_sum (evalAddMonoidHom i₂) _ f.support

Depends on / 依赖: evalAddMonoidHom, f.support, map_sum, support
-/
theorem sum_apply {ι} {β : ι -> Type v} {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁}
    [forall i₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i), Decidable (x != 0)] [forall i, AddCommMonoid (β i)]
    {f : Π₀ i₁, β₁ i₁} {g : forall i₁, β₁ i₁ -> Π₀ i, β i} {i₂ : ι} :
    (f.sum g) i₂ = f.sum fun i₁ b => g i₁ b i₂ :=
  map_sum (evalAddMonoidHom i₂) _ f.support

/--
theorem `support_sum` / 定理 `support_sum`

English:
theorem support_sum
  statement: {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)]
  proof: by
  have :
    forall i₁ : ι,
      (f.sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) != 0 -> exists i : ι₁, f i != 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply] using this

@[to_additive (attr := simp)]

中文:
定理 support_sum
  结论: {ι₁ : 类型u₁} [DecidableEq ι₁] {β₁ : ι₁ -> 类型v₁} [对任意 i₁, 零 (β₁ i₁)]
  证明: by
  have :
    forall i₁ : ι,
      (f.sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) != 0 -> exists i : ι₁, f i != 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply] using this

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.exists_ne_zero_of_sum_ne_zero, Finset.mem_biUnion, Finset.subset_iff, exists_ne_zero_of_sum_ne_zero, f.sum, mem_biUnion, mem_support_iff, subset_iff, sum_apply
-/
theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)]
    [forall (i) (x : β₁ i), Decidable (x != 0)] [forall i, AddCommMonoid (β i)]
    [forall (i) (x : β i), Decidable (x != 0)] {f : Π₀ i₁, β₁ i₁} {g : forall i₁, β₁ i₁ -> Π₀ i, β i} :
    (f.sum g).support subseteq f.support.biUnion fun i => (g i (f i)).support := by
  have :
    forall i₁ : ι,
      (f.sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) != 0 -> exists i : ι₁, f i != 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply] using this

@[to_additive (attr := simp)]
/--
theorem `prod_one` / 定理 `prod_one`

English:
theorem prod_one
  statement: [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
  proof: Finset.prod_const_one

@[to_additive (attr := simp)]

中文:
定理 prod_one
  结论: [对任意 i, 加法交换幺半群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [交换幺半群 γ]
  证明: Finset.prod_const_one

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_const_one, prod_const_one
-/
theorem prod_one [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {f : Π₀ i, β i} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[to_additive (attr := simp)]
/--
theorem `prod_mul` / 定理 `prod_mul`

English:
theorem prod_mul
  statement: [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
  proof: Finset.prod_mul_distrib

@[to_additive (attr := simp)]

中文:
定理 prod_mul
  结论: [对任意 i, 加法交换幺半群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [交换幺半群 γ]
  证明: Finset.prod_mul_distrib

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_mul_distrib, prod_mul_distrib
-/
theorem prod_mul [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h₁ h₂ : forall i, β i -> γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
/--
theorem `prod_inv` / 定理 `prod_inv`

English:
theorem prod_inv
  statement: [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: (map_prod (invMonoidHom : γ ->* γ) _ f.support).symm

@[to_additive]

中文:
定理 prod_inv
  结论: [对任意 i, 加法交换幺半群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: (map_prod (invMonoidHom : γ ->* γ) _ f.support).symm

@[to_additive]

Depends on / 依赖: f.support, invMonoidHom, map_prod, support
-/
theorem prod_inv [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [DivisionCommMonoid γ] {f : Π₀ i, β i} {h : forall i, β i -> γ} :
    (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ ->* γ) _ f.support).symm

@[to_additive]
/--
theorem `prod_eq_one` / 定理 `prod_eq_one`

English:
theorem prod_eq_one
  statement: [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
  proof: Finset.prod_eq_one fun i _ => hyp i

中文:
定理 prod_eq_one
  结论: [对任意 i, 零 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [交换幺半群 γ]
  证明: Finset.prod_eq_one fun i _ => hyp i

Depends on / 依赖: Finset, Finset.prod_eq_one, prod_eq_one
-/
theorem prod_eq_one [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h : forall i, β i -> γ} (hyp : forall i, h i (f i) = 1) : f.prod h = 1 :=
  Finset.prod_eq_one fun i _ => hyp i

/--
theorem `smul_sum` / 定理 `smul_sum`

English:
theorem smul_sum
  statement: {α : Type*} [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: Finset.smul_sum

@[to_additive]

中文:
定理 smul_sum
  结论: {α : 类型} [对任意 i, 零 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: Finset.smul_sum

@[to_additive]

Depends on / 依赖: Finset, Finset.smul_sum, smul_sum
-/
theorem smul_sum {α : Type*} [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [AddCommMonoid γ] [DistribSMul α γ] {f : Π₀ i, β i} {h : forall i, β i -> γ} {c : α} :
    c • f.sum h = f.sum fun a b => c • h a b :=
  Finset.smul_sum

@[to_additive]
/--
theorem `prod_add_index` / 定理 `prod_add_index`

English:
theorem prod_add_index
  statement: [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: have f_eq : (∏ i in f.support union g.support, h i (f i)) = f.prod h :=
    (Finset.prod_subset Finset.subset_union_left <| by
        simp +contextual [h_zero]).symm
  have g_eq : (∏ i in f.support union g.support, h i (g i)) = g.prod h :=
    (Finset.prod_subset Finset.subset_union_right <| by
        simp +contextual [h_zero]).symm
  calc
    (∏ i in (f + g).support, h i ((f + g) i)) = ∏ i in f.support union g.support, h i ((f + g) i) :=
Finset.prod_subset support_add by
        simp +contextual [h_zero]
    _ = (∏ i in f.support union g.support, h i (f i)) * ∏ i in f.support union g.support, h i (g i) := by
      { simp [h_add, Finset.prod_mul_distrib] }
    _ = _ := by rw [f_eq, g_eq]

@[to_additive (attr := simp)]

中文:
定理 prod_add_index
  结论: [对任意 i, 加法交换幺半群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: have f_eq : (∏ i in f.support union g.support, h i (f i)) = f.prod h :=
    (Finset.prod_subset Finset.subset_union_left <| by
        simp +contextual [h_zero]).symm
  have g_eq : (∏ i in f.support union g.support, h i (g i)) = g.prod h :=
    (Finset.prod_subset Finset.subset_union_right <| by
        simp +contextual [h_zero]).symm
  calc
    (∏ i in (f + g).support, h i ((f + g) i)) = ∏ i in f.support union g.support, h i ((f + g) i) :=
Finset.prod_subset support_add by
        simp +contextual [h_zero]
    _ = (∏ i in f.support union g.support, h i (f i)) * ∏ i in f.support union g.support, h i (g i) := by
      { simp [h_add, Finset.prod_mul_distrib] }
    _ = _ := by rw [f_eq, g_eq]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_subset, Finset.subset_union_left, Finset.subset_union_right, contextual, f.prod, f.support, f_eq, g.prod, g.support, g_eq, h_zero, prod_subset, subset_union_left, subset_union_right, support, support_add
-/
theorem prod_add_index [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [CommMonoid γ] {f g : Π₀ i, β i} {h : forall i, β i -> γ} (h_zero : forall i, h i 0 = 1)
    (h_add : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f + g).prod h = f.prod h * g.prod h :=
  have f_eq : (∏ i in f.support union g.support, h i (f i)) = f.prod h :=
    (Finset.prod_subset Finset.subset_union_left <| by
        simp +contextual [h_zero]).symm
  have g_eq : (∏ i in f.support union g.support, h i (g i)) = g.prod h :=
    (Finset.prod_subset Finset.subset_union_right <| by
        simp +contextual [h_zero]).symm
  calc
    (∏ i in (f + g).support, h i ((f + g) i)) = ∏ i in f.support union g.support, h i ((f + g) i) :=
Finset.prod_subset support_add by
        simp +contextual [h_zero]
    _ = (∏ i in f.support union g.support, h i (f i)) * ∏ i in f.support union g.support, h i (g i) := by
      { simp [h_add, Finset.prod_mul_distrib] }
    _ = _ := by rw [f_eq, g_eq]

@[to_additive (attr := simp)]
/--
theorem `prod_eq_prod_fintype` / 定理 `prod_eq_prod_fintype`

English:
theorem prod_eq_prod_fintype
  statement: [Fintype ι] [forall i, Zero (β i)] [forall (i : ι) (x : β i), Decidable (x != 0)]
  proof: by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff]; rw [not_not] at hi
  rw [hi]; rw [hf]

中文:
定理 prod_eq_prod_fintype
  结论: [有限类型 ι] [对任意 i, 零 (β i)] [对任意 (i : ι) (x : β i), 可判定 (x != 0)]
  证明: by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff]; rw [not_not] at hi
  rw [hi]; rw [hf]

Depends on / 依赖: DFinsupp, DFinsupp.prod, Finset, Finset.prod_subset, mem_support_iff, not_not, prod_subset, subset_univ, support, v.support, v.support.subset_univ
-/
theorem prod_eq_prod_fintype [Fintype ι] [forall i, Zero (β i)] [forall (i : ι) (x : β i), Decidable (x != 0)]
    [CommMonoid γ] (v : Π₀ i, β i) {f : forall i, β i -> γ} (hf : forall i, f i 0 = 1) :
    v.prod f = ∏ i, f i (DFinsupp.equivFunOnFintype v i) := by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff]; rw [not_not] at hi
  rw [hi]; rw [hf]

section CommMonoidWithZero
variable [Π i, Zero (β i)] [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀ i, β i} {g : Π i, β i -> γ}

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

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff, prod_ne_zero_iff
-/
lemma prod_ne_zero_iff : f.prod g != 0 ↔ forall i in f.support, g i (f i) != 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero

/--
Definition of `sumZeroHom` / `sumZeroHom` 的定义

English:
definition sumZeroHom
  signature: [forall i, Zero (β i)] [AddCommMonoid γ] (φ : forall i, ZeroHom (β i) γ)
  body: (f.support'.lift fun s => ∑ i in Multiset.toFinset s.1, φ i (f i)) by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset inter sy.toFinset subseteq sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset inter sy.toFinset subseteq sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl

@[simp]

中文:
定义 sumZeroHom
  签名: [对任意 i, 零 (β i)] [加法交换幺半群 γ] (φ : 对任意 i, 保零态射 (β i) γ)
  定义体: (f.support'.lift fun s => ∑ i in Multiset.toFinset s.1, φ i (f i)) by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset inter sy.toFinset subseteq sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset inter sy.toFinset subseteq sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl

@[simp]

Depends on / 依赖: Finset, Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, Finset.sum_congr, Finset.sum_subset, Multiset, Multiset.mem_toFinse, Multiset.toFinset, Subtype, Subtype.coe_mk, coe_mk, f.support, inter_subset_left, inter_subset_right, mem_inter, mem_toFinse, subseteq, sum_congr, sum_subset
-/
def sumZeroHom [forall i, Zero (β i)] [AddCommMonoid γ] (φ : forall i, ZeroHom (β i) γ) :
    ZeroHom (Π₀ i, β i) γ where
  toFun f :=
(f.support'.lift fun s => ∑ i in Multiset.toFinset s.1, φ i (f i)) by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset inter sy.toFinset subseteq sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset inter sy.toFinset subseteq sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert! map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl

@[simp]
/--
theorem `sumZeroHom_single` / 定理 `sumZeroHom_single`

English:
theorem sumZeroHom_single
  statement: [forall i, Zero (β i)] [AddCommMonoid γ] (φ : forall i, ZeroHom (β i) γ) (i)
  proof: by
  dsimp [sumZeroHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton]; rw [Finset.sum_singleton]; rw [Pi.single_eq_same]

中文:
定理 sumZeroHom_single
  结论: [对任意 i, 零 (β i)] [加法交换幺半群 γ] (φ : 对任意 i, 保零态射 (β i) γ) (i)
  证明: by
  dsimp [sumZeroHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton]; rw [Finset.sum_singleton]; rw [Pi.single_eq_same]

Depends on / 依赖: Finset, Finset.sum_singleton, Multiset, Multiset.toFinset_singleton, Pi.single_eq_same, Trunc.lift_mk, lift_mk, single, single_eq_same, sumZeroHom, sum_singleton, toFinset_singleton
-/
theorem sumZeroHom_single [forall i, Zero (β i)] [AddCommMonoid γ] (φ : forall i, ZeroHom (β i) γ) (i)
    (x : β i) : sumZeroHom φ (single i x) = φ i x := by
  dsimp [sumZeroHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton]; rw [Finset.sum_singleton]; rw [Pi.single_eq_same]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `sumZeroHom_piSingle` / 定理 `sumZeroHom_piSingle`

English:
theorem sumZeroHom_piSingle
  given: [forall i, Zero (β i)] [AddCommMonoid γ] (i) (φ : ZeroHom (β i) γ)
  proof: by
  ext ⟨f, sf, hf⟩
  simp only [sumZeroHom, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk', ZeroHom.coe_comp,
    Function.comp_apply]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => ?_)]; rw [Pi.single_eq_same]
  · simp [hji]
  · simp [(hf i).resolve_left (by simpa using hi)]

中文:
定理 sumZeroHom_piSingle
  条件: [对任意 i, 零 (β i)] [加法交换幺半群 γ] (i) (φ : 保零态射 (β i) γ)
  证明: by
  ext ⟨f, sf, hf⟩
  simp only [sumZeroHom, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk', ZeroHom.coe_comp,
    Function.comp_apply]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => ?_)]; rw [Pi.single_eq_same]
  · simp [hji]
  · simp [(hf i).resolve_left (by simpa using hi)]

Depends on / 依赖: Finset, Finset.sum_eq_single, Function, Function.comp_apply, Pi.single_eq_same, Trunc.lift, ZeroHom, ZeroHom.coe_comp, ZeroHom.coe_mk, coe_comp, coe_mk, comp_apply, map_zero, resolve_left, single_eq_same, sumZeroHom, sum_eq_single, toFun_eq_coe
-/
theorem sumZeroHom_piSingle [forall i, Zero (β i)] [AddCommMonoid γ] (i) (φ : ZeroHom (β i) γ) :
    sumZeroHom (Pi.single i φ) = φ.comp { toFun := (· i), map_zero' := rfl } := by
  ext ⟨f, sf, hf⟩
  simp only [sumZeroHom, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk', ZeroHom.coe_comp,
    Function.comp_apply]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => ?_)]; rw [Pi.single_eq_same]
  · simp [hji]
  · simp [(hf i).resolve_left (by simpa using hi)]

/--
theorem `sumZeroHom_apply` / 定理 `sumZeroHom_apply`

English:
theorem sumZeroHom_apply
  statement: [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: by
  rcases f with ⟨f, s, hf⟩
  change (∑ i in _, _) = ∑ i in _ with _, _
  rw [Finset.sum_filter]; rw [Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, map_zero]

中文:
定理 sumZeroHom_apply
  结论: [对任意 i, 加法零类 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: by
  rcases f with ⟨f, s, hf⟩
  change (∑ i in _, _) = ∑ i in _ with _, _
  rw [Finset.sum_filter]; rw [Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, map_zero]

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_filter, Subtype, Subtype.coe_mk, coe_mk, map_zero, not_not, not_not.mp, split_ifs, sum_congr, sum_filter
-/
theorem sumZeroHom_apply [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [AddCommMonoid γ] (φ : forall i, ZeroHom (β i) γ) (f : Π₀ i, β i) :
    sumZeroHom φ f = f.sum fun x => φ x := by
  rcases f with ⟨f, s, hf⟩
  change (∑ i in _, _) = ∑ i in _ with _, _
  rw [Finset.sum_filter]; rw [Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, map_zero]

set_option backward.isDefEq.respectTransparency false in
/--
When summing over an `AddMonoidHom`, the decidability assumption is not needed, and the result is
also an `AddMonoidHom`.
-/
@[simps toZeroHom]
/--
Definition of `sumAddHom` / `sumAddHom` 的定义

English:
definition sumAddHom
  signature: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ)
  body: sumZeroHom fun i => φ i
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i in _, _) = (∑ i in _, _) + ∑ i in _, _
    simp only [AddMonoidHom.toZeroHom_coe, coe_add, coe_mk', Pi.add_apply, map_add,
      Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hf i).resolve_left H2]; rw [map_zero]
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hg i).resolve_left H2]; rw [map_zero]

@[simp]

中文:
定义 sumAddHom
  签名: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (φ : 对任意 i, β i ->+ γ)
  定义体: sumZeroHom fun i => φ i
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i in _, _) = (∑ i in _, _) + ∑ i in _, _
    simp only [AddMonoidHom.toZeroHom_coe, coe_add, coe_mk', Pi.add_apply, map_add,
      Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hf i).resolve_left H2]; rw [map_zero]
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hg i).resolve_left H2]; rw [map_zero]

@[simp]

Depends on / 依赖: sumZeroHom
-/
def sumAddHom [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) :
    (Π₀ i, β i) ->+ γ where
.toZeroHom __ := sumZeroHom fun i => φ i
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i in _, _) = (∑ i in _, _) + ∑ i in _, _
    simp only [AddMonoidHom.toZeroHom_coe, coe_add, coe_mk', Pi.add_apply, map_add,
      Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hf i).resolve_left H2]; rw [map_zero]
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset] at H2
        rw [(hg i).resolve_left H2]; rw [map_zero]

@[simp]
/--
theorem `sumAddHom_single` / 定理 `sumAddHom_single`

English:
theorem sumAddHom_single
  statement: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i)
  proof: sumZeroHom_single _ _ _

@[simp]

中文:
定理 sumAddHom_single
  结论: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (φ : 对任意 i, β i ->+ γ) (i)
  证明: sumZeroHom_single _ _ _

@[simp]

Depends on / 依赖: sumZeroHom_single
-/
theorem sumAddHom_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i)
    (x : β i) : sumAddHom φ (single i x) = φ i x := sumZeroHom_single _ _ _

@[simp]
/--
theorem `sumAddHom_piSingle` / 定理 `sumAddHom_piSingle`

English:
theorem sumAddHom_piSingle
  given: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (i) (φ : β i ->+ γ)
  proof: AddMonoidHom.toZeroHom_injective by
    convert! sumZeroHom_piSingle i φ.toZeroHom using 1
    rw [DFinsupp.sumAddHom_toZeroHom]
    conv_lhs =>
      enter [1, i]
      rw [Pi.apply_single (fun i (x : β i ->+ γ) => x.toZeroHom) (fun _ => rfl)]

@[simp]

中文:
定理 sumAddHom_piSingle
  条件: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (i) (φ : β i ->+ γ)
  证明: AddMonoidHom.toZeroHom_injective by
    convert! sumZeroHom_piSingle i φ.toZeroHom using 1
    rw [DFinsupp.sumAddHom_toZeroHom]
    conv_lhs =>
      enter [1, i]
      rw [Pi.apply_single (fun i (x : β i ->+ γ) => x.toZeroHom) (fun _ => rfl)]

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toZeroHom_injective, DFinsupp, DFinsupp.sumAddHom_toZeroHom, Pi.apply_single, apply_single, conv_lhs, convert, sumAddHom_toZeroHom, sumZeroHom_piSingle, toZeroHom, toZeroHom_injective, x.toZeroHom
-/
theorem sumAddHom_piSingle [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (i) (φ : β i ->+ γ) :
    sumAddHom (Pi.single i φ) = φ.comp (evalAddMonoidHom i) :=
AddMonoidHom.toZeroHom_injective by
    convert! sumZeroHom_piSingle i φ.toZeroHom using 1
    rw [DFinsupp.sumAddHom_toZeroHom]
    conv_lhs =>
      enter [1, i]
      rw [Pi.apply_single (fun i (x : β i ->+ γ) => x.toZeroHom) (fun _ => rfl)]

@[simp]
/--
theorem `sumAddHom_comp_single` / 定理 `sumAddHom_comp_single`

English:
theorem sumAddHom_comp_single
  statement: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ)
  proof: AddMonoidHom.ext fun x => sumAddHom_single f i x

中文:
定理 sumAddHom_comp_single
  结论: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (f : 对任意 i, β i ->+ γ)
  证明: AddMonoidHom.ext fun x => sumAddHom_single f i x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, Fin.getElem_fin, Fin.is_lt, Option.getD_some, Option.get_some, _getD, _pos, getD_eq_getElem, getD_some, getElem, getElem_fin, get_some, is_lt, sumAddHom_single
-/
theorem sumAddHom_comp_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ)
    (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sumAddHom_single f i x

/--
theorem `sumAddHom_apply` / 定理 `sumAddHom_apply`

English:
theorem sumAddHom_apply
  statement: [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: sumZeroHom_apply _ _

中文:
定理 sumAddHom_apply
  结论: [对任意 i, 加法零类 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: sumZeroHom_apply _ _

Depends on / 依赖: sumZeroHom_apply
-/
theorem sumAddHom_apply [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (f : Π₀ i, β i) : sumAddHom φ f = f.sum fun x => φ x :=
  sumZeroHom_apply _ _

/--
theorem `sumAddHom_comm` / 定理 `sumAddHom_comm`

English:
theorem sumAddHom_comm
  statement: {ι₁ ι₂ : Sort _} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} {γ : Type*}
  proof: by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simpa [sumAddHom, sumZeroHom, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk,
      AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
    using Finset.sum_comm

中文:
定理 sumAddHom_comm
  结论: {ι₁ ι₂ : 类型层 _} {β₁ : ι₁ -> 类型} {β₂ : ι₂ -> 类型} {γ : 类型}
  证明: by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simpa [sumAddHom, sumZeroHom, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk,
      AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
    using Finset.sum_comm

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_mk, AddMonoidHom.finsetSum_apply, AddMonoidHom.flip_apply, Finset, Finset.sum_comm, Trunc.lift, ZeroHom, ZeroHom.coe_mk, coe_mk, finsetSum_apply, flip_apply, sumAddHom, sumZeroHom, sum_comm, toFun_eq_coe
-/
theorem sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ -> Type*} {β₂ : ι₂ -> Type*} {γ : Type*}
    [DecidableEq ι₁] [DecidableEq ι₂] [forall i, AddZeroClass (β₁ i)] [forall i, AddZeroClass (β₂ i)]
    [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : forall i j, β₁ i ->+ β₂ j ->+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ := by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simpa [sumAddHom, sumZeroHom, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk,
      AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
    using Finset.sum_comm

/-- The `DFinsupp` version of `Finsupp.liftAddHom` -/
@[simps apply symm_apply]
/--
Definition of `liftAddHom` / `liftAddHom` 的定义

English:
definition liftAddHom
  signature: [forall i, AddZeroClass (β i)] [AddCommMonoid γ]
  body: sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp

中文:
定义 liftAddHom
  签名: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ]
  定义体: sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp

Depends on / 依赖: sumAddHom
-/
def liftAddHom [forall i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (forall i, β i ->+ γ) ≃+ ((Π₀ i, β i) ->+ γ) where
  toFun := sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp

/--
theorem `liftAddHom_singleAddHom` / 定理 `liftAddHom_singleAddHom`

English:
theorem liftAddHom_singleAddHom
  given: [forall i, AddCommMonoid (β i)]
  proof: liftAddHom.toEquiv.eq_symm_apply.1 rfl

中文:
定理 liftAddHom_singleAddHom
  条件: [对任意 i, 加法交换幺半群 (β i)]
  证明: liftAddHom.toEquiv.eq_symm_apply.1 rfl

Depends on / 依赖: eq_symm_apply, liftAddHom, liftAddHom.toEquiv.eq_symm_apply, toEquiv
-/
theorem liftAddHom_singleAddHom [forall i, AddCommMonoid (β i)] :
    liftAddHom (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  liftAddHom.toEquiv.eq_symm_apply.1 rfl

/--
theorem `liftAddHom_apply_single` / 定理 `liftAddHom_apply_single`

English:
theorem liftAddHom_apply_single
  statement: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ)
  proof: by simp

中文:
定理 liftAddHom_apply_single
  结论: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (f : 对任意 i, β i ->+ γ)
  证明: by simp
-/
theorem liftAddHom_apply_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ)
    (i : ι) (x : β i) : liftAddHom f (single i x) = f i x := by simp

/--
theorem `liftAddHom_comp_single` / 定理 `liftAddHom_comp_single`

English:
theorem liftAddHom_comp_single
  statement: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ)
  proof: by simp

中文:
定理 liftAddHom_comp_single
  结论: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (f : 对任意 i, β i ->+ γ)
  证明: by simp
-/
theorem liftAddHom_comp_single [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ)
    (i : ι) : (liftAddHom f).comp (singleAddHom β i) = f i := by simp

/--
theorem `comp_liftAddHom` / 定理 `comp_liftAddHom`

English:
theorem comp_liftAddHom
  statement: {δ : Type*} [forall i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
  proof: liftAddHom.symm_apply_eq.1
    funext fun a => by
      rw [liftAddHom_symm_apply]; rw [AddMonoidHom.comp_assoc]; rw [liftAddHom_comp_single]

@[simp]

中文:
定理 comp_liftAddHom
  结论: {δ : 类型} [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] [加法交换幺半群 δ]
  证明: liftAddHom.symm_apply_eq.1
    funext fun a => by
      rw [liftAddHom_symm_apply]; rw [AddMonoidHom.comp_assoc]; rw [liftAddHom_comp_single]

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_assoc, comp_assoc, liftAddHom, liftAddHom.symm_apply_eq, liftAddHom_comp_single, liftAddHom_symm_apply, symm_apply_eq
-/
theorem comp_liftAddHom {δ : Type*} [forall i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ ->+ δ) (f : forall i, β i ->+ γ) :
    g.comp (liftAddHom f) = liftAddHom fun a => g.comp (f a) :=
liftAddHom.symm_apply_eq.1
    funext fun a => by
      rw [liftAddHom_symm_apply]; rw [AddMonoidHom.comp_assoc]; rw [liftAddHom_comp_single]

@[simp]
/--
theorem `sumAddHom_zero` / 定理 `sumAddHom_zero`

English:
theorem sumAddHom_zero
  given: [forall i, AddZeroClass (β i)] [AddCommMonoid γ]
  proof: map_zero liftAddHom

@[simp]

中文:
定理 sumAddHom_zero
  条件: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ]
  证明: map_zero liftAddHom

@[simp]

Depends on / 依赖: liftAddHom, map_zero
-/
theorem sumAddHom_zero [forall i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (sumAddHom fun i => (0 : β i ->+ γ)) = 0 :=
  map_zero liftAddHom

@[simp]
/--
theorem `sumAddHom_add` / 定理 `sumAddHom_add`

English:
theorem sumAddHom_add
  statement: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (g : forall i, β i ->+ γ)
  proof: map_add liftAddHom _ _

@[simp]

中文:
定理 sumAddHom_add
  结论: [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] (g : 对任意 i, β i ->+ γ)
  证明: map_add liftAddHom _ _

@[simp]

Depends on / 依赖: liftAddHom, map_add
-/
theorem sumAddHom_add [forall i, AddZeroClass (β i)] [AddCommMonoid γ] (g : forall i, β i ->+ γ)
    (h : forall i, β i ->+ γ) : (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  map_add liftAddHom _ _

@[simp]
/--
theorem `sumAddHom_singleAddHom` / 定理 `sumAddHom_singleAddHom`

English:
theorem sumAddHom_singleAddHom
  given: [forall i, AddCommMonoid (β i)]
  proof: liftAddHom_singleAddHom

中文:
定理 sumAddHom_singleAddHom
  条件: [对任意 i, 加法交换幺半群 (β i)]
  证明: liftAddHom_singleAddHom

Depends on / 依赖: liftAddHom_singleAddHom
-/
theorem sumAddHom_singleAddHom [forall i, AddCommMonoid (β i)] :
    sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  liftAddHom_singleAddHom

/--
theorem `comp_sumAddHom` / 定理 `comp_sumAddHom`

English:
theorem comp_sumAddHom
  statement: {δ : Type*} [forall i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
  proof: comp_liftAddHom _ _

中文:
定理 comp_sumAddHom
  结论: {δ : 类型} [对任意 i, 加法零类 (β i)] [加法交换幺半群 γ] [加法交换幺半群 δ]
  证明: comp_liftAddHom _ _

Depends on / 依赖: comp_liftAddHom
-/
theorem comp_sumAddHom {δ : Type*} [forall i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ ->+ δ) (f : forall i, β i ->+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_liftAddHom _ _

/--
theorem `sum_sub_index` / 定理 `sum_sub_index`

English:
theorem sum_sub_index
  statement: [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x != 0)] [AddCommGroup γ]
  proof: by
  have := (liftAddHom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [liftAddHom_apply]; rw [sumAddHom_apply]; rw [sumAddHom_apply]; rw [sumAddHom_apply] at this
  exact this

@[to_additive]

中文:
定理 sum_sub_index
  结论: [对任意 i, 加法群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] [加法交换群 γ]
  证明: by
  have := (liftAddHom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [liftAddHom_apply]; rw [sumAddHom_apply]; rw [sumAddHom_apply]; rw [sumAddHom_apply] at this
  exact this

@[to_additive]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ofMapSub, h_sub, liftAddHom, liftAddHom_apply, map_sub, ofMapSub, sumAddHom_apply
-/
theorem sum_sub_index [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x != 0)] [AddCommGroup γ]
    {f g : Π₀ i, β i} {h : forall i, β i -> γ} (h_sub : forall i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
    (f - g).sum h = f.sum h - g.sum h := by
  have := (liftAddHom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [liftAddHom_apply]; rw [sumAddHom_apply]; rw [sumAddHom_apply]; rw [sumAddHom_apply] at this
  exact this

@[to_additive]
/--
theorem `prod_finsetSum_index` / 定理 `prod_finsetSum_index`

English:
theorem prod_finsetSum_index
  statement: {γ : Type w} {α : Type x} [forall i, AddCommMonoid (β i)]
  proof: by
  classical
  exact Finset.induction_on s (by simp [prod_zero_index])
        (by simp +contextual [prod_add_index, h_zero, h_add])

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]

中文:
定理 prod_finsetSum_index
  结论: {γ : 类型 w} {α : 类型 x} [对任意 i, 加法交换幺半群 (β i)]
  证明: by
  classical
  exact Finset.induction_on s (by simp [prod_zero_index])
        (by simp +contextual [prod_add_index, h_zero, h_add])

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]

Depends on / 依赖: Finset, Finset.induction_on, classical, contextual, h_add, h_zero, induction_on, prod_add_index, prod_zero_index
-/
theorem prod_finsetSum_index {γ : Type w} {α : Type x} [forall i, AddCommMonoid (β i)]
    [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {s : Finset α} {g : α -> Π₀ i, β i}
    {h : forall i, β i -> γ} (h_zero : forall i, h i 0 = 1)
    (h_add : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (∏ i in s, (g i).prod h) = (∑ i in s, g i).prod h := by
  classical
  exact Finset.induction_on s (by simp [prod_zero_index])
        (by simp +contextual [prod_add_index, h_zero, h_add])

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]
/--
theorem `prod_sum_index` / 定理 `prod_sum_index`

English:
theorem prod_sum_index
  statement: {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)]
  proof: (prod_finsetSum_index h_zero h_add).symm

@[simp]

中文:
定理 prod_sum_index
  结论: {ι₁ : 类型u₁} [DecidableEq ι₁] {β₁ : ι₁ -> 类型v₁} [对任意 i₁, 零 (β₁ i₁)]
  证明: (prod_finsetSum_index h_zero h_add).symm

@[simp]

Depends on / 依赖: h_add, h_zero, prod_finsetSum_index
-/
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)]
    [forall (i) (x : β₁ i), Decidable (x != 0)] [forall i, AddCommMonoid (β i)]
    [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {f : Π₀ i₁, β₁ i₁}
    {g : forall i₁, β₁ i₁ -> Π₀ i, β i} {h : forall i, β i -> γ} (h_zero : forall i, h i 0 = 1)
    (h_add : forall i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (f.sum g).prod h = f.prod fun i b => (g i b).prod h :=
  (prod_finsetSum_index h_zero h_add).symm

@[simp]
/--
theorem `sum_single` / 定理 `sum_single`

English:
theorem sum_single
  given: [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i}
  proof: by
  have := DFunLike.congr_fun (liftAddHom_singleAddHom (β := β)) f
  rw [liftAddHom_apply]; rw [sumAddHom_apply] at this
  exact this

@[to_additive]

中文:
定理 sum_single
  条件: [对任意 i, 加法交换幺半群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] {f : Π₀ i, β i}
  证明: by
  have := DFunLike.congr_fun (liftAddHom_singleAddHom (β := β)) f
  rw [liftAddHom_apply]; rw [sumAddHom_apply] at this
  exact this

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, liftAddHom_apply, liftAddHom_singleAddHom, sumAddHom_apply
-/
theorem sum_single [forall i, AddCommMonoid (β i)] [forall (i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i} :
    f.sum single = f := by
  have := DFunLike.congr_fun (liftAddHom_singleAddHom (β := β)) f
  rw [liftAddHom_apply]; rw [sumAddHom_apply] at this
  exact this

@[to_additive]
/--
theorem `prod_subtypeDomain_index` / 定理 `prod_subtypeDomain_index`

English:
theorem prod_subtypeDomain_index
  statement: [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: by
  refine Finset.prod_bij (fun p _ => p) ?_ ?_ ?_ ?_ <;> aesop

中文:
定理 prod_subtypeDomain_index
  结论: [对任意 i, 零 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: by
  refine Finset.prod_bij (fun p _ => p) ?_ ?_ ?_ ?_ <;> aesop

Depends on / 依赖: Finset, Finset.prod_bij, prod_bij
-/
theorem prod_subtypeDomain_index [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [CommMonoid γ] {v : Π₀ i, β i} {p : ι -> Prop} [DecidablePred p] {h : forall i, β i -> γ}
    (hp : forall x in v.support, p x) : (v.subtypeDomain p).prod (fun i b => h i b) = v.prod h := by
  refine Finset.prod_bij (fun p _ => p) ?_ ?_ ?_ ?_ <;> aesop

/--
theorem `subtypeDomain_sum` / 定理 `subtypeDomain_sum`

English:
theorem subtypeDomain_sum
  statement: {ι} {β : ι -> Type v} [forall i, AddCommMonoid (β i)] {s : Finset γ}
  proof: map_sum (subtypeDomainAddMonoidHom β p) _ s

中文:
定理 subtypeDomain_sum
  结论: {ι} {β : ι -> 类型v} [对任意 i, 加法交换幺半群 (β i)] {s : 有限集 γ}
  证明: map_sum (subtypeDomainAddMonoidHom β p) _ s

Depends on / 依赖: map_sum, subtypeDomainAddMonoidHom
-/
theorem subtypeDomain_sum {ι} {β : ι -> Type v} [forall i, AddCommMonoid (β i)] {s : Finset γ}
    {h : γ -> Π₀ i, β i} {p : ι -> Prop} [DecidablePred p] :
    (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  map_sum (subtypeDomainAddMonoidHom β p) _ s

/--
theorem `subtypeDomain_finsupp_sum` / 定理 `subtypeDomain_finsupp_sum`

English:
theorem subtypeDomain_finsupp_sum
  statement: {ι} {β : ι -> Type v} {δ : γ -> Type x} [DecidableEq γ]
  proof: subtypeDomain_sum

中文:
定理 subtypeDomain_finsupp_sum
  结论: {ι} {β : ι -> 类型v} {δ : γ -> 类型 x} [DecidableEq γ]
  证明: subtypeDomain_sum

Depends on / 依赖: subtypeDomain_sum
-/
theorem subtypeDomain_finsupp_sum {ι} {β : ι -> Type v} {δ : γ -> Type x} [DecidableEq γ]
    [forall c, Zero (δ c)] [forall (c) (x : δ c), Decidable (x != 0)]
    [forall i, AddCommMonoid (β i)] {p : ι -> Prop} [DecidablePred p]
    {s : Π₀ c, δ c} {h : forall c, δ c -> Π₀ i, β i} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum

end ProdAndSum

end DFinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `AddMonoidHom.map_sum`, `AddMonoidHom.coe_finsetSum`,
and `AddMonoidHom.finsetSum_apply` for `DFinsupp.sum` and `DFinsupp.sumAddHom` instead of
`Finset.sum`.

We provide these for `AddMonoidHom`, `MonoidHom`, `RingHom`, `AddEquiv`, and `MulEquiv`.

Lemmas for `LinearMap` and `LinearEquiv` are in another file.
-/


section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type*}
variable [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_dfinsuppProd` / 定理 `coe_dfinsuppProd`

English:
theorem coe_dfinsuppProd
  given: [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : forall i, β i -> R ->* S)
  proof: coe_finsetProd _ _

@[to_additive]

中文:
定理 coe_dfinsuppProd
  条件: [MulOne类 R] [交换幺半群 S] (f : Π₀ i, β i) (g : 对任意 i, β i -> R ->* S)
  证明: coe_finsetProd _ _

@[to_additive]

Depends on / 依赖: coe_finsetProd
-/
theorem coe_dfinsuppProd [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : forall i, β i -> R ->* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finsetProd _ _

@[to_additive]
/--
theorem `dfinsuppProd_apply` / 定理 `dfinsuppProd_apply`

English:
theorem dfinsuppProd_apply
  statement: [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : forall i, β i -> R ->* S)
  proof: finsetProd_apply _ _ _

中文:
定理 dfinsuppProd_apply
  结论: [MulOne类 R] [交换幺半群 S] (f : Π₀ i, β i) (g : 对任意 i, β i -> R ->* S)
  证明: finsetProd_apply _ _ _

Depends on / 依赖: finsetProd_apply
-/
theorem dfinsuppProd_apply [MulOneClass R] [CommMonoid S] (f : Π₀ i, β i) (g : forall i, β i -> R ->* S)
    (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r :=
  finsetProd_apply _ _ _

end MonoidHom

/-! The above lemmas, repeated for `DFinsupp.sumAddHom`. -/


namespace AddMonoidHom

variable {R S : Type*}

open DFinsupp

@[simp]
/--
theorem `map_dfinsuppSumAddHom` / 定理 `map_dfinsuppSumAddHom`

English:
theorem map_dfinsuppSumAddHom
  statement: [AddCommMonoid R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
  proof: DFunLike.congr_fun (comp_liftAddHom h g) f

中文:
定理 map_dfinsuppSumAddHom
  结论: [加法交换幺半群 R] [加法交换幺半群 S] [对任意 i, 加法零类 (β i)]
  证明: DFunLike.congr_fun (comp_liftAddHom h g) f

Depends on / 依赖: DFunLike, DFunLike.congr_fun, _getD, comp_liftAddHom, congr_fun, getD_default_eq_getI, getD_eq_getElem
-/
theorem map_dfinsuppSumAddHom [AddCommMonoid R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
    (h : R ->+ S) (f : Π₀ i, β i) (g : forall i, β i ->+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h g) f

/--
theorem `dfinsuppSumAddHom_apply` / 定理 `dfinsuppSumAddHom_apply`

English:
theorem dfinsuppSumAddHom_apply
  statement: [AddZeroClass R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
  proof: map_dfinsuppSumAddHom (eval r) f g

@[simp, norm_cast]

中文:
定理 dfinsuppSumAddHom_apply
  结论: [加法零类 R] [加法交换幺半群 S] [对任意 i, 加法零类 (β i)]
  证明: map_dfinsuppSumAddHom (eval r) f g

@[simp, norm_cast]

Depends on / 依赖: map_dfinsuppSumAddHom
-/
theorem dfinsuppSumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : forall i, β i ->+ R ->+ S) (r : R) :
    (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsuppSumAddHom (eval r) f g

@[simp, norm_cast]
/--
theorem `coe_dfinsuppSumAddHom` / 定理 `coe_dfinsuppSumAddHom`

English:
theorem coe_dfinsuppSumAddHom
  statement: [AddZeroClass R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
  proof: map_dfinsuppSumAddHom (coeFn R S) f g

中文:
定理 coe_dfinsuppSumAddHom
  结论: [加法零类 R] [加法交换幺半群 S] [对任意 i, 加法零类 (β i)]
  证明: map_dfinsuppSumAddHom (coeFn R S) f g

Depends on / 依赖: map_dfinsuppSumAddHom
-/
theorem coe_dfinsuppSumAddHom [AddZeroClass R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : forall i, β i ->+ R ->+ S) :
    ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsuppSumAddHom (coeFn R S) f g

end AddMonoidHom

namespace RingHom

variable {R S : Type*}

open DFinsupp

@[simp]
/--
theorem `map_dfinsuppSumAddHom` / 定理 `map_dfinsuppSumAddHom`

English:
theorem map_dfinsuppSumAddHom
  statement: [NonAssocSemiring R] [NonAssocSemiring S] [forall i, AddZeroClass (β i)]
  proof: DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

中文:
定理 map_dfinsuppSumAddHom
  结论: [非结合半环 R] [非结合半环 S] [对任意 i, 加法零类 (β i)]
  证明: DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

Depends on / 依赖: DFunLike, DFunLike.congr_fun, comp_liftAddHom, congr_fun, h.toAddMonoidHom, toAddMonoidHom
-/
theorem map_dfinsuppSumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [forall i, AddZeroClass (β i)]
    (h : R ->+* S) (f : Π₀ i, β i) (g : forall i, β i ->+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

end RingHom

namespace AddEquiv

variable {R S : Type*}

open DFinsupp

@[simp]
/--
theorem `map_dfinsuppSumAddHom` / 定理 `map_dfinsuppSumAddHom`

English:
theorem map_dfinsuppSumAddHom
  statement: [AddCommMonoid R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
  proof: DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

中文:
定理 map_dfinsuppSumAddHom
  结论: [加法交换幺半群 R] [加法交换幺半群 S] [对任意 i, 加法零类 (β i)]
  证明: DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

Depends on / 依赖: DFunLike, DFunLike.congr_fun, comp_liftAddHom, congr_fun, h.toAddMonoidHom, toAddMonoidHom
-/
theorem map_dfinsuppSumAddHom [AddCommMonoid R] [AddCommMonoid S] [forall i, AddZeroClass (β i)]
    (h : R ≃+ S) (f : Π₀ i, β i) (g : forall i, β i ->+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

end AddEquiv

end
