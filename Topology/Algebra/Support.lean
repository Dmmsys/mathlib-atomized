/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The topological support of a function

In this file we define the topological support of a function `f`, `tsupport f`, as the closure of
the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `mulTSupport` & `tsupport`
* `HasCompactMulSupport` & `HasCompactSupport`

## TODO

The definitions have been put in the root namespace following many other topological definitions,
like `Embedding`. Since then, `Embedding` was renamed to `Topology.IsEmbedding`, so it might be
worth reconsidering namespacing the definitions here.
-/

@[expose] public section


open Function Set Filter Topology

variable {X α α' β γ δ M R : Type*}

section One

variable [One α] [TopologicalSpace X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
set of all elements where the function is not equal to 1. -/
@[to_additive /-- The topological support of a function is the closure of its support. i.e. the
closure of the set of all elements where the function is nonzero. -/]
/--
Definition of `mulTSupport` / `mulTSupport` 的定义

English:
definition mulTSupport
  signature: (f : X -> α)
  body: closure (mulSupport f)

@[to_additive]

中文:
定义 mulTSupport
  签名: (f : X -> α)
  定义体: closure (mulSupport f)

@[to_additive]

Depends on / 依赖: closure, mulSupport
-/
def mulTSupport (f : X -> α) : Set X := closure (mulSupport f)

@[to_additive]
/--
theorem `subset_mulTSupport` / 定理 `subset_mulTSupport`

English:
theorem subset_mulTSupport
  given: (f : X -> α)
  statement: mulSupport f subseteq mulTSupport f
  proof: subset_closure

@[to_additive]

中文:
定理 subset_mulTSupport
  条件: (f : X -> α)
  结论: mulSupport f subseteq mulTSupport f
  证明: subset_closure

@[to_additive]

Depends on / 依赖: subset_closure
-/
theorem subset_mulTSupport (f : X -> α) : mulSupport f subseteq mulTSupport f :=
  subset_closure

@[to_additive]
/--
theorem `isClosed_mulTSupport` / 定理 `isClosed_mulTSupport`

English:
theorem isClosed_mulTSupport
  given: (f : X -> α)
  statement: IsClosed (mulTSupport f)
  proof: isClosed_closure

@[to_additive]

中文:
定理 isClosed_mulTSupport
  条件: (f : X -> α)
  结论: 是闭集 (mulTSupport f)
  证明: isClosed_closure

@[to_additive]

Depends on / 依赖: isClosed_closure
-/
theorem isClosed_mulTSupport (f : X -> α) : IsClosed (mulTSupport f) :=
  isClosed_closure

@[to_additive]
/--
theorem `mulTSupport_eq_empty_iff` / 定理 `mulTSupport_eq_empty_iff`

English:
theorem mulTSupport_eq_empty_iff
  given: {f : X -> α}
  statement: mulTSupport f = ∅ ↔ f = 1
  proof: by
  rw [mulTSupport]; rw [closure_empty_iff]; rw [mulSupport_eq_empty_iff]

@[to_additive (attr := simp)]

中文:
定理 mulTSupport_eq_empty_iff
  条件: {f : X -> α}
  结论: mulTSupport f = ∅ ↔ f = 1
  证明: by
  rw [mulTSupport]; rw [closure_empty_iff]; rw [mulSupport_eq_empty_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: closure_empty_iff, mulSupport_eq_empty_iff, mulTSupport
-/
theorem mulTSupport_eq_empty_iff {f : X -> α} : mulTSupport f = ∅ ↔ f = 1 := by
  rw [mulTSupport]; rw [closure_empty_iff]; rw [mulSupport_eq_empty_iff]

@[to_additive (attr := simp)]
/--
theorem `mulTSupport_fun_one` / 定理 `mulTSupport_fun_one`

English:
theorem mulTSupport_fun_one
  statement: mulTSupport (fun _ => 1 : X -> α) = ∅
  proof: by
  rw [mulTSupport]; rw [mulSupport_fun_one]; rw [closure_empty]

@[to_additive (attr := simp)]

中文:
定理 mulTSupport_fun_one
  结论: mulTSupport (fun _ => 1 : X -> α) = ∅
  证明: by
  rw [mulTSupport]; rw [mulSupport_fun_one]; rw [closure_empty]

@[to_additive (attr := simp)]

Depends on / 依赖: closure_empty, mulSupport_fun_one, mulTSupport
-/
theorem mulTSupport_fun_one : mulTSupport (fun _ => 1 : X -> α) = ∅ := by
  rw [mulTSupport]; rw [mulSupport_fun_one]; rw [closure_empty]

@[to_additive (attr := simp)]
/--
theorem `mulTSupport_one` / 定理 `mulTSupport_one`

English:
theorem mulTSupport_one
  statement: mulTSupport (1 : X -> α) = ∅
  proof: by
  rw [mulTSupport]; rw [mulSupport_one]; rw [closure_empty]

@[to_additive]

中文:
定理 mulTSupport_one
  结论: mulTSupport (1 : X -> α) = ∅
  证明: by
  rw [mulTSupport]; rw [mulSupport_one]; rw [closure_empty]

@[to_additive]

Depends on / 依赖: closure_empty, mulSupport_one, mulTSupport
-/
theorem mulTSupport_one : mulTSupport (1 : X -> α) = ∅ := by
  rw [mulTSupport]; rw [mulSupport_one]; rw [closure_empty]

@[to_additive]
/--
theorem `mulTSupport_binop_subset` / 定理 `mulTSupport_binop_subset`

English:
theorem mulTSupport_binop_subset
  statement: [One β] [One γ] (op : α -> β -> γ)
  proof: .trans closure_union.subset closure_mono (mulSupport_binop_subset op op1 f g)

@[to_additive]

中文:
定理 mulTSupport_binop_subset
  结论: [幺 β] [幺 γ] (op : α -> β -> γ)
  证明: .trans closure_union.subset closure_mono (mulSupport_binop_subset op op1 f g)

@[to_additive]

Depends on / 依赖: closure_mono, closure_union, closure_union.subset, mulSupport_binop_subset, subset
-/
theorem mulTSupport_binop_subset [One β] [One γ] (op : α -> β -> γ)
    (op1 : op 1 1 = 1) (f : X -> α) (g : X -> β) :
    mulTSupport (fun x => op (f x) (g x)) subseteq mulTSupport f union mulTSupport g :=
.trans closure_union.subset closure_mono (mulSupport_binop_subset op op1 f g)

@[to_additive]
/--
lemma `mulTSupport_comp_subset` / 引理 `mulTSupport_comp_subset`

English:
lemma mulTSupport_comp_subset
  given: [One β] {g : α -> β} (hg : g 1 = 1) (f : X -> α)
  proof: closure_mono (mulSupport_comp_subset hg f)

@[to_additive]

中文:
引理 mulTSupport_comp_subset
  条件: [幺 β] {g : α -> β} (hg : g 1 = 1) (f : X -> α)
  证明: closure_mono (mulSupport_comp_subset hg f)

@[to_additive]

Depends on / 依赖: closure_mono, mulSupport_comp_subset
-/
lemma mulTSupport_comp_subset [One β] {g : α -> β} (hg : g 1 = 1) (f : X -> α) :
    mulTSupport (g ∘ f) subseteq mulTSupport f :=
  closure_mono (mulSupport_comp_subset hg f)

@[to_additive]
/--
lemma `mulTSupport_subset_comp` / 引理 `mulTSupport_subset_comp`

English:
lemma mulTSupport_subset_comp
  given: [One β] {g : α -> β} (hg : forall {x}, g x = 1 -> x = 1) (f : X -> α)
  proof: closure_mono (mulSupport_subset_comp hg f)

@[to_additive]

中文:
引理 mulTSupport_subset_comp
  条件: [幺 β] {g : α -> β} (hg : 对任意 {x}, g x = 1 -> x = 1) (f : X -> α)
  证明: closure_mono (mulSupport_subset_comp hg f)

@[to_additive]

Depends on / 依赖: closure_mono, mulSupport_subset_comp
-/
lemma mulTSupport_subset_comp [One β] {g : α -> β} (hg : forall {x}, g x = 1 -> x = 1) (f : X -> α) :
    mulTSupport f subseteq mulTSupport (g ∘ f) :=
  closure_mono (mulSupport_subset_comp hg f)

@[to_additive]
/--
lemma `mulTSupport_comp_eq` / 引理 `mulTSupport_comp_eq`

English:
lemma mulTSupport_comp_eq
  given: [One β] {g : α -> β} (hg : forall {x}, g x = 1 ↔ x = 1) (f : X -> α)
  proof: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq g hg]

@[to_additive]

中文:
引理 mulTSupport_comp_eq
  条件: [幺 β] {g : α -> β} (hg : 对任意 {x}, g x = 1 ↔ x = 1) (f : X -> α)
  证明: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq g hg]

@[to_additive]

Depends on / 依赖: mulSupport_comp_eq, mulTSupport
-/
lemma mulTSupport_comp_eq [One β] {g : α -> β} (hg : forall {x}, g x = 1 ↔ x = 1) (f : X -> α) :
    mulTSupport (g ∘ f) = mulTSupport f := by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq g hg]

@[to_additive]
/--
lemma `mulTSupport_comp_eq_of_range_subset` / 引理 `mulTSupport_comp_eq_of_range_subset`

English:
lemma mulTSupport_comp_eq_of_range_subset
  statement: [One β] {g : α -> β} {f : X -> α}
  proof: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_of_range_subset hg]

@[to_additive]

中文:
引理 mulTSupport_comp_eq_of_range_subset
  结论: [幺 β] {g : α -> β} {f : X -> α}
  证明: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_of_range_subset hg]

@[to_additive]

Depends on / 依赖: mulSupport_comp_eq_of_range_subset, mulTSupport
-/
lemma mulTSupport_comp_eq_of_range_subset [One β] {g : α -> β} {f : X -> α}
    (hg : forall {x}, x in range f -> (g x = 1 ↔ x = 1)) :
    mulTSupport (g ∘ f) = mulTSupport f := by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_of_range_subset hg]

@[to_additive]
/--
lemma `mulTSupport_comp_subset_preimage` / 引理 `mulTSupport_comp_subset_preimage`

English:
lemma mulTSupport_comp_subset_preimage
  statement: {Y : Type*} [TopologicalSpace Y] (g : Y -> α) {f : X -> Y}
  proof: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_preimage]
  exact hf.closure_preimage_subset _

@[to_additive]

中文:
引理 mulTSupport_comp_subset_preimage
  结论: {Y : 类型} [拓扑空间 Y] (g : Y -> α) {f : X -> Y}
  证明: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_preimage]
  exact hf.closure_preimage_subset _

@[to_additive]

Depends on / 依赖: closure_preimage_subset, hf.closure_preimage_subset, mulSupport_comp_eq_preimage, mulTSupport
-/
lemma mulTSupport_comp_subset_preimage {Y : Type*} [TopologicalSpace Y] (g : Y -> α) {f : X -> Y}
    (hf : Continuous f) :
    mulTSupport (g ∘ f) subseteq f ⁻¹' mulTSupport g := by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_preimage]
  exact hf.closure_preimage_subset _

@[to_additive]
/--
lemma `mulTSupport_comp_eq_preimage` / 引理 `mulTSupport_comp_eq_preimage`

English:
lemma mulTSupport_comp_eq_preimage
  given: {Y : Type*} [TopologicalSpace Y] (g : Y -> α) (f : X ≃ₜ Y)
  proof: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_preimage]; rw [Homeomorph.preimage_closure]

@[to_additive]

中文:
引理 mulTSupport_comp_eq_preimage
  条件: {Y : 类型} [拓扑空间 Y] (g : Y -> α) (f : X ≃ₜ Y)
  证明: by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_preimage]; rw [Homeomorph.preimage_closure]

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.preimage_closure, mulSupport_comp_eq_preimage, mulTSupport, preimage_closure
-/
lemma mulTSupport_comp_eq_preimage {Y : Type*} [TopologicalSpace Y] (g : Y -> α) (f : X ≃ₜ Y) :
    mulTSupport (g ∘ f) = f ⁻¹' mulTSupport g := by
  rw [mulTSupport]; rw [mulTSupport]; rw [mulSupport_comp_eq_preimage]; rw [Homeomorph.preimage_closure]

@[to_additive]
/--
theorem `image_eq_one_of_notMem_mulTSupport` / 定理 `image_eq_one_of_notMem_mulTSupport`

English:
theorem image_eq_one_of_notMem_mulTSupport
  given: {f : X -> α} {x : X} (hx : x ∉ mulTSupport f)
  statement: f x = 1
  proof: mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx

@[to_additive]

中文:
定理 image_eq_one_of_notMem_mulTSupport
  条件: {f : X -> α} {x : X} (hx : x ∉ mulTSupport f)
  结论: f x = 1
  证明: mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx

@[to_additive]

Depends on / 依赖: mulSupport_subset_iff, subset_mulTSupport
-/
theorem image_eq_one_of_notMem_mulTSupport {f : X -> α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1 :=
  mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx

@[to_additive]
/--
theorem `range_subset_insert_image_mulTSupport` / 定理 `range_subset_insert_image_mulTSupport`

English:
theorem range_subset_insert_image_mulTSupport
  given: (f : X -> α)
  proof: by
  grw [← subset_mulTSupport f]; exact range_subset_insert_image_mulSupport f

@[to_additive]

中文:
定理 range_subset_insert_image_mulTSupport
  条件: (f : X -> α)
  证明: by
  grw [← subset_mulTSupport f]; exact range_subset_insert_image_mulSupport f

@[to_additive]

Depends on / 依赖: range_subset_insert_image_mulSupport, subset_mulTSupport
-/
theorem range_subset_insert_image_mulTSupport (f : X -> α) :
    range f subseteq insert 1 (f '' mulTSupport f) := by
  grw [← subset_mulTSupport f]; exact range_subset_insert_image_mulSupport f

@[to_additive]
/--
theorem `range_eq_image_mulTSupport_or` / 定理 `range_eq_image_mulTSupport_or`

English:
theorem range_eq_image_mulTSupport_or
  given: (f : X -> α)
  proof: (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)

中文:
定理 range_eq_image_mulTSupport_or
  条件: (f : X -> α)
  证明: (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)

Depends on / 依赖: eq_or_eq, image_subset_range, range_subset_insert_image_mulTSupport, wcovBy_insert
-/
theorem range_eq_image_mulTSupport_or (f : X -> α) :
    range f = f '' mulTSupport f ∨ range f = insert 1 (f '' mulTSupport f) :=
  (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)

/--
theorem `tsupport_mul_subset_left` / 定理 `tsupport_mul_subset_left`

English:
theorem tsupport_mul_subset_left
  given: {α : Type*} [MulZeroClass α] {f g : X -> α}
  proof: closure_mono (support_mul_subset_left _ _)

中文:
定理 tsupport_mul_subset_left
  条件: {α : 类型} [乘零类 α] {f g : X -> α}
  证明: closure_mono (support_mul_subset_left _ _)

Depends on / 依赖: closure_mono, support_mul_subset_left
-/
theorem tsupport_mul_subset_left {α : Type*} [MulZeroClass α] {f g : X -> α} :
    (tsupport fun x => f x * g x) subseteq tsupport f :=
  closure_mono (support_mul_subset_left _ _)

/--
theorem `tsupport_mul_subset_right` / 定理 `tsupport_mul_subset_right`

English:
theorem tsupport_mul_subset_right
  given: {α : Type*} [MulZeroClass α] {f g : X -> α}
  proof: closure_mono (support_mul_subset_right _ _)

中文:
定理 tsupport_mul_subset_right
  条件: {α : 类型} [乘零类 α] {f g : X -> α}
  证明: closure_mono (support_mul_subset_right _ _)

Depends on / 依赖: closure_mono, support_mul_subset_right
-/
theorem tsupport_mul_subset_right {α : Type*} [MulZeroClass α] {f g : X -> α} :
    (tsupport fun x => f x * g x) subseteq tsupport g :=
  closure_mono (support_mul_subset_right _ _)

end One

section Operations

variable [TopologicalSpace X]

@[to_additive (attr := simp)]
/--
theorem `mulTSupport_mul` / 定理 `mulTSupport_mul`

English:
theorem mulTSupport_mul
  given: [MulOneClass α] (f g : X -> α)
  proof: mulTSupport_binop_subset (· * ·) (by simp) f g

@[to_additive]

中文:
定理 mulTSupport_mul
  条件: [MulOne类 α] (f g : X -> α)
  证明: mulTSupport_binop_subset (· * ·) (by simp) f g

@[to_additive]

Depends on / 依赖: mulTSupport_binop_subset
-/
theorem mulTSupport_mul [MulOneClass α] (f g : X -> α) :
    (mulTSupport fun x => f x * g x) subseteq mulTSupport f union mulTSupport g :=
  mulTSupport_binop_subset (· * ·) (by simp) f g

@[to_additive]
/--
theorem `mulTSupport_pow` / 定理 `mulTSupport_pow`

English:
theorem mulTSupport_pow
  given: [Monoid α] (f : X -> α) (n : Nat)
  proof: closure_mono mulSupport_pow f n

@[to_additive (attr := simp)]

中文:
定理 mulTSupport_pow
  条件: [幺半群 α] (f : X -> α) (n : 自然数)
  证明: closure_mono mulSupport_pow f n

@[to_additive (attr := simp)]

Depends on / 依赖: closure_mono, mulSupport_pow
-/
theorem mulTSupport_pow [Monoid α] (f : X -> α) (n : Nat) :
    (mulTSupport fun x => f x ^ n) subseteq mulTSupport f :=
closure_mono mulSupport_pow f n

@[to_additive (attr := simp)]
/--
theorem `mulTSupport_fun_inv` / 定理 `mulTSupport_fun_inv`

English:
theorem mulTSupport_fun_inv
  given: [DivisionMonoid α] (f : X -> α)
  proof: congrArg closure mulSupport_fun_inv f

@[to_additive (attr := simp)]

中文:
定理 mulTSupport_fun_inv
  条件: [Division幺半群 α] (f : X -> α)
  证明: congrArg closure mulSupport_fun_inv f

@[to_additive (attr := simp)]

Depends on / 依赖: closure, mulSupport_fun_inv
-/
theorem mulTSupport_fun_inv [DivisionMonoid α] (f : X -> α) :
    (mulTSupport fun x => (f x)⁻¹) = mulTSupport f :=
congrArg closure mulSupport_fun_inv f

@[to_additive (attr := simp)]
/--
theorem `mulTSupport_inv` / 定理 `mulTSupport_inv`

English:
theorem mulTSupport_inv
  given: [DivisionMonoid α] (f : X -> α)
  proof: mulTSupport_fun_inv f

@[to_additive]

中文:
定理 mulTSupport_inv
  条件: [Division幺半群 α] (f : X -> α)
  证明: mulTSupport_fun_inv f

@[to_additive]

Depends on / 依赖: mulTSupport_fun_inv
-/
theorem mulTSupport_inv [DivisionMonoid α] (f : X -> α) :
    mulTSupport f⁻¹ = mulTSupport f :=
  mulTSupport_fun_inv f

@[to_additive]
/--
theorem `mulTSupport_mul_inv` / 定理 `mulTSupport_mul_inv`

English:
theorem mulTSupport_mul_inv
  given: [DivisionMonoid α] (f g : X -> α)
  proof: mulTSupport_binop_subset (· * ·⁻¹) (by simp) f g

@[to_additive]

中文:
定理 mulTSupport_mul_inv
  条件: [Division幺半群 α] (f g : X -> α)
  证明: mulTSupport_binop_subset (· * ·⁻¹) (by simp) f g

@[to_additive]

Depends on / 依赖: mulTSupport_binop_subset
-/
theorem mulTSupport_mul_inv [DivisionMonoid α] (f g : X -> α) :
    (mulTSupport fun x => f x * (g x)⁻¹) subseteq mulTSupport f union mulTSupport g :=
  mulTSupport_binop_subset (· * ·⁻¹) (by simp) f g

@[to_additive]
/--
theorem `mulTSupport_div` / 定理 `mulTSupport_div`

English:
theorem mulTSupport_div
  given: [DivisionMonoid α] (f g : X -> α)
  proof: mulTSupport_binop_subset (· / ·) one_div_one f g

中文:
定理 mulTSupport_div
  条件: [Division幺半群 α] (f g : X -> α)
  证明: mulTSupport_binop_subset (· / ·) one_div_one f g

Depends on / 依赖: mulTSupport_binop_subset, one_div_one
-/
theorem mulTSupport_div [DivisionMonoid α] (f g : X -> α) :
    (mulTSupport fun x => f x / g x) subseteq mulTSupport f union mulTSupport g :=
  mulTSupport_binop_subset (· / ·) one_div_one f g

/--
theorem `tsupport_smul_subset_left` / 定理 `tsupport_smul_subset_left`

English:
theorem tsupport_smul_subset_left
  statement: {M α} [Zero M] [Zero α] [SMulWithZero M α]
  proof: closure_mono support_smul_subset_left f g

中文:
定理 tsupport_smul_subset_left
  结论: {M α} [零 M] [零 α] [带零标量乘法 M α]
  证明: closure_mono support_smul_subset_left f g

Depends on / 依赖: closure_mono, support_smul_subset_left
-/
theorem tsupport_smul_subset_left {M α} [Zero M] [Zero α] [SMulWithZero M α]
    (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x) subseteq tsupport f :=
closure_mono support_smul_subset_left f g

/--
theorem `tsupport_smul_subset_right` / 定理 `tsupport_smul_subset_right`

English:
theorem tsupport_smul_subset_right
  statement: {M α} [Zero α] [SMulZeroClass M α]
  proof: closure_mono support_smul_subset_right f g

中文:
定理 tsupport_smul_subset_right
  结论: {M α} [零 α] [SMulZero类 M α]
  证明: closure_mono support_smul_subset_right f g

Depends on / 依赖: closure_mono, support_smul_subset_right
-/
theorem tsupport_smul_subset_right {M α} [Zero α] [SMulZeroClass M α]
    (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x) subseteq tsupport g :=
closure_mono support_smul_subset_right f g

end Operations

section

variable [TopologicalSpace α]
variable [One β]
variable {f : α -> β} {x : α}

@[to_additive]
/--
theorem `notMem_mulTSupport_iff_eventuallyEq` / 定理 `notMem_mulTSupport_iff_eventuallyEq`

English:
theorem notMem_mulTSupport_iff_eventuallyEq
  statement: x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1
  proof: by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, exists_prop,
    ← disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem]

@[to_additive]

中文:
定理 notMem_mulTSupport_iff_eventuallyEq
  结论: x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1
  证明: by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, exists_prop,
    ← disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem]

@[to_additive]

Depends on / 依赖: disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem, exists_prop, mem_closure_iff_nhds, mulTSupport, not_forall, not_nonempty_iff_eq_empty, simp_rw
-/
theorem notMem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, exists_prop,
    ← disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem]

@[to_additive]
/--
theorem `continuous_of_mulTSupport` / 定理 `continuous_of_mulTSupport`

English:
theorem continuous_of_mulTSupport
  statement: [TopologicalSpace β] {f : α -> β}
  proof: continuous_iff_continuousAt.2 fun x => (em _).elim (hf x) fun hx =>
    (@continuousAt_const _ _ _ _ _ 1).congr (notMem_mulTSupport_iff_eventuallyEq.mp hx).symm

@[to_additive]

中文:
定理 continuous_of_mulTSupport
  结论: [拓扑空间 β] {f : α -> β}
  证明: continuous_iff_continuousAt.2 fun x => (em _).elim (hf x) fun hx =>
    (@continuousAt_const _ _ _ _ _ 1).congr (notMem_mulTSupport_iff_eventuallyEq.mp hx).symm

@[to_additive]

Depends on / 依赖: continuousAt_const, continuous_iff_continuousAt, notMem_mulTSupport_iff_eventuallyEq, notMem_mulTSupport_iff_eventuallyEq.mp
-/
theorem continuous_of_mulTSupport [TopologicalSpace β] {f : α -> β}
    (hf : forall x in mulTSupport f, ContinuousAt f x) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (em _).elim (hf x) fun hx =>
    (@continuousAt_const _ _ _ _ _ 1).congr (notMem_mulTSupport_iff_eventuallyEq.mp hx).symm

@[to_additive]
/--
lemma `ContinuousOn.continuous_of_mulTSupport_subset` / 引理 `ContinuousOn.continuous_of_mulTSupport_subset`

English:
lemma ContinuousOn.continuous_of_mulTSupport_subset
  statement: [TopologicalSpace β] {f : α -> β}
  proof: continuous_of_mulTSupport fun _ hx => h's.continuousOn_iff.mp hs h''s hx

中文:
引理 ContinuousOn.continuous_of_mulTSupport_subset
  结论: [拓扑空间 β] {f : α -> β}
  证明: continuous_of_mulTSupport fun _ hx => h's.continuousOn_iff.mp hs h''s hx

Depends on / 依赖: continuousOn_iff, continuous_of_mulTSupport, s.continuousOn_iff.mp
-/
lemma ContinuousOn.continuous_of_mulTSupport_subset [TopologicalSpace β] {f : α -> β}
    {s : Set α} (hs : ContinuousOn f s) (h's : IsOpen s) (h''s : mulTSupport f subseteq s) :
    Continuous f :=
continuous_of_mulTSupport fun _ hx => h's.continuousOn_iff.mp hs h''s hx

end

/-! ## Functions with compact support -/
section CompactSupport

variable [TopologicalSpace α] [TopologicalSpace α'] [One β] [One γ] [One δ]
  {g : β -> γ} {f : α -> β} {f₂ : α -> γ} {m : β -> γ -> δ}

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive /-- A function `f` *has compact support* or is *compactly supported* if the closure of
the support of `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a
compact set. -/]
/--
Definition of `HasCompactMulSupport` / `HasCompactMulSupport` 的定义

English:
definition HasCompactMulSupport
  signature: (f : α -> β)
  body: IsCompact (mulTSupport f)

@[to_additive]

中文:
定义 HasCompactMulSupport
  签名: (f : α -> β)
  定义体: IsCompact (mulTSupport f)

@[to_additive]

Depends on / 依赖: IsCompact, mulTSupport
-/
def HasCompactMulSupport (f : α -> β) : Prop :=
  IsCompact (mulTSupport f)

@[to_additive]
/--
theorem `hasCompactMulSupport_def` / 定理 `hasCompactMulSupport_def`

English:
theorem hasCompactMulSupport_def
  statement: HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f))
  proof: by
  rfl

@[to_additive]

中文:
定理 hasCompactMulSupport_def
  结论: HasCompactMulSupport f ↔ 是紧集 (closure (mulSupport f))
  证明: by
  rfl

@[to_additive]
-/
theorem hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl

@[to_additive]
/--
theorem `exists_compact_iff_hasCompactMulSupport` / 定理 `exists_compact_iff_hasCompactMulSupport`

English:
theorem exists_compact_iff_hasCompactMulSupport
  given: [R1Space α]
  proof: by
  simp_rw [← notMem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]

中文:
定理 存在_compact_iff_hasCompactMulSupport
  条件: [R1空间 α]
  证明: by
  simp_rw [← notMem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]

Depends on / 依赖: compl_subset_compl, exists_isCompact_superset_iff, hasCompactMulSupport_def, mem_compl_iff, notMem_mulSupport, simp_rw, subset_def
-/
theorem exists_compact_iff_hasCompactMulSupport [R1Space α] :
    (exists K : Set α, IsCompact K ∧ forall x, x ∉ K -> f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← notMem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]

namespace HasCompactMulSupport

variable {K : Set α}

@[to_additive]
/--
theorem `intro` / 定理 `intro`

English:
theorem intro
  given: [R1Space α] (hK : IsCompact K) (hfK : forall x, x ∉ K -> f x = 1)
  proof: exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩

@[to_additive]

中文:
定理 intro
  条件: [R1空间 α] (hK : 是紧集 K) (hfK : 对任意 x, x ∉ K -> f x = 1)
  证明: exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩

@[to_additive]

Depends on / 依赖: exists_compact_iff_hasCompactMulSupport, exists_compact_iff_hasCompactMulSupport.mp
-/
theorem intro [R1Space α] (hK : IsCompact K) (hfK : forall x, x ∉ K -> f x = 1) :
    HasCompactMulSupport f :=
  exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩

@[to_additive]
/--
theorem `intro'` / 定理 `intro'`

English:
theorem intro'
  given: (hK : IsCompact K) (h'K : IsClosed K) (hfK : forall x, x ∉ K -> f x = 1)
  proof: by
  have : mulTSupport f subseteq K := by
    rw [← h'K.closure_eq]
    apply closure_mono (mulSupport_subset_iff'.2 hfK)
  exact IsCompact.of_isClosed_subset hK (isClosed_mulTSupport f) this

@[to_additive]

中文:
定理 intro'
  条件: (hK : 是紧集 K) (h'K : 是闭集 K) (hfK : 对任意 x, x ∉ K -> f x = 1)
  证明: by
  have : mulTSupport f subseteq K := by
    rw [← h'K.closure_eq]
    apply closure_mono (mulSupport_subset_iff'.2 hfK)
  exact IsCompact.of_isClosed_subset hK (isClosed_mulTSupport f) this

@[to_additive]

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, K.closure_eq, closure_eq, closure_mono, isClosed_mulTSupport, mulSupport_subset_iff, mulTSupport, of_isClosed_subset, subseteq
-/
theorem intro' (hK : IsCompact K) (h'K : IsClosed K) (hfK : forall x, x ∉ K -> f x = 1) :
    HasCompactMulSupport f := by
  have : mulTSupport f subseteq K := by
    rw [← h'K.closure_eq]
    apply closure_mono (mulSupport_subset_iff'.2 hfK)
  exact IsCompact.of_isClosed_subset hK (isClosed_mulTSupport f) this

@[to_additive]
/--
theorem `of_mulSupport_subset_isCompact` / 定理 `of_mulSupport_subset_isCompact`

English:
theorem of_mulSupport_subset_isCompact
  given: [R1Space α] (hK : IsCompact K) (h : mulSupport f subseteq K)
  proof: hK.closure_of_subset h

@[to_additive]

中文:
定理 of_mulSupport_subset_isCompact
  条件: [R1空间 α] (hK : 是紧集 K) (h : mulSupport f subseteq K)
  证明: hK.closure_of_subset h

@[to_additive]

Depends on / 依赖: closure_of_subset, hK.closure_of_subset
-/
theorem of_mulSupport_subset_isCompact [R1Space α] (hK : IsCompact K) (h : mulSupport f subseteq K) :
    HasCompactMulSupport f :=
  hK.closure_of_subset h

@[to_additive]
/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (hf : HasCompactMulSupport f)
  statement: IsCompact (mulTSupport f)
  proof: hf

@[to_additive]

中文:
定理 isCompact
  条件: (hf : HasCompactMulSupport f)
  结论: 是紧集 (mulTSupport f)
  证明: hf

@[to_additive]
-/
theorem isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f) := hf

@[to_additive]
/--
theorem `_root_.hasCompactMulSupport_iff_eventuallyEq` / 定理 `_root_.hasCompactMulSupport_iff_eventuallyEq`

English:
theorem _root_.hasCompactMulSupport_iff_eventuallyEq
  proof: mem_coclosedCompact_iff.symm

@[to_additive]

中文:
定理 _root_.hasCompactMulSupport_iff_eventuallyEq
  证明: mem_coclosedCompact_iff.symm

@[to_additive]

Depends on / 依赖: mem_coclosedCompact_iff, mem_coclosedCompact_iff.symm
-/
theorem _root_.hasCompactMulSupport_iff_eventuallyEq :
    HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  mem_coclosedCompact_iff.symm

@[to_additive]
/--
theorem `_root_.isCompact_range_of_mulSupport_subset_isCompact` / 定理 `_root_.isCompact_range_of_mulSupport_subset_isCompact`

English:
theorem _root_.isCompact_range_of_mulSupport_subset_isCompact
  statement: [TopologicalSpace β]
  proof: by
  rcases range_eq_image_or_of_mulSupport_subset h'f with h2 | h2 <;> rw [h2]
  exacts [hk.image hf, (hk.image hf).insert 1]

@[to_additive]

中文:
定理 _root_.isCompact_range_of_mulSupport_subset_isCompact
  结论: [拓扑空间 β]
  证明: by
  rcases range_eq_image_or_of_mulSupport_subset h'f with h2 | h2 <;> rw [h2]
  exacts [hk.image hf, (hk.image hf).insert 1]

@[to_additive]

Depends on / 依赖: exacts, hk.image, insert, range_eq_image_or_of_mulSupport_subset
-/
theorem _root_.isCompact_range_of_mulSupport_subset_isCompact [TopologicalSpace β]
    (hf : Continuous f) (hk : IsCompact K) (h'f : mulSupport f subseteq K) :
    IsCompact (range f) := by
  rcases range_eq_image_or_of_mulSupport_subset h'f with h2 | h2 <;> rw [h2]
  exacts [hk.image hf, (hk.image hf).insert 1]

@[to_additive]
/--
theorem `isCompact_range` / 定理 `isCompact_range`

English:
theorem isCompact_range
  statement: [TopologicalSpace β] (h : HasCompactMulSupport f)
  proof: isCompact_range_of_mulSupport_subset_isCompact hf h (subset_mulTSupport f)

@[to_additive]

中文:
定理 isCompact_range
  结论: [拓扑空间 β] (h : HasCompactMulSupport f)
  证明: isCompact_range_of_mulSupport_subset_isCompact hf h (subset_mulTSupport f)

@[to_additive]

Depends on / 依赖: isCompact_range_of_mulSupport_subset_isCompact, subset_mulTSupport
-/
theorem isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f)
    (hf : Continuous f) : IsCompact (range f) :=
  isCompact_range_of_mulSupport_subset_isCompact hf h (subset_mulTSupport f)

@[to_additive]
/--
theorem `mono'` / 定理 `mono'`

English:
theorem mono'
  given: {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' subseteq mulTSupport f)
  proof: IsCompact.of_isClosed_subset hf isClosed_closure closure_minimal hff' isClosed_closure

@[to_additive]

中文:
定理 mono'
  条件: {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' subseteq mulTSupport f)
  证明: IsCompact.of_isClosed_subset hf isClosed_closure closure_minimal hff' isClosed_closure

@[to_additive]

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, closure_minimal, isClosed_closure, of_isClosed_subset
-/
theorem mono' {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' subseteq mulTSupport f) :
    HasCompactMulSupport f' :=
IsCompact.of_isClosed_subset hf isClosed_closure closure_minimal hff' isClosed_closure

@[to_additive]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' subseteq mulSupport f)
  proof: hf.mono' hff'.trans subset_closure

@[to_additive]

中文:
定理 mono
  条件: {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' subseteq mulSupport f)
  证明: hf.mono' hff'.trans subset_closure

@[to_additive]

Depends on / 依赖: hf.mono, subset_closure
-/
theorem mono {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' subseteq mulSupport f) :
    HasCompactMulSupport f' :=
hf.mono' hff'.trans subset_closure

@[to_additive]
/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  given: (hf : HasCompactMulSupport f) (hg : g 1 = 1)
  proof: hf.mono mulSupport_comp_subset hg f

@[to_additive]

中文:
定理 comp_left
  条件: (hf : HasCompactMulSupport f) (hg : g 1 = 1)
  证明: hf.mono mulSupport_comp_subset hg f

@[to_additive]

Depends on / 依赖: hf.mono, mulSupport_comp_subset
-/
theorem comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) :
    HasCompactMulSupport (g ∘ f) :=
hf.mono mulSupport_comp_subset hg f

@[to_additive]
/--
theorem `_root_.hasCompactMulSupport_comp_left` / 定理 `_root_.hasCompactMulSupport_comp_left`

English:
theorem _root_.hasCompactMulSupport_comp_left
  given: (hg : forall {x}, g x = 1 ↔ x = 1)
  proof: by
  simp_rw [hasCompactMulSupport_def, mulSupport_comp_eq g (@hg) f]

@[to_additive]

中文:
定理 _root_.hasCompactMulSupport_comp_left
  条件: (hg : 对任意 {x}, g x = 1 ↔ x = 1)
  证明: by
  simp_rw [hasCompactMulSupport_def, mulSupport_comp_eq g (@hg) f]

@[to_additive]

Depends on / 依赖: hasCompactMulSupport_def, mulSupport_comp_eq, simp_rw
-/
theorem _root_.hasCompactMulSupport_comp_left (hg : forall {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [hasCompactMulSupport_def, mulSupport_comp_eq g (@hg) f]

@[to_additive]
/--
theorem `comp_isClosedEmbedding` / 定理 `comp_isClosedEmbedding`

English:
theorem comp_isClosedEmbedding
  statement: (hf : HasCompactMulSupport f) {g : α' -> α}
  proof: by
  rw [hasCompactMulSupport_def]; rw [Function.mulSupport_comp_eq_preimage]
  refine IsCompact.of_isClosed_subset (hg.isCompact_preimage hf) isClosed_closure ?_
  rw [hg.isEmbedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)

@[to_additive]

中文:
定理 comp_isClosedEmbedding
  结论: (hf : HasCompactMulSupport f) {g : α' -> α}
  证明: by
  rw [hasCompactMulSupport_def]; rw [Function.mulSupport_comp_eq_preimage]
  refine IsCompact.of_isClosed_subset (hg.isCompact_preimage hf) isClosed_closure ?_
  rw [hg.isEmbedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)

@[to_additive]

Depends on / 依赖: Function, Function.mulSupport_comp_eq_preimage, IsCompact, IsCompact.of_isClosed_subset, closure_eq_preimage_closure_image, closure_mono, hasCompactMulSupport_def, hg.isCompact_preimage, hg.isEmbedding.closure_eq_preimage_closure_image, image_preimage_subset, isClosed_closure, isCompact_preimage, isEmbedding, mulSupport_comp_eq_preimage, of_isClosed_subset, preimage_mono
-/
theorem comp_isClosedEmbedding (hf : HasCompactMulSupport f) {g : α' -> α}
    (hg : IsClosedEmbedding g) : HasCompactMulSupport (f ∘ g) := by
  rw [hasCompactMulSupport_def]; rw [Function.mulSupport_comp_eq_preimage]
  refine IsCompact.of_isClosed_subset (hg.isCompact_preimage hf) isClosed_closure ?_
  rw [hg.isEmbedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)

@[to_additive]
/--
theorem `comp₂_left` / 定理 `comp₂_left`

English:
theorem comp₂_left
  statement: (hf : HasCompactMulSupport f)
  proof: by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  filter_upwards [hf, hf₂] with x hx hx₂
  simp_rw [hx, hx₂, Pi.one_apply, hm]

@[to_additive]

中文:
定理 comp₂_left
  结论: (hf : HasCompactMulSupport f)
  证明: by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  filter_upwards [hf, hf₂] with x hx hx₂
  simp_rw [hx, hx₂, Pi.one_apply, hm]

@[to_additive]

Depends on / 依赖: Pi.one_apply, filter_upwards, hasCompactMulSupport_iff_eventuallyEq, one_apply, simp_rw
-/
theorem comp₂_left (hf : HasCompactMulSupport f)
    (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) := by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  filter_upwards [hf, hf₂] with x hx hx₂
  simp_rw [hx, hx₂, Pi.one_apply, hm]

@[to_additive]
/--
lemma `isCompact_preimage` / 引理 `isCompact_preimage`

English:
lemma isCompact_preimage
  statement: [TopologicalSpace β] {K : Set β}
  proof: by
  apply IsCompact.of_isClosed_subset h'f (hk.preimage hf) (fun x hx => ?_)
  apply subset_mulTSupport
  aesop

中文:
引理 isCompact_preimage
  结论: [拓扑空间 β] {K : 集合 β}
  证明: by
  apply IsCompact.of_isClosed_subset h'f (hk.preimage hf) (fun x hx => ?_)
  apply subset_mulTSupport
  aesop

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, hk.preimage, of_isClosed_subset, preimage, subset_mulTSupport
-/
lemma isCompact_preimage [TopologicalSpace β] {K : Set β}
    (h'f : HasCompactMulSupport f) (hf : Continuous f) (hk : IsClosed K) (h'k : 1 ∉ K) :
    IsCompact (f ⁻¹' K) := by
  apply IsCompact.of_isClosed_subset h'f (hk.preimage hf) (fun x hx => ?_)
  apply subset_mulTSupport
  aesop

variable [T2Space α']

section

variable (hf : HasCompactMulSupport f) {g : α -> α'} (cont : Continuous g)
include hf cont

@[to_additive]
/--
theorem `mulTSupport_extend_one_subset` / 定理 `mulTSupport_extend_one_subset`

English:
theorem mulTSupport_extend_one_subset
  proof: (hf.image cont).isClosed.closure_subset_iff.mpr
    mulSupport_extend_one_subset.trans (image_mono subset_closure)

@[to_additive]

中文:
定理 mulTSupport_extend_one_subset
  证明: (hf.image cont).isClosed.closure_subset_iff.mpr
    mulSupport_extend_one_subset.trans (image_mono subset_closure)

@[to_additive]

Depends on / 依赖: closure_subset_iff, hf.image, image_mono, isClosed, isClosed.closure_subset_iff.mpr, mulSupport_extend_one_subset, mulSupport_extend_one_subset.trans, subset_closure
-/
theorem mulTSupport_extend_one_subset :
    mulTSupport (g.extend f 1) subseteq g '' mulTSupport f :=
(hf.image cont).isClosed.closure_subset_iff.mpr
    mulSupport_extend_one_subset.trans (image_mono subset_closure)

@[to_additive]
/--
theorem `extend_one` / 定理 `extend_one`

English:
theorem extend_one
  statement: HasCompactMulSupport (g.extend f 1)
  proof: HasCompactMulSupport.of_mulSupport_subset_isCompact (hf.image cont)
    (subset_closure.trans <| hf.mulTSupport_extend_one_subset cont)

@[to_additive]

中文:
定理 extend_one
  结论: HasCompactMulSupport (g.extend f 1)
  证明: HasCompactMulSupport.of_mulSupport_subset_isCompact (hf.image cont)
    (subset_closure.trans <| hf.mulTSupport_extend_one_subset cont)

@[to_additive]

Depends on / 依赖: HasCompactMulSupport, HasCompactMulSupport.of_mulSupport_subset_isCompact, hf.image, hf.mulTSupport_extend_one_subset, mulTSupport_extend_one_subset, of_mulSupport_subset_isCompact, subset_closure, subset_closure.trans
-/
theorem extend_one : HasCompactMulSupport (g.extend f 1) :=
  HasCompactMulSupport.of_mulSupport_subset_isCompact (hf.image cont)
    (subset_closure.trans <| hf.mulTSupport_extend_one_subset cont)

@[to_additive]
/--
theorem `mulTSupport_extend_one` / 定理 `mulTSupport_extend_one`

English:
theorem mulTSupport_extend_one
  given: (inj : g.Injective)
  proof: (hf.mulTSupport_extend_one_subset cont).antisymm
    (image_closure_subset_closure_image cont).trans
      (closure_mono (mulSupport_extend_one inj).superset)

中文:
定理 mulTSupport_extend_one
  条件: (inj : g.单射)
  证明: (hf.mulTSupport_extend_one_subset cont).antisymm
    (image_closure_subset_closure_image cont).trans
      (closure_mono (mulSupport_extend_one inj).superset)

Depends on / 依赖: antisymm, closure_mono, hf.mulTSupport_extend_one_subset, image_closure_subset_closure_image, mulSupport_extend_one, mulTSupport_extend_one_subset, superset
-/
theorem mulTSupport_extend_one (inj : g.Injective) :
    mulTSupport (g.extend f 1) = g '' mulTSupport f :=
(hf.mulTSupport_extend_one_subset cont).antisymm
    (image_closure_subset_closure_image cont).trans
      (closure_mono (mulSupport_extend_one inj).superset)

end

@[to_additive]
/--
theorem `continuous_extend_one` / 定理 `continuous_extend_one`

English:
theorem continuous_extend_one
  statement: [TopologicalSpace β] {U : Set α'} (hU : IsOpen U) {f : U -> β}
  proof: continuous_of_mulTSupport fun x h => by
    rw [show x = ↑(⟨x]; rw [Subtype.coe_image_subset _ _
      (supp.mulTSupport_extend_one_subset continuous_subtype_val h)⟩ : U) by rfl]; rw [← (hU.isOpenEmbedding_subtypeVal).continuousAt_iff]; rw [extend_comp Subtype.val_injective]
    exact cont.continuou

中文:
定理 continuous_extend_one
  结论: [拓扑空间 β] {U : 集合 α'} (hU : 是开集 U) {f : U -> β}
  证明: continuous_of_mulTSupport fun x h => by
    rw [show x = ↑(⟨x]; rw [Subtype.coe_image_subset _ _
      (supp.mulTSupport_extend_one_subset continuous_subtype_val h)⟩ : U) by rfl]; rw [← (hU.isOpenEmbedding_subtypeVal).continuousAt_iff]; rw [extend_comp Subtype.val_injective]
    exact cont.continuou

Depends on / 依赖: Subtype, Subtype.coe_image_subset, Subtype.val_injective, coe_image_subset, cont.continuousAt, continuousAt, continuousAt_iff, continuous_of_mulTSupport, continuous_subtype_val, extend_comp, hU.isOpenEmbedding_subtypeVal, isOpenEmbedding_subtypeVal, mulTSupport_extend_one_subset, supp.mulTSupport_extend_one_subset, val_injective
-/
theorem continuous_extend_one [TopologicalSpace β] {U : Set α'} (hU : IsOpen U) {f : U -> β}
    (cont : Continuous f) (supp : HasCompactMulSupport f) :
    Continuous (Subtype.val.extend f 1) :=
  continuous_of_mulTSupport fun x h => by
    rw [show x = ↑(⟨x]; rw [Subtype.coe_image_subset _ _
      (supp.mulTSupport_extend_one_subset continuous_subtype_val h)⟩ : U) by rfl]; rw [← (hU.isOpenEmbedding_subtypeVal).continuousAt_iff]; rw [extend_comp Subtype.val_injective]
    exact cont.continuousAt

/-- If `f` has compact multiplicative support, then `f` tends to 1 at infinity. -/
@[to_additive /-- If `f` has compact support, then `f` tends to zero at infinity. -/]
/--
theorem `is_one_at_infty` / 定理 `is_one_at_infty`

English:
theorem is_one_at_infty
  statement: {f : α -> γ} [TopologicalSpace γ]
  proof: by
  intro N hN
  rw [mem_map]; rw [mem_cocompact']
  refine ⟨mulTSupport f, h.isCompact, ?_⟩
  rw [compl_subset_comm]
  intro v hv
  rw [mem_preimage]; rw [image_eq_one_of_notMem_mulTSupport hv]
  exact mem_of_mem_nhds hN

中文:
定理 is_one_at_infty
  结论: {f : α -> γ} [拓扑空间 γ]
  证明: by
  intro N hN
  rw [mem_map]; rw [mem_cocompact']
  refine ⟨mulTSupport f, h.isCompact, ?_⟩
  rw [compl_subset_comm]
  intro v hv
  rw [mem_preimage]; rw [image_eq_one_of_notMem_mulTSupport hv]
  exact mem_of_mem_nhds hN

Depends on / 依赖: compl_subset_comm, h.isCompact, image_eq_one_of_notMem_mulTSupport, isCompact, mem_cocompact, mem_map, mem_of_mem_nhds, mem_preimage, mulTSupport
-/
theorem is_one_at_infty {f : α -> γ} [TopologicalSpace γ]
    (h : HasCompactMulSupport f) : Tendsto f (cocompact α) (𝓝 1) := by
  intro N hN
  rw [mem_map]; rw [mem_cocompact']
  refine ⟨mulTSupport f, h.isCompact, ?_⟩
  rw [compl_subset_comm]
  intro v hv
  rw [mem_preimage]; rw [image_eq_one_of_notMem_mulTSupport hv]
  exact mem_of_mem_nhds hN

end HasCompactMulSupport

section Compact

variable [CompactSpace α]

/-- In a compact space `α`, any function has compact support. -/
@[to_additive]
/--
theorem `HasCompactMulSupport.of_compactSpace` / 定理 `HasCompactMulSupport.of_compactSpace`

English:
theorem HasCompactMulSupport.of_compactSpace
  given: (f : α -> γ)
  proof: IsCompact.of_isClosed_subset isCompact_univ (isClosed_mulTSupport f)
    (Set.subset_univ (mulTSupport f))

中文:
定理 HasCompactMulSupport.of_compactSpace
  条件: (f : α -> γ)
  证明: IsCompact.of_isClosed_subset isCompact_univ (isClosed_mulTSupport f)
    (Set.subset_univ (mulTSupport f))

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, Set.subset_univ, isClosed_mulTSupport, isCompact_univ, mulTSupport, of_isClosed_subset, subset_univ
-/
theorem HasCompactMulSupport.of_compactSpace (f : α -> γ) :
    HasCompactMulSupport f :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_mulTSupport f)
    (Set.subset_univ (mulTSupport f))

end Compact

end CompactSupport

/-! ## Functions with compact support: algebraic operations -/
section CompactSupport2
section Monoid

variable [TopologicalSpace α] [MulOneClass β]
variable {f f' : α -> β}

@[to_additive]
/--
theorem `HasCompactMulSupport.mul` / 定理 `HasCompactMulSupport.mul`

English:
theorem HasCompactMulSupport.mul
  given: (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f')
  proof: hf.comp₂_left hf' (mul_one 1)

@[to_additive, simp]

中文:
定理 HasCompactMulSupport.mul
  条件: (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f')
  证明: hf.comp₂_left hf' (mul_one 1)

@[to_additive, simp]

Depends on / 依赖: hf.comp, mul_one
-/
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := hf.comp₂_left hf' (mul_one 1)

@[to_additive, simp]
/--
lemma `HasCompactMulSupport.one` / 引理 `HasCompactMulSupport.one`

English:
lemma HasCompactMulSupport.one
  given: {α β : Type*} [TopologicalSpace α] [One β]
  proof: by
  simp [HasCompactMulSupport]

中文:
引理 HasCompactMulSupport.one
  条件: {α β : 类型} [拓扑空间 α] [幺 β]
  证明: by
  simp [HasCompactMulSupport]
-/
protected lemma HasCompactMulSupport.one {α β : Type*} [TopologicalSpace α] [One β] :
    HasCompactMulSupport (1 : α -> β) := by
  simp [HasCompactMulSupport]

variable (α β) in
/-- The submonoid of functions `α → β` with compact multiplicative support. -/
@[to_additive /-- The additive submonoid of functions `α → β` with compact support. -/]
/--
Definition of `HasCompactMulSupport.submonoid` / `HasCompactMulSupport.submonoid` 的定义

English:
definition HasCompactMulSupport.submonoid
  signature: : Submonoid (α -> β) where
  body: {f | HasCompactMulSupport f}
  one_mem' := .one
  mul_mem' := .mul

@[to_additive (attr := simp)]

中文:
定义 HasCompactMulSupport.submonoid
  签名: : 子幺半群 (α -> β) where
  定义体: {f | HasCompactMulSupport f}
  one_mem' := .one
  mul_mem' := .mul

@[to_additive (attr := simp)]

Depends on / 依赖: HasCompactMulSupport
-/
def HasCompactMulSupport.submonoid : Submonoid (α -> β) where
  carrier := {f | HasCompactMulSupport f}
  one_mem' := .one
  mul_mem' := .mul

@[to_additive (attr := simp)]
/--
theorem `HasCompactMulSupport.mem_submonoid_iff` / 定理 `HasCompactMulSupport.mem_submonoid_iff`

English:
theorem HasCompactMulSupport.mem_submonoid_iff
  given: {f : α -> β}
  proof: Iff.rfl

@[to_additive]

中文:
定理 HasCompactMulSupport.mem_submonoid_iff
  条件: {f : α -> β}
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem HasCompactMulSupport.mem_submonoid_iff {f : α -> β} :
    f in HasCompactMulSupport.submonoid α β ↔ HasCompactMulSupport f :=
  Iff.rfl

@[to_additive]
/--
theorem `HasCompactMulSupport.list_prod` / 定理 `HasCompactMulSupport.list_prod`

English:
theorem HasCompactMulSupport.list_prod
  statement: {α β : Type*} [TopologicalSpace α] [Monoid β]
  proof: list_prod_mem (S := HasCompactMulSupport.submonoid α β) hl

中文:
定理 HasCompactMulSupport.list_prod
  结论: {α β : 类型} [拓扑空间 α] [幺半群 β]
  证明: list_prod_mem (S := HasCompactMulSupport.submonoid α β) hl

Depends on / 依赖: HasCompactMulSupport, HasCompactMulSupport.submonoid, list_prod_mem, submonoid
-/
theorem HasCompactMulSupport.list_prod {α β : Type*} [TopologicalSpace α] [Monoid β]
    {l : List (α -> β)} (hl : forall f in l, HasCompactMulSupport f) :
    HasCompactMulSupport l.prod :=
  list_prod_mem (S := HasCompactMulSupport.submonoid α β) hl

end Monoid

section CommMonoid

variable [TopologicalSpace α] [CommMonoid β]

@[to_additive]
/--
theorem `HasCompactMulSupport.multiset_prod` / 定理 `HasCompactMulSupport.multiset_prod`

English:
theorem HasCompactMulSupport.multiset_prod
  proof: multiset_prod_mem (S := HasCompactMulSupport.submonoid α β) m hm

@[to_additive]

中文:
定理 HasCompactMulSupport.multiset_prod
  证明: multiset_prod_mem (S := HasCompactMulSupport.submonoid α β) m hm

@[to_additive]

Depends on / 依赖: HasCompactMulSupport, HasCompactMulSupport.submonoid, multiset_prod_mem, submonoid
-/
theorem HasCompactMulSupport.multiset_prod
    (m : Multiset (α -> β)) (hm : forall f in m, HasCompactMulSupport f) :
    HasCompactMulSupport m.prod :=
  multiset_prod_mem (S := HasCompactMulSupport.submonoid α β) m hm

@[to_additive]
/--
theorem `HasCompactMulSupport.finset_prod` / 定理 `HasCompactMulSupport.finset_prod`

English:
theorem HasCompactMulSupport.finset_prod
  statement: {ι : Type*}
  proof: prod_mem (S := HasCompactMulSupport.submonoid α β) hf

中文:
定理 HasCompactMulSupport.finset_prod
  结论: {ι : 类型}
  证明: prod_mem (S := HasCompactMulSupport.submonoid α β) hf

Depends on / 依赖: HasCompactMulSupport, HasCompactMulSupport.submonoid, prod_mem, submonoid
-/
theorem HasCompactMulSupport.finset_prod {ι : Type*}
    {s : Finset ι} {f : ι -> α -> β} (hf : forall i in s, HasCompactMulSupport (f i)) :
    HasCompactMulSupport (∏ i in s, f i) :=
  prod_mem (S := HasCompactMulSupport.submonoid α β) hf

end CommMonoid

section DivisionMonoid

@[to_additive]
/--
lemma `HasCompactMulSupport.inv` / 引理 `HasCompactMulSupport.inv`

English:
lemma HasCompactMulSupport.inv
  statement: {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
  proof: by
  simpa only [HasCompactMulSupport, mulTSupport, mulSupport_inv] using hf

@[to_additive]

中文:
引理 HasCompactMulSupport.inv
  结论: {α β : 类型} [拓扑空间 α] [Division幺半群 β]
  证明: by
  simpa only [HasCompactMulSupport, mulTSupport, mulSupport_inv] using hf

@[to_additive]
-/
protected lemma HasCompactMulSupport.inv {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
    {f : α -> β} (hf : HasCompactMulSupport f) :
    HasCompactMulSupport (f⁻¹) := by
  simpa only [HasCompactMulSupport, mulTSupport, mulSupport_inv] using hf

@[to_additive]
/--
theorem `HasCompactSupport.div` / 定理 `HasCompactSupport.div`

English:
theorem HasCompactSupport.div
  statement: {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
  proof: div_eq_mul_inv f f' ▸ hf.mul hf'.inv

中文:
定理 HasCompactSupport.div
  结论: {α β : 类型} [拓扑空间 α] [Division幺半群 β]
  证明: div_eq_mul_inv f f' ▸ hf.mul hf'.inv

Depends on / 依赖: div_eq_mul_inv, hf.mul
-/
theorem HasCompactSupport.div {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
    {f f' : α -> β} (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f / f') :=
  div_eq_mul_inv f f' ▸ hf.mul hf'.inv

end DivisionMonoid

section SMulZeroClass

variable [TopologicalSpace α] [Zero M] [SMulZeroClass R M]
variable {f : α -> R} {f' : α -> M}

/--
theorem `HasCompactSupport.smul_left` / 定理 `HasCompactSupport.smul_left`

English:
theorem HasCompactSupport.smul_left
  given: (hf : HasCompactSupport f')
  statement: HasCompactSupport (f • f')
  proof: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]

中文:
定理 HasCompactSupport.smul_left
  条件: (hf : HasCompactSupport f')
  结论: HasCompactSupport (f • f')
  证明: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]

Depends on / 依赖: Pi.smul_apply, Pi.zero_apply, hasCompactSupport_iff_eventuallyEq, hf.mono, simp_rw, smul_apply, smul_zero, zero_apply
-/
theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]

end SMulZeroClass

section SMulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SMulWithZero R M]
variable {f : α -> R} {f' : α -> M}

/--
theorem `HasCompactSupport.smul_right` / 定理 `HasCompactSupport.smul_right`

English:
theorem HasCompactSupport.smul_right
  given: (hf : HasCompactSupport f)
  statement: HasCompactSupport (f • f')
  proof: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]

中文:
定理 HasCompactSupport.smul_right
  条件: (hf : HasCompactSupport f)
  结论: HasCompactSupport (f • f')
  证明: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]

Depends on / 依赖: Pi.smul_apply, Pi.zero_apply, hasCompactSupport_iff_eventuallyEq, hf.mono, simp_rw, smul_apply, zero_apply, zero_smul
-/
theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]

end SMulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]
variable {f f' : α -> β}

/--
theorem `HasCompactSupport.mul_right` / 定理 `HasCompactSupport.mul_right`

English:
theorem HasCompactSupport.mul_right
  given: (hf : HasCompactSupport f)
  statement: HasCompactSupport (f * f')
  proof: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]

中文:
定理 HasCompactSupport.mul_right
  条件: (hf : HasCompactSupport f)
  结论: HasCompactSupport (f * f')
  证明: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]

Depends on / 依赖: Pi.mul_apply, Pi.zero_apply, hasCompactSupport_iff_eventuallyEq, hf.mono, mul_apply, simp_rw, zero_apply, zero_mul
-/
theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]

/--
theorem `HasCompactSupport.mul_left` / 定理 `HasCompactSupport.mul_left`

English:
theorem HasCompactSupport.mul_left
  given: (hf : HasCompactSupport f')
  statement: HasCompactSupport (f * f')
  proof: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]

中文:
定理 HasCompactSupport.mul_left
  条件: (hf : HasCompactSupport f')
  结论: HasCompactSupport (f * f')
  证明: by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]

Depends on / 依赖: Pi.mul_apply, Pi.zero_apply, hasCompactSupport_iff_eventuallyEq, hf.mono, mul_apply, mul_zero, simp_rw, zero_apply
-/
theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]

end MulZeroClass

section OrderedAddGroup

variable [TopologicalSpace α] [AddGroup β] [Lattice β] [AddLeftMono β]

/--
theorem `HasCompactSupport.abs` / 定理 `HasCompactSupport.abs`

English:
theorem HasCompactSupport.abs
  given: {f : α -> β} (hf : HasCompactSupport f)
  proof: hf.comp_left (g := abs) abs_zero

中文:
定理 HasCompactSupport.abs
  条件: {f : α -> β} (hf : HasCompactSupport f)
  证明: hf.comp_left (g := abs) abs_zero
-/
protected theorem HasCompactSupport.abs {f : α -> β} (hf : HasCompactSupport f) :
    HasCompactSupport |f| :=
  hf.comp_left (g := abs) abs_zero

end OrderedAddGroup

end CompactSupport2

section LocallyFinite

variable {ι : Type*} [TopologicalSpace X]

-- TODO: reformulate for any locally finite family of sets
/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive /-- If a family of functions `f` has locally-finite support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are non-zero. -/]
/--
theorem `LocallyFinite.exists_finset_nhds_mulSupport_subset` / 定理 `LocallyFinite.exists_finset_nhds_mulSupport_subset`

English:
theorem LocallyFinite.exists_finset_nhds_mulSupport_subset
  statement: {U : ι -> Set X} [One R] {f : ι -> X -> R}
  proof: by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := {i in hnf.toFinset | x in U i}
    let js := {j in hnf.toFinset | x ∉ U j}
    refine
      ⟨is, (n inter ⋂ j in js, (mulTSupport (f j))ᶜ) inter ⋂ i in is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
   

中文:
定理 局部有限.存在_finset_nhds_mulSupport_subset
  结论: {U : ι -> 集合 X} [幺 R] {f : ι -> X -> R}
  证明: by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := {i in hnf.toFinset | x in U i}
    let js := {j in hnf.toFinset | x ∉ U j}
    refine
      ⟨is, (n inter ⋂ j in js, (mulTSupport (f j))ᶜ) inter ⋂ i in is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
   

Depends on / 依赖: Finset, Finset.mem_filt, Finset.mem_filter.mp, IsClosed, IsClosed.compl_mem_nhds, Set.notMem_subset, biInter_finset_mem, classical, compl_mem_nhds, hnf.toFinset, inter_mem, inter_subset_right, isClosed_mulTSupport, mem_filt, mem_filter, mem_nhds, mulTSupport, notMem_subset, toFinset
-/
theorem LocallyFinite.exists_finset_nhds_mulSupport_subset {U : ι -> Set X} [One R] {f : ι -> X -> R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : forall i, mulTSupport (f i) subseteq U i)
    (ho : forall i, IsOpen (U i)) (x : X) :
    exists (is : Finset ι), exists n, n in 𝓝 x ∧ (n subseteq ⋂ i in is, U i) ∧
      forall z in n, (mulSupport fun i => f i z) subseteq is := by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := {i in hnf.toFinset | x in U i}
    let js := {j in hnf.toFinset | x ∉ U j}
    refine
      ⟨is, (n inter ⋂ j in js, (mulTSupport (f j))ᶜ) inter ⋂ i in is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
    · exact (biInter_finset_mem js).mpr fun j hj => IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
        (Set.notMem_subset (hso j) (Finset.mem_filter.mp hj).2)
    · exact (biInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (Finset.mem_filter.mp hi).2
    · have hzn : z in n := by
        rw [inter_assoc] at hz
        exact mem_of_mem_inter_left hz
      replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz)
      simp only [js, Finset.mem_filter, Finite.mem_toFinset, mem_ofPred_eq, mem_iInter,
        and_imp] at hz
      suffices (mulSupport fun i => f i z) subseteq hnf.toFinset by
        refine hnf.toFinset.subset_coe_filter_of_subset_forall _ this fun i hi => ?_
        specialize hz i ⟨z, ⟨hi, hzn⟩⟩
        contrapose hz
        simp [hz, subset_mulTSupport (f i) hi]
      intro i hi
      simp only [Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨z, ⟨hi, hzn⟩⟩

@[to_additive]
/--
theorem `locallyFinite_mulSupport_iff` / 定理 `locallyFinite_mulSupport_iff`

English:
theorem locallyFinite_mulSupport_iff
  given: [One M] {f : ι -> X -> M}
  proof: ⟨LocallyFinite.closure, fun H => H.subset fun _ => subset_closure⟩

中文:
定理 locallyFinite_mulSupport_iff
  条件: [幺 M] {f : ι -> X -> M}
  证明: ⟨LocallyFinite.closure, fun H => H.subset fun _ => subset_closure⟩

Depends on / 依赖: H.subset, LocallyFinite, LocallyFinite.closure, closure, subset, subset_closure
-/
theorem locallyFinite_mulSupport_iff [One M] {f : ι -> X -> M} :
(LocallyFinite fun i => mulSupport <| f i) ↔ LocallyFinite fun i => mulTSupport f i :=
  ⟨LocallyFinite.closure, fun H => H.subset fun _ => subset_closure⟩

/--
theorem `LocallyFinite.smul_left` / 定理 `LocallyFinite.smul_left`

English:
theorem LocallyFinite.smul_left
  statement: [Zero R] [Zero M] [SMulWithZero R M]
  proof: h.subset fun i x => mt fun h => by rw [Pi.smul_apply', h, zero_smul]

中文:
定理 局部有限.smul_left
  结论: [零 R] [零 M] [带零标量乘法 R M]
  证明: h.subset fun i x => mt fun h => by rw [Pi.smul_apply', h, zero_smul]

Depends on / 依赖: Pi.smul_apply, h.subset, smul_apply, subset, zero_smul
-/
theorem LocallyFinite.smul_left [Zero R] [Zero M] [SMulWithZero R M]
    {s : ι -> X -> R} (h : LocallyFinite fun i => support <| s i) (f : ι -> X -> M) :
LocallyFinite fun i => support s i • f i :=
h.subset fun i x => mt fun h => by rw [Pi.smul_apply', h, zero_smul]

/--
theorem `LocallyFinite.smul_right` / 定理 `LocallyFinite.smul_right`

English:
theorem LocallyFinite.smul_right
  statement: [Zero M] [SMulZeroClass R M]
  proof: h.subset fun i x => mt fun h => by rw [Pi.smul_apply', h, smul_zero]

中文:
定理 局部有限.smul_right
  结论: [零 M] [SMulZero类 R M]
  证明: h.subset fun i x => mt fun h => by rw [Pi.smul_apply', h, smul_zero]

Depends on / 依赖: Pi.smul_apply, h.subset, smul_apply, smul_zero, subset
-/
theorem LocallyFinite.smul_right [Zero M] [SMulZeroClass R M]
    {f : ι -> X -> M} (h : LocallyFinite fun i => support <| f i) (s : ι -> X -> R) :
LocallyFinite fun i => support s i • f i :=
h.subset fun i x => mt fun h => by rw [Pi.smul_apply', h, smul_zero]

end LocallyFinite

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[to_additive]
/--
theorem `HasCompactMulSupport.comp_homeomorph` / 定理 `HasCompactMulSupport.comp_homeomorph`

English:
theorem HasCompactMulSupport.comp_homeomorph
  statement: {M} [One M] {f : Y -> M}
  proof: hf.comp_isClosedEmbedding φ.isClosedEmbedding

中文:
定理 HasCompactMulSupport.comp_homeomorph
  结论: {M} [幺 M] {f : Y -> M}
  证明: hf.comp_isClosedEmbedding φ.isClosedEmbedding

Depends on / 依赖: comp_isClosedEmbedding, hf.comp_isClosedEmbedding, isClosedEmbedding
-/
theorem HasCompactMulSupport.comp_homeomorph {M} [One M] {f : Y -> M}
    (hf : HasCompactMulSupport f) (φ : X ≃ₜ Y) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_isClosedEmbedding φ.isClosedEmbedding

end Homeomorph
