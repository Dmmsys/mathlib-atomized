/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Order.Filter.Cofinite  -- shake: keep (used in notation only)
public import Mathlib.Algebra.Module.Pi

/-!
# Restricted products of sets, groups and rings

We define the **restricted product** of `R : ι → Type*` of types, relative to
a family of subsets `A : (i : ι) → Set (R i)` and a filter `𝓕 : Filter ι`. This
is the set of all `x : Π i, R i` such that the set `{j | x j ∈ A j}` belongs to `𝓕`.
We denote it by `Πʳ i, [R i, A i]_[𝓕]`.

The main case of interest, which we shall refer to as the "classical restricted product",
is that of `𝓕 = cofinite`. Recall that this is the filter of all subsets of `ι`, which are
*cofinite* in the sense that they have finite complement.
Hence, the associated restricted product is the set of all `x : Π i, R i` such that
`x j ∈ A j` for all but finitely many `j`s. We denote it simply by `Πʳ i, [R i, A i]`.

Another notable case is that of the principal filter `𝓕 = 𝓟 s` corresponding to some subset `s`
of `ι`. The associated restricted product `Πʳ i, [R i, A i]_[𝓟 s]` is the set of all
`x : Π i, R i` such that `x j ∈ A j` for all `j ∈ s`. Put another way, this is just
`(Π i ∈ s, A i) × (Π i ∉ s, R i)`, modulo the obvious isomorphism.

We endow these types with the obvious algebraic structures. We also show various compatibility
results.

See also the file `Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`, which
puts the structure of a topological space on a restricted product of topological spaces.

## Main definitions

* `RestrictedProduct`: the restricted product of a family `R` of types, relative to a family `A` of
  subsets and a filter `𝓕` on the indexing set. This is denoted `Πʳ i, [R i, A i]_[𝓕]`,
  or simply `Πʳ i, [R i, A i]` when `𝓕 = cofinite`.
* `RestrictedProduct.instDFunLike`: interpret an element of `Πʳ i, [R i, A i]_[𝓕]` as an element
  of `Π i, R i` using the `DFunLike` machinery.
* `RestrictedProduct.structureMap`: the inclusion map from `Π i, A i` to `Πʳ i, [R i, A i]_[𝓕]`.

## Notation

* `Πʳ i, [R i, A i]_[𝓕]` is `RestrictedProduct R A 𝓕`.
* `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`.

## Tags

restricted product, adeles, ideles
-/

@[expose] public section

open Set Filter

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))

/-!
## Definition and elementary maps
-/

/-- The **restricted product** of a family `R : ι → Type*` of types, relative to subsets
`A : (i : ι) → Set (R i)` and the filter `𝓕 : Filter ι`, is the set of all `x : Π i, R i`
such that the set `{j | x j ∈ A j}` belongs to `𝓕`. We denote it by `Πʳ i, [R i, A i]_[𝓕]`.

The most common use case is with `𝓕 = cofinite`, in which case the restricted product is the set
of all `x : Π i, R i` such that `x j ∈ A j` for all but finitely many `j`. We denote it simply
by `Πʳ i, [R i, A i]`.

Similarly, if `S` is a principal filter, the restricted product `Πʳ i, [R i, A i]_[𝓟 s]`
is the set of all `x : Π i, R i` such that `∀ j ∈ S, x j ∈ A j`. -/
/-
**RestrictedProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RestrictedProduct (𝓕 : Filter ι) : Type _
参数：𝓕 : Filter ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **restricted product** of a family `R : ι → Type*` of types, relative to sub
sets
`A : (i : ι) → Set (R i)` and the filter `𝓕 : Filter ι`, is the set of all `x : 
Π i, R i`
such that the set `{j | x j ∈ A j}` belongs to `𝓕`. We denote it by `Πʳ i, [R i,
 A i]_[𝓕]`.

The most common use case is with `𝓕 = cofinite`, in which case the restricted pr
oduct is the set
of all `x : Π i, R i` such that `x j ∈ A j` for all but finitely many `j`. We de
note it simply
by `Πʳ i, [R i, A i]`.

Similarly, if `S` is a principal filter, the restricted product `Πʳ i, [R i, A i
]_[𝓟 s]`
is the set of all `x : Π i, R i` such that `∀ j ∈ S, x j ∈ A j`.
-/
def RestrictedProduct (𝓕 : Filter ι) : Type _ := {x : Π i, R i // ∀ᶠ i in 𝓕, x i ∈ A i}

open Batteries.ExtendedBinder

/-- `Πʳ i, [R i, A i]_[𝓕]` is `RestrictedProduct R A 𝓕`. -/
scoped[RestrictedProduct]
notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]_[" f "]" =>
  RestrictedProduct r a f

/-- `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`. -/
scoped[RestrictedProduct]
notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]" =>
  RestrictedProduct r a cofinite

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι}

/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R where
  coe x i := x.1 i
  coe_injective _ _ := Subtype.ext

variable {R A} in
/-- Constructor for `RestrictedProduct`. -/
/-
**RestrictedProduct.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `RestrictedProduct`。
形式化陈述：mk (x : Π i, R i) (hx : forallᶠ i in 𝓕, x i in A i) : Πʳ i, [R i, A i]_[𝓕]
参数：x : Π i, R i；hx : forallᶠ i in 𝓕, x i in A i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `RestrictedProduct`.
-/
abbrev mk (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, hx⟩

@[simp]
/-
**RestrictedProduct.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mk_apply (x : Π i, R i) (hx : forallᶠ i in 𝓕, x i in A i) (i : ι) : (mk x 
hx) i = x i
参数：x : Π i, R i；hx : forallᶠ i in 𝓕, x i in A i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) (i : ι) :
    (mk x hx) i = x i := rfl

@[ext]
/-
**RestrictedProduct.ext** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x i = y i) : x = y
参数：h : forall i, x i = y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : ∀ i, x i = y i) : x = y :=
  Subtype.ext <| funext h
/-
**RestrictedProduct.range_coe** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：range_coe : range ((↑) : Πʳ i, [R i, A i]_[𝓕] -> Π i, R i) = {x | forallᶠ 
i in 𝓕, x i in A i}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
-/
lemma range_coe :
    range ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) = {x | ∀ᶠ i in 𝓕, x i ∈ A i} :=
  Subtype.range_val_subtype
/-
**RestrictedProduct.range_coe_principal** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：range_coe_principal {S : Set ι} : range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π
 i, R i) = S.pi A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.range_coe`：range_coe : range ((↑) : Πʳ i, [R i, A i]_[
𝓕] -> Π i, R i) = {x | forallᶠ i in 𝓕, x i in A i}
-/
lemma range_coe_principal {S : Set ι} :
    range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) = S.pi A :=
  range_coe R A
/-
**RestrictedProduct.eventually** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduct`。
形式化陈述：∀ {ι : Type u_1} (R : ι → Type u_2) (A : (i : ι) → Set (R i)) {𝓕 : Filter 
ι}   (x : RestrictedProduct (fun i => R i) (fun i => A i) 𝓕), ∀ᶠ (i : ι) in 𝓕, x
 i ∈ A i
参数：R : ι → Type u_2；A : (i : ι) → Set (R i)；x : RestrictedProduct (fun i => R i)
 (fun i => A i) 𝓕；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[simp] lemma eventually (x : Πʳ i, [R i, A i]_[𝓕]) : ∀ᶠ i in 𝓕, x i ∈ A i := x.2

variable (𝓕) in
/-- The *structure map* of the restricted product is the obvious inclusion from `Π i, A i`
into `Πʳ i, [R i, A i]_[𝓕]`. -/
/-
**RestrictedProduct.structureMap** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：structureMap (x : Π i, A i) : Πʳ i, [R i, A i]_[𝓕]
参数：x : Π i, A i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *structure map* of the restricted product is the obvious inclusion from `Π i
, A i`
into `Πʳ i, [R i, A i]_[𝓕]`.
-/
def structureMap (x : Π i, A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨fun i ↦ x i, .of_forall fun i ↦ (x i).2⟩

@[simp]
/-
**RestrictedProduct.structureMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProd
uct`。
形式化陈述：structureMap_apply {x : Π i, A i} (i : ι) : structureMap R A 𝓕 x i = x i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma structureMap_apply {x : Π i, A i} (i : ι) :
    structureMap R A 𝓕 x i = x i :=
  rfl

/-- If `𝓕 ≤ 𝓖`, the restricted product `Πʳ i, [R i, A i]_[𝓖]` is naturally included in
`Πʳ i, [R i, A i]_[𝓕]`. This is the corresponding map. -/
/-
**RestrictedProduct.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：inclusion (h : 𝓕 <= 𝓖) (x : Πʳ i, [R i, A i]_[𝓖]) : Πʳ i, [R i, A i]_[𝓕]
参数：h : 𝓕 <= 𝓖；x : Πʳ i, [R i, A i]_[𝓖]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝓕 ≤ 𝓖`, the restricted product `Πʳ i, [R i, A i]_[𝓖]` is naturally included 
in
`Πʳ i, [R i, A i]_[𝓕]`. This is the corresponding map.
-/
def inclusion (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, A i]_[𝓖]) :
    Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, x.2.filter_mono h⟩

@[simp]
/-
**RestrictedProduct.inclusion_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct
`。
形式化陈述：inclusion_apply (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓖]} (i : ι) : inclusio
n R A h x i = x i
参数：h : 𝓕 <= 𝓖；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclusion_apply (h : 𝓕 ≤ 𝓖) {x : Πʳ i, [R i, A i]_[𝓖]} (i : ι) :
    inclusion R A h x i = x i :=
  rfl

variable (𝓕) in
/-
**RestrictedProduct.inclusion_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct
`。
形式化陈述：inclusion_eq_id : inclusion R A (le_refl 𝓕) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma inclusion_eq_id : inclusion R A (le_refl 𝓕) = id := rfl
/-
**RestrictedProduct.exists_inclusion_eq_of_eventually** 是 Mathlib 中的一个引理，位于命名空间 
`RestrictedProduct`。
形式化陈述：exists_inclusion_eq_of_eventually (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]} 
(hx𝓖 : forallᶠ i in 𝓖, x i in A i) : exists x' : Πʳ i, [R i, A i]_[𝓖], inclusion
 R A h x' = x
参数：h : 𝓕 <= 𝓖；hx𝓖 : forallᶠ i in 𝓖, x i in A i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_inclusion_eq_of_eventually (h : 𝓕 ≤ 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx𝓖 : ∀ᶠ i in 𝓖, x i ∈ A i) :
    ∃ x' : Πʳ i, [R i, A i]_[𝓖], inclusion R A h x' = x :=
  ⟨⟨x.1, hx𝓖⟩, rfl⟩
/-
**RestrictedProduct.exists_structureMap_eq_of_forall** 是 Mathlib 中的一个引理，位于命名空间 `
RestrictedProduct`。
形式化陈述：exists_structureMap_eq_of_forall {x : Πʳ i, [R i, A i]_[𝓕]} (hx : forall i
, x.1 i in A i) : exists x' : Π i, A i, structureMap R A 𝓕 x' = x
参数：hx : forall i, x.1 i in A i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_structureMap_eq_of_forall {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx : ∀ i, x.1 i ∈ A i) :
    ∃ x' : Π i, A i, structureMap R A 𝓕 x' = x :=
  ⟨fun i ↦ ⟨x i, hx i⟩, rfl⟩
/-
**RestrictedProduct.range_inclusion** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct
`。
形式化陈述：range_inclusion (h : 𝓕 <= 𝓖) : Set.range (inclusion R A h) = {x | forallᶠ 
i in 𝓖, x i in A i}
参数：h : 𝓕 <= 𝓖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用引理 `RestrictedProduct.exists_inclusion_eq_of_eventually`：exists_inclusion_eq
_of_eventually (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]} (hx𝓖 : forallᶠ i in 𝓖, x 
i in A i) : exists x' : Πʳ i, [R i, A i]_…
-/
lemma range_inclusion (h : 𝓕 ≤ 𝓖) :
    Set.range (inclusion R A h) = {x | ∀ᶠ i in 𝓖, x i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ x.2)
    (fun _ hx ↦ mem_range.mpr <| exists_inclusion_eq_of_eventually R A h hx)

@[simp]
/-
**RestrictedProduct.coe_comp_inclusion** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProd
uct`。
形式化陈述：coe_comp_inclusion (h : 𝓕 <= 𝓖) : DFunLike.coe ∘ inclusion R A h = DFunLik
e.coe
参数：h : 𝓕 <= 𝓖。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp_inclusion (h : 𝓕 ≤ 𝓖) :
    DFunLike.coe ∘ inclusion R A h = DFunLike.coe :=
  rfl
/-
**RestrictedProduct.image_coe_preimage_inclusion_subset** 是 Mathlib 中的一个引理，位于命名空
间 `RestrictedProduct`。
形式化陈述：image_coe_preimage_inclusion_subset (h : 𝓕 <= 𝓖) (U : Set Πʳ i, [R i, A i]
_[𝓕]) : (⇑) '' inclusion R A h ⁻¹' U subseteq (⇑) '' U
参数：h : 𝓕 <= 𝓖；U : Set Πʳ i, [R i, A i]_[𝓕]。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_coe_preimage_inclusion_subset (h : 𝓕 ≤ 𝓖)
    (U : Set Πʳ i, [R i, A i]_[𝓕]) : (⇑) '' inclusion R A h ⁻¹' U ⊆ (⇑) '' U :=
  fun _ ⟨x, hx, hx'⟩ ↦ ⟨inclusion R A h x, hx, hx'⟩
/-
**RestrictedProduct.range_structureMap** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProd
uct`。
形式化陈述：range_structureMap : Set.range (structureMap R A 𝓕) = {f | forall i, f.1 i
 in A i}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用引理 `RestrictedProduct.exists_structureMap_eq_of_forall`：exists_structureMap_
eq_of_forall {x : Πʳ i, [R i, A i]_[𝓕]} (hx : forall i, x.1 i in A i) : exists x
' : Π i, A i, structureMap R A 𝓕 x' = x
-/
lemma range_structureMap :
    Set.range (structureMap R A 𝓕) = {f | ∀ i, f.1 i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x i ↦ (x i).2)
    (fun _ hx ↦ mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

@[simp]
/-
**RestrictedProduct.coe_comp_structureMap** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedP
roduct`。
形式化陈述：coe_comp_structureMap : DFunLike.coe ∘ structureMap R A 𝓕 = fun x i => (x 
i).val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp_structureMap :
    DFunLike.coe ∘ structureMap R A 𝓕 = fun x i ↦ (x i).val :=
  rfl

section Algebra
/-!
## Algebraic instances on restricted products

In this section, we endow the restricted product with its algebraic instances.
To avoid any unnecessary coercions, we use subobject classes for the subset `B i` of each `R i`.
-/

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] : One (Πʳ i, [R i, B i]_[𝓕]) where
  one := ⟨fun _ ↦ 1, .of_forall fun _ ↦ one_mem _⟩

@[to_additive (attr := simp)]
/-
**RestrictedProduct.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：one_apply [Π i, One (R i)] [forall i, OneMemClass (S i) (R i)] (i : ι) : (
1 : Πʳ i, [R i, B i]_[𝓕]) i = 1
参数：R i；S i；R i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] (i : ι) :
    (1 : Πʳ i, [R i, B i]_[𝓕]) i = 1 :=
  rfl

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, B i]_[𝓕]) where
  inv x := ⟨fun i ↦ (x i)⁻¹, x.2.mono fun _ ↦ inv_mem⟩

@[to_additive (attr := simp)]
/-
**RestrictedProduct.inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：inv_apply [Π i, Inv (R i)] [forall i, InvMemClass (S i) (R i)] (x : Πʳ i, 
[R i, B i]_[𝓕]) (i : ι) : (x⁻¹) i = (x i)⁻¹
参数：R i；S i；R i；x : Πʳ i, [R i, B i]_[𝓕]；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_apply [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x⁻¹) i = (x i)⁻¹ :=
  rfl

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, B i]_[𝓕]) where
  mul x y := ⟨fun i ↦ x i * y i, y.2.mp (x.2.mono fun _ ↦ mul_mem)⟩

@[to_additive (attr := simp)]
/-
**RestrictedProduct.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mul_apply [Π i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] (x y : Πʳ i
, [R i, B i]_[𝓕]) (i : ι) : (x * y) i = x i * y i
参数：R i；S i；R i；x y : Πʳ i, [R i, B i]_[𝓕]；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)]
    (x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x * y) i = x i * y i :=
  rfl

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] :
    SMul G (Πʳ i, [R i, B i]_[𝓕]) where
  smul g x := ⟨fun i ↦ g • (x i), x.2.mono fun _ ↦ SMulMemClass.smul_mem g⟩

@[to_additive (attr := simp)]
/-
**RestrictedProduct.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：smul_apply {G : Type*} [Π i, SMul G (R i)] [forall i, SMulMemClass (S i) G
 (R i)] (g : G) (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (g • x) i = g • x i
参数：R i；S i；R i；g : G；x : Πʳ i, [R i, B i]_[𝓕]；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] (g : G)
    (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (g • x) i = g • x i :=
  rfl

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Div (Πʳ i, [R i, B i]_[𝓕]) where
  div x y := ⟨fun i ↦ x i / y i, y.2.mp (x.2.mono fun _ ↦ div_mem)⟩

@[to_additive (attr := simp)]
/-
**RestrictedProduct.div_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：div_apply [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)] 
(x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x / y) i = x i / y i
参数：R i；S i；R i；x y : Πʳ i, [R i, B i]_[𝓕]；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_apply [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)]
    (x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x / y) i = x i / y i :=
  rfl

@[to_additive]
/-
**RestrictedProduct.instPow** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
形式化陈述：instPow [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] : Pow (
Πʳ i, [R i, B i]_[𝓕]) Nat where pow x n
参数：R i；S i；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) ℕ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ pow_mem hi n⟩

@[to_additive]
/-
**RestrictedProduct.pow_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：pow_apply [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] (x : 
Πʳ i, [R i, B i]_[𝓕]) (n : Nat) (i : ι) : (x ^ n) i = x i ^ n
参数：R i；S i；R i；x : Πʳ i, [R i, B i]_[𝓕]；n : Nat；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_apply [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (n : ℕ) (i : ι) : (x ^ n) i = x i ^ n :=
  rfl

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Monoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.monoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, CommMonoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    CommMonoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.commMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
/-
**RestrictedProduct.instZPow** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
形式化陈述：instZPow [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)] :
 Pow (Πʳ i, [R i, B i]_[𝓕]) Int where pow x n
参数：R i；S i；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZPow [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) ℤ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ zpow_mem hi n⟩

@[to_additive]
/-
**RestrictedProduct.zpow_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：zpow_apply [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)]
 (x : Πʳ i, [R i, B i]_[𝓕]) (n : Int) (i : ι) : (x ^ n) i = x i ^ n
参数：R i；S i；R i；x : Πʳ i, [R i, B i]_[𝓕]；n : Int；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_apply [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (n : ℤ) (i : ι) : (x ^ n) i = x i ^ n :=
  rfl
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, AddMonoidWithOne (R i)] [∀ i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (Πʳ i, [R i, B i]_[𝓕]) where
  natCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ natCast_mem _ n⟩

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Group (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, CommGroup (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    CommGroup (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.commGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    IntCast (Πʳ i, [R i, B i]_[𝓕]) where
  intCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ intCast_mem _ n⟩
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    Ring (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Π i, CommRing (R i)] [∀ i, SubringClass (S i) (R i)] :
    CommRing (Πʳ i, [R i, B i]_[𝓕]) where
  mul_comm _ _ := DFunLike.coe_injective <| funext (fun _ ↦ mul_comm _ _)

variable {R} in
/-- The coercion from the restricted product of monoids `A i` to the (normal) product
is a monoid homomorphism. -/
@[to_additive /-- The coercion from the restricted product of additive monoids `A i` to the
(normal) product is an additive monoid homomorphism. -/]
/-
**RestrictedProduct.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：coeMonoidHom [forall i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i
)] : Πʳ i, [R i, B i]_[𝓕] ->* Π i, R i where toFun
参数：R i；S i；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coeMonoidHom [∀ i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Πʳ i, [R i, B i]_[𝓕] →* Π i, R i where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
/-
**RestrictedProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RestrictedProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀ : Type*} [Semiring R₀] [Π i, AddCommMonoid (R i)] [Π i, Module R₀ (R i)]
    [∀ i, AddSubmonoidClass (S i) (R i)] [∀ i, SMulMemClass (S i) R₀ (R i)] :
  Module R₀ (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.module R₀ (M := Π i, R i) coeAddMonoidHom (fun _ _ ↦ rfl)

end Algebra

section eval

variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

/-- `RestrictedProduct.evalMonoidHom j` is the monoid homomorphism from the restricted
product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`.
-/
@[to_additive /-- `RestrictedProduct.evalAddMonoidHom j` is the monoid homomorphism from the
restricted product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`. -/]
/-
**RestrictedProduct.evalMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：evalMonoidHom (j : ι) [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) 
(R i)] : (Πʳ i, [R i, B i]_[𝓕]) ->* R j where toFun x
参数：j : ι；R i；S i；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def evalMonoidHom (j : ι) [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →* R j where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**RestrictedProduct.evalMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：evalMonoidHom_apply [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R
 i)] (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalMonoidHom R j x = x j
参数：R i；S i；R i；x : Πʳ i, [R i, B i]_[𝓕]；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalMonoidHom_apply [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalMonoidHom R j x = x j :=
  rfl

/-- `RestrictedProduct.evalRingHom j` is the ring homomorphism from the restricted
product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`.
-/
/-
**RestrictedProduct.evalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：evalRingHom (j : ι) [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)]
 : (Πʳ i, [R i, B i]_[𝓕]) ->+* R j where __
参数：j : ι；R i；S i；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RestrictedProduct.evalRingHom j` is the ring homomorphism from the restricted
product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`.
-/
def evalRingHom (j : ι) [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →+* R j where
  __ := evalMonoidHom R j
  __ := evalAddMonoidHom R j

@[simp]
/-
**RestrictedProduct.evalRingHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProdu
ct`。
形式化陈述：evalRingHom_apply [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)] (
x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalRingHom R j x = x j
参数：R i；S i；R i；x : Πʳ i, [R i, B i]_[𝓕]；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalRingHom_apply [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalRingHom R j x = x j :=
  rfl

end eval

section map

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Tendsto f 𝓕₂ 𝓕₁)

section set

variable (φ : ∀ j, R₁ (f j) → R₂ j) (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (A₁ (f j)) (A₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, A₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, A₂ j]_[𝓕₂]`,
`RestrictedProduct.mapAlong` gives a function between them. The data needed is a
function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and functions `φ j : R₁ (f j) → R₂ j`
sending `A₁ (f j)` into `A₂ j` for an `𝓕₂`-large set of `j`'s.

See also `mapAlongMonoidHom`, `mapAlongAddMonoidHom` and `mapAlongRingHom` for variants.
-/
/-
**RestrictedProduct.mapAlong** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：mapAlong (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]
参数：x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two restricted products `Πʳ (i : ι₁), [R₁ i, A₁ i]_[𝓕₁]` and `Πʳ (j : ι₂),
 [R₂ j, A₂ j]_[𝓕₂]`,
`RestrictedProduct.mapAlong` gives a function between them. The data needed is a
function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and functions `φ 
j : R₁ (f j) → R₂ j`
sending `A₁ (f j)` into `A₂ j` for an `𝓕₂`-large set of `j`'s.

See also `mapAlongMonoidHom`, `mapAlongAddMonoidHom` and `mapAlongRingHom` for v
ariants.
-/
def mapAlong (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) : Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ⟨fun j ↦ φ j (x (f j)), by
  filter_upwards [hf.eventually x.2, hφ] using fun _ h1 h2 ↦ h2 h1⟩

@[simp]
/-
**RestrictedProduct.mapAlong_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`
。
形式化陈述：mapAlong_apply (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) (j : ι₂) : x.mapAlong R₁ R₂ f
 hf φ hφ j = φ j (x (f j))
参数：x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]；j : ι₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAlong_apply (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlong R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

-- variant of `mapAlong` where the index set is constant

/-- The maps between restricted products over a fixed index type,
given maps on the factors. -/
/-
**RestrictedProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：map {G H : ι -> Type*} {C : (i : ι) -> Set (G i)} {D : (i : ι) -> Set (H i
)} (φ : (i : ι) -> G i -> H i) (hφ : forallᶠ i in 𝓕, MapsTo (φ i) (C i) (D i)) (
x : Πʳ i, [G i, C i]_[𝓕]) : (Πʳ i, [H i, D i]_[𝓕])
参数：i : ι；G i；i : ι；H i；φ : (i : ι) -> G i -> H i；hφ : forallᶠ i in 𝓕, MapsTo (φ 
i) (C i) (D i)；x : Πʳ i, [G i, C i]_[𝓕]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
The maps between restricted products over a fixed index type,
given maps on the factors.
-/
def map {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)} (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) : (Πʳ i, [H i, D i]_[𝓕]) :=
  mapAlong G H id Filter.tendsto_id φ hφ x

@[simp]
/-
**RestrictedProduct.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：map_apply {G H : ι -> Type*} {C : (i : ι) -> Set (G i)} {D : (i : ι) -> Se
t (H i)} (φ : (i : ι) -> G i -> H i) (hφ : forallᶠ i in 𝓕, MapsTo (φ i) (C i) (D
 i)) (x : Πʳ i, [G i, C i]_[𝓕]) (j : ι) : x.map φ hφ j = φ j (x j)
参数：i : ι；G i；i : ι；H i；φ : (i : ι) -> G i -> H i；hφ : forallᶠ i in 𝓕, MapsTo (φ 
i) (C i) (D i)；x : Πʳ i, [G i, C i]_[𝓕]；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply {G H : ι → Type*} {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)} (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) (j : ι) :
    x.map φ hφ j = φ j (x j) :=
  rfl

end set

section monoid

variable [Π i, Monoid (R₁ i)] [Π i, Monoid (R₂ i)] [∀ i, SubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, SubmonoidClass (S₂ i) (R₂ i)] (φ : ∀ j, R₁ (f j) →* R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`
of monoids, `RestrictedProduct.mapAlongMonoidHom` gives a monoid homomorphism between them.
The data needed is a function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and monoid
homomorphisms `φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
@[to_additive
/-- Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and
`Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]` of additive monoids, `RestrictedProduct.mapAlongAddMonoidHom`
gives an additive monoid homomorphism between them. The data needed is a function `f : ι₂ → ι₁` such
that `𝓕₂` tends to `𝓕₁` along `f`, and additive monoid homomorphisms `φ j : R₁ (f j) → R₂ j`
sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s. -/]
/-
**RestrictedProduct.mapAlongMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProdu
ct`。
形式化陈述：mapAlongMonoidHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] wh
ere toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapAlongMonoidHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  toFun := mapAlong R₁ R₂ f hf (fun j r ↦ φ j r) hφ
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) _ _

@[to_additive (attr := simp)]
/-
**RestrictedProduct.mapAlongMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Restricte
dProduct`。
形式化陈述：mapAlongMonoidHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) : x.mapAlon
gMonoidHom R₁ R₂ f hf φ hφ j = φ j (x (f j))
参数：x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]；j : ι₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAlongMonoidHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongMonoidHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end monoid

section ring

variable [Π i, Ring (R₁ i)] [Π i, Ring (R₂ i)] [∀ i, SubringClass (S₁ i) (R₁ i)]
    [∀ i, SubringClass (S₂ i) (R₂ i)] (φ : ∀ j, R₁ (f j) →+* R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products of rings `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and
`Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`, `RestrictedProduct.mapAlongRingHom` gives a
ring homomorphism between them. The data needed is a
function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and ring homomorphisms
`φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
/-
**RestrictedProduct.mapAlongRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct
`。
形式化陈述：mapAlongRingHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] whe
re __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two restricted products of rings `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and
`Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`, `RestrictedProduct.mapAlongRingHom` gives a
ring homomorphism between them. The data needed is a
function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and ring homomorp
hisms
`φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of 
`j`'s.
-/
def mapAlongRingHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ

@[simp]
/-
**RestrictedProduct.mapAlongRingHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedP
roduct`。
形式化陈述：mapAlongRingHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) : x.mapAlongR
ingHom R₁ R₂ f hf φ hφ j = φ j (x (f j))
参数：x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]；j : ι₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAlongRingHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongRingHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end ring

end map

section single

variable {S : ι → Type*} {G : ι → Type*} [Π i, SetLike (S i) (G i)] (A : (i : ι) → (S i))
  [DecidableEq ι]

section one

variable [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι)

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive
/-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]
/-
**RestrictedProduct.mulSingle** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle (x : G i) : Πʳ i, [G i, A i] where val
参数：x : G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulSingle (x : G i) : Πʳ i, [G i, A i] where
  val := Pi.mulSingle i x
  property := by
    filter_upwards [show {i}ᶜ ∈ Filter.cofinite by simp]
    simp_all

@[to_additive (attr := simp)]
/-
**RestrictedProduct.coe_mulSingle_apply** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：coe_mulSingle_apply (x : G i) (j : ι) : mulSingle A i x j = Pi.mulSingle i
 x j
参数：x : G i；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mulSingle_apply (x : G i) (j : ι) : mulSingle A i x j = Pi.mulSingle i x j := rfl
/-
**RestrictedProduct.comp_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduct`
。
形式化陈述：∀ {ι : Type u_1} {S : ι → Type u_3} {G : ι → Type u_4} [inst : (i : ι) → S
etLike (S i) (G i)] (A : (i : ι) → S i)   [inst_1 : DecidableEq ι] [inst_2 : (i 
: ι) → One (G i)] [inst_3 : ∀ (i : ι), OneMemClass (S i) (G i)] (i : ι),   DFunL
ike.coe ∘ RestrictedProduct.mulSingle A i = Pi.mulSingle i
参数：i : ι；S i；G i；A : (i : ι) → S i；i : ι；G i；i : ι；S i；G i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma comp_mulSingle : (↑) ∘ mulSingle A i = Pi.mulSingle (M := G) i := by ext; simp

@[to_additive]
/-
**RestrictedProduct.mulSingle_injective** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：mulSingle_injective : (mulSingle A i).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用引理 `Pi.mulSingle_injective`：mulSingle_injective (i : ι) : Function.Injective
 (mulSingle i : M i -> forall i, M i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RestrictedProduct.comp_mulSingle`：∀ {ι : Type u_1} {S : ι → Type u_3} {G
 : ι → Type u_4} [inst : (i : ι) → SetLike (S i) (G i)] (A : (i : ι) → S i)   [i
nst_1 : DecidableEq ι]…
-/
lemma mulSingle_injective : (mulSingle A i).Injective :=
  (comp_mulSingle A _ ▸ Pi.mulSingle_injective i).of_comp

@[to_additive]
/-
**RestrictedProduct.mulSingle_inj** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle_inj {x y : G i} : mulSingle A i x = mulSingle A i y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `RestrictedProduct.mulSingle_injective`：mulSingle_injective : (mulSingle 
A i).Injective
-/
lemma mulSingle_inj {x y : G i} : mulSingle A i x = mulSingle A i y ↔ x = y :=
  (mulSingle_injective A i).eq_iff

@[to_additive]
/-
**RestrictedProduct.mulSingle_eq_same** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProdu
ct`。
形式化陈述：mulSingle_eq_same (r : G i) : mulSingle A i r i = r
参数：r : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
-/
lemma mulSingle_eq_same (r : G i) : mulSingle A i r i = r := Pi.mulSingle_eq_same i r

@[to_additive]
/-
**RestrictedProduct.mulSingle_eq_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProd
uct`。
形式化陈述：mulSingle_eq_of_ne {i j : ι} (r : G i) (h : j != i) : mulSingle A i r j = 
1
参数：r : G i；h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
-/
lemma mulSingle_eq_of_ne {i j : ι} (r : G i) (h : j ≠ i) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne h r

@[to_additive]
/-
**RestrictedProduct.mulSingle_eq_of_ne'** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPro
duct`。
形式化陈述：mulSingle_eq_of_ne' {i j : ι} (r : G i) (h : i != j) : mulSingle A i r j =
 1
参数：r : G i；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.mulSingle_eq_of_ne'`：mulSingle_eq_of_ne' {i i' : ι} (h : i != i') (x 
: M i) : mulSingle i x i' = 1
-/
lemma mulSingle_eq_of_ne' {i j : ι} (r : G i) (h : i ≠ j) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne' h r

@[to_additive (attr := simp)]
/-
**RestrictedProduct.mulSingle_one** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle_one : mulSingle A i 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Pi.mulSingle_one`：mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSingle_one : mulSingle A i 1 = 1 := by ext; simp

@[to_additive (attr := simp)]
/-
**RestrictedProduct.mulSingle_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPr
oduct`。
形式化陈述：mulSingle_eq_one_iff {x : G i} : mulSingle A i x = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用引理 `Pi.mulSingle_eq_one_iff`：mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 
1
-/
lemma mulSingle_eq_one_iff {x : G i} : mulSingle A i x = 1 ↔ x = 1 :=
  Subtype.ext_iff.trans Pi.mulSingle_eq_one_iff

@[to_additive]
/-
**RestrictedProduct.mulSingle_ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedPr
oduct`。
形式化陈述：mulSingle_ne_one_iff {x : G i} : mulSingle A i x != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用引理 `Pi.mulSingle_ne_one_iff`：mulSingle_ne_one_iff : mulSingle i x != 1 ↔ x !
= 1
-/
lemma mulSingle_ne_one_iff {x : G i} : mulSingle A i x ≠ 1 ↔ x ≠ 1 :=
  Subtype.coe_ne_coe.symm.trans Pi.mulSingle_ne_one_iff

end one

@[to_additive]
/-
**RestrictedProduct.mulSingle_mul** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle_mul [forall i, MulOneClass (G i)] [forall i, OneMemClass (S i) (
G i)] [forall i, MulMemClass (S i) (G i)] (i : ι) (r s : G i) : mulSingle A i (r
 * s) = mulSingle A i r * mulSingle A i s
参数：G i；S i；G i；S i；G i；i : ι；r s : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Pi.mulSingle_mul`：Pi.mulSingle_mul [forall i, MulOneClass <| f i] (i : I
) (x y : f i) : mulSingle i (x * y) = mulSingle i x * mulSingle i y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSingle_mul [∀ i, MulOneClass (G i)] [∀ i, OneMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r s : G i) :
    mulSingle A i (r * s) = mulSingle A i r * mulSingle A i s := by
  ext; simp [Pi.mulSingle_mul]

@[simp]
/-
**RestrictedProduct.mul_single** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mul_single [forall i, MulZeroClass (G i)] [forall i, ZeroMemClass (S i) (G
 i)] [forall i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]
) : single A i (x i * r) = x * single A i r
参数：G i；S i；G i；S i；G i；i : ι；r : G i；x : Πʳ i, [G i, A i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RestrictedProduct.single_eq_of_ne'`：∀ {ι : Type u_1} {S : ι → Type u_3} 
{G : ι → Type u_4} [inst : (i : ι) → SetLike (S i) (G i)] (A : (i : ι) → S i)   
[inst_1 : DecidableEq ι]…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma mul_single [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i (x i * r) = x * single A i r := by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[simp]
/-
**RestrictedProduct.single_mul** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：single_mul [forall i, MulZeroClass (G i)] [forall i, ZeroMemClass (S i) (G
 i)] [forall i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]
) : single A i (r * x i) = single A i r * x
参数：G i；S i；G i；S i；G i；i : ι；r : G i；x : Πʳ i, [G i, A i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RestrictedProduct.single_eq_of_ne'`：∀ {ι : Type u_1} {S : ι → Type u_3} 
{G : ι → Type u_4} [inst : (i : ι) → SetLike (S i) (G i)] (A : (i : ι) → S i)   
[inst_1 : DecidableEq ι]…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma single_mul [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i (r * x i) = single A i r * x := by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[to_additive]
/-
**RestrictedProduct.mulSingle_inv** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle_inv [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)
] (i : ι) (r : G i) : mulSingle A i r⁻¹ = (mulSingle A i r)⁻¹
参数：G i；S i；G i；i : ι；r : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Pi.mulSingle_inv`：Pi.mulSingle_inv [forall i, Group <| f i] (i : I) (x :
 f i) : mulSingle i x⁻¹ = (mulSingle i x)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSingle_inv [∀ i, Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (i : ι) (r : G i) :
    mulSingle A i r⁻¹ = (mulSingle A i r)⁻¹ := by
  ext; simp [Pi.mulSingle_inv]

@[to_additive]
/-
**RestrictedProduct.mulSingle_div** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle_div [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)
] (i : ι) (r s : G i) : mulSingle A i (r / s) = mulSingle A i r / mulSingle A i 
s
参数：G i；S i；G i；i : ι；r s : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Pi.mulSingle_div`：Pi.mulSingle_div [forall i, Group <| f i] (i : I) (x y
 : f i) : mulSingle i (x / y) = mulSingle i x / mulSingle i y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSingle_div [∀ i, Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (i : ι) (r s : G i) :
    mulSingle A i (r / s) = mulSingle A i r / mulSingle A i s := by
  ext; simp [Pi.mulSingle_div]

@[to_additive]
/-
**RestrictedProduct.mulSingle_pow** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`。
形式化陈述：mulSingle_pow [forall i, Monoid (G i)] [forall i, SubmonoidClass (S i) (G 
i)] (i : ι) (r : G i) (n : Nat) : mulSingle A i (r ^ n) = mulSingle A i r ^ n
参数：G i；S i；G i；i : ι；r : G i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Pi.mulSingle_pow`：Pi.mulSingle_pow [forall i, Monoid (f i)] (i : I) (x :
 f i) (n : Nat) : mulSingle i (x ^ n) = mulSingle i x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSingle_pow [∀ i, Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    (i : ι) (r : G i) (n : ℕ) :
    mulSingle A i (r ^ n) = mulSingle A i r ^ n := by
  ext; simp [Pi.mulSingle_pow, RestrictedProduct.pow_apply]

@[to_additive]
/-
**RestrictedProduct.mulSingle_zpow** 是 Mathlib 中的一个引理，位于命名空间 `RestrictedProduct`
。
形式化陈述：mulSingle_zpow [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i
)] (i : ι) (r : G i) (n : Int) : mulSingle A i (r ^ n) = mulSingle A i r ^ n
参数：G i；S i；G i；i : ι；r : G i；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RestrictedProduct.ext`：ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x
 i = y i) : x = y
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Pi.mulSingle_zpow`：Pi.mulSingle_zpow [forall i, Group (f i)] (i : I) (x 
: f i) (n : Int) : mulSingle i (x ^ n) = mulSingle i x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSingle_zpow [∀ i, Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (i : ι) (r : G i) (n : ℤ) :
    mulSingle A i (r ^ n) = mulSingle A i r ^ n := by
  ext; simp [Pi.mulSingle_zpow, RestrictedProduct.zpow_apply]

end single

end RestrictedProduct

