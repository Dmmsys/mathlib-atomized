/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Order.Filter.Cofinite -- shake: keep (used in notation only)
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
variable (R : ι -> Type*) (A : (i : ι) -> Set (R i))

/-!
## Definition and elementary maps
-/

/--
Definition of `RestrictedProduct` / `RestrictedProduct` 的定义

English:
definition RestrictedProduct
  signature: (𝓕 : Filter ι)
  body: {x : Π i, R i // forallᶠ i in 𝓕, x i in A i}

中文:
定义 RestrictedProduct
  签名: (𝓕 : Filter ι)
  定义体: {x : Π i, R i // forallᶠ i in 𝓕, x i in A i}
-/
def RestrictedProduct (𝓕 : Filter ι) : Type _ := {x : Π i, R i // forallᶠ i in 𝓕, x i in A i}

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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R
  body: x.1 i
  coe_injective _ _ := Subtype.ext

中文:
实例 :
  签名: DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R
  定义体: x.1 i
  coe_injective _ _ := Subtype.ext
-/
instance : DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R where
  coe x i := x.1 i
  coe_injective _ _ := Subtype.ext

variable {R A} in
/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (x : Π i, R i) (hx : forallᶠ i in 𝓕, x i in A i)
  body: ⟨x, hx⟩

@[simp]

中文:
缩写 mk
  签名: (x : Π i, R i) (hx : 对任意ᶠ i in 𝓕, x i in A i)
  定义体: ⟨x, hx⟩

@[simp]
-/
abbrev mk (x : Π i, R i) (hx : forallᶠ i in 𝓕, x i in A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, hx⟩

@[simp]
/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: (x : Π i, R i) (hx : forallᶠ i in 𝓕, x i in A i) (i : ι)
  proof: rfl

@[ext]

中文:
引理 mk_apply
  条件: (x : Π i, R i) (hx : 对任意ᶠ i in 𝓕, x i in A i) (i : ι)
  证明: rfl

@[ext]
-/
lemma mk_apply (x : Π i, R i) (hx : forallᶠ i in 𝓕, x i in A i) (i : ι) :
    (mk x hx) i = x i := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x i = y i)
  statement: x = y
  proof: Subtype.ext funext h

中文:
引理 ext
  条件: {x y : Πʳ i, [R i, A i]_[𝓕]} (h : 对任意 i, x i = y i)
  结论: x = y
  证明: Subtype.ext funext h

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : forall i, x i = y i) : x = y :=
Subtype.ext funext h

/--
lemma `range_coe` / 引理 `range_coe`

English:
lemma range_coe
  proof: Subtype.range_val_subtype

中文:
引理 range_coe
  证明: Subtype.range_val_subtype

Depends on / 依赖: Subtype, Subtype.range_val_subtype, range_val_subtype
-/
lemma range_coe :
    range ((↑) : Πʳ i, [R i, A i]_[𝓕] -> Π i, R i) = {x | forallᶠ i in 𝓕, x i in A i} :=
  Subtype.range_val_subtype

/--
lemma `range_coe_principal` / 引理 `range_coe_principal`

English:
lemma range_coe_principal
  given: {S : Set ι}
  proof: range_coe R A

中文:
引理 range_coe_principal
  条件: {S : Set ι}
  证明: range_coe R A

Depends on / 依赖: range_coe
-/
lemma range_coe_principal {S : Set ι} :
    range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] -> Π i, R i) = S.pi A :=
  range_coe R A

/--
lemma `eventually` / 引理 `eventually`

English:
lemma eventually
  given: (x : Πʳ i, [R i, A i]_[𝓕])
  statement: forallᶠ i in 𝓕, x i in A i
  proof: x.2

中文:
引理 eventually
  条件: (x : Πʳ i, [R i, A i]_[𝓕])
  结论: 对任意ᶠ i in 𝓕, x i in A i
  证明: x.2
-/
@[simp] lemma eventually (x : Πʳ i, [R i, A i]_[𝓕]) : forallᶠ i in 𝓕, x i in A i := x.2

variable (𝓕) in
/--
Definition of `structureMap` / `structureMap` 的定义

English:
definition structureMap
  signature: (x : Π i, A i)
  body: ⟨fun i => x i, .of_forall fun i => (x i).2⟩

@[simp]

中文:
定义 structureMap
  签名: (x : Π i, A i)
  定义体: ⟨fun i => x i, .of_forall fun i => (x i).2⟩

@[simp]

Depends on / 依赖: of_forall
-/
def structureMap (x : Π i, A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨fun i => x i, .of_forall fun i => (x i).2⟩

@[simp]
/--
lemma `structureMap_apply` / 引理 `structureMap_apply`

English:
lemma structureMap_apply
  given: {x : Π i, A i} (i : ι)
  proof: rfl

中文:
引理 structureMap_apply
  条件: {x : Π i, A i} (i : ι)
  证明: rfl
-/
lemma structureMap_apply {x : Π i, A i} (i : ι) :
    structureMap R A 𝓕 x i = x i :=
  rfl

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (h : 𝓕 <= 𝓖) (x : Πʳ i, [R i, A i]_[𝓖])
  body: ⟨x, x.2.filter_mono h⟩

@[simp]

中文:
定义 inclusion
  签名: (h : 𝓕 <= 𝓖) (x : Πʳ i, [R i, A i]_[𝓖])
  定义体: ⟨x, x.2.filter_mono h⟩

@[simp]

Depends on / 依赖: filter_mono
-/
def inclusion (h : 𝓕 <= 𝓖) (x : Πʳ i, [R i, A i]_[𝓖]) :
    Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, x.2.filter_mono h⟩

@[simp]
/--
lemma `inclusion_apply` / 引理 `inclusion_apply`

English:
lemma inclusion_apply
  given: (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓖]} (i : ι)
  proof: rfl

中文:
引理 inclusion_apply
  条件: (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓖]} (i : ι)
  证明: rfl
-/
lemma inclusion_apply (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓖]} (i : ι) :
    inclusion R A h x i = x i :=
  rfl

variable (𝓕) in
/--
lemma `inclusion_eq_id` / 引理 `inclusion_eq_id`

English:
lemma inclusion_eq_id
  statement: inclusion R A (le_refl 𝓕) = id
  proof: rfl

中文:
引理 inclusion_eq_id
  结论: inclusion R A (le_refl 𝓕) = id
  证明: rfl
-/
lemma inclusion_eq_id : inclusion R A (le_refl 𝓕) = id := rfl

/--
lemma `exists_inclusion_eq_of_eventually` / 引理 `exists_inclusion_eq_of_eventually`

English:
lemma exists_inclusion_eq_of_eventually
  statement: (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]}
  proof: ⟨⟨x.1, hx𝓖⟩, rfl⟩

中文:
引理 exists_inclusion_eq_of_eventually
  结论: (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]}
  证明: ⟨⟨x.1, hx𝓖⟩, rfl⟩
-/
lemma exists_inclusion_eq_of_eventually (h : 𝓕 <= 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx𝓖 : forallᶠ i in 𝓖, x i in A i) :
    exists x' : Πʳ i, [R i, A i]_[𝓖], inclusion R A h x' = x :=
  ⟨⟨x.1, hx𝓖⟩, rfl⟩

/--
lemma `exists_structureMap_eq_of_forall` / 引理 `exists_structureMap_eq_of_forall`

English:
lemma exists_structureMap_eq_of_forall
  statement: {x : Πʳ i, [R i, A i]_[𝓕]}
  proof: ⟨fun i => ⟨x i, hx i⟩, rfl⟩

中文:
引理 exists_structureMap_eq_of_forall
  结论: {x : Πʳ i, [R i, A i]_[𝓕]}
  证明: ⟨fun i => ⟨x i, hx i⟩, rfl⟩
-/
lemma exists_structureMap_eq_of_forall {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx : forall i, x.1 i in A i) :
    exists x' : Π i, A i, structureMap R A 𝓕 x' = x :=
  ⟨fun i => ⟨x i, hx i⟩, rfl⟩

/--
lemma `range_inclusion` / 引理 `range_inclusion`

English:
lemma range_inclusion
  given: (h : 𝓕 <= 𝓖)
  proof: subset_antisymm (range_subset_iff.mpr fun x => x.2)
    (fun _ hx => mem_range.mpr <| exists_inclusion_eq_of_eventually R A h hx)

@[simp]

中文:
引理 range_inclusion
  条件: (h : 𝓕 <= 𝓖)
  证明: subset_antisymm (range_subset_iff.mpr fun x => x.2)
    (fun _ hx => mem_range.mpr <| exists_inclusion_eq_of_eventually R A h hx)

@[simp]

Depends on / 依赖: exists_inclusion_eq_of_eventually, mem_range, mem_range.mpr, range_subset_iff, range_subset_iff.mpr, subset_antisymm
-/
lemma range_inclusion (h : 𝓕 <= 𝓖) :
    Set.range (inclusion R A h) = {x | forallᶠ i in 𝓖, x i in A i} :=
  subset_antisymm (range_subset_iff.mpr fun x => x.2)
    (fun _ hx => mem_range.mpr <| exists_inclusion_eq_of_eventually R A h hx)

@[simp]
/--
lemma `coe_comp_inclusion` / 引理 `coe_comp_inclusion`

English:
lemma coe_comp_inclusion
  given: (h : 𝓕 <= 𝓖)
  proof: rfl

中文:
引理 coe_comp_inclusion
  条件: (h : 𝓕 <= 𝓖)
  证明: rfl
-/
lemma coe_comp_inclusion (h : 𝓕 <= 𝓖) :
    DFunLike.coe ∘ inclusion R A h = DFunLike.coe :=
  rfl

/--
lemma `image_coe_preimage_inclusion_subset` / 引理 `image_coe_preimage_inclusion_subset`

English:
lemma image_coe_preimage_inclusion_subset
  statement: (h : 𝓕 <= 𝓖)
  proof: fun _ ⟨x, hx, hx'⟩ => ⟨inclusion R A h x, hx, hx'⟩

中文:
引理 image_coe_preimage_inclusion_subset
  结论: (h : 𝓕 <= 𝓖)
  证明: fun _ ⟨x, hx, hx'⟩ => ⟨inclusion R A h x, hx, hx'⟩

Depends on / 依赖: inclusion
-/
lemma image_coe_preimage_inclusion_subset (h : 𝓕 <= 𝓖)
    (U : Set Πʳ i, [R i, A i]_[𝓕]) : (⇑) '' inclusion R A h ⁻¹' U subseteq (⇑) '' U :=
  fun _ ⟨x, hx, hx'⟩ => ⟨inclusion R A h x, hx, hx'⟩

/--
lemma `range_structureMap` / 引理 `range_structureMap`

English:
lemma range_structureMap
  proof: subset_antisymm (range_subset_iff.mpr fun x i => (x i).2)
    (fun _ hx => mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

@[simp]

中文:
引理 range_structureMap
  证明: subset_antisymm (range_subset_iff.mpr fun x i => (x i).2)
    (fun _ hx => mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

@[simp]

Depends on / 依赖: exists_structureMap_eq_of_forall, mem_range, mem_range.mpr, range_subset_iff, range_subset_iff.mpr, subset_antisymm
-/
lemma range_structureMap :
    Set.range (structureMap R A 𝓕) = {f | forall i, f.1 i in A i} :=
  subset_antisymm (range_subset_iff.mpr fun x i => (x i).2)
    (fun _ hx => mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

@[simp]
/--
lemma `coe_comp_structureMap` / 引理 `coe_comp_structureMap`

English:
lemma coe_comp_structureMap
  proof: rfl

中文:
引理 coe_comp_structureMap
  证明: rfl
-/
lemma coe_comp_structureMap :
    DFunLike.coe ∘ structureMap R A 𝓕 = fun x i => (x i).val :=
  rfl

section Algebra
/-!
## Algebraic instances on restricted products

In this section, we endow the restricted product with its algebraic instances.
To avoid any unnecessary coercions, we use subobject classes for the subset `B i` of each `R i`.
-/

variable {S : ι -> Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, One (R i)] [forall i, OneMemClass (S i) (R i)] : One (Πʳ i, [R i, B i]_[𝓕]) where
  body: ⟨fun _ => 1, .of_forall fun _ => one_mem _⟩

@[to_additive (attr := simp)]

中文:
实例 [Π
  签名: i, One (R i)] [对任意 i, OneMemClass (S i) (R i)] : One (Πʳ i, [R i, B i]_[𝓕]) where
  定义体: ⟨fun _ => 1, .of_forall fun _ => one_mem _⟩

@[to_additive (attr := simp)]

Depends on / 依赖: of_forall, one_mem
-/
instance [Π i, One (R i)] [forall i, OneMemClass (S i) (R i)] : One (Πʳ i, [R i, B i]_[𝓕]) where
  one := ⟨fun _ => 1, .of_forall fun _ => one_mem _⟩

@[to_additive (attr := simp)]
/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: [Π i, One (R i)] [forall i, OneMemClass (S i) (R i)] (i : ι)
  proof: rfl

@[to_additive]

中文:
引理 one_apply
  条件: [Π i, One (R i)] [对任意 i, OneMemClass (S i) (R i)] (i : ι)
  证明: rfl

@[to_additive]
-/
lemma one_apply [Π i, One (R i)] [forall i, OneMemClass (S i) (R i)] (i : ι) :
    (1 : Πʳ i, [R i, B i]_[𝓕]) i = 1 :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Inv (R i)] [forall i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, B i]_[𝓕]) where
  body: ⟨fun i => (x i)⁻¹, x.2.mono fun _ => inv_mem⟩

@[to_additive (attr := simp)]

中文:
实例 [Π
  签名: i, Inv (R i)] [对任意 i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, B i]_[𝓕]) where
  定义体: ⟨fun i => (x i)⁻¹, x.2.mono fun _ => inv_mem⟩

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mem
-/
instance [Π i, Inv (R i)] [forall i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, B i]_[𝓕]) where
  inv x := ⟨fun i => (x i)⁻¹, x.2.mono fun _ => inv_mem⟩

@[to_additive (attr := simp)]
/--
lemma `inv_apply` / 引理 `inv_apply`

English:
lemma inv_apply
  statement: [Π i, Inv (R i)] [forall i, InvMemClass (S i) (R i)]
  proof: rfl

@[to_additive]

中文:
引理 inv_apply
  结论: [Π i, Inv (R i)] [对任意 i, InvMemClass (S i) (R i)]
  证明: rfl

@[to_additive]
-/
lemma inv_apply [Π i, Inv (R i)] [forall i, InvMemClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x⁻¹) i = (x i)⁻¹ :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, B i]_[𝓕]) where
  body: ⟨fun i => x i * y i, y.2.mp (x.2.mono fun _ => mul_mem)⟩

@[to_additive (attr := simp)]

中文:
实例 [Π
  签名: i, Mul (R i)] [对任意 i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, B i]_[𝓕]) where
  定义体: ⟨fun i => x i * y i, y.2.mp (x.2.mono fun _ => mul_mem)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: mul_mem
-/
instance [Π i, Mul (R i)] [forall i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, B i]_[𝓕]) where
  mul x y := ⟨fun i => x i * y i, y.2.mp (x.2.mono fun _ => mul_mem)⟩

@[to_additive (attr := simp)]
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  statement: [Π i, Mul (R i)] [forall i, MulMemClass (S i) (R i)]
  proof: rfl

@[to_additive]

中文:
引理 mul_apply
  结论: [Π i, Mul (R i)] [对任意 i, MulMemClass (S i) (R i)]
  证明: rfl

@[to_additive]
-/
lemma mul_apply [Π i, Mul (R i)] [forall i, MulMemClass (S i) (R i)]
    (x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x * y) i = x i * y i :=
  rfl

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [forall i, SMulMemClass (S i) G (R i)] :
    SMul G (Πʳ i, [R i, B i]_[𝓕]) where
  smul g x := ⟨fun i => g • (x i), x.2.mono fun _ => SMulMemClass.smul_mem g⟩

@[to_additive (attr := simp)]
/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  statement: {G : Type*} [Π i, SMul G (R i)] [forall i, SMulMemClass (S i) G (R i)] (g : G)
  proof: rfl

@[to_additive]

中文:
引理 smul_apply
  结论: {G : 类型} [Π i, SMul G (R i)] [对任意 i, SMulMemClass (S i) G (R i)] (g : G)
  证明: rfl

@[to_additive]
-/
lemma smul_apply {G : Type*} [Π i, SMul G (R i)] [forall i, SMulMemClass (S i) G (R i)] (g : G)
    (x : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (g • x) i = g • x i :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)] :
  body: ⟨fun i => x i / y i, y.2.mp (x.2.mono fun _ => div_mem)⟩

@[to_additive (attr := simp)]

中文:
实例 [Π
  签名: i, DivInvMonoid (R i)] [对任意 i, SubgroupClass (S i) (R i)] :
  定义体: ⟨fun i => x i / y i, y.2.mp (x.2.mono fun _ => div_mem)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: div_mem
-/
instance [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)] :
    Div (Πʳ i, [R i, B i]_[𝓕]) where
  div x y := ⟨fun i => x i / y i, y.2.mp (x.2.mono fun _ => div_mem)⟩

@[to_additive (attr := simp)]
/--
lemma `div_apply` / 引理 `div_apply`

English:
lemma div_apply
  statement: [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)]
  proof: rfl

@[to_additive]

中文:
引理 div_apply
  结论: [Π i, DivInvMonoid (R i)] [对任意 i, SubgroupClass (S i) (R i)]
  证明: rfl

@[to_additive]
-/
lemma div_apply [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)]
    (x y : Πʳ i, [R i, B i]_[𝓕]) (i : ι) : (x / y) i = x i / y i :=
  rfl

@[to_additive]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
  body: ⟨fun i => x i ^ n, x.2.mono fun _ hi => pow_mem hi n⟩

@[to_additive]

中文:
实例 instPow
  签名: [Π i, Monoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)]
  定义体: ⟨fun i => x i ^ n, x.2.mono fun _ hi => pow_mem hi n⟩

@[to_additive]

Depends on / 依赖: pow_mem
-/
instance instPow [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) Nat where
  pow x n := ⟨fun i => x i ^ n, x.2.mono fun _ hi => pow_mem hi n⟩

@[to_additive]
/--
lemma `pow_apply` / 引理 `pow_apply`

English:
lemma pow_apply
  statement: [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
  proof: rfl

@[to_additive]

中文:
引理 pow_apply
  结论: [Π i, Monoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)]
  证明: rfl

@[to_additive]
-/
lemma pow_apply [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (n : Nat) (i : ι) : (x ^ n) i = x i ^ n :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
  body: DFunLike.coe_injective.monoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 [Π
  签名: i, Monoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)] :
  定义体: DFunLike.coe_injective.monoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.monoid, coe_injective, monoid
-/
instance [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
    Monoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.monoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, CommMonoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
  body: DFunLike.coe_injective.commMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 [Π
  签名: i, CommMonoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)] :
  定义体: DFunLike.coe_injective.commMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.commMonoid, coe_injective, commMonoid
-/
instance [Π i, CommMonoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
    CommMonoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.commMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `instZPow` / 实例 `instZPow`

English:
instance instZPow
  signature: [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)]
  body: ⟨fun i => x i ^ n, x.2.mono fun _ hi => zpow_mem hi n⟩

@[to_additive]

中文:
实例 instZPow
  签名: [Π i, DivInvMonoid (R i)] [对任意 i, SubgroupClass (S i) (R i)]
  定义体: ⟨fun i => x i ^ n, x.2.mono fun _ hi => zpow_mem hi n⟩

@[to_additive]

Depends on / 依赖: zpow_mem
-/
instance instZPow [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)] :
    Pow (Πʳ i, [R i, B i]_[𝓕]) Int where
  pow x n := ⟨fun i => x i ^ n, x.2.mono fun _ hi => zpow_mem hi n⟩

@[to_additive]
/--
lemma `zpow_apply` / 引理 `zpow_apply`

English:
lemma zpow_apply
  statement: [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)]
  proof: rfl

中文:
引理 zpow_apply
  结论: [Π i, DivInvMonoid (R i)] [对任意 i, SubgroupClass (S i) (R i)]
  证明: rfl
-/
lemma zpow_apply [Π i, DivInvMonoid (R i)] [forall i, SubgroupClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (n : Int) (i : ι) : (x ^ n) i = x i ^ n :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, AddMonoidWithOne (R i)] [forall i, AddSubmonoidWithOneClass (S i) (R i)] :
  body: ⟨fun _ => n, .of_forall fun _ => natCast_mem _ n⟩

@[to_additive]

中文:
实例 [Π
  签名: i, AddMonoidWithOne (R i)] [对任意 i, AddSubmonoidWithOneClass (S i) (R i)] :
  定义体: ⟨fun _ => n, .of_forall fun _ => natCast_mem _ n⟩

@[to_additive]

Depends on / 依赖: natCast_mem, of_forall
-/
instance [Π i, AddMonoidWithOne (R i)] [forall i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (Πʳ i, [R i, B i]_[𝓕]) where
  natCast n := ⟨fun _ => n, .of_forall fun _ => natCast_mem _ n⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Group (R i)] [forall i, SubgroupClass (S i) (R i)] :
  body: DFunLike.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 [Π
  签名: i, Group (R i)] [对任意 i, SubgroupClass (S i) (R i)] :
  定义体: DFunLike.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.group, coe_injective
-/
instance [Π i, Group (R i)] [forall i, SubgroupClass (S i) (R i)] :
    Group (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, CommGroup (R i)] [forall i, SubgroupClass (S i) (R i)] :
  body: DFunLike.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [Π
  签名: i, CommGroup (R i)] [对任意 i, SubgroupClass (S i) (R i)] :
  定义体: DFunLike.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.commGroup, coe_injective, commGroup
-/
instance [Π i, CommGroup (R i)] [forall i, SubgroupClass (S i) (R i)] :
    CommGroup (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Ring (R i)] [forall i, SubringClass (S i) (R i)] :
  body: ⟨fun _ => n, .of_forall fun _ => intCast_mem _ n⟩

中文:
实例 [Π
  签名: i, Ring (R i)] [对任意 i, SubringClass (S i) (R i)] :
  定义体: ⟨fun _ => n, .of_forall fun _ => intCast_mem _ n⟩

Depends on / 依赖: intCast_mem, of_forall
-/
instance [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)] :
    IntCast (Πʳ i, [R i, B i]_[𝓕]) where
  intCast n := ⟨fun _ => n, .of_forall fun _ => intCast_mem _ n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, Ring (R i)] [forall i, SubringClass (S i) (R i)] :
  body: DFunLike.coe_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

中文:
实例 [Π
  签名: i, Ring (R i)] [对任意 i, SubringClass (S i) (R i)] :
  定义体: DFunLike.coe_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.ring, coe_injective
-/
instance [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)] :
    Ring (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Π
  signature: i, CommRing (R i)] [forall i, SubringClass (S i) (R i)] :
  body: DFunLike.coe_injective funext (fun _ => mul_comm _ _)

中文:
实例 [Π
  签名: i, CommRing (R i)] [对任意 i, SubringClass (S i) (R i)] :
  定义体: DFunLike.coe_injective funext (fun _ => mul_comm _ _)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, mul_comm
-/
instance [Π i, CommRing (R i)] [forall i, SubringClass (S i) (R i)] :
    CommRing (Πʳ i, [R i, B i]_[𝓕]) where
mul_comm _ _ := DFunLike.coe_injective funext (fun _ => mul_comm _ _)

variable {R} in
/-- The coercion from the restricted product of monoids `A i` to the (normal) product
is a monoid homomorphism. -/
@[to_additive /-- The coercion from the restricted product of additive monoids `A i` to the
(normal) product is an additive monoid homomorphism. -/]
/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: [forall i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
  body: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 coeMonoidHom
  签名: [对任意 i, Monoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)]
  定义体: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def coeMonoidHom [forall i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
    Πʳ i, [R i, B i]_[𝓕] ->* Π i, R i where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

instance {R₀ : Type*} [Semiring R₀] [Π i, AddCommMonoid (R i)] [Π i, Module R₀ (R i)]
    [forall i, AddSubmonoidClass (S i) (R i)] [forall i, SMulMemClass (S i) R₀ (R i)] :
  Module R₀ (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.module R₀ (M := Π i, R i) coeAddMonoidHom (fun _ _ => rfl)

end Algebra

section eval

variable {S : ι -> Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

/-- `RestrictedProduct.evalMonoidHom j` is the monoid homomorphism from the restricted
product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`.
-/
@[to_additive /-- `RestrictedProduct.evalAddMonoidHom j` is the monoid homomorphism from the
restricted product `Πʳ i, [R i, B i]_[𝓕]` to the component `R j`. -/]
/--
Definition of `evalMonoidHom` / `evalMonoidHom` 的定义

English:
definition evalMonoidHom
  signature: (j : ι) [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
  body: x j
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 evalMonoidHom
  签名: (j : ι) [Π i, Monoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)]
  定义体: x j
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
-/
def evalMonoidHom (j : ι) [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) ->* R j where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/--
lemma `evalMonoidHom_apply` / 引理 `evalMonoidHom_apply`

English:
lemma evalMonoidHom_apply
  statement: [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
  proof: rfl

中文:
引理 evalMonoidHom_apply
  结论: [Π i, Monoid (R i)] [对任意 i, SubmonoidClass (S i) (R i)]
  证明: rfl
-/
lemma evalMonoidHom_apply [Π i, Monoid (R i)] [forall i, SubmonoidClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalMonoidHom R j x = x j :=
  rfl

/--
Definition of `evalRingHom` / `evalRingHom` 的定义

English:
definition evalRingHom
  signature: (j : ι) [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)]
  body: evalMonoidHom R j
  __ := evalAddMonoidHom R j

@[simp]

中文:
定义 evalRingHom
  签名: (j : ι) [Π i, Ring (R i)] [对任意 i, SubringClass (S i) (R i)]
  定义体: evalMonoidHom R j
  __ := evalAddMonoidHom R j

@[simp]

Depends on / 依赖: evalMonoidHom
-/
def evalRingHom (j : ι) [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) ->+* R j where
  __ := evalMonoidHom R j
  __ := evalAddMonoidHom R j

@[simp]
/--
lemma `evalRingHom_apply` / 引理 `evalRingHom_apply`

English:
lemma evalRingHom_apply
  statement: [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)]
  proof: rfl

中文:
引理 evalRingHom_apply
  结论: [Π i, Ring (R i)] [对任意 i, SubringClass (S i) (R i)]
  证明: rfl
-/
lemma evalRingHom_apply [Π i, Ring (R i)] [forall i, SubringClass (S i) (R i)]
    (x : Πʳ i, [R i, B i]_[𝓕]) (j : ι) : evalRingHom R j x = x j :=
  rfl

end eval

section map

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ -> Type*) (R₂ : ι₂ -> Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) -> Set (R₁ i)} {A₂ : (i : ι₂) -> Set (R₂ i)}
variable {S₁ : ι₁ -> Type*} {S₂ : ι₂ -> Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ -> ι₁) (hf : Tendsto f 𝓕₂ 𝓕₁)

section set

variable (φ : forall j, R₁ (f j) -> R₂ j) (hφ : forallᶠ j in 𝓕₂, MapsTo (φ j) (A₁ (f j)) (A₂ j))

/--
Definition of `mapAlong` / `mapAlong` 的定义

English:
definition mapAlong
  signature: (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁])
  body: ⟨fun j => φ j (x (f j)), by
  filter_upwards [hf.eventually x.2, hφ] using fun _ h1 h2 => h2 h1⟩

@[simp]

中文:
定义 mapAlong
  签名: (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁])
  定义体: ⟨fun j => φ j (x (f j)), by
  filter_upwards [hf.eventually x.2, hφ] using fun _ h1 h2 => h2 h1⟩

@[simp]

Depends on / 依赖: eventually, filter_upwards, hf.eventually
-/
def mapAlong (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) : Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ⟨fun j => φ j (x (f j)), by
  filter_upwards [hf.eventually x.2, hφ] using fun _ h1 h2 => h2 h1⟩

@[simp]
/--
lemma `mapAlong_apply` / 引理 `mapAlong_apply`

English:
lemma mapAlong_apply
  given: (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) (j : ι₂)
  proof: rfl

中文:
引理 mapAlong_apply
  条件: (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) (j : ι₂)
  证明: rfl
-/
lemma mapAlong_apply (x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlong R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

-- variant of `mapAlong` where the index set is constant

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {G H : ι -> Type*}
  body: mapAlong G H id Filter.tendsto_id φ hφ x

@[simp]

中文:
定义 map
  签名: {G H : ι -> 类型}
  定义体: mapAlong G H id Filter.tendsto_id φ hφ x

@[simp]

Depends on / 依赖: Filter, Filter.tendsto_id, mapAlong, tendsto_id
-/
def map {G H : ι -> Type*}
    {C : (i : ι) -> Set (G i)}
    {D : (i : ι) -> Set (H i)} (φ : (i : ι) -> G i -> H i)
    (hφ : forallᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) : (Πʳ i, [H i, D i]_[𝓕]) :=
  mapAlong G H id Filter.tendsto_id φ hφ x

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  statement: {G H : ι -> Type*} {C : (i : ι) -> Set (G i)}
  proof: rfl

中文:
引理 map_apply
  结论: {G H : ι -> 类型} {C : (i : ι) -> Set (G i)}
  证明: rfl
-/
lemma map_apply {G H : ι -> Type*} {C : (i : ι) -> Set (G i)}
    {D : (i : ι) -> Set (H i)} (φ : (i : ι) -> G i -> H i)
    (hφ : forallᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) (j : ι) :
    x.map φ hφ j = φ j (x j) :=
  rfl

end set

section monoid

variable [Π i, Monoid (R₁ i)] [Π i, Monoid (R₂ i)] [forall i, SubmonoidClass (S₁ i) (R₁ i)]
    [forall i, SubmonoidClass (S₂ i) (R₂ i)] (φ : forall j, R₁ (f j) ->* R₂ j)
    (hφ : forallᶠ j in 𝓕₂, MapsTo (φ j) (B₁ (f j)) (B₂ j))

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
/--
Definition of `mapAlongMonoidHom` / `mapAlongMonoidHom` 的定义

English:
definition mapAlongMonoidHom
  signature: : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  body: mapAlong R₁ R₂ f hf (fun j r => φ j r) hφ
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) _ _

@[to_additive (attr := simp)]

中文:
定义 mapAlongMonoidHom
  签名: : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  定义体: mapAlong R₁ R₂ f hf (fun j r => φ j r) hφ
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) _ _

@[to_additive (attr := simp)]

Depends on / 依赖: mapAlong
-/
def mapAlongMonoidHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  toFun := mapAlong R₁ R₂ f hf (fun j r => φ j r) hφ
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) _ _

@[to_additive (attr := simp)]
/--
lemma `mapAlongMonoidHom_apply` / 引理 `mapAlongMonoidHom_apply`

English:
lemma mapAlongMonoidHom_apply
  given: (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂)
  proof: rfl

中文:
引理 mapAlongMonoidHom_apply
  条件: (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂)
  证明: rfl
-/
lemma mapAlongMonoidHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongMonoidHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end monoid

section ring

variable [Π i, Ring (R₁ i)] [Π i, Ring (R₂ i)] [forall i, SubringClass (S₁ i) (R₁ i)]
    [forall i, SubringClass (S₂ i) (R₂ i)] (φ : forall j, R₁ (f j) ->+* R₂ j)
    (hφ : forallᶠ j in 𝓕₂, MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Definition of `mapAlongRingHom` / `mapAlongRingHom` 的定义

English:
definition mapAlongRingHom
  signature: : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  body: mapAlongMonoidHom R₁ R₂ f hf (fun j => φ j) hφ
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j => φ j) hφ

@[simp]

中文:
定义 mapAlongRingHom
  签名: : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  定义体: mapAlongMonoidHom R₁ R₂ f hf (fun j => φ j) hφ
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j => φ j) hφ

@[simp]

Depends on / 依赖: mapAlongMonoidHom
-/
def mapAlongRingHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] ->+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongMonoidHom R₁ R₂ f hf (fun j => φ j) hφ
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j => φ j) hφ

@[simp]
/--
lemma `mapAlongRingHom_apply` / 引理 `mapAlongRingHom_apply`

English:
lemma mapAlongRingHom_apply
  given: (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂)
  proof: rfl

中文:
引理 mapAlongRingHom_apply
  条件: (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂)
  证明: rfl
-/
lemma mapAlongRingHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongRingHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end ring

end map

section single

variable {S : ι -> Type*} {G : ι -> Type*} [Π i, SetLike (S i) (G i)] (A : (i : ι) -> (S i))
  [DecidableEq ι]

section one

variable [forall i, One (G i)] [forall i, OneMemClass (S i) (G i)] (i : ι)

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive
/-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]
/--
Definition of `mulSingle` / `mulSingle` 的定义

English:
definition mulSingle
  signature: (x : G i)
  body: Pi.mulSingle i x
  property := by
    filter_upwards [show {i}ᶜ in Filter.cofinite by simp]
    simp_all

@[to_additive (attr := simp)]

中文:
定义 mulSingle
  签名: (x : G i)
  定义体: Pi.mulSingle i x
  property := by
    filter_upwards [show {i}ᶜ in Filter.cofinite by simp]
    simp_all

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.mulSingle, mulSingle
-/
def mulSingle (x : G i) : Πʳ i, [G i, A i] where
  val := Pi.mulSingle i x
  property := by
    filter_upwards [show {i}ᶜ in Filter.cofinite by simp]
    simp_all

@[to_additive (attr := simp)]
/--
lemma `coe_mulSingle_apply` / 引理 `coe_mulSingle_apply`

English:
lemma coe_mulSingle_apply
  given: (x : G i) (j : ι)
  statement: mulSingle A i x j = Pi.mulSingle i x j
  proof: rfl

中文:
引理 coe_mulSingle_apply
  条件: (x : G i) (j : ι)
  结论: mulSingle A i x j = Pi.mulSingle i x j
  证明: rfl
-/
lemma coe_mulSingle_apply (x : G i) (j : ι) : mulSingle A i x j = Pi.mulSingle i x j := rfl
/--
lemma `comp_mulSingle` / 引理 `comp_mulSingle`

English:
lemma comp_mulSingle
  statement: (↑) ∘ mulSingle A i = Pi.mulSingle (M := G) i
  proof: by ext; simp

@[to_additive]

中文:
引理 comp_mulSingle
  结论: (↑) ∘ mulSingle A i = Pi.mulSingle (M := G) i
  证明: by ext; simp

@[to_additive]
-/
@[to_additive] lemma comp_mulSingle : (↑) ∘ mulSingle A i = Pi.mulSingle (M := G) i := by ext; simp

@[to_additive]
/--
lemma `mulSingle_injective` / 引理 `mulSingle_injective`

English:
lemma mulSingle_injective
  statement: (mulSingle A i).Injective
  proof: (comp_mulSingle A _ ▸ Pi.mulSingle_injective i).of_comp

@[to_additive]

中文:
引理 mulSingle_injective
  结论: (mulSingle A i).Injective
  证明: (comp_mulSingle A _ ▸ Pi.mulSingle_injective i).of_comp

@[to_additive]

Depends on / 依赖: Pi.mulSingle_injective, comp_mulSingle, mulSingle_injective, of_comp
-/
lemma mulSingle_injective : (mulSingle A i).Injective :=
  (comp_mulSingle A _ ▸ Pi.mulSingle_injective i).of_comp

@[to_additive]
/--
lemma `mulSingle_inj` / 引理 `mulSingle_inj`

English:
lemma mulSingle_inj
  given: {x y : G i}
  statement: mulSingle A i x = mulSingle A i y ↔ x = y
  proof: (mulSingle_injective A i).eq_iff

@[to_additive]

中文:
引理 mulSingle_inj
  条件: {x y : G i}
  结论: mulSingle A i x = mulSingle A i y ↔ x = y
  证明: (mulSingle_injective A i).eq_iff

@[to_additive]

Depends on / 依赖: eq_iff, mulSingle_injective
-/
lemma mulSingle_inj {x y : G i} : mulSingle A i x = mulSingle A i y ↔ x = y :=
  (mulSingle_injective A i).eq_iff

@[to_additive]
/--
lemma `mulSingle_eq_same` / 引理 `mulSingle_eq_same`

English:
lemma mulSingle_eq_same
  given: (r : G i)
  statement: mulSingle A i r i = r
  proof: Pi.mulSingle_eq_same i r

@[to_additive]

中文:
引理 mulSingle_eq_same
  条件: (r : G i)
  结论: mulSingle A i r i = r
  证明: Pi.mulSingle_eq_same i r

@[to_additive]

Depends on / 依赖: Pi.mulSingle_eq_same, mulSingle_eq_same
-/
lemma mulSingle_eq_same (r : G i) : mulSingle A i r i = r := Pi.mulSingle_eq_same i r

@[to_additive]
/--
lemma `mulSingle_eq_of_ne` / 引理 `mulSingle_eq_of_ne`

English:
lemma mulSingle_eq_of_ne
  given: {i j : ι} (r : G i) (h : j != i)
  statement: mulSingle A i r j = 1
  proof: Pi.mulSingle_eq_of_ne h r

@[to_additive]

中文:
引理 mulSingle_eq_of_ne
  条件: {i j : ι} (r : G i) (h : j != i)
  结论: mulSingle A i r j = 1
  证明: Pi.mulSingle_eq_of_ne h r

@[to_additive]

Depends on / 依赖: Pi.mulSingle_eq_of_ne, mulSingle_eq_of_ne
-/
lemma mulSingle_eq_of_ne {i j : ι} (r : G i) (h : j != i) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne h r

@[to_additive]
/--
lemma `mulSingle_eq_of_ne'` / 引理 `mulSingle_eq_of_ne'`

English:
lemma mulSingle_eq_of_ne'
  given: {i j : ι} (r : G i) (h : i != j)
  statement: mulSingle A i r j = 1
  proof: Pi.mulSingle_eq_of_ne' h r

@[to_additive (attr := simp)]

中文:
引理 mulSingle_eq_of_ne'
  条件: {i j : ι} (r : G i) (h : i != j)
  结论: mulSingle A i r j = 1
  证明: Pi.mulSingle_eq_of_ne' h r

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.mulSingle_eq_of_ne, mulSingle_eq_of_ne
-/
lemma mulSingle_eq_of_ne' {i j : ι} (r : G i) (h : i != j) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne' h r

@[to_additive (attr := simp)]
/--
lemma `mulSingle_one` / 引理 `mulSingle_one`

English:
lemma mulSingle_one
  statement: mulSingle A i 1 = 1
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 mulSingle_one
  结论: mulSingle A i 1 = 1
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma mulSingle_one : mulSingle A i 1 = 1 := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `mulSingle_eq_one_iff` / 引理 `mulSingle_eq_one_iff`

English:
lemma mulSingle_eq_one_iff
  given: {x : G i}
  statement: mulSingle A i x = 1 ↔ x = 1
  proof: Subtype.ext_iff.trans Pi.mulSingle_eq_one_iff

@[to_additive]

中文:
引理 mulSingle_eq_one_iff
  条件: {x : G i}
  结论: mulSingle A i x = 1 ↔ x = 1
  证明: Subtype.ext_iff.trans Pi.mulSingle_eq_one_iff

@[to_additive]

Depends on / 依赖: Pi.mulSingle_eq_one_iff, Subtype, Subtype.ext_iff.trans, ext_iff, mulSingle_eq_one_iff
-/
lemma mulSingle_eq_one_iff {x : G i} : mulSingle A i x = 1 ↔ x = 1 :=
  Subtype.ext_iff.trans Pi.mulSingle_eq_one_iff

@[to_additive]
/--
lemma `mulSingle_ne_one_iff` / 引理 `mulSingle_ne_one_iff`

English:
lemma mulSingle_ne_one_iff
  given: {x : G i}
  statement: mulSingle A i x != 1 ↔ x != 1
  proof: Subtype.coe_ne_coe.symm.trans Pi.mulSingle_ne_one_iff

中文:
引理 mulSingle_ne_one_iff
  条件: {x : G i}
  结论: mulSingle A i x != 1 ↔ x != 1
  证明: Subtype.coe_ne_coe.symm.trans Pi.mulSingle_ne_one_iff

Depends on / 依赖: Pi.mulSingle_ne_one_iff, Subtype, Subtype.coe_ne_coe.symm.trans, coe_ne_coe, mulSingle_ne_one_iff
-/
lemma mulSingle_ne_one_iff {x : G i} : mulSingle A i x != 1 ↔ x != 1 :=
  Subtype.coe_ne_coe.symm.trans Pi.mulSingle_ne_one_iff

end one

@[to_additive]
/--
lemma `mulSingle_mul` / 引理 `mulSingle_mul`

English:
lemma mulSingle_mul
  statement: [forall i, MulOneClass (G i)] [forall i, OneMemClass (S i) (G i)]
  proof: by
  ext; simp [Pi.mulSingle_mul]

@[simp]

中文:
引理 mulSingle_mul
  结论: [对任意 i, MulOneClass (G i)] [对任意 i, OneMemClass (S i) (G i)]
  证明: by
  ext; simp [Pi.mulSingle_mul]

@[simp]

Depends on / 依赖: Pi.mulSingle_mul, mulSingle_mul
-/
lemma mulSingle_mul [forall i, MulOneClass (G i)] [forall i, OneMemClass (S i) (G i)]
    [forall i, MulMemClass (S i) (G i)] (i : ι) (r s : G i) :
    mulSingle A i (r * s) = mulSingle A i r * mulSingle A i s := by
  ext; simp [Pi.mulSingle_mul]

@[simp]
/--
lemma `mul_single` / 引理 `mul_single`

English:
lemma mul_single
  statement: [forall i, MulZeroClass (G i)] [forall i, ZeroMemClass (S i) (G i)]
  proof: by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[simp]

中文:
引理 mul_single
  结论: [对任意 i, MulZeroClass (G i)] [对任意 i, ZeroMemClass (S i) (G i)]
  证明: by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[simp]

Depends on / 依赖: eq_or_ne, single_eq_of_ne
-/
lemma mul_single [forall i, MulZeroClass (G i)] [forall i, ZeroMemClass (S i) (G i)]
    [forall i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i (x i * r) = x * single A i r := by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[simp]
/--
lemma `single_mul` / 引理 `single_mul`

English:
lemma single_mul
  statement: [forall i, MulZeroClass (G i)] [forall i, ZeroMemClass (S i) (G i)]
  proof: by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[to_additive]

中文:
引理 single_mul
  结论: [对任意 i, MulZeroClass (G i)] [对任意 i, ZeroMemClass (S i) (G i)]
  证明: by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[to_additive]

Depends on / 依赖: eq_or_ne, single_eq_of_ne
-/
lemma single_mul [forall i, MulZeroClass (G i)] [forall i, ZeroMemClass (S i) (G i)]
    [forall i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i (r * x i) = single A i r * x := by
  ext j
  rcases eq_or_ne i j with rfl | hne; · simp
  simp [single_eq_of_ne' A _ hne]

@[to_additive]
/--
lemma `mulSingle_inv` / 引理 `mulSingle_inv`

English:
lemma mulSingle_inv
  statement: [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)]
  proof: by
  ext; simp [Pi.mulSingle_inv]

@[to_additive]

中文:
引理 mulSingle_inv
  结论: [对任意 i, Group (G i)] [对任意 i, SubgroupClass (S i) (G i)]
  证明: by
  ext; simp [Pi.mulSingle_inv]

@[to_additive]

Depends on / 依赖: Pi.mulSingle_inv, mulSingle_inv
-/
lemma mulSingle_inv [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)]
    (i : ι) (r : G i) :
    mulSingle A i r⁻¹ = (mulSingle A i r)⁻¹ := by
  ext; simp [Pi.mulSingle_inv]

@[to_additive]
/--
lemma `mulSingle_div` / 引理 `mulSingle_div`

English:
lemma mulSingle_div
  statement: [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)]
  proof: by
  ext; simp [Pi.mulSingle_div]

@[to_additive]

中文:
引理 mulSingle_div
  结论: [对任意 i, Group (G i)] [对任意 i, SubgroupClass (S i) (G i)]
  证明: by
  ext; simp [Pi.mulSingle_div]

@[to_additive]

Depends on / 依赖: Pi.mulSingle_div, mulSingle_div
-/
lemma mulSingle_div [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)]
    (i : ι) (r s : G i) :
    mulSingle A i (r / s) = mulSingle A i r / mulSingle A i s := by
  ext; simp [Pi.mulSingle_div]

@[to_additive]
/--
lemma `mulSingle_pow` / 引理 `mulSingle_pow`

English:
lemma mulSingle_pow
  statement: [forall i, Monoid (G i)] [forall i, SubmonoidClass (S i) (G i)]
  proof: by
  ext; simp [Pi.mulSingle_pow, RestrictedProduct.pow_apply]

@[to_additive]

中文:
引理 mulSingle_pow
  结论: [对任意 i, Monoid (G i)] [对任意 i, SubmonoidClass (S i) (G i)]
  证明: by
  ext; simp [Pi.mulSingle_pow, RestrictedProduct.pow_apply]

@[to_additive]

Depends on / 依赖: Pi.mulSingle_pow, RestrictedProduct, RestrictedProduct.pow_apply, mulSingle_pow, pow_apply
-/
lemma mulSingle_pow [forall i, Monoid (G i)] [forall i, SubmonoidClass (S i) (G i)]
    (i : ι) (r : G i) (n : Nat) :
    mulSingle A i (r ^ n) = mulSingle A i r ^ n := by
  ext; simp [Pi.mulSingle_pow, RestrictedProduct.pow_apply]

@[to_additive]
/--
lemma `mulSingle_zpow` / 引理 `mulSingle_zpow`

English:
lemma mulSingle_zpow
  statement: [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)]
  proof: by
  ext; simp [Pi.mulSingle_zpow, RestrictedProduct.zpow_apply]

中文:
引理 mulSingle_zpow
  结论: [对任意 i, Group (G i)] [对任意 i, SubgroupClass (S i) (G i)]
  证明: by
  ext; simp [Pi.mulSingle_zpow, RestrictedProduct.zpow_apply]

Depends on / 依赖: Pi.mulSingle_zpow, RestrictedProduct, RestrictedProduct.zpow_apply, mulSingle_zpow, zpow_apply
-/
lemma mulSingle_zpow [forall i, Group (G i)] [forall i, SubgroupClass (S i) (G i)]
    (i : ι) (r : G i) (n : Int) :
    mulSingle A i (r ^ n) = mulSingle A i r ^ n := by
  ext; simp [Pi.mulSingle_zpow, RestrictedProduct.zpow_apply]

end single

end RestrictedProduct
