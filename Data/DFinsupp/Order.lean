/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.DFinsupp.Module

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `DFinsupp.orderEmbeddingToFun`: The order embedding from finitely supported dependent functions
  to functions.

-/

@[expose] public section

open Finset

variable {ι : Type*} {α : ι -> Type*}

namespace DFinsupp

/-! ### Order structures -/


section Zero
variable [forall i, Zero (α i)]

section LE
variable [forall i, LE (α i)] {f g : Π₀ i, α i}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Π₀ i, α i)
  body: ⟨fun f g => forall i, f i <= g i⟩

中文:
实例 :
  签名: LE (Π₀ i, α i)
  定义体: ⟨fun f g => forall i, f i <= g i⟩
-/
instance : LE (Π₀ i, α i) :=
  ⟨fun f g => forall i, f i <= g i⟩

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  statement: f <= g ↔ forall i, f i <= g i
  proof: Iff.rfl

中文:
引理 le_def
  结论: f <= g ↔ 对任意 i, f i <= g i
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def : f <= g ↔ forall i, f i <= g i := Iff.rfl

/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: ⇑f <= g ↔ f <= g
  proof: Iff.rfl

中文:
引理 coe_le_coe
  结论: ⇑f <= g ↔ f <= g
  证明: Iff.rfl
-/
@[simp, norm_cast] lemma coe_le_coe : ⇑f <= g ↔ f <= g := Iff.rfl

/--
Definition of `orderEmbeddingToFun` / `orderEmbeddingToFun` 的定义

English:
definition orderEmbeddingToFun
  signature: : (Π₀ i, α i) ↪o forall i, α i where
  body: DFunLike.coe
  inj' := DFunLike.coe_injective
  map_rel_iff' := Iff.rfl

@[simp, norm_cast]

中文:
定义 orderEmbeddingToFun
  签名: : (Π₀ i, α i) ↪o 对任意 i, α i where
  定义体: DFunLike.coe
  inj' := DFunLike.coe_injective
  map_rel_iff' := Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: DFunLike, DFunLike.coe
-/
def orderEmbeddingToFun : (Π₀ i, α i) ↪o forall i, α i where
  toFun := DFunLike.coe
  inj' := DFunLike.coe_injective
  map_rel_iff' := Iff.rfl

@[simp, norm_cast]
/--
lemma `coe_orderEmbeddingToFun` / 引理 `coe_orderEmbeddingToFun`

English:
lemma coe_orderEmbeddingToFun
  statement: ⇑(orderEmbeddingToFun (α := α)) = DFunLike.coe
  proof: rfl

中文:
引理 coe_orderEmbeddingToFun
  结论: ⇑(orderEmbeddingToFun (α := α)) = 依赖函数状.coe
  证明: rfl

Depends on / 依赖: DFunLike, DFunLike.coe
-/
lemma coe_orderEmbeddingToFun : ⇑(orderEmbeddingToFun (α := α)) = DFunLike.coe := rfl

/--
theorem `orderEmbeddingToFun_apply` / 定理 `orderEmbeddingToFun_apply`

English:
theorem orderEmbeddingToFun_apply
  given: {f : Π₀ i, α i} {i : ι}
  proof: rfl

中文:
定理 orderEmbeddingToFun_apply
  条件: {f : Π₀ i, α i} {i : ι}
  证明: rfl
-/
theorem orderEmbeddingToFun_apply {f : Π₀ i, α i} {i : ι} :
    orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorder
variable [forall i, Preorder (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (Π₀ i, α i)
  body: { (inferInstance : LE (DFinsupp α)) with
    le_refl := fun _ _ => le_rfl
    le_trans := fun _ _ _ hfg hgh i => (hfg i).trans (hgh i) }

中文:
实例 :
  签名: 预序 (Π₀ i, α i)
  定义体: { (inferInstance : LE (DFinsupp α)) with
    le_refl := fun _ _ => le_rfl
    le_trans := fun _ _ _ hfg hgh i => (hfg i).trans (hgh i) }

Depends on / 依赖: DFinsupp, le_refl, le_rfl, le_trans
-/
instance : Preorder (Π₀ i, α i) :=
  { (inferInstance : LE (DFinsupp α)) with
    le_refl := fun _ _ => le_rfl
    le_trans := fun _ _ _ hfg hgh i => (hfg i).trans (hgh i) }

/--
lemma `lt_def` / 引理 `lt_def`

English:
lemma lt_def
  statement: f < g ↔ f <= g ∧ exists i, f i < g i
  proof: Pi.lt_def

中文:
引理 lt_def
  结论: f < g ↔ f <= g ∧ 存在 i, f i < g i
  证明: Pi.lt_def

Depends on / 依赖: Pi.lt_def, lt_def
-/
lemma lt_def : f < g ↔ f <= g ∧ exists i, f i < g i := Pi.lt_def
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: ⇑f < g ↔ f < g
  proof: Iff.rfl

中文:
引理 coe_lt_coe
  结论: ⇑f < g ↔ f < g
  证明: Iff.rfl
-/
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl

/--
lemma `coe_mono` / 引理 `coe_mono`

English:
lemma coe_mono
  statement: Monotone ((⇑) : (Π₀ i, α i) -> forall i, α i)
  proof: fun _ _ => id

中文:
引理 coe_mono
  结论: 递增 ((⇑) : (Π₀ i, α i) -> 对任意 i, α i)
  证明: fun _ _ => id
-/
lemma coe_mono : Monotone ((⇑) : (Π₀ i, α i) -> forall i, α i) := fun _ _ => id

/--
lemma `coe_strictMono` / 引理 `coe_strictMono`

English:
lemma coe_strictMono
  statement: Monotone ((⇑) : (Π₀ i, α i) -> forall i, α i)
  proof: fun _ _ => id

中文:
引理 coe_strictMono
  结论: 递增 ((⇑) : (Π₀ i, α i) -> 对任意 i, α i)
  证明: fun _ _ => id
-/
lemma coe_strictMono : Monotone ((⇑) : (Π₀ i, α i) -> forall i, α i) := fun _ _ => id

variable [DecidableEq ι]

/--
lemma `single_le_single` / 引理 `single_le_single`

English:
lemma single_le_single
  statement: single i a <= single i b ↔ a <= b
  proof: Pi.single_le_single

中文:
引理 single_le_single
  结论: single i a <= single i b ↔ a <= b
  证明: Pi.single_le_single
-/
@[simp, gcongr] lemma single_le_single : single i a <= single i b ↔ a <= b :=
  Pi.single_le_single

/--
lemma `single_mono` / 引理 `single_mono`

English:
lemma single_mono
  statement: Monotone (single i : α i -> Π₀ i, α i)
  proof: fun _ _ => single_le_single.2

中文:
引理 single_mono
  结论: 递增 (single i : α i -> Π₀ i, α i)
  证明: fun _ _ => single_le_single.2

Depends on / 依赖: single_le_single
-/
lemma single_mono : Monotone (single i : α i -> Π₀ i, α i) := fun _ _ => single_le_single.2

/--
lemma `single_nonneg` / 引理 `single_nonneg`

English:
lemma single_nonneg
  statement: 0 <= single i a ↔ 0 <= a
  proof: Pi.single_nonneg

中文:
引理 single_nonneg
  结论: 0 <= single i a ↔ 0 <= a
  证明: Pi.single_nonneg
-/
@[simp] lemma single_nonneg : 0 <= single i a ↔ 0 <= a := Pi.single_nonneg
/--
lemma `single_nonpos` / 引理 `single_nonpos`

English:
lemma single_nonpos
  statement: single i a <= 0 ↔ a <= 0
  proof: Pi.single_nonpos

中文:
引理 single_nonpos
  结论: single i a <= 0 ↔ a <= 0
  证明: Pi.single_nonpos
-/
@[simp] lemma single_nonpos : single i a <= 0 ↔ a <= 0 := Pi.single_nonpos

end Preorder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, PartialOrder (α i)] : PartialOrder (Π₀ i, α i)
  body: { (inferInstance : Preorder (DFinsupp α)) with
    le_antisymm := fun _ _ hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

中文:
实例 [对任意
  签名: i, 偏序 (α i)] : 偏序 (Π₀ i, α i)
  定义体: { (inferInstance : Preorder (DFinsupp α)) with
    le_antisymm := fun _ _ hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

Depends on / 依赖: DFinsupp, Preorder, antisymm, le_antisymm
-/
instance [forall i, PartialOrder (α i)] : PartialOrder (Π₀ i, α i) :=
  { (inferInstance : Preorder (DFinsupp α)) with
    le_antisymm := fun _ _ hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i)
  body: { (inferInstance : PartialOrder (DFinsupp α)) with
    inf := zipWith (fun _ => (· ⊓ ·)) fun _ => inf_idem _
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _ _ _ hf hg i => le_inf (hf i) (hg i) }

@[simp, norm_cast]

中文:
实例 [对任意
  签名: i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i)
  定义体: { (inferInstance : PartialOrder (DFinsupp α)) with
    inf := zipWith (fun _ => (· ⊓ ·)) fun _ => inf_idem _
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _ _ _ hf hg i => le_inf (hf i) (hg i) }

@[simp, norm_cast]

Depends on / 依赖: DFinsupp, PartialOrder, inf_idem, inf_le_left, inf_le_right, le_inf, zipWith
-/
instance [forall i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    inf := zipWith (fun _ => (· ⊓ ·)) fun _ => inf_idem _
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _ _ _ hf hg i => le_inf (hf i) (hg i) }

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [forall i, SemilatticeInf (α i)] (f g : Π₀ i, α i)
  statement: f ⊓ g = ⇑f ⊓ g
  proof: rfl

中文:
引理 coe_inf
  条件: [对任意 i, SemilatticeInf (α i)] (f g : Π₀ i, α i)
  结论: f ⊓ g = ⇑f ⊓ g
  证明: rfl
-/
lemma coe_inf [forall i, SemilatticeInf (α i)] (f g : Π₀ i, α i) : f ⊓ g = ⇑f ⊓ g := rfl

/--
theorem `inf_apply` / 定理 `inf_apply`

English:
theorem inf_apply
  given: [forall i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι)
  statement: (f ⊓ g) i = f i ⊓ g i
  proof: zipWith_apply _ _ _ _ _

中文:
定理 inf_apply
  条件: [对任意 i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι)
  结论: (f ⊓ g) i = f i ⊓ g i
  证明: zipWith_apply _ _ _ _ _

Depends on / 依赖: zipWith_apply
-/
theorem inf_apply [forall i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  zipWith_apply _ _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i)
  body: { (inferInstance : PartialOrder (DFinsupp α)) with
    sup := zipWith (fun _ => (· ⊔ ·)) fun _ => sup_idem _
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ hf hg i => sup_le (hf i) (hg i) }

@[simp, norm_cast]

中文:
实例 [对任意
  签名: i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i)
  定义体: { (inferInstance : PartialOrder (DFinsupp α)) with
    sup := zipWith (fun _ => (· ⊔ ·)) fun _ => sup_idem _
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ hf hg i => sup_le (hf i) (hg i) }

@[simp, norm_cast]

Depends on / 依赖: DFinsupp, PartialOrder, le_sup_left, le_sup_right, sup_idem, sup_le, zipWith
-/
instance [forall i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    sup := zipWith (fun _ => (· ⊔ ·)) fun _ => sup_idem _
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ hf hg i => sup_le (hf i) (hg i) }

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [forall i, SemilatticeSup (α i)] (f g : Π₀ i, α i)
  statement: f ⊔ g = ⇑f ⊔ g
  proof: rfl

中文:
引理 coe_sup
  条件: [对任意 i, SemilatticeSup (α i)] (f g : Π₀ i, α i)
  结论: f ⊔ g = ⇑f ⊔ g
  证明: rfl
-/
lemma coe_sup [forall i, SemilatticeSup (α i)] (f g : Π₀ i, α i) : f ⊔ g = ⇑f ⊔ g := rfl

/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: [forall i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι)
  statement: (f ⊔ g) i = f i ⊔ g i
  proof: zipWith_apply _ _ _ _ _

中文:
定理 sup_apply
  条件: [对任意 i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι)
  结论: (f ⊔ g) i = f i ⊔ g i
  证明: zipWith_apply _ _ _ _ _

Depends on / 依赖: zipWith_apply
-/
theorem sup_apply [forall i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  zipWith_apply _ _ _ _ _

section Lattice
variable [forall i, Lattice (α i)] (f g : Π₀ i, α i)

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: : Lattice (Π₀ i, α i)
  body: { (inferInstance : SemilatticeInf (DFinsupp α)),
    (inferInstance : SemilatticeSup (DFinsupp α)) with }

中文:
实例 lattice
  签名: : 格 (Π₀ i, α i)
  定义体: { (inferInstance : SemilatticeInf (DFinsupp α)),
    (inferInstance : SemilatticeSup (DFinsupp α)) with }

Depends on / 依赖: DFinsupp, SemilatticeInf, SemilatticeSup
-/
instance lattice : Lattice (Π₀ i, α i) :=
  { (inferInstance : SemilatticeInf (DFinsupp α)),
    (inferInstance : SemilatticeSup (DFinsupp α)) with }

variable [DecidableEq ι] [forall (i) (x : α i), Decidable (x != 0)]

/--
theorem `support_inf_union_support_sup` / 定理 `support_inf_union_support_sup`

English:
theorem support_inf_union_support_sup
  statement: (f ⊓ g).support union (f ⊔ g).support = f.support union g.support
  proof: coe_injective compl_injective by ext; simp [inf_eq_and_sup_eq_iff]

中文:
定理 support_inf_union_support_sup
  结论: (f ⊓ g).support union (f ⊔ g).support = f.support union g.support
  证明: coe_injective compl_injective by ext; simp [inf_eq_and_sup_eq_iff]

Depends on / 依赖: coe_injective, compl_injective, inf_eq_and_sup_eq_iff
-/
theorem support_inf_union_support_sup : (f ⊓ g).support union (f ⊔ g).support = f.support union g.support :=
coe_injective compl_injective by ext; simp [inf_eq_and_sup_eq_iff]

/--
theorem `support_sup_union_support_inf` / 定理 `support_sup_union_support_inf`

English:
theorem support_sup_union_support_inf
  statement: (f ⊔ g).support union (f ⊓ g).support = f.support union g.support
  proof: (union_comm _ _).trans support_inf_union_support_sup _ _

中文:
定理 support_sup_union_support_inf
  结论: (f ⊔ g).support union (f ⊓ g).support = f.support union g.support
  证明: (union_comm _ _).trans support_inf_union_support_sup _ _

Depends on / 依赖: support_inf_union_support_sup, union_comm
-/
theorem support_sup_union_support_inf : (f ⊔ g).support union (f ⊓ g).support = f.support union g.support :=
(union_comm _ _).trans support_inf_union_support_sup _ _

end Lattice
end Zero

/-! ### Algebraic order structures -/

instance (α : ι -> Type*) [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedAddMonoid (α i)] : IsOrderedAddMonoid (Π₀ i, α i) :=
  { add_le_add_left := fun _ _ h c i => add_le_add_left (h i) (c i) }

instance (α : ι -> Type*) [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]
    [forall i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Π₀ i, α i) :=
  { le_of_add_le_add_left := fun _ _ _ H i => le_of_add_le_add_left (H i) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)] [forall i, AddLeftReflectLE (α i)] :
  body: le_of_add_le_add_left H i

中文:
实例 [对任意
  签名: i, 加法交换幺半群 (α i)] [对任意 i, 偏序 (α i)] [对任意 i, 加法LeftReflectLE (α i)] :
  定义体: le_of_add_le_add_left H i

Depends on / 依赖: le_of_add_le_add_left
-/
instance [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)] [forall i, AddLeftReflectLE (α i)] :
    AddLeftReflectLE (Π₀ i, α i) where
le_of_add_le_add_left H i := le_of_add_le_add_left H i

section Module
variable {α : Type*} {β : ι -> Type*} [Semiring α] [Preorder α] [forall i, AddCommMonoid (β i)]
  [forall i, Preorder (β i)] [forall i, Module α (β i)]

/--
Instance `instPosSMulMono` / 实例 `instPosSMulMono`

English:
instance instPosSMulMono
  signature: [forall i, PosSMulMono α (β i)]
  body: PosSMulMono.lift _ coe_le_coe coe_smul

中文:
实例 instPosSMulMono
  签名: [对任意 i, 正标量乘递增 α (β i)]
  定义体: PosSMulMono.lift _ coe_le_coe coe_smul

Depends on / 依赖: PosSMulMono, PosSMulMono.lift, coe_le_coe, coe_smul
-/
instance instPosSMulMono [forall i, PosSMulMono α (β i)] : PosSMulMono α (Π₀ i, β i) :=
  PosSMulMono.lift _ coe_le_coe coe_smul

/--
Instance `instSMulPosMono` / 实例 `instSMulPosMono`

English:
instance instSMulPosMono
  signature: [forall i, SMulPosMono α (β i)]
  body: SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosMono
  签名: [对任意 i, 标量乘正递增 α (β i)]
  定义体: SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosMono, SMulPosMono.lift, coe_le_coe, coe_smul, coe_zero
-/
instance instSMulPosMono [forall i, SMulPosMono α (β i)] : SMulPosMono α (Π₀ i, β i) :=
  SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

/--
Instance `instPosSMulReflectLE` / 实例 `instPosSMulReflectLE`

English:
instance instPosSMulReflectLE
  signature: [forall i, PosSMulReflectLE α (β i)]
  body: PosSMulReflectLE.lift _ coe_le_coe coe_smul

中文:
实例 instPosSMulReflectLE
  签名: [对任意 i, 正标量乘反映偏序 α (β i)]
  定义体: PosSMulReflectLE.lift _ coe_le_coe coe_smul

Depends on / 依赖: PosSMulReflectLE, PosSMulReflectLE.lift, coe_le_coe, coe_smul
-/
instance instPosSMulReflectLE [forall i, PosSMulReflectLE α (β i)] : PosSMulReflectLE α (Π₀ i, β i) :=
  PosSMulReflectLE.lift _ coe_le_coe coe_smul

/--
Instance `instSMulPosReflectLE` / 实例 `instSMulPosReflectLE`

English:
instance instSMulPosReflectLE
  signature: [forall i, SMulPosReflectLE α (β i)]
  body: SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosReflectLE
  签名: [对任意 i, 标量乘正反映偏序 α (β i)]
  定义体: SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosReflectLE, SMulPosReflectLE.lift, coe_le_coe, coe_smul, coe_zero
-/
instance instSMulPosReflectLE [forall i, SMulPosReflectLE α (β i)] : SMulPosReflectLE α (Π₀ i, β i) :=
  SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

end Module

section Module
variable {α : Type*} {β : ι -> Type*} [Semiring α] [PartialOrder α] [forall i, AddCommMonoid (β i)]
  [forall i, PartialOrder (β i)] [forall i, Module α (β i)]

/--
Instance `instPosSMulStrictMono` / 实例 `instPosSMulStrictMono`

English:
instance instPosSMulStrictMono
  signature: [forall i, PosSMulStrictMono α (β i)]
  body: PosSMulStrictMono.lift _ coe_le_coe coe_smul

中文:
实例 instPosSMulStrictMono
  签名: [对任意 i, 正标量乘严格递增 α (β i)]
  定义体: PosSMulStrictMono.lift _ coe_le_coe coe_smul

Depends on / 依赖: PosSMulStrictMono, PosSMulStrictMono.lift, coe_le_coe, coe_smul
-/
instance instPosSMulStrictMono [forall i, PosSMulStrictMono α (β i)] : PosSMulStrictMono α (Π₀ i, β i) :=
  PosSMulStrictMono.lift _ coe_le_coe coe_smul

/--
Instance `instSMulPosStrictMono` / 实例 `instSMulPosStrictMono`

English:
instance instSMulPosStrictMono
  signature: [forall i, SMulPosStrictMono α (β i)]
  body: SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosStrictMono
  签名: [对任意 i, 标量乘正严格递增 α (β i)]
  定义体: SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: SMulPosStrictMono, SMulPosStrictMono.lift, _eq_some_iff_getElem, coe_le_coe, coe_smul, coe_zero, i.isLt, length_ofFn
-/
instance instSMulPosStrictMono [forall i, SMulPosStrictMono α (β i)] : SMulPosStrictMono α (Π₀ i, β i) :=
  SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

-- Note: There is no interesting instance for `PosSMulReflectLT α (Π₀ i, β i)` that's not already
-- implied by the other instances

/--
Instance `instSMulPosReflectLT` / 实例 `instSMulPosReflectLT`

English:
instance instSMulPosReflectLT
  signature: [forall i, SMulPosReflectLT α (β i)]
  body: SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

中文:
实例 instSMulPosReflectLT
  签名: [对任意 i, 标量乘正反映严格偏序 α (β i)]
  定义体: SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

Depends on / 依赖: Bool.not_eq_true, SMulPosReflectLT, SMulPosReflectLT.lift, _ofFn_eq_some, coe_le_coe, coe_smul, coe_zero, eq_iff, exists_eq_left, h.eq_iff, not_eq_true
-/
instance instSMulPosReflectLT [forall i, SMulPosReflectLT α (β i)] : SMulPosReflectLT α (Π₀ i, β i) :=
  SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

end Module

section PartialOrder

variable (α) [forall i, AddCommMonoid (α i)] [forall i, PartialOrder (α i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IsBotZeroClass (α i)] : OrderBot (Π₀ i, α i) where
  body: 0
  bot_le := by simp [le_def]

中文:
实例 [对任意
  签名: i, 是BotZero类 (α i)] : 有底序 (Π₀ i, α i) where
  定义体: 0
  bot_le := by simp [le_def]
-/
instance [forall i, IsBotZeroClass (α i)] : OrderBot (Π₀ i, α i) where
  bot := 0
  bot_le := by simp [le_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IsBotZeroClass (α i)] : IsBotZeroClass (Π₀ i, α i) where
  body: isBot_bot

中文:
实例 [对任意
  签名: i, 是BotZero类 (α i)] : 是BotZero类 (Π₀ i, α i) where
  定义体: isBot_bot

Depends on / 依赖: isBot_bot
-/
instance [forall i, IsBotZeroClass (α i)] : IsBotZeroClass (Π₀ i, α i) where
  isBot_zero := isBot_bot

variable {α}

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  given: [forall i, IsBotZeroClass (α i)]
  statement: (⊥ : Π₀ i, α i) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  条件: [对任意 i, 是BotZero类 (α i)]
  结论: (⊥ : Π₀ i, α i) = 0
  证明: rfl
-/
protected theorem bot_eq_zero [forall i, IsBotZeroClass (α i)] : (⊥ : Π₀ i, α i) = 0 :=
  rfl

variable [forall i, CanonicallyOrderedAdd (α i)]

@[simp]
/--
theorem `add_eq_zero_iff` / 定理 `add_eq_zero_iff`

English:
theorem add_eq_zero_iff
  given: (f g : Π₀ i, α i)
  statement: f + g = 0 ↔ f = 0 ∧ g = 0
  proof: by
  simp [DFunLike.ext_iff, forall_and]

中文:
定理 add_eq_zero_iff
  条件: (f g : Π₀ i, α i)
  结论: f + g = 0 ↔ f = 0 ∧ g = 0
  证明: by
  simp [DFunLike.ext_iff, forall_and]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, forall_and
-/
theorem add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [DFunLike.ext_iff, forall_and]

section LE

variable [DecidableEq ι]

section

variable [forall (i) (x : α i), Decidable (x != 0)] {f g : Π₀ i, α i} {s : Finset ι}

/--
theorem `le_iff'` / 定理 `le_iff'`

English:
theorem le_iff'
  given: (hf : f.support subseteq s)
  statement: f <= g ↔ forall i in s, f i <= g i
  proof: ⟨fun h s _ => h s, fun h s =>
    if H : s in f.support then h s (hf H) else (notMem_support_iff.1 H).symm ▸ zero_le⟩

中文:
定理 le_iff'
  条件: (hf : f.support subseteq s)
  结论: f <= g ↔ 对任意 i in s, f i <= g i
  证明: ⟨fun h s _ => h s, fun h s =>
    if H : s in f.support then h s (hf H) else (notMem_support_iff.1 H).symm ▸ zero_le⟩

Depends on / 依赖: f.support, notMem_support_iff, support, zero_le
-/
theorem le_iff' (hf : f.support subseteq s) : f <= g ↔ forall i in s, f i <= g i :=
  ⟨fun h s _ => h s, fun h s =>
    if H : s in f.support then h s (hf H) else (notMem_support_iff.1 H).symm ▸ zero_le⟩

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  statement: f <= g ↔ forall i in f.support, f i <= g i
  proof: le_iff' Subset.refl _

中文:
定理 le_iff
  结论: f <= g ↔ 对任意 i in f.support, f i <= g i
  证明: le_iff' Subset.refl _

Depends on / 依赖: Subset, Subset.refl, le_iff
-/
theorem le_iff : f <= g ↔ forall i in f.support, f i <= g i :=
le_iff' Subset.refl _

/--
lemma `support_monotone` / 引理 `support_monotone`

English:
lemma support_monotone
  statement: Monotone (support (ι := ι) (β := α))
  proof: fun f g h a ha => by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

中文:
引理 support_monotone
  结论: 递增 (support (ι := ι) (β := α))
  证明: fun f g h a ha => by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)
-/
lemma support_monotone : Monotone (support (ι := ι) (β := α)) :=
  fun f g h a ha => by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

/--
lemma `support_mono` / 引理 `support_mono`

English:
lemma support_mono
  given: (hfg : f <= g)
  statement: f.support subseteq g.support
  proof: support_monotone hfg

中文:
引理 support_mono
  条件: (hfg : f <= g)
  结论: f.support subseteq g.support
  证明: support_monotone hfg

Depends on / 依赖: support_monotone
-/
lemma support_mono (hfg : f <= g) : f.support subseteq g.support := support_monotone hfg

variable (α) in
/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [forall i, DecidableLE (α i)]
  body: fun _ _ => decidable_of_iff _ le_iff.symm

中文:
实例 decidableLE
  签名: [对任意 i, DecidableLE (α i)]
  定义体: fun _ _ => decidable_of_iff _ le_iff.symm

Depends on / 依赖: decidable_of_iff, le_iff, le_iff.symm
-/
instance decidableLE [forall i, DecidableLE (α i)] : DecidableLE (Π₀ i, α i) :=
  fun _ _ => decidable_of_iff _ le_iff.symm

end

@[simp]
/--
theorem `single_le_iff` / 定理 `single_le_iff`

English:
theorem single_le_iff
  given: {f : Π₀ i, α i} {i : ι} {a : α i}
  proof: by
classical exact (le_iff' support_single_subset).trans by simp

中文:
定理 single_le_iff
  条件: {f : Π₀ i, α i} {i : ι} {a : α i}
  证明: by
classical exact (le_iff' support_single_subset).trans by simp

Depends on / 依赖: classical, le_iff, support_single_subset
-/
theorem single_le_iff {f : Π₀ i, α i} {i : ι} {a : α i} :
    single i a <= f ↔ a <= f i := by
classical exact (le_iff' support_single_subset).trans by simp

end LE

variable (α) [forall i, Sub (α i)] [forall i, OrderedSub (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/--
Instance `tsub` / 实例 `tsub`

English:
instance tsub
  signature: : Sub (Π₀ i, α i)
  body: ⟨zipWith (fun _ m n => m - n) fun _ => tsub_self 0⟩

中文:
实例 tsub
  签名: : 减法 (Π₀ i, α i)
  定义体: ⟨zipWith (fun _ m n => m - n) fun _ => tsub_self 0⟩

Depends on / 依赖: tsub_self, zipWith
-/
instance tsub : Sub (Π₀ i, α i) :=
  ⟨zipWith (fun _ m n => m - n) fun _ => tsub_self 0⟩

variable {α}

/--
theorem `tsub_apply` / 定理 `tsub_apply`

English:
theorem tsub_apply
  given: (f g : Π₀ i, α i) (i : ι)
  statement: (f - g) i = f i - g i
  proof: zipWith_apply _ _ _ _ _

@[simp, norm_cast]

中文:
定理 tsub_apply
  条件: (f g : Π₀ i, α i) (i : ι)
  结论: (f - g) i = f i - g i
  证明: zipWith_apply _ _ _ _ _

@[simp, norm_cast]

Depends on / 依赖: zipWith_apply
-/
theorem tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i :=
  zipWith_apply _ _ _ _ _

@[simp, norm_cast]
/--
theorem `coe_tsub` / 定理 `coe_tsub`

English:
theorem coe_tsub
  given: (f g : Π₀ i, α i)
  statement: ⇑(f - g) = f - g
  proof: by
  ext i
  exact tsub_apply f g i

中文:
定理 coe_tsub
  条件: (f g : Π₀ i, α i)
  结论: ⇑(f - g) = f - g
  证明: by
  ext i
  exact tsub_apply f g i

Depends on / 依赖: tsub_apply
-/
theorem coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by
  ext i
  exact tsub_apply f g i

variable (α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderedSub (Π₀ i, α i)
  body: ⟨fun _ _ _ => forall_congr' fun _ => tsub_le_iff_right⟩

中文:
实例 :
  签名: OrderedSub (Π₀ i, α i)
  定义体: ⟨fun _ _ _ => forall_congr' fun _ => tsub_le_iff_right⟩

Depends on / 依赖: forall_congr, tsub_le_iff_right
-/
instance : OrderedSub (Π₀ i, α i) :=
  ⟨fun _ _ _ => forall_congr' fun _ => tsub_le_iff_right⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddLeftMono (α i)] : CanonicallyOrderedAdd (Π₀ i, α i) where
  body: by
    intro f g h
    exists g - f
    ext i
    exact (add_tsub_cancel_of_le <| h i).symm
  le_add_self := fun _ _ _ => le_add_self
  le_self_add := fun _ _ _ => le_self_add

中文:
实例 [对任意
  签名: i, AddLeftMono (α i)] : 典范有序加法 (Π₀ i, α i) where
  定义体: by
    intro f g h
    exists g - f
    ext i
    exact (add_tsub_cancel_of_le <| h i).symm
  le_add_self := fun _ _ _ => le_add_self
  le_self_add := fun _ _ _ => le_self_add

Depends on / 依赖: add_tsub_cancel_of_le, le_add_self, le_self_add
-/
instance [forall i, AddLeftMono (α i)] : CanonicallyOrderedAdd (Π₀ i, α i) where
  exists_add_of_le := by
    intro f g h
    exists g - f
    ext i
    exact (add_tsub_cancel_of_le <| h i).symm
  le_add_self := fun _ _ _ => le_add_self
  le_self_add := fun _ _ _ => le_self_add

variable {α} [DecidableEq ι]

@[simp]
/--
theorem `single_tsub` / 定理 `single_tsub`

English:
theorem single_tsub
  statement: single i (a - b) = single i a - single i b
  proof: by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

中文:
定理 single_tsub
  结论: single i (a - b) = single i a - single i b
  证明: by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

Depends on / 依赖: eq_or_ne, single_eq_of_ne, single_eq_same, tsub_apply, tsub_self
-/
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

variable [forall (i) (x : α i), Decidable (x != 0)]

/--
theorem `support_tsub` / 定理 `support_tsub`

English:
theorem support_tsub
  statement: (f - g).support subseteq f.support
  proof: by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

中文:
定理 support_tsub
  结论: (f - g).support subseteq f.support
  证明: by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

Depends on / 依赖: Pi.sub_apply, coe_tsub, contextual, imp_true_iff, mem_support_iff, not_imp_not, sub_apply, subset_iff, tsub_eq_zero_iff_le, zero_le
-/
theorem support_tsub : (f - g).support subseteq f.support := by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

/--
theorem `subset_support_tsub` / 定理 `subset_support_tsub`

English:
theorem subset_support_tsub
  statement: f.support \ g.support subseteq (f - g).support
  proof: by
  simp +contextual [subset_iff]

中文:
定理 subset_support_tsub
  结论: f.support \ g.support subseteq (f - g).support
  证明: by
  simp +contextual [subset_iff]

Depends on / 依赖: contextual, subset_iff
-/
theorem subset_support_tsub : f.support \ g.support subseteq (f - g).support := by
  simp +contextual [subset_iff]

end PartialOrder

section LinearOrder
variable [forall i, AddCommMonoid (α i)] [forall i, LinearOrder (α i)] [forall i, IsBotZeroClass (α i)]
  [DecidableEq ι] {f g : Π₀ i, α i}

@[simp]
/--
theorem `support_inf` / 定理 `support_inf`

English:
theorem support_inf
  statement: (f ⊓ g).support = f.support inter g.support
  proof: by
  ext
  simp

@[simp]

中文:
定理 support_inf
  结论: (f ⊓ g).support = f.support inter g.support
  证明: by
  ext
  simp

@[simp]
-/
theorem support_inf : (f ⊓ g).support = f.support inter g.support := by
  ext
  simp

@[simp]
/--
theorem `support_sup` / 定理 `support_sup`

English:
theorem support_sup
  statement: (f ⊔ g).support = f.support union g.support
  proof: by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  simp [disjoint_iff, bot_eq_zero, ← DFinsupp.support_eq_empty]

中文:
定理 support_sup
  结论: (f ⊔ g).support = f.support union g.support
  证明: by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  simp [disjoint_iff, bot_eq_zero, ← DFinsupp.support_eq_empty]

Depends on / 依赖: imp_iff_not_or
-/
theorem support_sup : (f ⊔ g).support = f.support union g.support := by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  simp [disjoint_iff, bot_eq_zero, ← DFinsupp.support_eq_empty]

end LinearOrder

end DFinsupp
