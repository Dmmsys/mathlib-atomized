/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Declarations about scalar multiplication on `Finsupp`

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/

@[expose] public section


noncomputable section

open Finset Function

variable {α β M N G R : Type*}

namespace Finsupp

section

variable [Zero M] [MonoidWithZero R] [MulActionWithZero R M]

@[simp]
/--
theorem `single_smul` / 定理 `single_smul`

English:
theorem single_smul
  given: (a b : α) (f : α -> M) (r : R)
  statement: single a r b • f a = single a (r • f b) b
  proof: by
  by_cases h : a = b <;> simp [h]

中文:
定理 single_smul
  条件: (a b : α) (f : α -> M) (r : R)
  结论: single a r b • f a = single a (r • f b) b
  证明: by
  by_cases h : a = b <;> simp [h]
-/
theorem single_smul (a b : α) (f : α -> M) (r : R) : single a r b • f a = single a (r • f b) b := by
  by_cases h : a = b <;> simp [h]

end

section

variable [Monoid G] [MulAction G α] [AddCommMonoid M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
@[instance_reducible]
/--
Definition of `comapSMul` / `comapSMul` 的定义

English:
definition comapSMul
  signature: : SMul G (α ->₀ M) where smul g
  body: mapDomain (g • ·)

中文:
定义 comapSMul
  签名: : 标量乘法 G (α ->₀ M) where smul g
  定义体: mapDomain (g • ·)

Depends on / 依赖: mapDomain
-/
def comapSMul : SMul G (α ->₀ M) where smul g := mapDomain (g • ·)

attribute [local instance] comapSMul

/--
theorem `comapSMul_def` / 定理 `comapSMul_def`

English:
theorem comapSMul_def
  given: (g : G) (f : α ->₀ M)
  statement: g • f = mapDomain (g • ·) f
  proof: rfl

@[simp]

中文:
定理 comapSMul_def
  条件: (g : G) (f : α ->₀ M)
  结论: g • f = mapDomain (g • ·) f
  证明: rfl

@[simp]
-/
theorem comapSMul_def (g : G) (f : α ->₀ M) : g • f = mapDomain (g • ·) f :=
  rfl

@[simp]
/--
theorem `comapSMul_single` / 定理 `comapSMul_single`

English:
theorem comapSMul_single
  given: (g : G) (a : α) (b : M)
  statement: g • single a b = single (g • a) b
  proof: mapDomain_single

中文:
定理 comapSMul_single
  条件: (g : G) (a : α) (b : M)
  结论: g • single a b = single (g • a) b
  证明: mapDomain_single

Depends on / 依赖: mapDomain_single
-/
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single

/-- `Finsupp.comapSMul` is multiplicative -/
@[instance_reducible]
/--
Definition of `comapMulAction` / `comapMulAction` 的定义

English:
definition comapMulAction
  signature: : MulAction G (α ->₀ M) where
  body: by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def]; rw [comapSMul_def]; rw [comapSMul_def]; rw [← comp_smul_left]; rw [mapDomain_comp]

中文:
定义 comapMulAction
  签名: : 乘法作用 G (α ->₀ M) where
  定义体: by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def]; rw [comapSMul_def]; rw [comapSMul_def]; rw [← comp_smul_left]; rw [mapDomain_comp]

Depends on / 依赖: comapSMul_def, comp_smul_left, mapDomain_comp, mapDomain_id, mul_smul, one_smul_eq_id
-/
def comapMulAction : MulAction G (α ->₀ M) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def]; rw [comapSMul_def]; rw [comapSMul_def]; rw [← comp_smul_left]; rw [mapDomain_comp]

attribute [local instance] comapMulAction

/-- `Finsupp.comapSMul` is distributive -/
@[instance_reducible]
/--
Definition of `comapDistribMulAction` / `comapDistribMulAction` 的定义

English:
definition comapDistribMulAction
  signature: : DistribMulAction G (α ->₀ M) where
  body: by
    ext a
    simp only [comapSMul_def]
    simp
  smul_add g f f' := by
    ext
    simp only [comapSMul_def]
    simp [mapDomain_add]

中文:
定义 comapDistribMulAction
  签名: : 分配乘法作用 G (α ->₀ M) where
  定义体: by
    ext a
    simp only [comapSMul_def]
    simp
  smul_add g f f' := by
    ext
    simp only [comapSMul_def]
    simp [mapDomain_add]

Depends on / 依赖: comapSMul_def, mapDomain_add, smul_add
-/
def comapDistribMulAction : DistribMulAction G (α ->₀ M) where
  smul_zero g := by
    ext a
    simp only [comapSMul_def]
    simp
  smul_add g f f' := by
    ext
    simp only [comapSMul_def]
    simp [mapDomain_add]

end

section

variable [Group G] [MulAction G α] [AddCommMonoid M]

attribute [local instance] comapSMul comapMulAction comapDistribMulAction

/-- When `G` is a group, `Finsupp.comapSMul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp]
/--
theorem `comapSMul_apply` / 定理 `comapSMul_apply`

English:
theorem comapSMul_apply
  given: (g : G) (f : α ->₀ M) (a : α)
  statement: (g • f) a = f (g⁻¹ • a)
  proof: by
  conv_lhs => rw [← smul_inv_smul g a]
  exact mapDomain_apply (MulAction.injective g) _ (g⁻¹ • a)

中文:
定理 comapSMul_apply
  条件: (g : G) (f : α ->₀ M) (a : α)
  结论: (g • f) a = f (g⁻¹ • a)
  证明: by
  conv_lhs => rw [← smul_inv_smul g a]
  exact mapDomain_apply (MulAction.injective g) _ (g⁻¹ • a)

Depends on / 依赖: MulAction, MulAction.injective, conv_lhs, injective, mapDomain_apply, smul_inv_smul
-/
theorem comapSMul_apply (g : G) (f : α ->₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) := by
  conv_lhs => rw [← smul_inv_smul g a]
  exact mapDomain_apply (MulAction.injective g) _ (g⁻¹ • a)

end

section


/--
theorem `_root_.IsSMulRegular.finsupp` / 定理 `_root_.IsSMulRegular.finsupp`

English:
theorem _root_.IsSMulRegular.finsupp
  statement: [Zero M] [SMulZeroClass R M] {k : R}
  proof: fun _ _ h => ext fun i => hk (DFunLike.congr_fun h i)

中文:
定理 _root_.IsSMulRegular.finsupp
  结论: [零 M] [SMulZero类 R M] {k : R}
  证明: fun _ _ h => ext fun i => hk (DFunLike.congr_fun h i)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem _root_.IsSMulRegular.finsupp [Zero M] [SMulZeroClass R M] {k : R}
    (hk : IsSMulRegular M k) : IsSMulRegular (α ->₀ M) k :=
  fun _ _ h => ext fun i => hk (DFunLike.congr_fun h i)

/--
Instance `faithfulSMul` / 实例 `faithfulSMul`

English:
instance faithfulSMul
  signature: [Nonempty α] [Zero M] [SMulZeroClass R M] [FaithfulSMul R M]
  body: let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by simpa using DFunLike.congr_fun (h (single a m)) a

中文:
实例 faithfulSMul
  签名: [非空 α] [零 M] [SMulZero类 R M] [忠实标量乘法 R M]
  定义体: let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by simpa using DFunLike.congr_fun (h (single a m)) a

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Nonempty, congr_fun, eq_of_smul_eq_smul, single
-/
instance faithfulSMul [Nonempty α] [Zero M] [SMulZeroClass R M] [FaithfulSMul R M] :
    FaithfulSMul R (α ->₀ M) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by simpa using DFunLike.congr_fun (h (single a m)) a

variable (α M)

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  body: { Finsupp.distribSMul _ _ with
    one_smul := fun x => ext fun y => one_smul R (x y)
    mul_smul := fun r s x => ext fun y => mul_smul r s (x y) }

中文:
实例 distribMulAction
  签名: [幺半群 R] [加法幺半群 M] [分配乘法作用 R M]
  定义体: { Finsupp.distribSMul _ _ with
    one_smul := fun x => ext fun y => one_smul R (x y)
    mul_smul := fun r s x => ext fun y => mul_smul r s (x y) }

Depends on / 依赖: Finsupp, Finsupp.distribSMul, distribSMul, mul_smul, one_smul
-/
instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (α ->₀ M) :=
  { Finsupp.distribSMul _ _ with
    one_smul := fun x => ext fun y => one_smul R (x y)
    mul_smul := fun r s x => ext fun y => mul_smul r s (x y) }

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: { toDistribMulAction := Finsupp.distribMulAction α M
    zero_smul := fun _ => ext fun _ => zero_smul _ _
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }

中文:
实例 module
  签名: [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { toDistribMulAction := Finsupp.distribMulAction α M
    zero_smul := fun _ => ext fun _ => zero_smul _ _
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }

Depends on / 依赖: Finsupp, Finsupp.distribMulAction, add_smul, distribMulAction, toDistribMulAction, zero_smul
-/
instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α ->₀ M) :=
  { toDistribMulAction := Finsupp.distribMulAction α M
    zero_smul := fun _ => ext fun _ => zero_smul _ _
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }

variable {α M}

@[simp]
/--
theorem `support_smul_eq` / 定理 `support_smul_eq`

English:
theorem support_smul_eq
  statement: [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
  proof: Finset.ext fun a => by simp [Finsupp.smul_apply, hb]

中文:
定理 support_smul_eq
  结论: [半环 R] [是整环 R] [加法交换幺半群 M] [模 R M]
  证明: Finset.ext fun a => by simp [Finsupp.smul_apply, hb]

Depends on / 依赖: Finset, Finset.ext, Finsupp, Finsupp.smul_apply, smul_apply
-/
theorem support_smul_eq [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] {b : R} (hb : b != 0) {g : α ->₀ M} : (b • g).support = g.support :=
  Finset.ext fun a => by simp [Finsupp.smul_apply, hb]

section

variable {p : α -> Prop} [DecidablePred p]

@[simp]
/--
theorem `filter_smul` / 定理 `filter_smul`

English:
theorem filter_smul
  given: [Zero M] [SMulZeroClass R M] {b : R} {v : α ->₀ M}
  proof: DFunLike.coe_injective by
    simp only [filter_eq_indicator, coe_smul]
    exact Set.indicator_const_smul { x | p x } b v

中文:
定理 filter_smul
  条件: [零 M] [SMulZero类 R M] {b : R} {v : α ->₀ M}
  证明: DFunLike.coe_injective by
    simp only [filter_eq_indicator, coe_smul]
    exact Set.indicator_const_smul { x | p x } b v

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Set.indicator_const_smul, coe_injective, coe_smul, filter_eq_indicator, indicator_const_smul
-/
theorem filter_smul [Zero M] [SMulZeroClass R M] {b : R} {v : α ->₀ M} :
    (b • v).filter p = b • v.filter p :=
DFunLike.coe_injective by
    simp only [filter_eq_indicator, coe_smul]
    exact Set.indicator_const_smul { x | p x } b v

end

/--
theorem `mapDomain_smul` / 定理 `mapDomain_smul`

English:
theorem mapDomain_smul
  statement: [AddCommMonoid M] [DistribSMul R M] {f : α -> β} (b : R)
  proof: mapDomain_mapRange _ _ _ _ (smul_add b)

中文:
定理 mapDomain_smul
  结论: [加法交换幺半群 M] [分配标量乘法 R M] {f : α -> β} (b : R)
  证明: mapDomain_mapRange _ _ _ _ (smul_add b)

Depends on / 依赖: mapDomain_mapRange, smul_add
-/
theorem mapDomain_smul [AddCommMonoid M] [DistribSMul R M] {f : α -> β} (b : R)
    (v : α ->₀ M) : mapDomain f (b • v) = b • mapDomain f v :=
  mapDomain_mapRange _ _ _ _ (smul_add b)

/--
theorem `smul_single'` / 定理 `smul_single'`

English:
theorem smul_single'
  given: {_ : Semiring R} (c : R) (a : α) (b : R)
  proof: by simp

中文:
定理 smul_single'
  条件: {_ : 半环 R} (c : R) (a : α) (b : R)
  证明: by simp
-/
theorem smul_single' {_ : Semiring R} (c : R) (a : α) (b : R) :
    c • Finsupp.single a b = Finsupp.single a (c * b) := by simp

/--
theorem `smul_single_one` / 定理 `smul_single_one`

English:
theorem smul_single_one
  given: [MulZeroOneClass R] (a : α) (b : R)
  proof: by
  rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 smul_single_one
  条件: [乘零幺类 R] (a : α) (b : R)
  证明: by
  rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: mul_one, smul_eq_mul, smul_single
-/
theorem smul_single_one [MulZeroOneClass R] (a : α) (b : R) :
    b • single a (1 : R) = single a b := by
  rw [smul_single]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `comapDomain_smul` / 定理 `comapDomain_smul`

English:
theorem comapDomain_smul
  statement: [Zero M] [SMulZeroClass R M] {f : α -> β} (r : R)
  proof: by
  ext
  rfl

中文:
定理 comapDomain_smul
  结论: [零 M] [SMulZero类 R M] {f : α -> β} (r : R)
  证明: by
  ext
  rfl

Depends on / 依赖: Finset, Finset.coe_subset.mpr, Set.preimage_mono, coe_subset, comapDomain, hfv.mono, preimage_mono, support_smul
-/
theorem comapDomain_smul [Zero M] [SMulZeroClass R M] {f : α -> β} (r : R)
    (v : β ->₀ M) (hfv : Set.InjOn f (f ⁻¹' ↑v.support))
    (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v).support) :=
hfv.mono Set.preimage_mono Finset.coe_subset.mpr support_smul) :
    comapDomain f (r • v) hfrv = r • comapDomain f v hfv := by
  ext
  rfl

/--
theorem `comapDomain_smul_of_injective` / 定理 `comapDomain_smul_of_injective`

English:
theorem comapDomain_smul_of_injective
  statement: [Zero M] [SMulZeroClass R M] {f : α -> β}
  proof: comapDomain_smul _ _ _ _

中文:
定理 comapDomain_smul_of_injective
  结论: [零 M] [SMulZero类 R M] {f : α -> β}
  证明: comapDomain_smul _ _ _ _

Depends on / 依赖: comapDomain_smul
-/
theorem comapDomain_smul_of_injective [Zero M] [SMulZeroClass R M] {f : α -> β}
    (hf : Function.Injective f) (r : R) (v : β ->₀ M) :
    comapDomain f (r • v) hf.injOn = r • comapDomain f v hf.injOn :=
  comapDomain_smul _ _ _ _

end

/--
theorem `sum_smul_index` / 定理 `sum_smul_index`

English:
theorem sum_smul_index
  statement: [MulZeroClass R] [AddCommMonoid M] {g : α ->₀ R} {b : R} {h : α -> R -> M}
  proof: Finsupp.sum_mapRange_index h0

中文:
定理 sum_smul_index
  结论: [乘零类 R] [加法交换幺半群 M] {g : α ->₀ R} {b : R} {h : α -> R -> M}
  证明: Finsupp.sum_mapRange_index h0

Depends on / 依赖: Finsupp, Finsupp.sum_mapRange_index, sum_mapRange_index
-/
theorem sum_smul_index [MulZeroClass R] [AddCommMonoid M] {g : α ->₀ R} {b : R} {h : α -> R -> M}
    (h0 : forall i, h i 0 = 0) : (b • g).sum h = g.sum fun i a => h i (b * a) :=
  Finsupp.sum_mapRange_index h0

/--
theorem `sum_smul_index'` / 定理 `sum_smul_index'`

English:
theorem sum_smul_index'
  statement: [Zero M] [SMulZeroClass R M] [AddCommMonoid N] {g : α ->₀ M} {b : R}
  proof: Finsupp.sum_mapRange_index h0

中文:
定理 sum_smul_index'
  结论: [零 M] [SMulZero类 R M] [加法交换幺半群 N] {g : α ->₀ M} {b : R}
  证明: Finsupp.sum_mapRange_index h0

Depends on / 依赖: Finsupp, Finsupp.sum_mapRange_index, sum_mapRange_index
-/
theorem sum_smul_index' [Zero M] [SMulZeroClass R M] [AddCommMonoid N] {g : α ->₀ M} {b : R}
    {h : α -> M -> N} (h0 : forall i, h i 0 = 0) : (b • g).sum h = g.sum fun i c => h i (b • c) :=
  Finsupp.sum_mapRange_index h0

/--
theorem `sum_smul_index_addMonoidHom` / 定理 `sum_smul_index_addMonoidHom`

English:
theorem sum_smul_index_addMonoidHom
  statement: [AddZeroClass M] [AddCommMonoid N] [SMulZeroClass R M]
  proof: sum_mapRange_index fun i => (h i).map_zero

中文:
定理 sum_smul_index_addMonoidHom
  结论: [加法零类 M] [加法交换幺半群 N] [SMulZero类 R M]
  证明: sum_mapRange_index fun i => (h i).map_zero

Depends on / 依赖: map_zero, sum_mapRange_index
-/
theorem sum_smul_index_addMonoidHom [AddZeroClass M] [AddCommMonoid N] [SMulZeroClass R M]
    {g : α ->₀ M} {b : R} {h : α -> M ->+ N} :
    ((b • g).sum fun a => h a) = g.sum fun i c => h i (b • c) :=
  sum_mapRange_index fun i => (h i).map_zero

/--
Instance `moduleIsTorsionFree` / 实例 `moduleIsTorsionFree`

English:
instance moduleIsTorsionFree
  signature: [Semiring R] [AddCommMonoid M] [Module R M] {ι : Type*}
  body: by ext i; exact hr.isSMulRegular congr($hfg i)

中文:
实例 moduleIsTorsionFree
  签名: [半环 R] [加法交换幺半群 M] [模 R M] {ι : 类型}
  定义体: by ext i; exact hr.isSMulRegular congr($hfg i)

Depends on / 依赖: hr.isSMulRegular, isSMulRegular
-/
instance moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [Module R M] {ι : Type*}
    [Module.IsTorsionFree R M] : Module.IsTorsionFree R (ι ->₀ M) where
  isSMulRegular r hr f g hfg := by ext i; exact hr.isSMulRegular congr($hfg i)

section DistribMulActionSemiHom
variable [Monoid R] [AddMonoid M] [AddMonoid N] [DistribMulAction R M] [DistribMulAction R N]

/--
Definition of `DistribMulActionHom.single` / `DistribMulActionHom.single` 的定义

English:
definition DistribMulActionHom.single
  signature: (a : α)
  body: { singleAddHom a with
    map_smul' := fun k m => by simp }

中文:
定义 分配乘法作用态射.single
  签名: (a : α)
  定义体: { singleAddHom a with
    map_smul' := fun k m => by simp }
-/
def DistribMulActionHom.single (a : α) : M ->+[R] α ->₀ M :=
  { singleAddHom a with
    map_smul' := fun k m => by simp }

/--
theorem `distribMulActionHom_ext` / 定理 `distribMulActionHom_ext`

English:
theorem distribMulActionHom_ext
  statement: {f g : (α ->₀ M) ->+[R] N}
  proof: DistribMulActionHom.toAddMonoidHom_injective addHom_ext h

中文:
定理 distribMulActionHom_ext
  结论: {f g : (α ->₀ M) ->+[R] N}
  证明: DistribMulActionHom.toAddMonoidHom_injective addHom_ext h

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.toAddMonoidHom_injective, addHom_ext, toAddMonoidHom_injective
-/
theorem distribMulActionHom_ext {f g : (α ->₀ M) ->+[R] N}
    (h : forall (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
DistribMulActionHom.toAddMonoidHom_injective addHom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `distribMulActionHom_ext'` / 定理 `distribMulActionHom_ext'`

English:
theorem distribMulActionHom_ext'
  statement: {f g : (α ->₀ M) ->+[R] N}
  proof: distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

中文:
定理 distribMulActionHom_ext'
  结论: {f g : (α ->₀ M) ->+[R] N}
  证明: distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.congr_fun, congr_fun, distribMulActionHom_ext
-/
theorem distribMulActionHom_ext' {f g : (α ->₀ M) ->+[R] N}
    (h : forall a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

end DistribMulActionSemiHom

end Finsupp
