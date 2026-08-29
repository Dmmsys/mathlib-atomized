/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Continuous multilinear maps

We define continuous multilinear maps as maps from `(i : ι) → M₁ i` to `M₂` which are multilinear
and continuous, by extending the space of multilinear maps with a continuity assumption.
Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type, and all these
spaces are also topological spaces.

## Main definitions

* `ContinuousMultilinearMap R M₁ M₂` is the space of continuous multilinear maps from
  `(i : ι) → M₁ i` to `M₂`. We show that it is an `R`-module.

## Implementation notes

We mostly follow the API of multilinear maps.

## Notation

We introduce the notation `M [×n]→L[R] M'` for the space of continuous `n`-multilinear maps from
`M^n` to `M'`. This is a particular case of the general notion (where we allow varying dependent
types as the arguments of our continuous multilinear maps), but arguably the most important one,
especially when defining iterated derivatives.
-/

@[expose] public section


open Function Fin Set

universe u v w w₁ w₁' w₂ w₃ w₄

variable {R : Type u} {ι : Type v} {n : Nat} {M : Fin n.succ -> Type w} {M₁ : ι -> Type w₁}
  {M₁' : ι -> Type w₁'} {M₂ : Type w₂} {M₃ : Type w₃} {M₄ : Type w₄}

/--
Definition of `ContinuousMultilinearMap` / `ContinuousMultilinearMap` 的定义

English:
structure ContinuousMultilinearMap
  parameters: (R : Type u) {ι : Type v} (M₁ : ι -> Type w₁) (M₂ : Type w₂)
  extends: MultilinearMap R M₁ M₂
  axioms and operations (1):
    - cont : Continuous toFun

中文:
结构 连续多重线性映射
  参数: (R : 类型u) {ι : 类型v} (M₁ : ι -> 类型 w₁) (M₂ : 类型 w₂)
  继承: 多重线性映射 R M₁ M₂
  公理与运算 (1 个):
    - cont : 连续 toFun
-/
structure ContinuousMultilinearMap (R : Type u) {ι : Type v} (M₁ : ι -> Type w₁) (M₂ : Type w₂)
  [Semiring R] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [forall i, Module R (M₁ i)] [Module R M₂]
  [forall i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] extends MultilinearMap R M₁ M₂ where
  cont : Continuous toFun

attribute [inherit_doc ContinuousMultilinearMap] ContinuousMultilinearMap.cont

@[inherit_doc ContinuousMultilinearMap]
notation3:25 M " [×" n "]->L[" R "] " M' => ContinuousMultilinearMap R (fun _i : Fin n => M) M'

namespace ContinuousMultilinearMap

section Semiring

variable [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, AddCommMonoid (M₁ i)]
  [forall i, AddCommMonoid (M₁' i)] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [forall i, Module R (M i)] [forall i, Module R (M₁ i)] [forall i, Module R (M₁' i)] [Module R M₂] [Module R M₃]
  [Module R M₄] [forall i, TopologicalSpace (M i)] [forall i, TopologicalSpace (M₁ i)]
  [forall i, TopologicalSpace (M₁' i)] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]
  (f f' : ContinuousMultilinearMap R M₁ M₂)

/--
theorem `toMultilinearMap_injective` / 定理 `toMultilinearMap_injective`

English:
theorem toMultilinearMap_injective

中文:
定理 toMultilinearMap_injective
-/
theorem toMultilinearMap_injective :
    Function.Injective
      (ContinuousMultilinearMap.toMultilinearMap :
        ContinuousMultilinearMap R M₁ M₂ -> MultilinearMap R M₁ M₂)
  | ⟨f, hf⟩, ⟨g, hg⟩, h => by subst h; rfl

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  body: f.toFun
coe_injective _ _ h := toMultilinearMap_injective MultilinearMap.coe_injective h

中文:
实例 funLike
  签名: : 函数状 (连续多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂ where
  定义体: f.toFun
coe_injective _ _ h := toMultilinearMap_injective MultilinearMap.coe_injective h

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  coe f := f.toFun
coe_injective _ _ h := toMultilinearMap_injective MultilinearMap.coe_injective h

/--
Instance `continuousMapClass` / 实例 `continuousMapClass`

English:
instance continuousMapClass
  signature: :
  body: ContinuousMultilinearMap.cont

中文:
实例 continuousMapClass
  签名: :
  定义体: ContinuousMultilinearMap.cont

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.cont
-/
instance continuousMapClass :
    ContinuousMapClass (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  map_continuous := ContinuousMultilinearMap.cont

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (L₁ : ContinuousMultilinearMap R M₁ M₂) (v : forall i, M₁ i)
  body: L₁ v

initialize_simps_projections ContinuousMultilinearMap (-toMultilinearMap,
  toMultilinearMap_toFun -> apply)

@[continuity]

中文:
定义 Simps.apply
  签名: (L₁ : 连续多重线性映射 R M₁ M₂) (v : 对任意 i, M₁ i)
  定义体: L₁ v

initialize_simps_projections ContinuousMultilinearMap (-toMultilinearMap,
  toMultilinearMap_toFun -> apply)

@[continuity]
-/
def Simps.apply (L₁ : ContinuousMultilinearMap R M₁ M₂) (v : forall i, M₁ i) : M₂ :=
  L₁ v

initialize_simps_projections ContinuousMultilinearMap (-toMultilinearMap,
  toMultilinearMap_toFun -> apply)

@[continuity]
/--
theorem `coe_continuous` / 定理 `coe_continuous`

English:
theorem coe_continuous
  statement: Continuous (f : (forall i, M₁ i) -> M₂)
  proof: f.cont

@[simp]

中文:
定理 coe_continuous
  结论: 连续 (f : (对任意 i, M₁ i) -> M₂)
  证明: f.cont

@[simp]

Depends on / 依赖: f.cont
-/
theorem coe_continuous : Continuous (f : (forall i, M₁ i) -> M₂) :=
  f.cont

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: (f.toMultilinearMap : (forall i, M₁ i) -> M₂) = f
  proof: rfl

@[ext]

中文:
定理 coe_coe
  结论: (f.toMultilinearMap : (对任意 i, M₁ i) -> M₂) = f
  证明: rfl

@[ext]
-/
theorem coe_coe : (f.toMultilinearMap : (forall i, M₁ i) -> M₂) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f f' : ContinuousMultilinearMap R M₁ M₂} (H : forall x, f x = f' x)
  statement: f = f'
  proof: DFunLike.ext _ _ H

@[simp]

中文:
定理 ext
  条件: {f f' : 连续多重线性映射 R M₁ M₂} (H : 对任意 x, f x = f' x)
  结论: f = f'
  证明: DFunLike.ext _ _ H

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : forall x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

@[simp]
/--
theorem `map_update_add` / 定理 `map_update_add`

English:
theorem map_update_add
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i)
  proof: f.map_update_add' m i x y

@[simp]

中文:
定理 map_update_add
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (x y : M₁ i)
  证明: f.map_update_add' m i x y

@[simp]

Depends on / 依赖: f.map_update_add, map_update_add
-/
theorem map_update_add [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

@[simp]
/--
theorem `map_update_smul` / 定理 `map_update_smul`

English:
theorem map_update_smul
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i)
  proof: f.map_update_smul' m i c x

中文:
定理 map_update_smul
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (c : R) (x : M₁ i)
  证明: f.map_update_smul' m i c x

Depends on / 依赖: f.map_update_smul, map_update_smul
-/
theorem map_update_smul [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x

/--
theorem `map_coord_zero` / 定理 `map_coord_zero`

English:
theorem map_coord_zero
  given: {m : forall i, M₁ i} (i : ι) (h : m i = 0)
  statement: f m = 0
  proof: f.toMultilinearMap.map_coord_zero i h

@[simp]

中文:
定理 map_coord_zero
  条件: {m : 对任意 i, M₁ i} (i : ι) (h : m i = 0)
  结论: f m = 0
  证明: f.toMultilinearMap.map_coord_zero i h

@[simp]

Depends on / 依赖: f.toMultilinearMap.map_coord_zero, map_coord_zero, toMultilinearMap
-/
theorem map_coord_zero {m : forall i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: [Nonempty ι]
  statement: f 0 = 0
  proof: f.toMultilinearMap.map_zero

中文:
定理 map_zero
  条件: [非空 ι]
  结论: f 0 = 0
  证明: f.toMultilinearMap.map_zero

Depends on / 依赖: f.toMultilinearMap.map_zero, map_zero, toMultilinearMap
-/
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ContinuousMultilinearMap R M₁ M₂)
  body: ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩

中文:
实例 :
  签名: 零 (连续多重线性映射 R M₁ M₂)
  定义体: ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩

Depends on / 依赖: MultilinearMap, continuous_const
-/
instance : Zero (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ContinuousMultilinearMap R M₁ M₂)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (连续多重线性映射 R M₁ M₂)
  定义体: ⟨0⟩
-/
instance : Inhabited (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

@[simp]

中文:
实例 :
  签名: 是ZeroApply (连续多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

@[simp]
-/
instance : IsZeroApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

@[simp]
/--
theorem `toMultilinearMap_zero` / 定理 `toMultilinearMap_zero`

English:
theorem toMultilinearMap_zero
  statement: (0 : ContinuousMultilinearMap R M₁ M₂).toMultilinearMap = 0
  proof: rfl

中文:
定理 toMultilinearMap_zero
  结论: (0 : 连续多重线性映射 R M₁ M₂).toMultilinearMap = 0
  证明: rfl
-/
theorem toMultilinearMap_zero : (0 : ContinuousMultilinearMap R M₁ M₂).toMultilinearMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Semiring A] [forall i, Module A (M₁ i)]
  [Module A M₂] [DistribSMul R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribSMul R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R' (ContinuousMultilinearMap A M₁ M₂)
  body: ⟨fun c f => { c • f.toMultilinearMap with cont := f.cont.const_smul c }⟩

中文:
实例 :
  签名: 标量乘法 R' (连续多重线性映射 A M₁ M₂)
  定义体: ⟨fun c f => { c • f.toMultilinearMap with cont := f.cont.const_smul c }⟩

Depends on / 依赖: const_smul, f.cont.const_smul, f.toMultilinearMap, toMultilinearMap
-/
instance : SMul R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c f => { c • f.toMultilinearMap with cont := f.cont.const_smul c }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply R' (ContinuousMultilinearMap A M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[simp]

中文:
实例 :
  签名: 是SMulApply R' (连续多重线性映射 A M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[simp]
-/
instance : IsSMulApply R' (ContinuousMultilinearMap A M₁ M₂) (forall i, M₁ i) M₂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[simp]
/--
theorem `toMultilinearMap_smul` / 定理 `toMultilinearMap_smul`

English:
theorem toMultilinearMap_smul
  given: (c : R') (f : ContinuousMultilinearMap A M₁ M₂)
  proof: rfl

中文:
定理 toMultilinearMap_smul
  条件: (c : R') (f : 连续多重线性映射 A M₁ M₂)
  证明: rfl
-/
theorem toMultilinearMap_smul (c : R') (f : ContinuousMultilinearMap A M₁ M₂) :
    (c • f).toMultilinearMap = c • f.toMultilinearMap :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R' R'' M₂] : SMulCommClass R' R'' (ContinuousMultilinearMap A M₁ M₂)
  body: FunLike.smulCommClass

中文:
实例 [标量交换类
  签名: R' R'' M₂] : 标量交换类 R' R'' (连续多重线性映射 A M₁ M₂)
  定义体: FunLike.smulCommClass

Depends on / 依赖: FunLike, FunLike.smulCommClass, smulCommClass
-/
instance [SMulCommClass R' R'' M₂] : SMulCommClass R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  FunLike.smulCommClass

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R' R''] [IsScalarTower R' R'' M₂] :
  body: FunLike.isScalarTower

中文:
实例 [标量乘法
  签名: R' R''] [标量塔 R' R'' M₂] :
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance [SMul R' R''] [IsScalarTower R' R'' M₂] :
    IsScalarTower R' R'' (ContinuousMultilinearMap A M₁ M₂) := FunLike.isScalarTower

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: R'ᵐᵒᵖ M₂] [IsCentralScalar R' M₂] :
  body: FunLike.isCentralScalar

中文:
实例 [分配标量乘法
  签名: R'ᵐᵒᵖ M₂] [中心标量 R' M₂] :
  定义体: FunLike.isCentralScalar

Depends on / 依赖: FunLike, FunLike.isCentralScalar, isCentralScalar
-/
instance [DistribSMul R'ᵐᵒᵖ M₂] [IsCentralScalar R' M₂] :
    IsCentralScalar R' (ContinuousMultilinearMap A M₁ M₂) := FunLike.isCentralScalar

end SMul

section SMulMonoid

variable {R' A : Type*} [Monoid R'] [Semiring A] [forall i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction R' (ContinuousMultilinearMap A M₁ M₂)
  body: fast_instance%
  Function.Injective.mulAction toMultilinearMap toMultilinearMap_injective fun _ _ => rfl

中文:
实例 :
  签名: 乘法作用 R' (连续多重线性映射 A M₁ M₂)
  定义体: fast_instance%
  Function.Injective.mulAction toMultilinearMap toMultilinearMap_injective fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : MulAction R' (ContinuousMultilinearMap A M₁ M₂) := fast_instance%
  Function.Injective.mulAction toMultilinearMap toMultilinearMap_injective fun _ _ => rfl

end SMulMonoid

section ContinuousAdd

variable [ContinuousAdd M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (ContinuousMultilinearMap R M₁ M₂)
  body: ⟨fun f f' => ⟨f.toMultilinearMap + f'.toMultilinearMap, f.cont.add f'.cont⟩⟩

中文:
实例 :
  签名: 加法 (连续多重线性映射 R M₁ M₂)
  定义体: ⟨fun f f' => ⟨f.toMultilinearMap + f'.toMultilinearMap, f.cont.add f'.cont⟩⟩

Depends on / 依赖: f.cont.add, f.toMultilinearMap, toMultilinearMap
-/
instance : Add (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f f' => ⟨f.toMultilinearMap + f'.toMultilinearMap, f.cont.add f'.cont⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

@[simp]

中文:
实例 :
  签名: 是加法Apply (连续多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

@[simp]
-/
instance : IsAddApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

@[simp]
/--
theorem `toMultilinearMap_add` / 定理 `toMultilinearMap_add`

English:
theorem toMultilinearMap_add
  given: (f g : ContinuousMultilinearMap R M₁ M₂)
  proof: rfl

中文:
定理 toMultilinearMap_add
  条件: (f g : 连续多重线性映射 R M₁ M₂)
  证明: rfl
-/
theorem toMultilinearMap_add (f g : ContinuousMultilinearMap R M₁ M₂) :
    (f + g).toMultilinearMap = f.toMultilinearMap + g.toMultilinearMap :=
  rfl

-- The `AddMonoid` instance exists to help speedup unification
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (ContinuousMultilinearMap R M₁ M₂)
  body: fast_instance%
  toMultilinearMap_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 加法幺半群 (连续多重线性映射 R M₁ M₂)
  定义体: fast_instance%
  toMultilinearMap_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : AddMonoid (ContinuousMultilinearMap R M₁ M₂) := fast_instance%
  toMultilinearMap_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (ContinuousMultilinearMap R M₁ M₂)
  body: fast_instance%
  toMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (连续多重线性映射 R M₁ M₂)
  定义体: fast_instance%
  toMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance addCommMonoid : AddCommMonoid (ContinuousMultilinearMap R M₁ M₂) := fast_instance%
  toMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Definition of `applyAddHom` / `applyAddHom` 的定义

English:
definition applyAddHom
  signature: (m : forall i, M₁ i)
  body: f m
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

中文:
定义 applyAddHom
  签名: (m : 对任意 i, M₁ i)
  定义体: f m
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply
-/
def applyAddHom (m : forall i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ ->+ M₂ where
  toFun f := f m
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

end ContinuousAdd

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: [DecidableEq ι] (m : forall i, M₁ i) (i : ι)
  body: { f.toMultilinearMap.toLinearMap m i with }

中文:
定义 toContinuousLinearMap
  签名: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι)
  定义体: { f.toMultilinearMap.toLinearMap m i with }
-/
@[simps!] def toContinuousLinearMap [DecidableEq ι] (m : forall i, M₁ i) (i : ι) : M₁ i ->L[R] M₂ :=
  { f.toMultilinearMap.toLinearMap m i with }

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃)
  body: { f.toMultilinearMap.prod g.toMultilinearMap with cont := f.cont.prodMk g.cont }

@[simp]

中文:
定义 乘积
  签名: (f : 连续多重线性映射 R M₁ M₂) (g : 连续多重线性映射 R M₁ M₃)
  定义体: { f.toMultilinearMap.prod g.toMultilinearMap with cont := f.cont.prodMk g.cont }

@[simp]

Depends on / 依赖: f.cont.prodMk, f.toMultilinearMap.prod, g.cont, g.toMultilinearMap, prodMk, toMultilinearMap
-/
def prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    ContinuousMultilinearMap R M₁ (M₂ × M₃) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with cont := f.cont.prodMk g.cont }

@[simp]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  statement: (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃)
  proof: rfl

中文:
定理 prod_apply
  结论: (f : 连续多重线性映射 R M₁ M₂) (g : 连续多重线性映射 R M₁ M₃)
  证明: rfl
-/
theorem prod_apply (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃)
    (m : forall i, M₁ i) : (f.prod g) m = (f m, g m) :=
  rfl

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [forall i, TopologicalSpace (M' i)]
  body: continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap

@[simp]

中文:
定义 pi
  签名: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)] [对任意 i, 拓扑空间 (M' i)]
  定义体: continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap

@[simp]

Depends on / 依赖: coe_continuous, continuous_pi
-/
def pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [forall i, TopologicalSpace (M' i)]
    [forall i, Module R (M' i)] (f : forall i, ContinuousMultilinearMap R M₁ (M' i)) :
    ContinuousMultilinearMap R M₁ (forall i, M' i) where
  cont := continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap

@[simp]
/--
theorem `coe_pi` / 定理 `coe_pi`

English:
theorem coe_pi
  statement: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  proof: rfl

中文:
定理 coe_pi
  结论: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  证明: rfl
-/
theorem coe_pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)]
    (f : forall i, ContinuousMultilinearMap R M₁ (M' i)) : ⇑(pi f) = fun m j => f j m :=
  rfl

/--
theorem `pi_apply` / 定理 `pi_apply`

English:
theorem pi_apply
  statement: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  proof: rfl

中文:
定理 pi_apply
  结论: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  证明: rfl
-/
theorem pi_apply {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)]
    (f : forall i, ContinuousMultilinearMap R M₁ (M' i)) (m : forall i, M₁ i) (j : ι') : pi f m j = f j m :=
  rfl

/-- Restrict the codomain of a continuous multilinear map to a submodule. -/
@[simps! toMultilinearMap apply_coe]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : ContinuousMultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : forall v, f v in p)
  body: ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩

中文:
定义 codRestrict
  签名: (f : 连续多重线性映射 R M₁ M₂) (p : 子模 R M₂) (h : 对任意 v, f v in p)
  定义体: ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩

Depends on / 依赖: codRestrict, f.cont.subtype_mk, subtype_mk
-/
def codRestrict (f : ContinuousMultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : forall v, f v in p) :
    ContinuousMultilinearMap R M₁ p :=
  ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩

section

variable (R M₂ M₃)

/-- The natural equivalence between continuous linear maps from `M₂` to `M₃`
and continuous 1-multilinear maps from `M₂` to `M₃`. -/
@[simps! apply_toMultilinearMap apply_apply symm_apply_apply]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: [Subsingleton ι] (i : ι)
  body: ⟨MultilinearMap.ofSubsingleton R M₂ M₃ i f,
    (map_continuous f).comp (continuous_apply i)⟩
  invFun f := ⟨(MultilinearMap.ofSubsingleton R M₂ M₃ i).symm f.toMultilinearMap,
(map_continuous f).comp continuous_pi fun _ => continuous_id⟩
right_inv f := toMultilinearMap_injective
    (MultilinearMap.ofSubsingleton R M₂ M₃ i).apply_symm_apply f.toMultilinearMap

中文:
定义 ofSubsingleton
  签名: [子单例 ι] (i : ι)
  定义体: ⟨MultilinearMap.ofSubsingleton R M₂ M₃ i f,
    (map_continuous f).comp (continuous_apply i)⟩
  invFun f := ⟨(MultilinearMap.ofSubsingleton R M₂ M₃ i).symm f.toMultilinearMap,
(map_continuous f).comp continuous_pi fun _ => continuous_id⟩
right_inv f := toMultilinearMap_injective
    (MultilinearMap.ofSubsingleton R M₂ M₃ i).apply_symm_apply f.toMultilinearMap

Depends on / 依赖: MultilinearMap, MultilinearMap.ofSubsingleton, ofSubsingleton
-/
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ ->L[R] M₃) ≃ ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M₂ M₃ i f,
    (map_continuous f).comp (continuous_apply i)⟩
  invFun f := ⟨(MultilinearMap.ofSubsingleton R M₂ M₃ i).symm f.toMultilinearMap,
(map_continuous f).comp continuous_pi fun _ => continuous_id⟩
right_inv f := toMultilinearMap_injective
    (MultilinearMap.ofSubsingleton R M₂ M₃ i).apply_symm_apply f.toMultilinearMap

variable (M₁) {M₂}

/-- The constant map is multilinear when `ι` is empty. -/
@[simps! toMultilinearMap apply]
/--
Definition of `constOfIsEmpty` / `constOfIsEmpty` 的定义

English:
definition constOfIsEmpty
  signature: [IsEmpty ι] (m : M₂)
  body: MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const

中文:
定义 constOfIsEmpty
  签名: [是空 ι] (m : M₂)
  定义体: MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const

Depends on / 依赖: MultilinearMap, MultilinearMap.constOfIsEmpty, constOfIsEmpty
-/
def constOfIsEmpty [IsEmpty ι] (m : M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const

end

/--
Definition of `compContinuousLinearMap` / `compContinuousLinearMap` 的定义

English:
definition compContinuousLinearMap
  signature: (g : ContinuousMultilinearMap R M₁' M₄)
  body: { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
cont := g.cont.comp continuous_pi fun j => (f j).cont.comp continuous_apply _ }

@[simp]

中文:
定义 compContinuousLinearMap
  签名: (g : 连续多重线性映射 R M₁' M₄)
  定义体: { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
cont := g.cont.comp continuous_pi fun j => (f j).cont.comp continuous_apply _ }

@[simp]

Depends on / 依赖: compLinearMap, cont.comp, continuous_apply, continuous_pi, g.cont.comp, g.toMultilinearMap.compLinearMap, toLinearMap, toMultilinearMap
-/
def compContinuousLinearMap (g : ContinuousMultilinearMap R M₁' M₄)
    (f : forall i : ι, M₁ i ->L[R] M₁' i) : ContinuousMultilinearMap R M₁ M₄ :=
  { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
cont := g.cont.comp continuous_pi fun j => (f j).cont.comp continuous_apply _ }

@[simp]
/--
theorem `compContinuousLinearMap_apply` / 定理 `compContinuousLinearMap_apply`

English:
theorem compContinuousLinearMap_apply
  statement: (g : ContinuousMultilinearMap R M₁' M₄)
  proof: rfl

中文:
定理 compContinuousLinearMap_apply
  结论: (g : 连续多重线性映射 R M₁' M₄)
  证明: rfl
-/
theorem compContinuousLinearMap_apply (g : ContinuousMultilinearMap R M₁' M₄)
    (f : forall i : ι, M₁ i ->L[R] M₁' i) (m : forall i, M₁ i) :
g.compContinuousLinearMap f m = g fun i => f i m i :=
  rfl

/--
Definition of `_root_.ContinuousLinearMap.compContinuousMultilinearMap` / `_root_.ContinuousLinearMap.compContinuousMultilinearMap` 的定义

English:
definition _root_.ContinuousLinearMap.compContinuousMultilinearMap
  signature: (g : M₂ ->L[R] M₃)
  body: { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }

@[simp]

中文:
定义 _root_.连续线性映射.compContinuousMultilinearMap
  签名: (g : M₂ ->L[R] M₃)
  定义体: { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }

@[simp]

Depends on / 依赖: compMultilinearMap, f.cont, f.toMultilinearMap, g.cont.comp, g.toLinearMap.compMultilinearMap, toLinearMap, toMultilinearMap
-/
def _root_.ContinuousLinearMap.compContinuousMultilinearMap (g : M₂ ->L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) : ContinuousMultilinearMap R M₁ M₃ :=
  { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }

@[simp]
/--
theorem `_root_.ContinuousLinearMap.compContinuousMultilinearMap_coe` / 定理 `_root_.ContinuousLinearMap.compContinuousMultilinearMap_coe`

English:
theorem _root_.ContinuousLinearMap.compContinuousMultilinearMap_coe
  statement: (g : M₂ ->L[R] M₃)
  proof: by
  ext m
  rfl

中文:
定理 _root_.连续线性映射.compContinuousMultilinearMap_coe
  结论: (g : M₂ ->L[R] M₃)
  证明: by
  ext m
  rfl
-/
theorem _root_.ContinuousLinearMap.compContinuousMultilinearMap_coe (g : M₂ ->L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) :
    (g.compContinuousMultilinearMap f : (forall i, M₁ i) -> M₃) =
      (g : M₂ -> M₃) ∘ (f : (forall i, M₁ i) -> M₂) := by
  ext m
  rfl

/-- `ContinuousMultilinearMap.prod` as an `Equiv`. -/
@[simps apply symm_apply_fst symm_apply_snd, simps -isSimp symm_apply]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: :
  body: f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f,
    (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f)

中文:
定义 prodEquiv
  签名: :
  定义体: f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f,
    (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f)
-/
def prodEquiv :
    (ContinuousMultilinearMap R M₁ M₂ × ContinuousMultilinearMap R M₁ M₃) ≃
      ContinuousMultilinearMap R M₁ (M₂ × M₃) where
  toFun f := f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f,
    (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f)

/--
theorem `prod_ext_iff` / 定理 `prod_ext_iff`

English:
theorem prod_ext_iff
  given: {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
  proof: by
  rw [← Prod.mk_inj]; rw [← prodEquiv_symm_apply]; rw [← prodEquiv_symm_apply]; rw [Equiv.apply_eq_iff_eq]

@[ext]

中文:
定理 prod_ext_iff
  条件: {f g : 连续多重线性映射 R M₁ (M₂ × M₃)}
  证明: by
  rw [← Prod.mk_inj]; rw [← prodEquiv_symm_apply]; rw [← prodEquiv_symm_apply]; rw [Equiv.apply_eq_iff_eq]

@[ext]

Depends on / 依赖: Equiv.apply_eq_iff_eq, Prod.mk_inj, apply_eq_iff_eq, mk_inj, prodEquiv_symm_apply
-/
theorem prod_ext_iff {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)} :
    f = g ↔ (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g ∧
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap g := by
  rw [← Prod.mk_inj]; rw [← prodEquiv_symm_apply]; rw [← prodEquiv_symm_apply]; rw [Equiv.apply_eq_iff_eq]

@[ext]
/--
theorem `prod_ext` / 定理 `prod_ext`

English:
theorem prod_ext
  statement: {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
  proof: prod_ext_iff.mpr ⟨h₁, h₂⟩

中文:
定理 prod_ext
  结论: {f g : 连续多重线性映射 R M₁ (M₂ × M₃)}
  证明: prod_ext_iff.mpr ⟨h₁, h₂⟩

Depends on / 依赖: prod_ext_iff, prod_ext_iff.mpr
-/
theorem prod_ext {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
    (h₁ : (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g)
    (h₂ : (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap g) : f = g :=
  prod_ext_iff.mpr ⟨h₁, h₂⟩

/--
theorem `eq_prod_iff` / 定理 `eq_prod_iff`

English:
theorem eq_prod_iff
  statement: {f : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
  proof: prod_ext_iff

中文:
定理 eq_prod_iff
  结论: {f : 连续多重线性映射 R M₁ (M₂ × M₃)}
  证明: prod_ext_iff

Depends on / 依赖: prod_ext_iff
-/
theorem eq_prod_iff {f : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
    {g : ContinuousMultilinearMap R M₁ M₂} {h : ContinuousMultilinearMap R M₁ M₃} :
    f = g.prod h ↔ (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f = g ∧
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f = h :=
  prod_ext_iff

/--
theorem `add_prod_add` / 定理 `add_prod_add`

English:
theorem add_prod_add
  statement: [ContinuousAdd M₂] [ContinuousAdd M₃]
  proof: rfl

中文:
定理 add_prod_add
  结论: [连续加法 M₂] [连续加法 M₃]
  证明: rfl
-/
theorem add_prod_add [ContinuousAdd M₂] [ContinuousAdd M₃]
    (f₁ f₂ : ContinuousMultilinearMap R M₁ M₂) (g₁ g₂ : ContinuousMultilinearMap R M₁ M₃) :
    (f₁ + f₂).prod (g₁ + g₂) = f₁.prod g₁ + f₂.prod g₂ :=
  rfl

/--
theorem `smul_prod_smul` / 定理 `smul_prod_smul`

English:
theorem smul_prod_smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S M₂] [DistribMulAction S M₃]
  proof: rfl

@[simp]

中文:
定理 smul_prod_smul
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S M₂] [分配乘法作用 S M₃]
  证明: rfl

@[simp]
-/
theorem smul_prod_smul {S : Type*} [Monoid S] [DistribMulAction S M₂] [DistribMulAction S M₃]
    [ContinuousConstSMul S M₂] [SMulCommClass R S M₂]
    [ContinuousConstSMul S M₃] [SMulCommClass R S M₃]
    (c : S) (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    (c • f).prod (c • g) = c • f.prod g :=
  rfl

@[simp]
/--
theorem `zero_prod_zero` / 定理 `zero_prod_zero`

English:
theorem zero_prod_zero
  proof: rfl

中文:
定理 zero_prod_zero
  证明: rfl
-/
theorem zero_prod_zero :
    (0 : ContinuousMultilinearMap R M₁ M₂).prod (0 : ContinuousMultilinearMap R M₁ M₃) = 0 :=
  rfl

/-- `ContinuousMultilinearMap.pi` as an `Equiv`. -/
@[simps]
/--
Definition of `piEquiv` / `piEquiv` 的定义

English:
definition piEquiv
  signature: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  body: ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ ->L[R] M' i).compContinuousMultilinearMap f

中文:
定义 piEquiv
  签名: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  定义体: ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ ->L[R] M' i).compContinuousMultilinearMap f

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.pi
-/
def piEquiv {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] :
    (forall i, ContinuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (forall i, M' i) where
  toFun := ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ ->L[R] M' i).compContinuousMultilinearMap f

/-- An equivalence of the index set defines an equivalence between the spaces of continuous
multilinear maps. This is the forward map of this equivalence. -/
@[simps! toMultilinearMap apply]
nonrec def domDomCongr {ι' : Type*} (e : ι ≃ ι')
    (f : ContinuousMultilinearMap R (fun _ : ι => M₂) M₃) :
    ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toMultilinearMap := f.domDomCongr e
cont := f.cont.comp continuous_pi fun _ => continuous_apply _

/-- An equivalence of the index set defines an equivalence between the spaces of continuous
multilinear maps. In case of normed spaces, this is a linear isometric equivalence, see
`ContinuousMultilinearMap.domDomCongrₗᵢ`. -/
@[simps]
/--
Definition of `domDomCongrEquiv` / `domDomCongrEquiv` 的定义

English:
definition domDomCongrEquiv
  signature: {ι' : Type*} (e : ι ≃ ι')
  body: domDomCongr e
  invFun := domDomCongr e.symm
  left_inv _ := ext fun _ => by simp
  right_inv _ := ext fun _ => by simp

中文:
定义 domDomCongrEquiv
  签名: {ι' : 类型} (e : ι ≃ ι')
  定义体: domDomCongr e
  invFun := domDomCongr e.symm
  left_inv _ := ext fun _ => by simp
  right_inv _ := ext fun _ => by simp

Depends on / 依赖: domDomCongr
-/
def domDomCongrEquiv {ι' : Type*} (e : ι ≃ ι') :
    ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ ≃
      ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toFun := domDomCongr e
  invFun := domDomCongr e.symm
  left_inv _ := ext fun _ => by simp
  right_inv _ := ext fun _ => by simp

section linearDeriv

variable [ContinuousAdd M₂] [DecidableEq ι] [Fintype ι] (x y : forall i, M₁ i)

/--
Definition of `linearDeriv` / `linearDeriv` 的定义

English:
definition linearDeriv
  signature: : (forall i, M₁ i) ->L[R] M₂
  body: ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)

@[simp]

中文:
定义 linearDeriv
  签名: : (对任意 i, M₁ i) ->L[R] M₂
  定义体: ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)

@[simp]

Depends on / 依赖: f.toContinuousLinearMap, toContinuousLinearMap
-/
def linearDeriv : (forall i, M₁ i) ->L[R] M₂ := ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)

@[simp]
/--
lemma `linearDeriv_apply` / 引理 `linearDeriv_apply`

English:
lemma linearDeriv_apply
  statement: f.linearDeriv x y = ∑ i, f (Function.update x i (y i))
  proof: by
  simp [linearDeriv, toContinuousLinearMap]

中文:
引理 linearDeriv_apply
  结论: f.linearDeriv x y = ∑ i, f (函数.update x i (y i))
  证明: by
  simp [linearDeriv, toContinuousLinearMap]

Depends on / 依赖: linearDeriv, toContinuousLinearMap
-/
lemma linearDeriv_apply : f.linearDeriv x y = ∑ i, f (Function.update x i (y i)) := by
  simp [linearDeriv, toContinuousLinearMap]

end linearDeriv

/--
theorem `cons_add` / 定理 `cons_add`

English:
theorem cons_add
  given: (f : ContinuousMultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (x y : M 0)
  proof: f.toMultilinearMap.cons_add m x y

中文:
定理 cons_add
  条件: (f : 连续多重线性映射 R M M₂) (m : 对任意 i : 有限集 n, M i.succ) (x y : M 0)
  证明: f.toMultilinearMap.cons_add m x y

Depends on / 依赖: cons_add, f.toMultilinearMap.cons_add, toMultilinearMap
-/
theorem cons_add (f : ContinuousMultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) :=
  f.toMultilinearMap.cons_add m x y

/--
theorem `cons_smul` / 定理 `cons_smul`

English:
theorem cons_smul
  statement: (f : ContinuousMultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (c : R)
  proof: f.toMultilinearMap.cons_smul m c x

中文:
定理 cons_smul
  结论: (f : 连续多重线性映射 R M M₂) (m : 对任意 i : 有限集 n, M i.succ) (c : R)
  证明: f.toMultilinearMap.cons_smul m c x

Depends on / 依赖: cons_smul, f.toMultilinearMap.cons_smul, toMultilinearMap
-/
theorem cons_smul (f : ContinuousMultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (c : R)
    (x : M 0) : f (cons (c • x) m) = c • f (cons x m) :=
  f.toMultilinearMap.cons_smul m c x

/--
theorem `map_piecewise_add` / 定理 `map_piecewise_add`

English:
theorem map_piecewise_add
  given: [DecidableEq ι] (m m' : forall i, M₁ i) (t : Finset ι)
  proof: f.toMultilinearMap.map_piecewise_add _ _ _

中文:
定理 map_piecewise_add
  条件: [DecidableEq ι] (m m' : 对任意 i, M₁ i) (t : 有限集 ι)
  证明: f.toMultilinearMap.map_piecewise_add _ _ _

Depends on / 依赖: f.toMultilinearMap.map_piecewise_add, map_piecewise_add, toMultilinearMap
-/
theorem map_piecewise_add [DecidableEq ι] (m m' : forall i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _

/--
theorem `map_add_univ` / 定理 `map_add_univ`

English:
theorem map_add_univ
  given: [DecidableEq ι] [Fintype ι] (m m' : forall i, M₁ i)
  proof: f.toMultilinearMap.map_add_univ _ _

中文:
定理 map_add_univ
  条件: [DecidableEq ι] [有限类型 ι] (m m' : 对任意 i, M₁ i)
  证明: f.toMultilinearMap.map_add_univ _ _

Depends on / 依赖: f.toMultilinearMap.map_add_univ, map_add_univ, toMultilinearMap
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : forall i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _

section ApplySum

open Fintype Finset

variable {α : ι -> Type*} [Fintype ι] (g : forall i, α i -> M₁ i) (A : forall i, Finset (α i))

/--
theorem `map_sum_finset` / 定理 `map_sum_finset`

English:
theorem map_sum_finset
  given: [DecidableEq ι]
  proof: f.toMultilinearMap.map_sum_finset _ _

中文:
定理 map_sum_finset
  条件: [DecidableEq ι]
  证明: f.toMultilinearMap.map_sum_finset _ _

Depends on / 依赖: f.toMultilinearMap.map_sum_finset, map_sum_finset, toMultilinearMap
-/
theorem map_sum_finset [DecidableEq ι] :
    (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  given: [DecidableEq ι] [forall i, Fintype (α i)]
  proof: f.toMultilinearMap.map_sum _

中文:
定理 map_sum
  条件: [DecidableEq ι] [对任意 i, 有限类型 (α i)]
  证明: f.toMultilinearMap.map_sum _

Depends on / 依赖: f.toMultilinearMap.map_sum, map_sum, toMultilinearMap
-/
theorem map_sum [DecidableEq ι] [forall i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : forall i, α i, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum _

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [forall i : ι, Module A (M₁ i)] [Module A M₂]
  [forall i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : ContinuousMultilinearMap A M₁ M₂)
  body: f.toMultilinearMap.restrictScalars R
  cont := f.cont

@[simp]

中文:
定义 restrictScalars
  签名: (f : 连续多重线性映射 A M₁ M₂)
  定义体: f.toMultilinearMap.restrictScalars R
  cont := f.cont

@[simp]

Depends on / 依赖: f.toMultilinearMap.restrictScalars, restrictScalars, toMultilinearMap
-/
def restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  cont := f.cont

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : ContinuousMultilinearMap A M₁ M₂)
  statement: ⇑(f.restrictScalars R) = f
  proof: rfl

中文:
定理 coe_restrictScalars
  条件: (f : 连续多重线性映射 A M₁ M₂)
  结论: ⇑(f.restrictScalars R) = f
  证明: rfl
-/
theorem coe_restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

end Semiring

section Ring

variable [Ring R] [forall i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [forall i, Module R (M₁ i)] [Module R M₂]
  [forall i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] (f f' : ContinuousMultilinearMap R M₁ M₂)

@[simp]
/--
theorem `map_update_sub` / 定理 `map_update_sub`

English:
theorem map_update_sub
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i)
  proof: f.toMultilinearMap.map_update_sub _ _ _ _

中文:
定理 map_update_sub
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (x y : M₁ i)
  证明: f.toMultilinearMap.map_update_sub _ _ _ _

Depends on / 依赖: f.toMultilinearMap.map_update_sub, map_update_sub, toMultilinearMap
-/
theorem map_update_sub [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_update_sub _ _ _ _

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (ContinuousMultilinearMap R M₁ M₂)
  body: ⟨fun f => { -f.toMultilinearMap with cont := f.cont.neg }⟩

中文:
实例 :
  签名: 取负 (连续多重线性映射 R M₁ M₂)
  定义体: ⟨fun f => { -f.toMultilinearMap with cont := f.cont.neg }⟩

Depends on / 依赖: f.cont.neg, f.toMultilinearMap, toMultilinearMap
-/
instance : Neg (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f => { -f.toMultilinearMap with cont := f.cont.neg }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: 是NegApply (连续多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (ContinuousMultilinearMap R M₁ M₂)
  body: ⟨fun f g => { f.toMultilinearMap - g.toMultilinearMap with cont := f.cont.sub g.cont }⟩

中文:
实例 :
  签名: 减法 (连续多重线性映射 R M₁ M₂)
  定义体: ⟨fun f g => { f.toMultilinearMap - g.toMultilinearMap with cont := f.cont.sub g.cont }⟩

Depends on / 依赖: f.cont.sub, f.toMultilinearMap, g.cont, g.toMultilinearMap, toMultilinearMap
-/
instance : Sub (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f g => { f.toMultilinearMap - g.toMultilinearMap with cont := f.cont.sub g.cont }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: 是SubApply (连续多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (ContinuousMultilinearMap R M₁ M₂)
  body: fast_instance%
  toMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 加法交换群 (连续多重线性映射 R M₁ M₂)
  定义体: fast_instance%
  toMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : AddCommGroup (ContinuousMultilinearMap R M₁ M₂) := fast_instance%
  toMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
theorem `neg_prod_neg` / 定理 `neg_prod_neg`

English:
theorem neg_prod_neg
  statement: [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
  proof: rfl

中文:
定理 neg_prod_neg
  结论: [加法交换群 M₃] [模 R M₃] [拓扑空间 M₃]
  证明: rfl
-/
theorem neg_prod_neg [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
    [IsTopologicalAddGroup M₃] (f : ContinuousMultilinearMap R M₁ M₂)
    (g : ContinuousMultilinearMap R M₁ M₃) : (-f).prod (-g) = - f.prod g :=
  rfl

/--
theorem `sub_prod_sub` / 定理 `sub_prod_sub`

English:
theorem sub_prod_sub
  statement: [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
  proof: rfl

中文:
定理 sub_prod_sub
  结论: [加法交换群 M₃] [模 R M₃] [拓扑空间 M₃]
  证明: rfl
-/
theorem sub_prod_sub [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
    [IsTopologicalAddGroup M₃] (f₁ f₂ : ContinuousMultilinearMap R M₁ M₂)
    (g₁ g₂ : ContinuousMultilinearMap R M₁ M₃) :
    (f₁ - f₂).prod (g₁ - g₂) = f₁.prod g₁ - f₂.prod g₂ :=
  rfl

end IsTopologicalAddGroup

end Ring

section CommSemiring

variable [CommSemiring R] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [forall i, Module R (M₁ i)]
  [Module R M₂] [forall i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  (f : ContinuousMultilinearMap R M₁ M₂)

/--
theorem `map_piecewise_smul` / 定理 `map_piecewise_smul`

English:
theorem map_piecewise_smul
  given: [DecidableEq ι] (c : ι -> R) (m : forall i, M₁ i) (s : Finset ι)
  proof: f.toMultilinearMap.map_piecewise_smul _ _ _

中文:
定理 map_piecewise_smul
  条件: [DecidableEq ι] (c : ι -> R) (m : 对任意 i, M₁ i) (s : 有限集 ι)
  证明: f.toMultilinearMap.map_piecewise_smul _ _ _

Depends on / 依赖: f.toMultilinearMap.map_piecewise_smul, map_piecewise_smul, toMultilinearMap
-/
theorem map_piecewise_smul [DecidableEq ι] (c : ι -> R) (m : forall i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _

/--
theorem `map_smul_univ` / 定理 `map_smul_univ`

English:
theorem map_smul_univ
  given: [Fintype ι] (c : ι -> R) (m : forall i, M₁ i)
  proof: f.toMultilinearMap.map_smul_univ _ _

中文:
定理 map_smul_univ
  条件: [有限类型 ι] (c : ι -> R) (m : 对任意 i, M₁ i)
  证明: f.toMultilinearMap.map_smul_univ _ _

Depends on / 依赖: f.toMultilinearMap.map_smul_univ, map_smul_univ, toMultilinearMap
-/
theorem map_smul_univ [Fintype ι] (c : ι -> R) (m : forall i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _

/-- If two continuous `R`-multilinear maps from `R` are equal on 1, then they are equal.

This is the multilinear version of `ContinuousLinearMap.ext_ring`. -/
@[ext]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  statement: [Finite ι] [TopologicalSpace R]
  proof: toMultilinearMap_injective MultilinearMap.ext_ring h

中文:
定理 ext_ring
  结论: [有限 ι] [拓扑空间 R]
  证明: toMultilinearMap_injective MultilinearMap.ext_ring h

Depends on / 依赖: MultilinearMap, MultilinearMap.ext_ring, ext_ring, toMultilinearMap_injective
-/
theorem ext_ring [Finite ι] [TopologicalSpace R]
    ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄
    (h : f (fun _ => 1) = g (fun _ => 1)) : f = g :=
toMultilinearMap_injective MultilinearMap.ext_ring h

end CommSemiring

section DistribMulAction

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [forall i, AddCommMonoid (M₁ i)]
  [AddCommMonoid M₂] [forall i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [forall i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribMulAction R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousAdd
  signature: M₂] : DistribMulAction R' (ContinuousMultilinearMap A M₁ M₂)
  body: fast_instance%
  Function.Injective.distribMulAction
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective
    fun _ _ => rfl

中文:
实例 [连续加法
  签名: M₂] : 分配乘法作用 R' (连续多重线性映射 A M₁ M₂)
  定义体: fast_instance%
  Function.Injective.distribMulAction
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective
    fun _ _ => rfl

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, distribMulAction, fast_instance, map_add, map_zero, toMultilinearMap, toMultilinearMap_add, toMultilinearMap_injective, toMultilinearMap_zero
-/
instance [ContinuousAdd M₂] : DistribMulAction R' (ContinuousMultilinearMap A M₁ M₂) :=
  fast_instance%
  Function.Injective.distribMulAction
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective
    fun _ _ => rfl

end DistribMulAction

section Module

variable {R' A : Type*} [Semiring R'] [Semiring A] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [forall i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [ContinuousAdd M₂] [forall i, Module A (M₁ i)]
  [Module A M₂] [Module R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R' (ContinuousMultilinearMap A M₁ M₂)
  body: fast_instance%
  Function.Injective.module _
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective fun _ _ => rfl

中文:
实例 :
  签名: 模 R' (连续多重线性映射 A M₁ M₂)
  定义体: fast_instance%
  Function.Injective.module _
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : Module R' (ContinuousMultilinearMap A M₁ M₂) := fast_instance%
  Function.Injective.module _
    { toFun := toMultilinearMap,
      map_zero' := toMultilinearMap_zero,
      map_add' := toMultilinearMap_add }
    toMultilinearMap_injective fun _ _ => rfl

/-- Linear map version of the map `toMultilinearMap` associating to a continuous multilinear map
the corresponding multilinear map. -/
@[simps]
/--
Definition of `toMultilinearMapLinear` / `toMultilinearMapLinear` 的定义

English:
definition toMultilinearMapLinear
  signature: : ContinuousMultilinearMap A M₁ M₂ ->ₗ[R'] MultilinearMap A M₁ M₂ where
  body: toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul

中文:
定义 toMultilinearMapLinear
  签名: : 连续多重线性映射 A M₁ M₂ ->ₗ[R'] 多重线性映射 A M₁ M₂ where
  定义体: toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul

Depends on / 依赖: toMultilinearMap
-/
def toMultilinearMapLinear : ContinuousMultilinearMap A M₁ M₂ ->ₗ[R'] MultilinearMap A M₁ M₂ where
  toFun := toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul

/-- `ContinuousMultilinearMap.pi` as a `LinearEquiv`. -/
@[simps +simpRhs]
/--
Definition of `piLinearEquiv` / `piLinearEquiv` 的定义

English:
definition piLinearEquiv
  signature: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  body: { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 piLinearEquiv
  签名: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  定义体: { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: map_add, map_smul, piEquiv
-/
def piLinearEquiv {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, ContinuousAdd (M' i)] [forall i, Module R' (M' i)]
    [forall i, Module A (M' i)] [forall i, SMulCommClass A R' (M' i)] [forall i, ContinuousConstSMul R' (M' i)] :
    (forall i, ContinuousMultilinearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (forall i, M' i) :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end Module


section Algebra

variable (R n) (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [ContinuousMul A]

/--
Definition of `mkPiAlgebraFin` / `mkPiAlgebraFin` 的定义

English:
definition mkPiAlgebraFin
  signature: : A [×n]->L[R] A where
  body: by
    change Continuous fun m => (List.ofFn m).prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A

中文:
定义 mkPiAlgebraFin
  签名: : A [×n]->L[R] A where
  定义体: by
    change Continuous fun m => (List.ofFn m).prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A
-/
protected def mkPiAlgebraFin : A [×n]->L[R] A where
  cont := by
    change Continuous fun m => (List.ofFn m).prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A

variable {R n A}

@[simp]
/--
theorem `mkPiAlgebraFin_apply` / 定理 `mkPiAlgebraFin_apply`

English:
theorem mkPiAlgebraFin_apply
  given: (m : Fin n -> A)
  proof: rfl

中文:
定理 mkPiAlgebraFin_apply
  条件: (m : 有限集 n -> A)
  证明: rfl
-/
theorem mkPiAlgebraFin_apply (m : Fin n -> A) :
    ContinuousMultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl

end Algebra

section CommAlgebra

variable (R ι) (A : Type*) [Fintype ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A]

/--
Definition of `mkPiAlgebra` / `mkPiAlgebra` 的定义

English:
definition mkPiAlgebra
  signature: : ContinuousMultilinearMap R (fun _ : ι => A) A where
  body: continuous_finsetProd _ fun _ _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A

@[simp]

中文:
定义 mkPiAlgebra
  签名: : 连续多重线性映射 R (fun _ : ι => A) A where
  定义体: continuous_finsetProd _ fun _ _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A

@[simp]
-/
protected def mkPiAlgebra : ContinuousMultilinearMap R (fun _ : ι => A) A where
  cont := continuous_finsetProd _ fun _ _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A

@[simp]
/--
theorem `mkPiAlgebra_apply` / 定理 `mkPiAlgebra_apply`

English:
theorem mkPiAlgebra_apply
  given: (m : ι -> A)
  statement: ContinuousMultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i
  proof: rfl

中文:
定理 mkPiAlgebra_apply
  条件: (m : ι -> A)
  结论: 连续多重线性映射.mkPiAlgebra R ι A m = ∏ i, m i
  证明: rfl
-/
theorem mkPiAlgebra_apply (m : ι -> A) : ContinuousMultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl

/--
theorem `mkPiAlgebra_eq_mkPiAlgebraFin` / 定理 `mkPiAlgebra_eq_mkPiAlgebraFin`

English:
theorem mkPiAlgebra_eq_mkPiAlgebraFin
  given: {n : Nat}
  statement: ContinuousMultilinearMap.mkPiAlgebra R (Fin n) A
  proof: by
  ext
  simp [List.prod_ofFn]

中文:
定理 mkPiAlgebra_eq_mkPiAlgebraFin
  条件: {n : 自然数}
  结论: 连续多重线性映射.mkPiAlgebra R (有限集 n) A
  证明: by
  ext
  simp [List.prod_ofFn]

Depends on / 依赖: List.prod_ofFn, prod_ofFn
-/
theorem mkPiAlgebra_eq_mkPiAlgebraFin {n : Nat} : ContinuousMultilinearMap.mkPiAlgebra R (Fin n) A
    = ContinuousMultilinearMap.mkPiAlgebraFin R n A := by
  ext
  simp [List.prod_ofFn]

end CommAlgebra

section SMulRight

variable [CommSemiring R] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [forall i, Module R (M₁ i)]
  [Module R M₂] [TopologicalSpace R] [forall i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  [ContinuousSMul R M₂] (f : ContinuousMultilinearMap R M₁ R) (z : M₂)

/-- Given a continuous `R`-multilinear map `f` taking values in `R`, `f.smulRight z` is the
continuous multilinear map sending `m` to `f m • z`. -/
@[simps! toMultilinearMap apply]
/--
Definition of `smulRight` / `smulRight` 的定义

English:
definition smulRight
  signature: : ContinuousMultilinearMap R M₁ M₂ where
  body: f.toMultilinearMap.smulRight z
  cont := f.cont.smul continuous_const

中文:
定义 smulRight
  签名: : 连续多重线性映射 R M₁ M₂ where
  定义体: f.toMultilinearMap.smulRight z
  cont := f.cont.smul continuous_const

Depends on / 依赖: f.toMultilinearMap.smulRight, smulRight, toMultilinearMap
-/
def smulRight : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.smulRight z
  cont := f.cont.smul continuous_const

end SMulRight

section CommRing
variable {M : Type*}
variable [Fintype ι] [CommRing R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace R] [TopologicalSpace M]
variable [ContinuousMul R] [ContinuousSMul R M]

variable (R ι) in
/--
Definition of `mkPiRing` / `mkPiRing` 的定义

English:
definition mkPiRing
  signature: (z : M)
  body: (ContinuousMultilinearMap.mkPiAlgebra R ι R).smulRight z


@[simp]

中文:
定义 mkPiRing
  签名: (z : M)
  定义体: (ContinuousMultilinearMap.mkPiAlgebra R ι R).smulRight z


@[simp]
-/
protected def mkPiRing (z : M) : ContinuousMultilinearMap R (fun _ : ι => R) M :=
  (ContinuousMultilinearMap.mkPiAlgebra R ι R).smulRight z


@[simp]
/--
theorem `mkPiRing_apply` / 定理 `mkPiRing_apply`

English:
theorem mkPiRing_apply
  given: (z : M) (m : ι -> R)
  proof: rfl

中文:
定理 mkPiRing_apply
  条件: (z : M) (m : ι -> R)
  证明: rfl
-/
theorem mkPiRing_apply (z : M) (m : ι -> R) :
    (ContinuousMultilinearMap.mkPiRing R ι z : (ι -> R) -> M) m = (∏ i, m i) • z :=
  rfl

/--
theorem `mkPiRing_apply_one_eq_self` / 定理 `mkPiRing_apply_one_eq_self`

English:
theorem mkPiRing_apply_one_eq_self
  given: (f : ContinuousMultilinearMap R (fun _ : ι => R) M)
  proof: toMultilinearMap_injective f.toMultilinearMap.mkPiRing_apply_one_eq_self

中文:
定理 mkPiRing_apply_one_eq_self
  条件: (f : 连续多重线性映射 R (fun _ : ι => R) M)
  证明: toMultilinearMap_injective f.toMultilinearMap.mkPiRing_apply_one_eq_self

Depends on / 依赖: f.toMultilinearMap.mkPiRing_apply_one_eq_self, mkPiRing_apply_one_eq_self, toMultilinearMap, toMultilinearMap_injective
-/
theorem mkPiRing_apply_one_eq_self (f : ContinuousMultilinearMap R (fun _ : ι => R) M) :
    ContinuousMultilinearMap.mkPiRing R ι (f fun _ => 1) = f :=
  toMultilinearMap_injective f.toMultilinearMap.mkPiRing_apply_one_eq_self

/--
theorem `mkPiRing_eq_iff` / 定理 `mkPiRing_eq_iff`

English:
theorem mkPiRing_eq_iff
  given: {z₁ z₂ : M}
  proof: by
  rw [← toMultilinearMap_injective.eq_iff]
  exact MultilinearMap.mkPiRing_eq_iff

中文:
定理 mkPiRing_eq_iff
  条件: {z₁ z₂ : M}
  证明: by
  rw [← toMultilinearMap_injective.eq_iff]
  exact MultilinearMap.mkPiRing_eq_iff

Depends on / 依赖: MultilinearMap, MultilinearMap.mkPiRing_eq_iff, eq_iff, mkPiRing_eq_iff, toMultilinearMap_injective, toMultilinearMap_injective.eq_iff
-/
theorem mkPiRing_eq_iff {z₁ z₂ : M} :
    ContinuousMultilinearMap.mkPiRing R ι z₁ = ContinuousMultilinearMap.mkPiRing R ι z₂ ↔
      z₁ = z₂ := by
  rw [← toMultilinearMap_injective.eq_iff]
  exact MultilinearMap.mkPiRing_eq_iff

/--
theorem `mkPiRing_zero` / 定理 `mkPiRing_zero`

English:
theorem mkPiRing_zero
  statement: ContinuousMultilinearMap.mkPiRing R ι (0 : M) = 0
  proof: by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]

中文:
定理 mkPiRing_zero
  结论: 连续多重线性映射.mkPiRing R ι (0 : M) = 0
  证明: by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]

Depends on / 依赖: mkPiRing_apply, smul_zero, zero_apply
-/
theorem mkPiRing_zero : ContinuousMultilinearMap.mkPiRing R ι (0 : M) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]

/--
theorem `mkPiRing_eq_zero_iff` / 定理 `mkPiRing_eq_zero_iff`

English:
theorem mkPiRing_eq_zero_iff
  given: (z : M)
  statement: ContinuousMultilinearMap.mkPiRing R ι z = 0 ↔ z = 0
  proof: by
  rw [← mkPiRing_zero]; rw [mkPiRing_eq_iff]

中文:
定理 mkPiRing_eq_zero_iff
  条件: (z : M)
  结论: 连续多重线性映射.mkPiRing R ι z = 0 ↔ z = 0
  证明: by
  rw [← mkPiRing_zero]; rw [mkPiRing_eq_iff]

Depends on / 依赖: mkPiRing_eq_iff, mkPiRing_zero
-/
theorem mkPiRing_eq_zero_iff (z : M) : ContinuousMultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero]; rw [mkPiRing_eq_iff]

end CommRing

end ContinuousMultilinearMap
