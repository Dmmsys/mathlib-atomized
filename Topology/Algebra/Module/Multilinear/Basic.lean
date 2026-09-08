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

variable {R : Type u} {ι : Type v} {n : ℕ} {M : Fin n.succ → Type w} {M₁ : ι → Type w₁}
  {M₁' : ι → Type w₁'} {M₂ : Type w₂} {M₃ : Type w₃} {M₄ : Type w₄}

/-- Continuous multilinear maps over the ring `R`, from `∀ i, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
/-
**ContinuousMultilinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   {ι : Type v} →     (M₁ : ι → Type w₁) →       (M₂ : Type 
w₂) →         [inst : Semiring R] →           [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] →             [inst_2 : AddCommMonoid M₂] →               [(i : ι) → _ro
ot_.Module R (M₁ i)] →                 [_root_.Module R M₂] →                   
[(i : ι) → TopologicalSpace (M₁ i)] → [TopologicalSpace M₂] → Type (max (max v w
₁) w₂)
参数：max v w₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous multilinear maps over the ring `R`, from `∀ i, M₁ i` to `M₂` where `M
₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will b
e compatibility
conditions between the algebraic and the topological structures, but this is not
 needed for the
definition.
-/
structure ContinuousMultilinearMap (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] extends MultilinearMap R M₁ M₂ where
  cont : Continuous toFun

attribute [inherit_doc ContinuousMultilinearMap] ContinuousMultilinearMap.cont

@[inherit_doc ContinuousMultilinearMap]
notation3:25 M " [×" n "]→L[" R "] " M' => ContinuousMultilinearMap R (fun _i : Fin n => M) M'

namespace ContinuousMultilinearMap

section Semiring

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)]
  [∀ i, AddCommMonoid (M₁' i)] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)] [Module R M₂] [Module R M₃]
  [Module R M₄] [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (M₁ i)]
  [∀ i, TopologicalSpace (M₁' i)] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]
  (f f' : ContinuousMultilinearMap R M₁ M₂)

/-
**ContinuousMultilinearMap.toMultilinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：∀ {R : Type u} {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semi
ring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁ i)] [inst_2 : AddCommMonoid M₂] 
[inst_3 : (i : ι) → _root_.Module R (M₁ i)]   [inst_4 : _root_.Module R M₂] [ins
t_5 : (i : ι) → TopologicalSpace (M₁ i)] [inst_6 : TopologicalSpace M₂],   Funct
ion.Injective ContinuousMultilinearMap.toMultilinearMap
参数：i : ι；M₁ i；i : ι；M₁ i；i : ι；M₁ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMultilinearMap_injective :
    Function.Injective
      (ContinuousMultilinearMap.toMultilinearMap :
        ContinuousMultilinearMap R M₁ M₂ → MultilinearMap R M₁ M₂)
  | ⟨f, hf⟩, ⟨g, hg⟩, h => by subst h; rfl
/-
**ContinuousMultilinearMap.funLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilin
earMap`。
形式化陈述：funLike : FunLike (ContinuousMultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ w
here coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective _ _ h := toMultilinearMap_injective <| MultilinearMap.coe_injective h
/-
**ContinuousMultilinearMap.continuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：continuousMapClass : ContinuousMapClass (ContinuousMultilinearMap R M₁ M₂)
 (forall i, M₁ i) M₂ where map_continuous
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
-/
instance continuousMapClass :
    ContinuousMapClass (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  map_continuous := ContinuousMultilinearMap.cont

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**ContinuousMultilinearMap.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMult
ilinearMap.Simps`。
形式化陈述：{R : Type u} →   {ι : Type v} →     {M₁ : ι → Type w₁} →       {M₂ : Type 
w₂} →         [inst : Semiring R] →           [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] →             [inst_2 : AddCommMonoid M₂] →               [inst_3 : (i :
 ι) → _root_.Module R (M₁ i)] →                 [inst_4 : _root_.Module R M₂] → 
                  [inst_5 : (i : ι) → TopologicalSpace (M₁ i)] →                
     [inst_6 : TopologicalSpace M₂] → ContinuousMultilinearMap R M₁ M₂ → ((i : ι
) → M₁ i) → M₂
参数：i : ι；M₁ i；i : ι；M₁ i；i : ι；M₁ i；(i : ι) → M₁ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (L₁ : ContinuousMultilinearMap R M₁ M₂) (v : ∀ i, M₁ i) : M₂ :=
  L₁ v

initialize_simps_projections ContinuousMultilinearMap (-toMultilinearMap,
  toMultilinearMap_toFun → apply)

@[continuity]
/-
**ContinuousMultilinearMap.coe_continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：coe_continuous : Continuous (f : (forall i, M₁ i) -> M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
-/
theorem coe_continuous : Continuous (f : (∀ i, M₁ i) → M₂) :=
  f.cont

@[simp]
/-
**ContinuousMultilinearMap.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilin
earMap`。
形式化陈述：coe_coe : (f.toMultilinearMap : (forall i, M₁ i) -> M₂) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe : (f.toMultilinearMap : (∀ i, M₁ i) → M₂) = f :=
  rfl

@[ext]
/-
**ContinuousMultilinearMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilinearM
ap`。
形式化陈述：ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : forall x, f x = f' x) :
 f = f'
参数：H : forall x, f x = f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

@[simp]
/-
**ContinuousMultilinearMap.map_update_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：map_update_add [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
 f (update m i (x + y)) = f (update m i x) + f (update m i y)
参数：m : forall i, M₁ i；i : ι；x y : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_add'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
-/
theorem map_update_add [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

@[simp]
/-
**ContinuousMultilinearMap.map_update_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：map_update_smul [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : 
M₁ i) : f (update m i (c • x)) = c • f (update m i x)
参数：m : forall i, M₁ i；i : ι；c : R；x : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_smul'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι →
 Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid
 (M₁ i)] [inst_2 : Ad…
-/
theorem map_update_smul [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x
/-
**ContinuousMultilinearMap.map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：map_coord_zero {m : forall i, M₁ i} (i : ι) (h : m i = 0) : f m = 0
参数：i : ι；h : m i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
-/
theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
/-
**ContinuousMultilinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：map_zero [Nonempty ι] : f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
-/
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨0⟩
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

@[simp]
/-
**ContinuousMultilinearMap.toMultilinearMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：toMultilinearMap_zero : (0 : ContinuousMultilinearMap R M₁ M₂).toMultiline
arMap = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMultilinearMap_zero : (0 : ContinuousMultilinearMap R M₁ M₂).toMultilinearMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Semiring A] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribSMul R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribSMul R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]

/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c f => { c • f.toMultilinearMap with cont := f.cont.const_smul c }⟩
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply R' (ContinuousMultilinearMap A M₁ M₂) (∀ i, M₁ i) M₂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[simp]
/-
**ContinuousMultilinearMap.toMultilinearMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：toMultilinearMap_smul (c : R') (f : ContinuousMultilinearMap A M₁ M₂) : (c
 • f).toMultilinearMap = c • f.toMultilinearMap
参数：c : R'；f : ContinuousMultilinearMap A M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMultilinearMap_smul (c : R') (f : ContinuousMultilinearMap A M₁ M₂) :
    (c • f).toMultilinearMap = c • f.toMultilinearMap :=
  rfl
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass R' R'' M₂] : SMulCommClass R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  FunLike.smulCommClass
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R' R''] [IsScalarTower R' R'' M₂] :
    IsScalarTower R' R'' (ContinuousMultilinearMap A M₁ M₂) := FunLike.isScalarTower
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul R'ᵐᵒᵖ M₂] [IsCentralScalar R' M₂] :
    IsCentralScalar R' (ContinuousMultilinearMap A M₁ M₂) := FunLike.isCentralScalar

end SMul

section SMulMonoid

variable {R' A : Type*} [Monoid R'] [Semiring A] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]

/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction R' (ContinuousMultilinearMap A M₁ M₂) := fast_instance%
  Function.Injective.mulAction toMultilinearMap toMultilinearMap_injective fun _ _ => rfl

end SMulMonoid

section ContinuousAdd

variable [ContinuousAdd M₂]

/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f f' => ⟨f.toMultilinearMap + f'.toMultilinearMap, f.cont.add f'.cont⟩⟩
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

@[simp]
/-
**ContinuousMultilinearMap.toMultilinearMap_add** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：toMultilinearMap_add (f g : ContinuousMultilinearMap R M₁ M₂) : (f + g).to
MultilinearMap = f.toMultilinearMap + g.toMultilinearMap
参数：f g : ContinuousMultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMultilinearMap_add (f g : ContinuousMultilinearMap R M₁ M₂) :
    (f + g).toMultilinearMap = f.toMultilinearMap + g.toMultilinearMap :=
  rfl

-- The `AddMonoid` instance exists to help speedup unification
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (ContinuousMultilinearMap R M₁ M₂) := fast_instance%
  toMultilinearMap_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
/-
**ContinuousMultilinearMap.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：addCommMonoid : AddCommMonoid (ContinuousMultilinearMap R M₁ M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (ContinuousMultilinearMap R M₁ M₂) := fast_instance%
  toMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/-- Evaluation of a `ContinuousMultilinearMap` at a vector as an `AddMonoidHom`. -/
/-
**ContinuousMultilinearMap.applyAddHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：applyAddHom (m : forall i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ ->+ M₂
 where toFun f
参数：m : forall i, M₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of a `ContinuousMultilinearMap` at a vector as an `AddMonoidHom`.
-/
def applyAddHom (m : ∀ i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ →+ M₂ where
  toFun f := f m
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply

end ContinuousAdd

set_option backward.defeqAttrib.useBackward true in
/-- If `f` is a continuous multilinear map, then `f.toContinuousLinearMap m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
/-
**ContinuousMultilinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：{R : Type u} →   {ι : Type v} →     {M₁ : ι → Type w₁} →       {M₂ : Type 
w₂} →         [inst : Semiring R] →           [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] →             [inst_2 : AddCommMonoid M₂] →               [inst_3 : (i :
 ι) → _root_.Module R (M₁ i)] →                 [inst_4 : _root_.Module R M₂] → 
                  [inst_5 : (i : ι) → TopologicalSpace (M₁ i)] →                
     [inst_6 : TopologicalSpace M₂] →                       ContinuousMultilinea
rMap R M₁ M₂ → [DecidableEq ι] → ((i : ι) → M₁ i) → (i : ι) → M₁ i →L[R] M₂
参数：i : ι；M₁ i；i : ι；M₁ i；i : ι；M₁ i；(i : ι) → M₁ i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a continuous multilinear map, then `f.toContinuousLinearMap m i` is th
e continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and
 varying the
`i`-th coordinate.
-/
@[simps!] def toContinuousLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
  { f.toMultilinearMap.toLinearMap m i with }

/-- The Cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
/-
**ContinuousMultilinearMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinear
Map`。
形式化陈述：prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap 
R M₁ M₃) : ContinuousMultilinearMap R M₁ (M₂ × M₃)
参数：f : ContinuousMultilinearMap R M₁ M₂；g : ContinuousMultilinearMap R M₁ M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two continuous multilinear maps, as a continuous multil
inear map.
-/
def prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    ContinuousMultilinearMap R M₁ (M₂ × M₃) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with cont := f.cont.prodMk g.cont }

@[simp]
/-
**ContinuousMultilinearMap.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：prod_apply (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultiline
arMap R M₁ M₃) (m : forall i, M₁ i) : (f.prod g) m = (f m, g m)
参数：f : ContinuousMultilinearMap R M₁ M₂；g : ContinuousMultilinearMap R M₁ M₃；m :
 forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃)
    (m : ∀ i, M₁ i) : (f.prod g) m = (f m, g m) :=
  rfl

/-- Combine a family of continuous multilinear maps with the same domain and codomains `M' i` into a
continuous multilinear map taking values in the space of functions `∀ i, M' i`. -/
/-
**ContinuousMultilinearMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinearMa
p`。
形式化陈述：pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [foral
l i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, Continu
ousMultilinearMap R M₁ (M' i)) : ContinuousMultilinearMap R M₁ (forall i, M' i) 
where cont
参数：M' i；M' i；M' i；f : forall i, ContinuousMultilinearMap R M₁ (M' i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of continuous multilinear maps with the same domain and codomai
ns `M' i` into a
continuous multilinear map taking values in the space of functions `∀ i, M' i`.
-/
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) :
    ContinuousMultilinearMap R M₁ (∀ i, M' i) where
  cont := continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap

@[simp]
/-
**ContinuousMultilinearMap.coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultiline
arMap`。
形式化陈述：coe_pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [f
orall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, Con
tinuousMultilinearMap R M₁ (M' i)) : ⇑(pi f) = fun m j => f j m
参数：M' i；M' i；M' i；f : forall i, ContinuousMultilinearMap R M₁ (M' i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) : ⇑(pi f) = fun m j => f j m :=
  rfl
/-
**ContinuousMultilinearMap.pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：pi_apply {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] 
[forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, C
ontinuousMultilinearMap R M₁ (M' i)) (m : forall i, M₁ i) (j : ι') : pi f m j = 
f j m
参数：M' i；M' i；M' i；f : forall i, ContinuousMultilinearMap R M₁ (M' i)；m : forall 
i, M₁ i；j : ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_apply {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) (m : ∀ i, M₁ i) (j : ι') : pi f m j = f j m :=
  rfl

/-- Restrict the codomain of a continuous multilinear map to a submodule. -/
@[simps! toMultilinearMap apply_coe]
/-
**ContinuousMultilinearMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：codRestrict (f : ContinuousMultilinearMap R M₁ M₂) (p : Submodule R M₂) (h
 : forall v, f v in p) : ContinuousMultilinearMap R M₁ p
参数：f : ContinuousMultilinearMap R M₁ M₂；p : Submodule R M₂；h : forall v, f v in 
p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a continuous multilinear map to a submodule.
-/
def codRestrict (f : ContinuousMultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    ContinuousMultilinearMap R M₁ p :=
  ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩

section

variable (R M₂ M₃)

/-- The natural equivalence between continuous linear maps from `M₂` to `M₃`
and continuous 1-multilinear maps from `M₂` to `M₃`. -/
@[simps! apply_toMultilinearMap apply_apply symm_apply_apply]
/-
**ContinuousMultilinearMap.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：ofSubsingleton [Subsingleton ι] (i : ι) : (M₂ ->L[R] M₃) ≃ ContinuousMulti
linearMap R (fun _ : ι => M₂) M₃ where toFun f
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural equivalence between continuous linear maps from `M₂` to `M₃`
and continuous 1-multilinear maps from `M₂` to `M₃`.
-/
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →L[R] M₃) ≃ ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M₂ M₃ i f,
    (map_continuous f).comp (continuous_apply i)⟩
  invFun f := ⟨(MultilinearMap.ofSubsingleton R M₂ M₃ i).symm f.toMultilinearMap,
    (map_continuous f).comp <| continuous_pi fun _ ↦ continuous_id⟩
  right_inv f := toMultilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M₂ M₃ i).apply_symm_apply f.toMultilinearMap

variable (M₁) {M₂}

/-- The constant map is multilinear when `ι` is empty. -/
@[simps! toMultilinearMap apply]
/-
**ContinuousMultilinearMap.constOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：constOfIsEmpty [IsEmpty ι] (m : M₂) : ContinuousMultilinearMap R M₁ M₂ whe
re toMultilinearMap
参数：m : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant map is multilinear when `ι` is empty.
-/
def constOfIsEmpty [IsEmpty ι] (m : M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const

end

/-- If `g` is continuous multilinear and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.compContinuousLinearMap f`. -/
/-
**ContinuousMultilinearMap.compContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousMultilinearMap`。
形式化陈述：compContinuousLinearMap (g : ContinuousMultilinearMap R M₁' M₄) (f : foral
l i : ι, M₁ i ->L[R] M₁' i) : ContinuousMultilinearMap R M₁ M₄
参数：g : ContinuousMultilinearMap R M₁' M₄；f : forall i : ι, M₁ i ->L[R] M₁' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is continuous multilinear and `f` is a collection of continuous linear ma
ps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.compContinuousLinearMap f`.
-/
def compContinuousLinearMap (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) : ContinuousMultilinearMap R M₁ M₄ :=
  { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
    cont := g.cont.comp <| continuous_pi fun j => (f j).cont.comp <| continuous_apply _ }

@[simp]
/-
**ContinuousMultilinearMap.compContinuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousMultilinearMap`。
形式化陈述：compContinuousLinearMap_apply (g : ContinuousMultilinearMap R M₁' M₄) (f :
 forall i : ι, M₁ i ->L[R] M₁' i) (m : forall i, M₁ i) : g.compContinuousLinearM
ap f m = g fun i => f i m i
参数：g : ContinuousMultilinearMap R M₁' M₄；f : forall i : ι, M₁ i ->L[R] M₁' i；m :
 forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compContinuousLinearMap_apply (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) (m : ∀ i, M₁ i) :
    g.compContinuousLinearMap f m = g fun i => f i <| m i :=
  rfl

/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
/-
**ContinuousMultilinearMap._root_.ContinuousLinearMap.compContinuousMultilinearM
ap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a continuous multilinear map with a continuous linear map gives again 
a
continuous multilinear map.
-/
def _root_.ContinuousLinearMap.compContinuousMultilinearMap (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) : ContinuousMultilinearMap R M₁ M₃ :=
  { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }

@[simp]
/-
**ContinuousMultilinearMap._root_.ContinuousLinearMap.compContinuousMultilinearM
ap_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.compContinuousMultilinearMap_coe (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) :
    (g.compContinuousMultilinearMap f : (∀ i, M₁ i) → M₃) =
      (g : M₂ → M₃) ∘ (f : (∀ i, M₁ i) → M₂) := by
  ext m
  rfl

/-- `ContinuousMultilinearMap.prod` as an `Equiv`. -/
@[simps apply symm_apply_fst symm_apply_snd, simps -isSimp symm_apply]
/-
**ContinuousMultilinearMap.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：prodEquiv : (ContinuousMultilinearMap R M₁ M₂ × ContinuousMultilinearMap R
 M₁ M₃) ≃ ContinuousMultilinearMap R M₁ (M₂ × M₃) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.prod` as an `Equiv`.
-/
def prodEquiv :
    (ContinuousMultilinearMap R M₁ M₂ × ContinuousMultilinearMap R M₁ M₃) ≃
      ContinuousMultilinearMap R M₁ (M₂ × M₃) where
  toFun f := f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f,
    (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f)
/-
**ContinuousMultilinearMap.prod_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：prod_ext_iff {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)} : f = g ↔ (Co
ntinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f = (ContinuousLinearM
ap.fst _ _ _).compContinuousMultilinearMap g ∧ (ContinuousLinearMap.snd _ _ _).c
ompContinuousMultilinearMap f = (ContinuousLinearMap.snd _ _ _).compContinuousMu
ltilinearMap g
参数：M₂ × M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ContinuousMultilinearMap.prodEquiv_symm_apply`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]   [inst_
1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_ext_iff {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)} :
    f = g ↔ (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g ∧
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap g := by
  rw [← Prod.mk_inj, ← prodEquiv_symm_apply, ← prodEquiv_symm_apply, Equiv.apply_eq_iff_eq]

@[ext]
/-
**ContinuousMultilinearMap.prod_ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：prod_ext {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)} (h₁ : (Continuous
LinearMap.fst _ _ _).compContinuousMultilinearMap f = (ContinuousLinearMap.fst _
 _ _).compContinuousMultilinearMap g) (h₂ : (ContinuousLinearMap.snd _ _ _).comp
ContinuousMultilinearMap f = (ContinuousLinearMap.snd _ _ _).compContinuousMulti
linearMap g) : f = g
参数：M₂ × M₃；h₁ : (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
 (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g；h₂ : (Continuous
LinearMap.snd _ _ _).compContinuousMultilinearMap f = (ContinuousLinearMap.snd _
 _ _).compContinuousMultilinearMap g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMultilinearMap.prod_ext_iff`：prod_ext_iff {f g : ContinuousMul
tilinearMap R M₁ (M₂ × M₃)} : f = g ↔ (ContinuousLinearMap.fst _ _ _).compContin
uousMultilinearMap f = (Con…
-/
theorem prod_ext {f g : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
    (h₁ : (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g)
    (h₂ : (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap g) : f = g :=
  prod_ext_iff.mpr ⟨h₁, h₂⟩
/-
**ContinuousMultilinearMap.eq_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：eq_prod_iff {f : ContinuousMultilinearMap R M₁ (M₂ × M₃)} {g : ContinuousM
ultilinearMap R M₁ M₂} {h : ContinuousMultilinearMap R M₁ M₃} : f = g.prod h ↔ (
ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f = g ∧ (ContinuousL
inearMap.snd _ _ _).compContinuousMultilinearMap f = h
参数：M₂ × M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.prod_ext_iff`：prod_ext_iff {f g : ContinuousMul
tilinearMap R M₁ (M₂ × M₃)} : f = g ↔ (ContinuousLinearMap.fst _ _ _).compContin
uousMultilinearMap f = (Con…
-/
theorem eq_prod_iff {f : ContinuousMultilinearMap R M₁ (M₂ × M₃)}
    {g : ContinuousMultilinearMap R M₁ M₂} {h : ContinuousMultilinearMap R M₁ M₃} :
    f = g.prod h ↔ (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f = g ∧
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f = h :=
  prod_ext_iff
/-
**ContinuousMultilinearMap.add_prod_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：add_prod_add [ContinuousAdd M₂] [ContinuousAdd M₃] (f₁ f₂ : ContinuousMult
ilinearMap R M₁ M₂) (g₁ g₂ : ContinuousMultilinearMap R M₁ M₃) : (f₁ + f₂).prod 
(g₁ + g₂) = f₁.prod g₁ + f₂.prod g₂
参数：f₁ f₂ : ContinuousMultilinearMap R M₁ M₂；g₁ g₂ : ContinuousMultilinearMap R M
₁ M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_prod_add [ContinuousAdd M₂] [ContinuousAdd M₃]
    (f₁ f₂ : ContinuousMultilinearMap R M₁ M₂) (g₁ g₂ : ContinuousMultilinearMap R M₁ M₃) :
    (f₁ + f₂).prod (g₁ + g₂) = f₁.prod g₁ + f₂.prod g₂ :=
  rfl
/-
**ContinuousMultilinearMap.smul_prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：smul_prod_smul {S : Type*} [Monoid S] [DistribMulAction S M₂] [DistribMulA
ction S M₃] [ContinuousConstSMul S M₂] [SMulCommClass R S M₂] [ContinuousConstSM
ul S M₃] [SMulCommClass R S M₃] (c : S) (f : ContinuousMultilinearMap R M₁ M₂) (
g : ContinuousMultilinearMap R M₁ M₃) : (c • f).prod (c • g) = c • f.prod g
参数：c : S；f : ContinuousMultilinearMap R M₁ M₂；g : ContinuousMultilinearMap R M₁ 
M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_prod_smul {S : Type*} [Monoid S] [DistribMulAction S M₂] [DistribMulAction S M₃]
    [ContinuousConstSMul S M₂] [SMulCommClass R S M₂]
    [ContinuousConstSMul S M₃] [SMulCommClass R S M₃]
    (c : S) (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    (c • f).prod (c • g) = c • f.prod g :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.zero_prod_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：zero_prod_zero : (0 : ContinuousMultilinearMap R M₁ M₂).prod (0 : Continuo
usMultilinearMap R M₁ M₃) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_prod_zero :
    (0 : ContinuousMultilinearMap R M₁ M₂).prod (0 : ContinuousMultilinearMap R M₁ M₃) = 0 :=
  rfl

/-- `ContinuousMultilinearMap.pi` as an `Equiv`. -/
@[simps]
/-
**ContinuousMultilinearMap.piEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilin
earMap`。
形式化陈述：piEquiv {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [
forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] : (forall i, Cont
inuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (forall i, M' 
i) where toFun
参数：M' i；M' i；M' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.pi` as an `Equiv`.
-/
def piEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] :
    (∀ i, ContinuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (∀ i, M' i) where
  toFun := ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] M' i).compContinuousMultilinearMap f

/-- An equivalence of the index set defines an equivalence between the spaces of continuous
multilinear maps. This is the forward map of this equivalence. -/
@[simps! toMultilinearMap apply]
nonrec def domDomCongr {ι' : Type*} (e : ι ≃ ι')
    (f : ContinuousMultilinearMap R (fun _ : ι => M₂) M₃) :
    ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toMultilinearMap := f.domDomCongr e
  cont := f.cont.comp <| continuous_pi fun _ => continuous_apply _

/-- An equivalence of the index set defines an equivalence between the spaces of continuous
multilinear maps. In case of normed spaces, this is a linear isometric equivalence, see
`ContinuousMultilinearMap.domDomCongrₗᵢ`. -/
@[simps]
/-
**ContinuousMultilinearMap.domDomCongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：domDomCongrEquiv {ι' : Type*} (e : ι ≃ ι') : ContinuousMultilinearMap R (f
un _ : ι => M₂) M₃ ≃ ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where toFu
n
参数：e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence of the index set defines an equivalence between the spaces of con
tinuous
multilinear maps. In case of normed spaces, this is a linear isometric equivalen
ce, see
`ContinuousMultilinearMap.domDomCongrₗᵢ`.
-/
def domDomCongrEquiv {ι' : Type*} (e : ι ≃ ι') :
    ContinuousMultilinearMap R (fun _ : ι => M₂) M₃ ≃
      ContinuousMultilinearMap R (fun _ : ι' => M₂) M₃ where
  toFun := domDomCongr e
  invFun := domDomCongr e.symm
  left_inv _ := ext fun _ => by simp
  right_inv _ := ext fun _ => by simp

section linearDeriv

variable [ContinuousAdd M₂] [DecidableEq ι] [Fintype ι] (x y : ∀ i, M₁ i)

/-- The derivative of a continuous multilinear map, as a continuous linear map
from `∀ i, M₁ i` to `M₂`; see `ContinuousMultilinearMap.hasFDerivAt`. -/
/-
**ContinuousMultilinearMap.linearDeriv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：linearDeriv : (forall i, M₁ i) ->L[R] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of a continuous multilinear map, as a continuous linear map
from `∀ i, M₁ i` to `M₂`; see `ContinuousMultilinearMap.hasFDerivAt`.
-/
def linearDeriv : (∀ i, M₁ i) →L[R] M₂ := ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)

@[simp]
/-
**ContinuousMultilinearMap.linearDeriv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：linearDeriv_apply : f.linearDeriv x y = ∑ i, f (Function.update x i (y i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MultilinearMap.toLinearMap_apply`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι 
→ Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoi
d (M₁ i)] [inst_2 : Ad…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearDeriv_apply : f.linearDeriv x y = ∑ i, f (Function.update x i (y i)) := by
  simp [linearDeriv, toContinuousLinearMap]

end linearDeriv

/-- In the specific case of continuous multilinear maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `(i : Fin (n+1)) → M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
/-
**ContinuousMultilinearMap.cons_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：cons_add (f : ContinuousMultilinearMap R M M₂) (m : forall i : Fin n, M i.
succ) (x y : M 0) : f (cons (x + y) m) = f (cons x m) + f (cons y m)
参数：f : ContinuousMultilinearMap R M M₂；m : forall i : Fin n, M i.succ；x y : M 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MultilinearMap.cons_add`：cons_add (f : MultilinearMap R M M₂) (m : foral
l i : Fin n, M i.succ) (x y : M 0) : f (cons (x + y) m) = f (cons x m) + f (cons
 y m)

--- 原说明 ---
In the specific case of continuous multilinear maps on spaces indexed by `Fin (n
+1)`, where one
can build an element of `(i : Fin (n+1)) → M i` using `cons`, one can express di
rectly the
additivity of a multilinear map along the first variable.
-/
theorem cons_add (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `(i : Fin (n+1)) → M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
/-
**ContinuousMultilinearMap.cons_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：cons_smul (f : ContinuousMultilinearMap R M M₂) (m : forall i : Fin n, M i
.succ) (c : R) (x : M 0) : f (cons (c • x) m) = c • f (cons x m)
参数：f : ContinuousMultilinearMap R M M₂；m : forall i : Fin n, M i.succ；c : R；x : 
M 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MultilinearMap.cons_smul`：cons_smul (f : MultilinearMap R M M₂) (m : for
all i : Fin n, M i.succ) (c : R) (x : M 0) : f (cons (c • x) m) = c • f (cons x 
m)

--- 原说明 ---
In the specific case of continuous multilinear maps on spaces indexed by `Fin (n
+1)`, where one
can build an element of `(i : Fin (n+1)) → M i` using `cons`, one can express di
rectly the
multiplicativity of a multilinear map along the first variable.
-/
theorem cons_smul (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (c : R)
    (x : M 0) : f (cons (c • x) m) = c • f (cons x m) :=
  f.toMultilinearMap.cons_smul m c x
/-
**ContinuousMultilinearMap.map_piecewise_add** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：map_piecewise_add [DecidableEq ι] (m m' : forall i, M₁ i) (t : Finset ι) :
 f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m')
参数：m m' : forall i, M₁ i；t : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_piecewise_add`：map_piecewise_add [DecidableEq ι] (m m
' : forall i, M₁ i) (t : Finset ι) : f (t.piecewise (m + m') m') = ∑ s in t.powe
rset, f (s.piecewise m…
-/
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
/-
**ContinuousMultilinearMap.map_add_univ** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：map_add_univ [DecidableEq ι] [Fintype ι] (m m' : forall i, M₁ i) : f (m + 
m') = ∑ s : Finset ι, f (s.piecewise m m')
参数：m m' : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_add_univ`：map_add_univ [DecidableEq ι] [Fintype ι] (m
 m' : forall i, M₁ i) : f (m + m') = ∑ s : Finset ι, f (s.piecewise m m')

--- 原说明 ---
Additivity of a continuous multilinear map along all coordinates at the same tim
e,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`.
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _

section ApplySum

open Fintype Finset

variable {α : ι → Type*} [Fintype ι] (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
/-
**ContinuousMultilinearMap.map_sum_finset** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：map_sum_finset [DecidableEq ι] : (f fun i => ∑ j in A i, g i j) = ∑ r in p
iFinset A, f fun i => g i (r i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] [Fintype ι
] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)

--- 原说明 ---
If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} g
ₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r
 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with resp
ect to each
coordinate.
-/
theorem map_sum_finset [DecidableEq ι] :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _

/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
/-
**ContinuousMultilinearMap.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilin
earMap`。
形式化陈述：map_sum [DecidableEq ι] [forall i, Fintype (α i)] : (f fun i => ∑ j, g i j
) = ∑ r : forall i, α i, f fun i => g i (r i)
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_sum`：map_sum [DecidableEq ι] [Fintype ι] [forall i, F
intype (α i)] : (f fun i => ∑ j, g i j) = ∑ r : forall i, α i, f fun i => g i (r
 i)

--- 原说明 ---
If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is 
the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This foll
ows from
multilinearity by expanding successively with respect to each coordinate.
-/
theorem map_sum [DecidableEq ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum _

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
/-
**ContinuousMultilinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultili
nearMap R M₁ M₂ where toMultilinearMap
参数：f : ContinuousMultilinearMap A M₁ M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…

--- 原说明 ---
Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algeb
ra over `R`
and their actions on all involved modules agree with the action of `R` on `A`.
-/
def restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultilinearMap R M₁ M₂ where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  cont := f.cont

@[simp]
/-
**ContinuousMultilinearMap.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMultilinearMap`。
形式化陈述：coe_restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ⇑(f.restrictS
calars R) = f
参数：f : ContinuousMultilinearMap A M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

end Semiring

section Ring

variable [Ring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] (f f' : ContinuousMultilinearMap R M₁ M₂)

@[simp]
/-
**ContinuousMultilinearMap.map_update_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：map_update_sub [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
 f (update m i (x - y)) = f (update m i x) - f (update m i y)
参数：m : forall i, M₁ i；i : ι；x y : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_sub`：map_update_sub [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f 
(update m i y)
-/
theorem map_update_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_update_sub _ _ _ _

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup M₂]

/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f => { -f.toMultilinearMap with cont := f.cont.neg }⟩
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f g => { f.toMultilinearMap - g.toMultilinearMap with cont := f.cont.sub g.cont }⟩
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (ContinuousMultilinearMap R M₁ M₂) := fast_instance%
  toMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**ContinuousMultilinearMap.neg_prod_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：neg_prod_neg [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsTopo
logicalAddGroup M₃] (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultil
inearMap R M₁ M₃) : (-f).prod (-g) = - f.prod g
参数：f : ContinuousMultilinearMap R M₁ M₂；g : ContinuousMultilinearMap R M₁ M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_prod_neg [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
    [IsTopologicalAddGroup M₃] (f : ContinuousMultilinearMap R M₁ M₂)
    (g : ContinuousMultilinearMap R M₁ M₃) : (-f).prod (-g) = - f.prod g :=
  rfl
/-
**ContinuousMultilinearMap.sub_prod_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：sub_prod_sub [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsTopo
logicalAddGroup M₃] (f₁ f₂ : ContinuousMultilinearMap R M₁ M₂) (g₁ g₂ : Continuo
usMultilinearMap R M₁ M₃) : (f₁ - f₂).prod (g₁ - g₂) = f₁.prod g₁ - f₂.prod g₂
参数：f₁ f₂ : ContinuousMultilinearMap R M₁ M₂；g₁ g₂ : ContinuousMultilinearMap R M
₁ M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_prod_sub [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
    [IsTopologicalAddGroup M₃] (f₁ f₂ : ContinuousMultilinearMap R M₁ M₂)
    (g₁ g₂ : ContinuousMultilinearMap R M₁ M₃) :
    (f₁ - f₂).prod (g₁ - g₂) = f₁.prod g₁ - f₂.prod g₂ :=
  rfl

end IsTopologicalAddGroup

end Ring

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  (f : ContinuousMultilinearMap R M₁ M₂)

/-
**ContinuousMultilinearMap.map_piecewise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：map_piecewise_smul [DecidableEq ι] (c : ι -> R) (m : forall i, M₁ i) (s : 
Finset ι) : f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m
参数：c : ι -> R；m : forall i, M₁ i；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_piecewise_smul`：map_piecewise_smul [DecidableEq ι] (c
 : ι -> R) (m : forall i, M₁ i) (s : Finset ι) : f (s.piecewise (fun i => c i • 
m i) m) = (∏ i in s, c …
-/
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i ∈ s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (fun i ↦ c i • m i)` as `(∏ i, c i) • f m`. -/
/-
**ContinuousMultilinearMap.map_smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：map_smul_univ [Fintype ι] (c : ι -> R) (m : forall i, M₁ i) : (f fun i => 
c i • m i) = (∏ i, c i) • f m
参数：c : ι -> R；m : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m

--- 原说明 ---
Multiplicativity of a continuous multilinear map along all coordinates at the sa
me time,
writing `f (fun i ↦ c i • m i)` as `(∏ i, c i) • f m`.
-/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _

/-- If two continuous `R`-multilinear maps from `R` are equal on 1, then they are equal.

This is the multilinear version of `ContinuousLinearMap.ext_ring`. -/
@[ext]
/-
**ContinuousMultilinearMap.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：ext_ring [Finite ι] [TopologicalSpace R] ⦃f g : ContinuousMultilinearMap R
 (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.toMultilinearMap_injective`：∀ {R : Type u} {ι :
 Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : 
ι) → AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `MultilinearMap.ext_ring`：ext_ring [Finite ι] ⦃f g : MultilinearMap R (fu
n _ : ι => R) M₂⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g

--- 原说明 ---
If two continuous `R`-multilinear maps from `R` are equal on 1, then they are eq
ual.

This is the multilinear version of `ContinuousLinearMap.ext_ring`.
-/
theorem ext_ring [Finite ι] [TopologicalSpace R]
    ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g :=
  toMultilinearMap_injective <| MultilinearMap.ext_ring h

end CommSemiring

section DistribMulAction

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [∀ i, AddCommMonoid (M₁ i)]
  [AddCommMonoid M₂] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribMulAction R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]

/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

variable {R' A : Type*} [Semiring R'] [Semiring A] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [ContinuousAdd M₂] [∀ i, Module A (M₁ i)]
  [Module A M₂] [Module R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]

/-- The space of continuous multilinear maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous multilinear maps over an algebra over `R` is a module ov
er `R`, for the
pointwise addition and scalar multiplication.
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
/-
**ContinuousMultilinearMap.toMultilinearMapLinear** 是 Mathlib 中的一个定义，位于命名空间 `Con
tinuousMultilinearMap`。
形式化陈述：toMultilinearMapLinear : ContinuousMultilinearMap A M₁ M₂ ->ₗ[R'] Multilin
earMap A M₁ M₂ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.toMultilinearMap_add`：toMultilinearMap_add (f g
 : ContinuousMultilinearMap R M₁ M₂) : (f + g).toMultilinearMap = f.toMultilinea
rMap + g.toMultilinearMap

--- 原说明 ---
Linear map version of the map `toMultilinearMap` associating to a continuous mul
tilinear map
the corresponding multilinear map.
-/
def toMultilinearMapLinear : ContinuousMultilinearMap A M₁ M₂ →ₗ[R'] MultilinearMap A M₁ M₂ where
  toFun := toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul

/-- `ContinuousMultilinearMap.pi` as a `LinearEquiv`. -/
@[simps +simpRhs]
/-
**ContinuousMultilinearMap.piLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：piLinearEquiv {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M'
 i)] [forall i, TopologicalSpace (M' i)] [forall i, ContinuousAdd (M' i)] [foral
l i, Module R' (M' i)] [forall i, Module A (M' i)] [forall i, SMulCommClass A R'
 (M' i)] [forall i, ContinuousConstSMul R' (M' i)] : (forall i, ContinuousMultil
inearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (forall i, M' i)
参数：M' i；M' i；M' i；M' i；M' i；M' i；M' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.pi` as a `LinearEquiv`.
-/
def piLinearEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R' (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R' (M' i)] [∀ i, ContinuousConstSMul R' (M' i)] :
    (∀ i, ContinuousMultilinearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (∀ i, M' i) :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end Module


section Algebra

variable (R n) (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [ContinuousMul A]

/-- The continuous multilinear map on `A^n`, where `A` is a normed algebra over `𝕜`, associating to
`m` the product of all the `m i`.

See also: `ContinuousMultilinearMap.mkPiAlgebra`. -/
/-
**ContinuousMultilinearMap.mkPiAlgebraFin** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：(R : Type u) →   (n : ℕ) →     (A : Type u_1) →       [inst : CommSemiring
 R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A] → [inst_3
 : TopologicalSpace A] → [ContinuousMul A] → A [×n]→L[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous multilinear map on `A^n`, where `A` is a normed algebra over `𝕜`,
 associating to
`m` the product of all the `m i`.

See also: `ContinuousMultilinearMap.mkPiAlgebra`.
-/
protected def mkPiAlgebraFin : A [×n]→L[R] A where
  cont := by
    change Continuous fun m => (List.ofFn m).prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A

variable {R n A}

@[simp]
/-
**ContinuousMultilinearMap.mkPiAlgebraFin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：mkPiAlgebraFin_apply (m : Fin n -> A) : ContinuousMultilinearMap.mkPiAlgeb
raFin R n A m = (List.ofFn m).prod
参数：m : Fin n -> A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    ContinuousMultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl

end Algebra

section CommAlgebra

variable (R ι) (A : Type*) [Fintype ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A]

/-- The continuous multilinear map on `A^ι`, where `A` is a normed commutative algebra
over `𝕜`, associating to `m` the product of all the `m i`.

See also `ContinuousMultilinearMap.mkPiAlgebraFin`. -/
/-
**ContinuousMultilinearMap.mkPiAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：(R : Type u) →   (ι : Type v) →     (A : Type u_1) →       [Fintype ι] →  
       [inst : CommSemiring R] →           [inst_1 : CommSemiring A] →          
   [inst_2 : Algebra R A] →               [inst_3 : TopologicalSpace A] → [Conti
nuousMul A] → ContinuousMultilinearMap R (fun x => A) A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous multilinear map on `A^ι`, where `A` is a normed commutative algeb
ra
over `𝕜`, associating to `m` the product of all the `m i`.

See also `ContinuousMultilinearMap.mkPiAlgebraFin`.
-/
protected def mkPiAlgebra : ContinuousMultilinearMap R (fun _ : ι => A) A where
  cont := continuous_finsetProd _ fun _ _ => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A

@[simp]
/-
**ContinuousMultilinearMap.mkPiAlgebra_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：mkPiAlgebra_apply (m : ι -> A) : ContinuousMultilinearMap.mkPiAlgebra R ι 
A m = ∏ i, m i
参数：m : ι -> A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkPiAlgebra_apply (m : ι → A) : ContinuousMultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl
/-
**ContinuousMultilinearMap.mkPiAlgebra_eq_mkPiAlgebraFin** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousMultilinearMap`。
形式化陈述：mkPiAlgebra_eq_mkPiAlgebraFin {n : Nat} : ContinuousMultilinearMap.mkPiAlg
ebra R (Fin n) A = ContinuousMultilinearMap.mkPiAlgebraFin R n A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_ofFn`：prod_ofFn {n : Nat} {f : Fin n -> M} : (ofFn f).prod = ∏
 i, f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkPiAlgebra_eq_mkPiAlgebraFin {n : ℕ} : ContinuousMultilinearMap.mkPiAlgebra R (Fin n) A
    = ContinuousMultilinearMap.mkPiAlgebraFin R n A := by
  ext
  simp [List.prod_ofFn]

end CommAlgebra

section SMulRight

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] [TopologicalSpace R] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  [ContinuousSMul R M₂] (f : ContinuousMultilinearMap R M₁ R) (z : M₂)

/-- Given a continuous `R`-multilinear map `f` taking values in `R`, `f.smulRight z` is the
continuous multilinear map sending `m` to `f m • z`. -/
@[simps! toMultilinearMap apply]
/-
**ContinuousMultilinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：smulRight : ContinuousMultilinearMap R M₁ M₂ where toMultilinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous `R`-multilinear map `f` taking values in `R`, `f.smulRight z`
 is the
continuous multilinear map sending `m` to `f m • z`.
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
/-- The canonical continuous multilinear map on `R^ι`, associating to `m` the product of all the
`m i` (multiplied by a fixed reference element `z` in the target module) -/
/-
**ContinuousMultilinearMap.mkPiRing** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：(R : Type u) →   (ι : Type v) →     {M : Type u_1} →       [Fintype ι] →  
       [inst : CommRing R] →           [inst_1 : AddCommMonoid M] →             
[inst_2 : _root_.Module R M] →               [inst_3 : TopologicalSpace R] →    
             [inst_4 : TopologicalSpace M] →                   [ContinuousMul R]
 → [ContinuousSMul R M] → M → ContinuousMultilinearMap R (fun x => R) M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical continuous multilinear map on `R^ι`, associating to `m` the produc
t of all the
`m i` (multiplied by a fixed reference element `z` in the target module)
-/
protected def mkPiRing (z : M) : ContinuousMultilinearMap R (fun _ : ι => R) M :=
  (ContinuousMultilinearMap.mkPiAlgebra R ι R).smulRight z


@[simp]
/-
**ContinuousMultilinearMap.mkPiRing_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：mkPiRing_apply (z : M) (m : ι -> R) : (ContinuousMultilinearMap.mkPiRing R
 ι z : (ι -> R) -> M) m = (∏ i, m i) • z
参数：z : M；m : ι -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkPiRing_apply (z : M) (m : ι → R) :
    (ContinuousMultilinearMap.mkPiRing R ι z : (ι → R) → M) m = (∏ i, m i) • z :=
  rfl
/-
**ContinuousMultilinearMap.mkPiRing_apply_one_eq_self** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：mkPiRing_apply_one_eq_self (f : ContinuousMultilinearMap R (fun _ : ι => R
) M) : ContinuousMultilinearMap.mkPiRing R ι (f fun _ => 1) = f
参数：f : ContinuousMultilinearMap R (fun _ : ι => R) M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.toMultilinearMap_injective`：∀ {R : Type u} {ι :
 Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : 
ι) → AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `MultilinearMap.mkPiRing_apply_one_eq_self`：mkPiRing_apply_one_eq_self [F
intype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) : MultilinearMap.mkPiRing R
 ι (f fun _ => 1) = f
-/
theorem mkPiRing_apply_one_eq_self (f : ContinuousMultilinearMap R (fun _ : ι => R) M) :
    ContinuousMultilinearMap.mkPiRing R ι (f fun _ => 1) = f :=
  toMultilinearMap_injective f.toMultilinearMap.mkPiRing_apply_one_eq_self
/-
**ContinuousMultilinearMap.mkPiRing_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：mkPiRing_eq_iff {z₁ z₂ : M} : ContinuousMultilinearMap.mkPiRing R ι z₁ = C
ontinuousMultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ContinuousMultilinearMap.toMultilinearMap_injective`：∀ {R : Type u} {ι :
 Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : 
ι) → AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `MultilinearMap.mkPiRing_eq_iff`：mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂}
 : MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂
-/
theorem mkPiRing_eq_iff {z₁ z₂ : M} :
    ContinuousMultilinearMap.mkPiRing R ι z₁ = ContinuousMultilinearMap.mkPiRing R ι z₂ ↔
      z₁ = z₂ := by
  rw [← toMultilinearMap_injective.eq_iff]
  exact MultilinearMap.mkPiRing_eq_iff
/-
**ContinuousMultilinearMap.mkPiRing_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：mkPiRing_zero : ContinuousMultilinearMap.mkPiRing R ι (0 : M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.mkPiRing_apply`：mkPiRing_apply (z : M) (m : ι -
> R) : (ContinuousMultilinearMap.mkPiRing R ι z : (ι -> R) -> M) m = (∏ i, m i) 
• z
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
-/
theorem mkPiRing_zero : ContinuousMultilinearMap.mkPiRing R ι (0 : M) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]
/-
**ContinuousMultilinearMap.mkPiRing_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：mkPiRing_eq_zero_iff (z : M) : ContinuousMultilinearMap.mkPiRing R ι z = 0
 ↔ z = 0
参数：z : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.mkPiRing_zero`：mkPiRing_zero : ContinuousMultil
inearMap.mkPiRing R ι (0 : M) = 0
· 使用定理 `ContinuousMultilinearMap.mkPiRing_eq_iff`：mkPiRing_eq_iff {z₁ z₂ : M} : 
ContinuousMultilinearMap.mkPiRing R ι z₁ = ContinuousMultilinearMap.mkPiRing R ι
 z₂ ↔ z₁ = z₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mkPiRing_eq_zero_iff (z : M) : ContinuousMultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero, mkPiRing_eq_iff]

end CommRing

end ContinuousMultilinearMap

