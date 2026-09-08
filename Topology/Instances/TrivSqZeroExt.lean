/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Topology on `TrivSqZeroExt R M`

The type `TrivSqZeroExt R M` inherits the topology from `R × M`.

Note that this is not the topology induced by the seminorm on the dual numbers suggested by
[this Math.SE answer](https://math.stackexchange.com/a/1056378/1896), which instead induces
the topology pulled back through the projection map `TrivSqZeroExt.fst : tsze R M → R`.
Obviously, that topology is not Hausdorff and using it would result in `exp` converging to more than
one value.

## Main results

* `TrivSqZeroExt.topologicalRing`: the ring operations are continuous

-/

@[expose] public section

open Topology

variable {α S R M : Type*}

local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Topology

variable [TopologicalSpace R] [TopologicalSpace M]

/-
**TrivSqZeroExt.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instTopologicalSpace : TopologicalSpace (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace : TopologicalSpace (tsze R M) :=
  TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space R] [T2Space M] : T2Space (tsze R M) :=
  Prod.t2Space
/-
**TrivSqZeroExt.nhds_def** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：nhds_def (x : tsze R M) : 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.snd
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
-/
theorem nhds_def (x : tsze R M) : 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.snd := nhds_prod_eq
/-
**TrivSqZeroExt.nhds_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：nhds_inl [Zero M] (x : R) : 𝓝 (inl x : tsze R M) = 𝓝 x ×ˢ 𝓝 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.nhds_def`：nhds_def (x : tsze R M) : 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.s
nd
-/
theorem nhds_inl [Zero M] (x : R) : 𝓝 (inl x : tsze R M) = 𝓝 x ×ˢ 𝓝 0 :=
  nhds_def _
/-
**TrivSqZeroExt.nhds_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：nhds_inr [Zero R] (m : M) : 𝓝 (inr m : tsze R M) = 𝓝 0 ×ˢ 𝓝 m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.nhds_def`：nhds_def (x : tsze R M) : 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.s
nd
-/
theorem nhds_inr [Zero R] (m : M) : 𝓝 (inr m : tsze R M) = 𝓝 0 ×ˢ 𝓝 m :=
  nhds_def _

nonrec theorem continuous_fst : Continuous (fst : tsze R M → R) :=
  continuous_fst

nonrec theorem continuous_snd : Continuous (snd : tsze R M → M) :=
  continuous_snd
/-
**TrivSqZeroExt.continuous_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：continuous_inl [Zero M] : Continuous (inl : R -> tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_inl [Zero M] : Continuous (inl : R → tsze R M) :=
  continuous_id.prodMk continuous_const
/-
**TrivSqZeroExt.continuous_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：continuous_inr [Zero R] : Continuous (inr : M -> tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_inr [Zero R] : Continuous (inr : M → tsze R M) :=
  continuous_const.prodMk continuous_id
/-
**TrivSqZeroExt.IsEmbedding.inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt.IsEmbed
ding`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst_1 : Topo
logicalSpace M] [inst_2 : Zero M],   Topology.IsEmbedding TrivSqZeroExt.inl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `TrivSqZeroExt.continuous_inl`：continuous_inl [Zero M] : Continuous (inl 
: R -> tsze R M)
· 使用定理 `TrivSqZeroExt.continuous_fst`：∀ {R : Type u_3} {M : Type u_4} [inst : To
pologicalSpace R] [inst_1 : TopologicalSpace M], Continuous TrivSqZeroExt.fst
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
-/
theorem IsEmbedding.inl [Zero M] : IsEmbedding (inl : R → tsze R M) :=
  .of_comp continuous_inl continuous_fst .id
/-
**TrivSqZeroExt.IsEmbedding.inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt.IsEmbed
ding`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst_1 : Topo
logicalSpace M] [inst_2 : Zero R],   Topology.IsEmbedding TrivSqZeroExt.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `TrivSqZeroExt.continuous_inr`：continuous_inr [Zero R] : Continuous (inr 
: M -> tsze R M)
· 使用定理 `TrivSqZeroExt.continuous_snd`：∀ {R : Type u_3} {M : Type u_4} [inst : To
pologicalSpace R] [inst_1 : TopologicalSpace M], Continuous TrivSqZeroExt.snd
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
-/
theorem IsEmbedding.inr [Zero R] : IsEmbedding (inr : M → tsze R M) :=
  .of_comp continuous_inr continuous_snd .id

variable (R M)

/-- `TrivSqZeroExt.fst` as a continuous linear map. -/
@[simps]
/-
**TrivSqZeroExt.fstCLM** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fstCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : StrongDual R (tsz
e R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TrivSqZeroExt.fst` as a continuous linear map.
-/
def fstCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : StrongDual R (tsze R M) :=
  { ContinuousLinearMap.fst R R M with toFun := fst }

/-- `TrivSqZeroExt.snd` as a continuous linear map. -/
@[simps]
/-
**TrivSqZeroExt.sndCLM** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：sndCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M ->L[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TrivSqZeroExt.snd` as a continuous linear map.
-/
def sndCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] M :=
  { ContinuousLinearMap.snd R R M with toFun := snd }

/-- `TrivSqZeroExt.inl` as a continuous linear map. -/
@[simps]
/-
**TrivSqZeroExt.inlCLM** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inlCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : R ->L[R] tsze R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TrivSqZeroExt.inl` as a continuous linear map.
-/
def inlCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : R →L[R] tsze R M :=
  { ContinuousLinearMap.inl R R M with toFun := inl }

/-- `TrivSqZeroExt.inr` as a continuous linear map. -/
@[simps]
/-
**TrivSqZeroExt.inrCLM** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inrCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : M ->L[R] tsze R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TrivSqZeroExt.inr` as a continuous linear map.
-/
def inrCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : M →L[R] tsze R M :=
  { ContinuousLinearMap.inr R R M with toFun := inr }

variable {R M}
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [Add M] [ContinuousAdd R] [ContinuousAdd M] : ContinuousAdd (tsze R M) :=
  Prod.continuousAdd
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousMul R] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] [ContinuousAdd M] : ContinuousMul (tsze R M) :=
  ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prodMk <|
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Neg R] [Neg M] [ContinuousNeg R] [ContinuousNeg M] : ContinuousNeg (tsze R M) :=
  Prod.continuousNeg

/-- This is not an instance due to complaints by the `fails_quickly` linter. At any rate, we only
really care about the `IsTopologicalRing` instance below. -/
/-
**TrivSqZeroExt.topologicalSemiring** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：topologicalSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐ
ᵒᵖ M] [IsTopologicalSemiring R] [ContinuousAdd M] [ContinuousSMul R M] [Continuo
usSMul Rᵐᵒᵖ M] : IsTopologicalSemiring (tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instContinuousAdd`：∀ {R : Type u_3} {M : Type u_4} [inst :
 TopologicalSpace R] [inst_1 : TopologicalSpace M] [inst_2 : Add R]   [inst_3 : 
Add M] [ContinuousAdd…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `TrivSqZeroExt.instContinuousMulOfContinuousSMulMulOppositeOfContinuousAd
d`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst_1 : Topolog
icalSpace M] [inst_2 : Mul R]   [inst_3 : Add M] [inst_4 : SMul…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R

--- 原说明 ---
This is not an instance due to complaints by the `fails_quickly` linter. At any 
rate, we only
really care about the `IsTopologicalRing` instance below.
-/
theorem topologicalSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsTopologicalSemiring R] [ContinuousAdd M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    IsTopologicalSemiring (tsze R M) := { }
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsTopologicalRing R]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    IsTopologicalRing (tsze R M) where
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S R] [SMul S M] [ContinuousConstSMul S R] [ContinuousConstSMul S M] :
    ContinuousConstSMul S (tsze R M) :=
  Prod.continuousConstSMul
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace S] [SMul S R] [SMul S M] [ContinuousSMul S R] [ContinuousSMul S M] :
    ContinuousSMul S (tsze R M) :=
  Prod.continuousSMul

variable (M)
/-
**TrivSqZeroExt.hasSum_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：hasSum_inl [AddCommMonoid R] [AddCommMonoid M] {f : α -> R} {a : R} (h : H
asSum f a) : HasSum (fun x => inl (f x)) (inl a : tsze R M)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `TrivSqZeroExt.inl_zero`：inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) 
= 0
· 使用定理 `TrivSqZeroExt.inl_add`：inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) : (i
nl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂
· 使用定理 `TrivSqZeroExt.continuous_inl`：continuous_inl [Zero M] : Continuous (inl 
: R -> tsze R M)
-/
theorem hasSum_inl [AddCommMonoid R] [AddCommMonoid M] {f : α → R} {a : R} (h : HasSum f a) :
    HasSum (fun x ↦ inl (f x)) (inl a : tsze R M) :=
  h.map (⟨⟨inl, inl_zero _⟩, inl_add _⟩ : R →+ tsze R M) continuous_inl
/-
**TrivSqZeroExt.hasSum_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：hasSum_inr [AddCommMonoid R] [AddCommMonoid M] {f : α -> M} {a : M} (h : H
asSum f a) : HasSum (fun x => inr (f x)) (inr a : tsze R M)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `TrivSqZeroExt.inr_zero`：inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) 
= 0
· 使用定理 `TrivSqZeroExt.inr_add`：inr_add [AddZeroClass R] [Add M] (m₁ m₂ : M) : (i
nr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂
· 使用定理 `TrivSqZeroExt.continuous_inr`：continuous_inr [Zero R] : Continuous (inr 
: M -> tsze R M)
-/
theorem hasSum_inr [AddCommMonoid R] [AddCommMonoid M] {f : α → M} {a : M} (h : HasSum f a) :
    HasSum (fun x ↦ inr (f x)) (inr a : tsze R M) :=
  h.map (⟨⟨inr, inr_zero _⟩, inr_add _⟩ : M →+ tsze R M) continuous_inr
/-
**TrivSqZeroExt.hasSum_fst** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：hasSum_fst [AddCommMonoid R] [AddCommMonoid M] {f : α -> tsze R M} {a : ts
ze R M} (h : HasSum f a) : HasSum (fun x => fst (f x)) (fst a)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `TrivSqZeroExt.fst_zero`：fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst 
= 0
· 使用定理 `TrivSqZeroExt.fst_add`：fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ 
+ x₂).fst = x₁.fst + x₂.fst
· 使用定理 `TrivSqZeroExt.continuous_fst`：∀ {R : Type u_3} {M : Type u_4} [inst : To
pologicalSpace R] [inst_1 : TopologicalSpace M], Continuous TrivSqZeroExt.fst
-/
theorem hasSum_fst [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x ↦ fst (f x)) (fst a) :=
  h.map (⟨⟨fst, fst_zero⟩, fst_add⟩ : tsze R M →+ R) continuous_fst
/-
**TrivSqZeroExt.hasSum_snd** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：hasSum_snd [AddCommMonoid R] [AddCommMonoid M] {f : α -> tsze R M} {a : ts
ze R M} (h : HasSum f a) : HasSum (fun x => snd (f x)) (snd a)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `TrivSqZeroExt.snd_zero`：snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd 
= 0
· 使用定理 `TrivSqZeroExt.snd_add`：snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ 
+ x₂).snd = x₁.snd + x₂.snd
· 使用定理 `TrivSqZeroExt.continuous_snd`：∀ {R : Type u_3} {M : Type u_4} [inst : To
pologicalSpace R] [inst_1 : TopologicalSpace M], Continuous TrivSqZeroExt.snd
-/
theorem hasSum_snd [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x ↦ snd (f x)) (snd a) :=
  h.map (⟨⟨snd, snd_zero⟩, snd_add⟩ : tsze R M →+ M) continuous_snd

end Topology

section Uniformity
variable [UniformSpace R] [UniformSpace M]

/-
**TrivSqZeroExt.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instUniformSpace : UniformSpace (tsze R M) where toTopologicalSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (tsze R M) where
  toTopologicalSpace := instTopologicalSpace
  __ := instUniformSpaceProd
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace R] [CompleteSpace M] : CompleteSpace (tsze R M) :=
  inferInstanceAs <| CompleteSpace (R × M)
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup R] [AddGroup M] [IsUniformAddGroup R] [IsUniformAddGroup M] :
    IsUniformAddGroup (tsze R M) :=
  inferInstanceAs <| IsUniformAddGroup (R × M)

open Uniformity
/-
**TrivSqZeroExt.uniformity_def** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：uniformity_def : 𝓤 (tsze R M) = ((𝓤 R).comap fun p => (p.1.fst, p.2.fst)) 
⊓ ((𝓤 M).comap fun p => (p.1.snd, p.2.snd))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_def :
    𝓤 (tsze R M) =
      ((𝓤 R).comap fun p => (p.1.fst, p.2.fst)) ⊓ ((𝓤 M).comap fun p => (p.1.snd, p.2.snd)) :=
  rfl

nonrec theorem uniformContinuous_fst : UniformContinuous (fst : tsze R M → R) :=
  uniformContinuous_fst

nonrec theorem uniformContinuous_snd : UniformContinuous (snd : tsze R M → M) :=
  uniformContinuous_snd
/-
**TrivSqZeroExt.uniformContinuous_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：uniformContinuous_inl [Zero M] : UniformContinuous (inl : R -> tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
-/
theorem uniformContinuous_inl [Zero M] : UniformContinuous (inl : R → tsze R M) :=
  uniformContinuous_id.prodMk uniformContinuous_const
/-
**TrivSqZeroExt.uniformContinuous_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：uniformContinuous_inr [Zero R] : UniformContinuous (inr : M -> tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_inr [Zero R] : UniformContinuous (inr : M → tsze R M) :=
  uniformContinuous_const.prodMk uniformContinuous_id

end Uniformity

end TrivSqZeroExt

