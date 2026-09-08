/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Dilation

/-!
# Normed rings

In this file we continue building the theory of (semi)normed rings.
-/

@[expose] public section

variable {α : Type*} {β : Type*} {ι : Type*}

open Filter Bornology
open scoped Topology NNReal Pointwise

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

/-
**Filter.Tendsto.zero_mul_isBoundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι -> α} {l : Filter ι} (h
f : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· <= ·) l ((‖·‖) ∘ g)) : Tendsto (f
un x => f x * g x) l (𝓝 0)
参数：hf : Tendsto f l (𝓝 0)；hg : IsBoundedUnder (· <= ·) l ((‖·‖) ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.op_zero_isBoundedUnder_le`：∀ {α : Type u_1} {E : Type u_2
} {F : Type u_3} {G : Type u_4} [inst : SeminormedAddGroup E]   [inst_1 : Semino
rmedAddGroup F] [inst_2 : Semi…
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι → α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l ((‖·‖) ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le
/-
**Filter.isBoundedUnder_le_mul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι -> α} {l : Filter ι} (h
f : IsBoundedUnder (· <= ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) : Tendsto (fu
n x => f x * g x) l (𝓝 0)
参数：hf : IsBoundedUnder (· <= ·) l (norm ∘ f)；hg : Tendsto g l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.op_zero_isBoundedUnder_le`：∀ {α : Type u_1} {E : Type u_2
} {F : Type u_3} {G : Type u_4} [inst : SeminormedAddGroup E]   [inst_1 : Semino
rmedAddGroup F] [inst_2 : Semi…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

open Finset in
/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
/-
**Pi.nonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.nonUnitalSeminormedRing {R : ι -> Type*} [Fintype ι] [forall i, NonUnit
alSeminormedRing (R i)] : NonUnitalSeminormedRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital seminormed ring structure on the product of finitely many non-unital 
seminormed
rings, using the sup norm.
-/
instance Pi.nonUnitalSeminormedRing {R : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedRing (R i)] : NonUnitalSeminormedRing (∀ i, R i) :=
  { seminormedAddCommGroup, nonUnitalRing with
    norm_mul_le x y := NNReal.coe_mono <| calc
      (univ.sup fun i ↦ ‖x i * y i‖₊) ≤ univ.sup ((‖x ·‖₊) * (‖y ·‖₊)) :=
        sup_mono_fun fun _ _ ↦ nnnorm_mul_le _ _
      _ ≤ (univ.sup (‖x ·‖₊)) * univ.sup (‖y ·‖₊) :=
        sup_mul_le_mul_sup_of_nonneg (fun _ _ ↦ zero_le) fun _ _ ↦ zero_le }

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
/-
**Pi.seminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.seminormedRing {R : ι -> Type*} [Fintype ι] [forall i, SeminormedRing (
R i)] : SeminormedRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm.
-/
instance Pi.seminormedRing {R : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (R i)] :
    SeminormedRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.ring with }
/-
**RingHom.isometry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂] (
σ : 𝕜₁ ->+* 𝕜₂) [RingHomIsometric σ] : Isometry σ
参数：σ : 𝕜₁ ->+* 𝕜₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHomIsometric.norm_map`：∀ {R₁ : Type u_5} {R₂ : Type u_6} {inst : Sem
iring R₁} {inst_1 : Semiring R₂} {inst_2 : Norm R₁} {inst_3 : Norm R₂}   {σ : R₁
 →+* R₂} [self …
-/
lemma RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) [RingHomIsometric σ] :
    Isometry σ := AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map

/-- If `σ` and `σ'` are mutually inverse, then one is `RingHomIsometric` if the other is. Not an
instance, as it would cause loops. -/
/-
**RingHomIsometric.inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜
₂] (σ : 𝕜₁ ->+* 𝕜₂) {σ' : 𝕜₂ ->+* 𝕜₁} [RingHomInvPair σ σ'] [RingHomIsometric σ]
 : RingHomIsometric σ'
参数：σ : 𝕜₁ ->+* 𝕜₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomIsometric.norm_map`：∀ {R₁ : Type u_5} {R₂ : Type u_6} {inst : Sem
iring R₁} {inst_1 : Semiring R₂} {inst_2 : Norm R₁} {inst_3 : Norm R₂}   {σ : R₁
 →+* R₂} [self …
· 使用定理 `RingHomInvPair.comp_apply_eq₂`：comp_apply_eq₂ {x : R₂} : σ (σ' x) = x

--- 原说明 ---
If `σ` and `σ'` are mutually inverse, then one is `RingHomIsometric` if the othe
r is. Not an
instance, as it would cause loops.
-/
lemma RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    RingHomIsometric σ' :=
  ⟨fun {x} ↦ by rw [← RingHomIsometric.norm_map (σ := σ), RingHomInvPair.comp_apply_eq₂]⟩
/-
**tendsto_pow_cobounded_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_pow_cobounded_cobounded [NormOneClass α] [NormMulClass α] {m : Nat
} (hm : m != 0) : Tendsto (· ^ m) (cobounded α) (cobounded α)
参数：hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `tendsto_norm_cobounded_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto norm (Bornology.cobounded E) Filter.atTop
-/
lemma tendsto_pow_cobounded_cobounded
    [NormOneClass α] [NormMulClass α] {m : ℕ} (hm : m ≠ 0) :
    Tendsto (· ^ m) (cobounded α) (cobounded α) := by
  simpa [← tendsto_norm_atTop_iff_cobounded] using!
    (tendsto_pow_atTop hm).comp (tendsto_norm_cobounded_atTop (E := α))

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
/-
**Pi.nonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.nonUnitalNormedRing {R : ι -> Type*} [Fintype ι] [forall i, NonUnitalNo
rmedRing (R i)] : NonUnitalNormedRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed ring structure on the product of finitely many non-unital normed rings, u
sing the sup
norm.
-/
instance Pi.nonUnitalNormedRing {R : ι → Type*} [Fintype ι] [∀ i, NonUnitalNormedRing (R i)] :
    NonUnitalNormedRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
/-
**Pi.normedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normedRing {R : ι -> Type*} [Fintype ι] [forall i, NormedRing (R i)] : 
NormedRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed ring structure on the product of finitely many normed rings, using the su
p norm.
-/
instance Pi.normedRing {R : ι → Type*} [Fintype ι] [∀ i, NormedRing (R i)] :
    NormedRing (∀ i, R i) :=
  { Pi.seminormedRing, Pi.normedAddCommGroup with }

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

/-- Non-unital seminormed commutative ring structure on the product of finitely many non-unital
seminormed commutative rings, using the sup norm. -/
/-
**Pi.nonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.nonUnitalSeminormedCommRing {R : ι -> Type*} [Fintype ι] [forall i, Non
UnitalSeminormedCommRing (R i)] : NonUnitalSeminormedCommRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital seminormed commutative ring structure on the product of finitely many
 non-unital
seminormed commutative rings, using the sup norm.
-/
instance Pi.nonUnitalSeminormedCommRing {R : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedCommRing (R i)] : NonUnitalSeminormedCommRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- Normed commutative ring structure on the product of finitely many non-unital normed
commutative rings, using the sup norm. -/
/-
**Pi.nonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.nonUnitalNormedCommRing {R : ι -> Type*} [Fintype ι] [forall i, NonUnit
alNormedCommRing (R i)] : NonUnitalNormedCommRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed commutative ring structure on the product of finitely many non-unital nor
med
commutative rings, using the sup norm.
-/
instance Pi.nonUnitalNormedCommRing {R : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalNormedCommRing (R i)] : NonUnitalNormedCommRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

/-- Seminormed commutative ring structure on the product of finitely many seminormed commutative
rings, using the sup norm. -/
/-
**Pi.seminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.seminormedCommRing {R : ι -> Type*} [Fintype ι] [forall i, SeminormedCo
mmRing (R i)] : SeminormedCommRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed commutative ring structure on the product of finitely many seminormed
 commutative
rings, using the sup norm.
-/
instance Pi.seminormedCommRing {R : ι → Type*} [Fintype ι] [∀ i, SeminormedCommRing (R i)] :
    SeminormedCommRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

end SeminormedCommRing

section NormedCommRing

variable [NormedCommRing α]

/-- Normed commutative ring structure on the product of finitely many normed commutative rings,
using the sup norm. -/
/-
**Pi.normedCommutativeRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normedCommutativeRing {R : ι -> Type*} [Fintype ι] [forall i, NormedCom
mRing (R i)] : NormedCommRing (forall i, R i)
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed commutative ring structure on the product of finitely many normed commuta
tive rings,
using the sup norm.
-/
instance Pi.normedCommutativeRing {R : ι → Type*} [Fintype ι] [∀ i, NormedCommRing (R i)] :
    NormedCommRing (∀ i, R i) :=
  { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

end NormedCommRing

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalSeminormedRing.toContinuousMul [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_sub_tendsto_zero.2 <| by
        have : ∀ e : α × α,
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [mul_sub, sub_mul, sub_add_sub_cancel]
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine squeeze_zero (fun e => norm_nonneg _) this ?_
        convert!
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul tendsto_const_nhds)
        simp⟩

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminormed ring is a topological ring.
-/
instance (priority := 100) NonUnitalSeminormedRing.toIsTopologicalRing [NonUnitalSeminormedRing α] :
    IsTopologicalRing α where

namespace SeparationQuotient

/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSeminormedRing α] : NonUnitalNormedRing (SeparationQuotient α) where
  __ : NonUnitalRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSeminormedCommRing α] : NonUnitalNormedCommRing (SeparationQuotient α) where
  __ : NonUnitalCommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeminormedRing α] : NormedRing (SeparationQuotient α) where
  __ : Ring (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeminormedCommRing α] : NormedCommRing (SeparationQuotient α) where
  __ : CommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (SeparationQuotient α) where
  norm_one := norm_one (α := α)

end SeparationQuotient

namespace NNReal

/-
**NNReal.lipschitzWith_sub** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：lipschitzWith_sub : LipschitzWith 2 (fun (p : Real>=0 × Real>=0) => p.1 - 
p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Isometry.lipschitzWith_iff`：Isometry.lipschitzWith_iff {α β γ : Type*} [
PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : α -> β}
 {g : β -> γ} (K…
· 使用定理 `NNReal.isometry_coe`：Isometry NNReal.toReal
· 使用定理 `Isometry.prodMap`：prodMap {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ
 -> δ} (hf : Isometry f) (hg : Isometry g) : Isometry (Prod.map f g)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LipschitzWith.max_const`：max_const (hf : LipschitzWith Kf f) (a : Real) 
: LipschitzWith Kf fun x => max (f x) a
· 使用定理 `LipschitzWith.sub`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] [inst_1 : PseudoEMetricSpace α] {Kf Kg : NNReal}   {f g : α → E}, L
ipschit…
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `LipschitzWith.prod_fst`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.fst
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `LipschitzWith.prod_snd`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.snd
-/
lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : ℝ≥0 × ℝ≥0) ↦ p.1 - p.2) := by
  rw [← NNReal.isometry_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : ℝ≥0 → ℝ) ((↑) : ℝ≥0 → ℝ)) :=
    NNReal.isometry_coe.prodMap NNReal.isometry_coe
  convert!
    (((LipschitzWith.prod_fst.comp this.lipschitz).sub
          (LipschitzWith.prod_snd.comp this.lipschitz)).max_const
      0)
  norm_num

end NNReal

/-
**Int.instNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instNormedCommRing : NormedCommRing Int where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedAddCommGroup 
E] (x y : E), dist x y = ‖-x + y‖
· 使用定理 `CommRing.mul_comm`：∀ {α : Type u} [self : CommRing α] (a b : α), a * b =
 b * a
-/
instance Int.instNormedCommRing : NormedCommRing ℤ where
  __ := instCommRing
  __ := instNormedAddCommGroup
  norm_mul_le m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]
/-
**Int.instNormOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instNormOneClass : NormOneClass Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Int.instNormOneClass : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩
/-
**Int.instNormMulClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instNormMulClass : NormMulClass Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Int.instNormMulClass : NormMulClass ℤ :=
  ⟨fun a b ↦ by simp [← Int.norm_cast_real, abs_mul]⟩

section NonUnitalNormedRing
variable [NonUnitalNormedRing α] [NormMulClass α] {a : α}

/-
**antilipschitzWith_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antilipschitzWith_mul_left {a : α} (ha : a != 0) : AntilipschitzWith (‖a‖₊
⁻¹) (a * ·)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma antilipschitzWith_mul_left {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (a * ·) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by simp [dist_eq_norm, ← mul_sub, ha]
/-
**antilipschitzWith_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antilipschitzWith_mul_right {a : α} (ha : a != 0) : AntilipschitzWith (‖a‖
₊⁻¹) (· * a)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma antilipschitzWith_mul_right {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (· * a) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by simp [dist_eq_norm, ← sub_mul, mul_comm, ha]

/-- Multiplication by a nonzero element `a` on the left, as a `Dilation` of a ring with a strictly
multiplicative norm. -/
@[simps!]
/-
**Dilation.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Dilation.mulLeft (a : α) (ha : a != 0) : α ->ᵈ α where toFun b
参数：a : α；ha : a != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication by a nonzero element `a` on the left, as a `Dilation` of a ring w
ith a strictly
multiplicative norm.
-/
def Dilation.mulLeft (a : α) (ha : a ≠ 0) : α →ᵈ α where
  toFun b := a * b
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

/-- Multiplication by a nonzero element `a` on the right, as a `Dilation` of a ring with a strictly
multiplicative norm. -/
@[simps!]
/-
**Dilation.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Dilation.mulRight (a : α) (ha : a != 0) : α ->ᵈ α where toFun b
参数：a : α；ha : a != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication by a nonzero element `a` on the right, as a `Dilation` of a ring 
with a strictly
multiplicative norm.
-/
def Dilation.mulRight (a : α) (ha : a ≠ 0) : α →ᵈ α where
  toFun b := b * a
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

namespace Filter

@[simp]
/-
**Filter.comap_mul_left_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：comap_mul_left_cobounded {a : α} (ha : a != 0) : comap (a * ·) (cobounded 
α) = cobounded α
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Dilation.comap_cobounded`：comap_cobounded : Filter.comap f (cobounded β)
 = cobounded α
-/
lemma comap_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    comap (a * ·) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (Dilation.mulLeft a ha)

@[simp]
/-
**Filter.comap_mul_right_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：comap_mul_right_cobounded {a : α} (ha : a != 0) : comap (· * a) (cobounded
 α) = cobounded α
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Dilation.comap_cobounded`：comap_cobounded : Filter.comap f (cobounded β)
 = cobounded α
-/
lemma comap_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    comap (· * a) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (Dilation.mulRight a ha)

end Filter

end NonUnitalNormedRing

