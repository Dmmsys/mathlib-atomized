/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.MulAction

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/

@[expose] public section

variable {𝕜 𝕜' E F α : Type*}

open Filter Metric Function Set Topology Bornology
open scoped NNReal ENNReal uniformity

section SeminormedAddCommGroup

/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definition, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `SeminormedAddCommGroup` and not `NormedAddCommGroup`, this
typeclass can be used for "seminormed spaces" too, just as `Module` can be used for
"semimodules". -/
@[ext]
/-
**NormedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_6) → (E : Type u_7) → [NormedField 𝕜] → [SeminormedAddCommGrou
p E] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed space over a normed field is a vector space endowed with a norm which s
atisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definit
ion, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `SeminormedAddCommGroup` and not `NormedAddCommGro
up`, this
typeclass can be used for "seminormed spaces" too, just as `Module` can be used 
for
"semimodules".
-/
class NormedSpace (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E]
    extends Module 𝕜 E where
  protected norm_smul_le : ∀ (a : 𝕜) (b : E), ‖a • b‖ ≤ ‖a‖ * ‖b‖

attribute [inherit_doc NormedSpace] NormedSpace.norm_smul_le

variable [NormedField 𝕜] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedSpace.toNormSMulClass : NormSMulClass 𝕜 E :=
  haveI : IsBoundedSMul 𝕜 E := .of_norm_smul_le NormedSpace.norm_smul_le
  NormedDivisionRing.toNormSMulClass

/-- This is a shortcut instance, which was found to help with performance in
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Normed.20modules/near/516757412.

It is implied via `NormedSpace.toNormSMulClass`. -/
/-
**NormedSpace.toIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedSpace.toIsBoundedSMul : IsBoundedSMul 𝕜 E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E

--- 原说明 ---
This is a shortcut instance, which was found to help with performance in
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Normed.20
modules/near/516757412.

It is implied via `NormedSpace.toNormSMulClass`.
-/
instance NormedSpace.toIsBoundedSMul : IsBoundedSMul 𝕜 E := inferInstance
/-
**NormedField.toNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedField.toNormedSpace : NormedSpace 𝕜 𝕜 where norm_smul_le a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NormedField.toNormedSpace : NormedSpace 𝕜 𝕜 where norm_smul_le a b := norm_mul_le a b

variable (𝕜) in
/-
**norm_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_zsmul (n : Int) (x : E) : ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖
参数：n : Int；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Int.smul_one_eq_cast`：Int.smul_one_eq_cast {R : Type*} [NonAssocRing R] 
(m : Int) : m • (1 : R) = ↑m
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem norm_zsmul (n : ℤ) (x : E) : ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖ := by
  rw [← norm_smul, ← Int.smul_one_eq_cast, smul_assoc, one_smul]
/-
**norm_intCast_eq_abs_mul_norm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_intCast_eq_abs_mul_norm_one (α) [SeminormedRing α] [NormSMulClass Int
 α] (n : Int) : ‖(n : α)‖ = |n| * ‖(1 : α)‖
参数：α；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `Int.norm_eq_abs`：norm_eq_abs (n : Int) : ‖n‖ = |(n : Real)|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
-/
theorem norm_intCast_eq_abs_mul_norm_one (α) [SeminormedRing α] [NormSMulClass ℤ α] (n : ℤ) :
    ‖(n : α)‖ = |n| * ‖(1 : α)‖ := by
  rw [← zsmul_one, norm_smul, Int.norm_eq_abs, Int.cast_abs]
/-
**norm_natCast_eq_mul_norm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_natCast_eq_mul_norm_one (α) [SeminormedRing α] [NormSMulClass Int α] 
(n : Nat) : ‖(n : α)‖ = n * ‖(1 : α)‖
参数：α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `norm_intCast_eq_abs_mul_norm_one`：norm_intCast_eq_abs_mul_norm_one (α) [
SeminormedRing α] [NormSMulClass Int α] (n : Int) : ‖(n : α)‖ = |n| * ‖(1 : α)‖
-/
theorem norm_natCast_eq_mul_norm_one (α) [SeminormedRing α] [NormSMulClass ℤ α] (n : ℕ) :
    ‖(n : α)‖ = n * ‖(1 : α)‖ := by
  simpa using norm_intCast_eq_abs_mul_norm_one α n

@[simp]
/-
**norm_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_natCast {α : Type*} [SeminormedRing α] [NormOneClass α] [NormSMulClas
s Int α] (a : Nat) : ‖(a : α)‖ = a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_natCast_eq_mul_norm_one`：norm_natCast_eq_mul_norm_one (α) [Seminorm
edRing α] [NormSMulClass Int α] (n : Nat) : ‖(n : α)‖ = n * ‖(1 : α)‖
-/
lemma norm_natCast {α : Type*} [SeminormedRing α] [NormOneClass α] [NormSMulClass ℤ α]
    (a : ℕ) : ‖(a : α)‖ = a := by
  simpa using norm_natCast_eq_mul_norm_one α a
/-
**eventually_nhds_norm_smul_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhds_norm_smul_sub_lt (c : 𝕜) (x : E) {ε : Real} (h : 0 < ε) : 
forallᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε
参数：c : 𝕜；x : E；h : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem eventually_nhds_norm_smul_sub_lt (c : 𝕜) (x : E) {ε : ℝ} (h : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε :=
  have : Tendsto (fun y ↦ ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  this.eventually (gt_mem_nhds h)
/-
**Filter.Tendsto.zero_smul_isBoundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.zero_smul_isBoundedUnder_le {f : α -> 𝕜} {g : α -> E} {l : 
Filter α} (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ 
g)) : Tendsto (fun x => f x • g x) l (𝓝 0)
参数：hf : Tendsto f l (𝓝 0)；hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.op_zero_isBoundedUnder_le`：∀ {α : Type u_1} {E : Type u_2
} {F : Type u_3} {G : Type u_4} [inst : SeminormedAddGroup E]   [inst_1 : Semino
rmedAddGroup F] [inst_2 : Semi…
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
-/
theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : α → 𝕜} {g : α → E} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le
/-
**Filter.IsBoundedUnder.smul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.IsBoundedUnder.smul_tendsto_zero {f : α -> 𝕜} {g : α -> E} {l : Fil
ter α} (hf : IsBoundedUnder (· <= ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) : Te
ndsto (fun x => f x • g x) l (𝓝 0)
参数：hf : IsBoundedUnder (· <= ·) l (norm ∘ f)；hg : Tendsto g l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.op_zero_isBoundedUnder_le`：∀ {α : Type u_1} {E : Type u_2
} {F : Type u_3} {G : Type u_4} [inst : SeminormedAddGroup E]   [inst_1 : Semino
rmedAddGroup F] [inst_2 : Semi…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Filter.IsBoundedUnder.smul_tendsto_zero {f : α → 𝕜} {g : α → E} {l : Filter α}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)
/-
**NormedSpace.discreteTopology_zmultiples** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedSpace.discreteTopology_zmultiples {E : Type*} [NormedAddCommGroup E]
 [NormedSpace Rat E] (e : E) : DiscreteTopology AddSubgroup.zmultiples e
参数：e : E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_module_rat`：IsAddTorsionFree.of_module_rat [AddCommG
roup M] [Module Rat M] : IsAddTorsionFree M where nsmul_right_injective n hn x y
 hxy
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.zmultiples_zero_eq_bot`：∀ {G : Type u_1} [inst : AddGroup G]
, AddSubgroup.zmultiples 0 = ⊥
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `discreteTopology_iff_isOpen_singleton_zero`：∀ {G : Type w} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G],   DiscreteTopo
logy G ↔ IsOpen {0}
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `AddSubgroup.instIsTopologicalAddGroupSubtypeMem`：∀ {G : Type w} [inst : 
TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (S : AddSubg
roup G),   IsTopologicalAddGroup ↥S
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubgroup.mem_zmultiples_iff`：∀ {G : Type u_1} [inst : AddGroup G] {g 
h : G}, h ∈ AddSubgroup.zmultiples g ↔ ∃ k, k • g = h
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `AddSubgroup.coe_mk`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSubgrou
p G) (x : G) (hx : x ∈ H), ↑⟨x, hx⟩ = x
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AddSubgroup.coe_zero`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSubgr
oup G), ↑0 = 0
· 使用定理 `norm_zsmul`：norm_zsmul (n : Int) (x : E) : ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖
· 使用定理 `Int.norm_cast_rat`：∀ (m : ℤ), ‖↑m‖ = ‖m‖
· 使用定理 `Int.norm_eq_abs`：norm_eq_abs (n : Int) : ‖n‖ = |(n : Real)|
· 使用定理 `mul_lt_iff_lt_one_left`：mul_lt_iff_lt_one_left [MulPosStrictMono α] [Mul
PosReflectLT α] (b0 : 0 < b) : a * b < b ↔ a < 1
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 43 条，此处仅展示前 30 条）
-/
instance NormedSpace.discreteTopology_zmultiples
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ E] (e : E) :
    DiscreteTopology <| AddSubgroup.zmultiples e := by
  have : IsAddTorsionFree E := .of_module_rat E
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := ↑(⊥ : Subspace ℚ E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage, mem_ball_zero_iff, AddSubgroup.coe_mk, mem_singleton_iff, Subtype.ext_iff,
      AddSubgroup.coe_mk, AddSubgroup.coe_zero, norm_zsmul ℚ k e, Int.norm_cast_rat,
      Int.norm_eq_abs, mul_lt_iff_lt_one_left (norm_pos_iff.mpr he), ← @Int.cast_one ℝ _,
      ← Int.cast_abs, Int.cast_lt, Int.abs_lt_one_iff, smul_eq_zero, or_iff_left he]

section Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-
**Metric.diam_sphere_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Metric.diam_sphere_eq (x : E) {r : Real} (hr : 0 <= r) : diam (sphere x r)
 = 2 * r
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.diam_mono`：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBou
nded t) : diam s <= diam t
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `Metric.diam_closedBall`：diam_closedBall {r : Real} (h : 0 <= r) : diam (
closedBall x r) <= 2 * r
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 38 条，此处仅展示前 30 条）
-/
lemma Metric.diam_sphere_eq (x : E) {r : ℝ} (hr : 0 ≤ r) : diam (sphere x r) = 2 * r := by
  apply le_antisymm
    (diam_mono sphere_subset_closedBall isBounded_closedBall |>.trans <| diam_closedBall hr)
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  calc
    2 * r = dist (x + r • ‖y‖⁻¹ • y) (x - r • ‖y‖⁻¹ • y) := by
      simp [dist_eq_norm, ← two_nsmul, ← smul_assoc, norm_smul, abs_of_nonneg hr, hy, mul_assoc]
    _ ≤ diam (sphere x r) := by
      apply dist_le_diam_of_mem isBounded_sphere <;> simp [norm_smul, hy, abs_of_nonneg hr]
/-
**Metric.diam_closedBall_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Metric.diam_closedBall_eq (x : E) {r : Real} (hr : 0 <= r) : diam (closedB
all x r) = 2 * r
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.diam_closedBall`：diam_closedBall {r : Real} (h : 0 <= r) : diam (
closedBall x r) <= 2 * r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.diam_sphere_eq`：Metric.diam_sphere_eq (x : E) {r : Real} (hr : 0 
<= r) : diam (sphere x r) = 2 * r
· 使用定理 `Metric.diam_mono`：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBou
nded t) : diam s <= diam t
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
-/
lemma Metric.diam_closedBall_eq (x : E) {r : ℝ} (hr : 0 ≤ r) : diam (closedBall x r) = 2 * r :=
  le_antisymm (diam_closedBall hr) <|
    diam_sphere_eq x hr |>.symm.le.trans <| diam_mono sphere_subset_closedBall isBounded_closedBall
/-
**Metric.diam_ball_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Metric.diam_ball_eq (x : E) {r : Real} (hr : 0 <= r) : diam (ball x r) = 2
 * r
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.diam_ball`：diam_ball {r : Real} (h : 0 <= r) : diam (ball x r) <=
 2 * r
· 使用引理 `mul_le_of_forall_lt_of_nonneg`：mul_le_of_forall_lt_of_nonneg {a b c : α}
 (ha : 0 <= a) (hc : 0 <= c) (h : forall a' >= 0, a' < a -> forall b' >= 0, b' <
 b -> a' * b' <= c)…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Metric.diam_nonneg`：diam_nonneg : 0 <= diam s
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.diam_sphere_eq`：Metric.diam_sphere_eq (x : E) {r : Real} (hr : 0 
<= r) : diam (sphere x r) = 2 * r
· 使用定理 `GE.ge.le`：∀ {α : Type u_2} [inst : LE α] {a b : α}, a ≥ b → b ≤ a
· 使用定理 `Metric.diam_mono`：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBou
nded t) : diam s <= diam t
· 使用引理 `Metric.sphere_subset_ball`：sphere_subset_ball {r R : Real} (h : r < R) :
 sphere x r subseteq ball x R
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
-/
lemma Metric.diam_ball_eq (x : E) {r : ℝ} (hr : 0 ≤ r) : diam (ball x r) = 2 * r := by
  /- This proof could be simplified with `Metric.diam_closure` and `closure_ball`,
  but we opt for this proof to minimize dependencies. -/
  refine le_antisymm (diam_ball hr) <|
    mul_le_of_forall_lt_of_nonneg (by positivity) diam_nonneg fun a ha ha' r' hr' hr'' ↦ ?_
  calc a * r' ≤ 2 * r' := by gcongr
    _ ≤ _ := by simpa only [← Metric.diam_sphere_eq x hr'.le]
      using diam_mono (sphere_subset_ball hr'') isBounded_ball

end Real

open NormedField

/-
**ULift.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.normedSpace : NormedSpace 𝕜 (ULift E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.normedSpace : NormedSpace 𝕜 (ULift E) :=
  { __ := ULift.seminormedAddCommGroup (E := E),
    __ := ULift.module'
    norm_smul_le := fun s x => (norm_smul_le s x.down :) }

/-- The product of two normed spaces is a normed space, with the sup norm. -/
/-
**Prod.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.normedSpace : NormedSpace 𝕜 (E × F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two normed spaces is a normed space, with the sup norm.
-/
instance Prod.normedSpace : NormedSpace 𝕜 (E × F) :=
  { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, le_rfl] }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
/-
**Pi.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normedSpace {ι : Type*} {E : ι -> Type*} [Fintype ι] [forall i, Seminor
medAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (forall i
, E i) where norm_smul_le a f
参数：E i；E i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many normed spaces is a normed space, with the sup norm.
-/
instance Pi.normedSpace {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (∀ i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _
/-
**SeparationQuotient.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instNormedSpace : NormedSpace 𝕜 (SeparationQuotient E) 
where norm_smul_le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SeparationQuotient.instNormedSpace : NormedSpace 𝕜 (SeparationQuotient E) where
  norm_smul_le := norm_smul_le
/-
**MulOpposite.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNormedSpace : NormedSpace 𝕜 Eᵐᵒᵖ where norm_smul_le _ x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNormedSpace : NormedSpace 𝕜 Eᵐᵒᵖ where
  norm_smul_le _ x := norm_smul_le _ x.unop

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
/-
**Submodule.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.normedSpace {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E
 : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTow
er 𝕜 R E] (s : Submodule R E) : NormedSpace 𝕜 s where norm_smul_le c x
参数：s : Submodule R E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subspace of a normed space is also a normed space, with the restriction of the
 norm.
-/
instance Submodule.normedSpace {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E]
    (s : Submodule R E) : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

variable {S 𝕜 R E : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] [SeminormedAddCommGroup E]
variable [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] [SetLike S E] [AddSubgroupClass S E]
variable [SMulMemClass S R E] (s : S)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) SubmoduleClass.toNormedSpace : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SeminormedAddCommGroup

/-- A linear map from a `Module` to a `NormedSpace` induces a `NormedSpace` structure on the
domain, using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances] -/
/-
**NormedSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedSpace.induced {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGr
oup E] [Module 𝕜 E] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [FunLike F E G]
 [LinearMapClass F 𝕜 E G] (f : F) : @NormedSpace 𝕜 E _ (SeminormedAddCommGroup.i
nduced E G f)
参数：𝕜 E G : Type*；f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map from a `Module` to a `NormedSpace` induces a `NormedSpace` structur
e on the
domain, using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances]
-/
abbrev NormedSpace.induced {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [FunLike F E G] [LinearMapClass F 𝕜 E G] (f : F) :
    @NormedSpace 𝕜 E _ (SeminormedAddCommGroup.induced E G f) :=
  letI := SeminormedAddCommGroup.induced E G f
  { norm_smul_le a b := by simpa only [← map_smul f a b] using! norm_smul_le a (f b) }

section NontriviallyNormedSpace

variable (𝕜 E)
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
include 𝕜

/-- If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
/-
**NormedSpace.exists_lt_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedSpace.exists_lt_norm (c : Real) : exists x : E, c < ‖x‖
参数：c : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, then `
E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `
c`.
-/
theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ‖x‖ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff₀]
  rwa [norm_pos_iff]
/-
**NormedSpace.unbounded_univ** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E] [NormedSpace 𝕜 E]   [Nontrivial E], ¬Bornology.IsBounde
d Set.univ
参数：𝕜 : Type u_1；E : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `NormedSpace.exists_lt_norm`：NormedSpace.exists_lt_norm (c : Real) : exis
ts x : E, c < ‖x‖
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `trivial`：True
-/
protected theorem NormedSpace.unbounded_univ : ¬Bornology.IsBounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_ge (hR x trivial)
/-
**NormedSpace.cobounded_neBot** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E] [NormedSpace 𝕜 E]   [Nontrivial E], (Bornology.cobounde
d E).NeBot
参数：𝕜 : Type u_1；E : Type u_3；Bornology.cobounded E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Bornology.cobounded_eq_bot_iff`：cobounded_eq_bot_iff : cobounded α = ⊥ ↔
 BoundedSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_univ`：isBounded_univ : IsBounded (univ : Set α) ↔ Bo
undedSpace α
· 使用定理 `NormedSpace.unbounded_univ`：∀ (𝕜 : Type u_1) (E : Type u_3) [inst : Nont
riviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E] [NormedSpace 𝕜 E]   [Nont
rivial E], ¬Born…
-/
protected lemma NormedSpace.cobounded_neBot : NeBot (cobounded E) := by
  rw [neBot_iff, Ne, cobounded_eq_bot_iff, ← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NontriviallyNormedField.cobounded_neBot : NeBot (cobounded 𝕜) :=
  NormedSpace.cobounded_neBot 𝕜 𝕜
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) RealNormedSpace.cobounded_neBot [NormedSpace ℝ E] :
    NeBot (cobounded E) := NormedSpace.cobounded_neBot ℝ E
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) NontriviallyNormedField.infinite : Infinite 𝕜 :=
  ⟨fun _ ↦ NormedSpace.unbounded_univ 𝕜 𝕜 (Set.toFinite _).isBounded⟩

end NontriviallyNormedSpace

section NormedSpace

variable (𝕜 E)
variable [NormedField 𝕜] [Infinite 𝕜] [NormedAddCommGroup E] [Nontrivial E] [NormedSpace 𝕜 E]
include 𝕜

/-- A normed vector space over an infinite normed field is a noncompact space.
This cannot be an instance because in order to apply it,
Lean would have to search for `NormedSpace 𝕜 E` with unknown `𝕜`.
We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
/-
**NormedSpace.noncompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_3) [inst : NormedField 𝕜] [Infinite 𝕜] [inst_
2 : NormedAddCommGroup E] [Nontrivial E]   [NormedSpace 𝕜 E], NoncompactSpace E
参数：𝕜 : Type u_1；E : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.unbounded_univ`：∀ (𝕜 : Type u_1) (E : Type u_3) [inst : Nont
riviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E] [NormedSpace 𝕜 E]   [Nont
rivial E], ¬Born…
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Metric.isClosedEmbedding_of_pairwise_le_dist`：isClosedEmbedding_of_pairw
ise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α] {ε : Real} (hε
 : 0 < ε) {f : α -> γ} (hf : Pairw…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Topology.IsClosedEmbedding.noncompactSpace`：∀ {X : Type u} {Y : Type v} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [NoncompactSpace X] {f
 : X → Y},   Topology.IsClosedEm…
· 使用定理 `Nat.instNoncompactSpace`：NoncompactSpace ℕ

--- 原说明 ---
A normed vector space over an infinite normed field is a noncompact space.
This cannot be an instance because in order to apply it,
Lean would have to search for `NormedSpace 𝕜 E` with unknown `𝕜`.
We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`.
-/
protected theorem NormedSpace.noncompactSpace : NoncompactSpace E := by
  by_cases! H : ∃ c : 𝕜, c ≠ 0 ∧ ‖c‖ ≠ 1
  · let := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h ↦ NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices IsClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne ↦ ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H, one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace ℝ E

end NormedSpace

section NormedAlgebra

/-- A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `Algebra` for a discussion about non-unital algebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variable [NormedField 𝕜] [NonUnitalSeminormedRing 𝕜']
variable [NormedSpace 𝕜 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
```
-/
/-
**NormedAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_6) → (𝕜' : Type u_7) → [NormedField 𝕜] → [SeminormedRing 𝕜'] →
 Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `Algebra` for a discussion about non-unital alg
ebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variable [NormedField 𝕜] [NonUnitalSeminormedRing 𝕜']
variable [NormedSpace 𝕜 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
```
-/
class NormedAlgebra (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ‖r • x‖ ≤ ‖r‖ * ‖x‖

attribute [inherit_doc NormedAlgebra] NormedAlgebra.norm_smul_le

variable (𝕜')
variable [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜' :=
  { NormedAlgebra.toAlgebra.toModule with
  norm_smul_le := NormedAlgebra.norm_smul_le }
/-
**norm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _
/-
**nnnorm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `norm_algebraMap`：norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖
(1 : 𝕜')‖
-/
theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
  Subtype.ext <| norm_algebraMap 𝕜' x
/-
**dist_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_algebraMap (x y : 𝕜) : (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y))
 = dist x y * ‖(1 : 𝕜')‖
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_algebraMap`：norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖
(1 : 𝕜')‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_algebraMap (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y * ‖(1 : 𝕜')‖ := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap]

/-- This is a simpler version of `norm_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
/-
**norm_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_algebraMap`：norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖
(1 : 𝕜')‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
This is a simpler version of `norm_algebraMap` when `‖1‖ = 1` in `𝕜'`.
-/
theorem norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap, norm_one, mul_one]

@[simp]
/-
**Algebra.norm_smul_one_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.norm_smul_one_eq_norm [NormOneClass 𝕜'] (x : 𝕜) : ‖x • (1 : 𝕜')‖ =
 ‖x‖
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Algebra.norm_smul_one_eq_norm [NormOneClass 𝕜'] (x : 𝕜) : ‖x • (1 : 𝕜')‖ = ‖x‖ := by
  simp [norm_smul]

/-- This is a simpler version of `nnnorm_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
/-
**nnnorm_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖

--- 原说明 ---
This is a simpler version of `nnnorm_algebraMap` when `‖1‖ = 1` in `𝕜'`.
-/
theorem nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_algebraMap' _ _

/-- This is a simpler version of `dist_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
/-
**dist_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_algebraMap' [NormOneClass 𝕜'] (x y : 𝕜) : (dist (algebraMap 𝕜 𝕜' x) (
algebraMap 𝕜 𝕜' y)) = dist x y
参数：x y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is a simpler version of `dist_algebraMap` when `‖1‖ = 1` in `𝕜'`.
-/
theorem dist_algebraMap' [NormOneClass 𝕜'] (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap']

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra ℝ 𝕜']

@[simp]
/-
**norm_algebraMap_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_algebraMap_nnreal (x : Real>=0) : ‖algebraMap Real>=0 𝕜' x‖ = x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
-/
theorem norm_algebraMap_nnreal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖ = x :=
  (norm_algebraMap' 𝕜' (x : ℝ)).symm ▸ Real.norm_of_nonneg x.prop

@[simp]
/-
**nnnorm_algebraMap_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_algebraMap_nnreal (x : Real>=0) : ‖algebraMap Real>=0 𝕜' x‖₊ = x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `norm_algebraMap_nnreal`：norm_algebraMap_nnreal (x : Real>=0) : ‖algebraM
ap Real>=0 𝕜' x‖ = x
-/
theorem nnnorm_algebraMap_nnreal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖₊ = x :=
  Subtype.ext <| norm_algebraMap_nnreal 𝕜' x

end NNReal

variable (𝕜)

open Filter Bornology in
/-- Preimages of cobounded sets under the algebra map are cobounded. -/
@[simp]
/-
**tendsto_algebraMap_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_algebraMap_cobounded (𝕜 𝕜' : Type*) [NormedField 𝕜] [SeminormedRin
g 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] : Tendsto (algebraMap 𝕜 𝕜') (coboun
ded 𝕜) (cobounded 𝕜')
参数：𝕜 𝕜' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isCobounded_def`：isCobounded_def {s : Set α} : IsCobounded s ↔
 s in cobounded α
· 使用定理 `Bornology.isBounded_compl_iff`：isBounded_compl_iff : IsBounded sᶜ ↔ IsCo
bounded s
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖

--- 原说明 ---
Preimages of cobounded sets under the algebra map are cobounded.
-/
theorem tendsto_algebraMap_cobounded (𝕜 𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] :
    Tendsto (algebraMap 𝕜 𝕜') (cobounded 𝕜) (cobounded 𝕜') := by
  intro c hc
  rw [mem_map]
  rw [← isCobounded_def, ← isBounded_compl_iff, isBounded_iff_forall_norm_le] at hc ⊢
  obtain ⟨s, hs⟩ := hc
  exact ⟨s, fun x hx ↦ by simpa using hs (algebraMap 𝕜 𝕜' x) hx⟩

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
/-
**algebraMap_isometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖

--- 原说明 ---
In a normed algebra, the inclusion of the base field in the extended field is an
 isometry.
-/
theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_algebraMap']
/-
**NormedAlgebra.id** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedAlgebra.id : NormedAlgebra 𝕜 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }

/-- Any normed characteristic-zero division ring that is a normed algebra over the reals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `AlgebraRat` respects that
norm. -/
/-
**normedAlgebraRat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra Re
al 𝕜] : NormedAlgebra Rat 𝕜 where norm_smul_le q x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any normed characteristic-zero division ring that is a normed algebra over the r
eals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `AlgebraRat
` respects that
norm.
-/
instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra ℝ 𝕜] :
    NormedAlgebra ℚ 𝕜 where
  norm_smul_le q x := by
    rw [← smul_one_smul ℝ q x, Rat.smul_one_eq_cast, norm_smul, Rat.norm_cast_real]
/-
**PUnit.normedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit where norm_smul_le q _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit where
  norm_smul_le q _ := by simp only [norm_eq_zero, mul_zero, le_refl]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace, ULift.algebra with }

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
/-
**Prod.normedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [No
rmedAlgebra 𝕜 E] [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two normed algebras is a normed algebra, with the sup norm.
-/
instance Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }

/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
/-
**Pi.normedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normedAlgebra {ι : Type*} {E : ι -> Type*} [Fintype ι] [forall i, Semin
ormedRing (E i)] [forall i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (forall i, 
E i)
参数：E i；E i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many normed algebras is a normed algebra, with the sup n
orm.
-/
instance Pi.normedAlgebra {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }

variable [SeminormedRing E] [NormedAlgebra 𝕜 E]
/-
**SeparationQuotient.instNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instNormedAlgebra : NormedAlgebra 𝕜 (SeparationQuotient
 E) where __ : NormedSpace 𝕜 (SeparationQuotient E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SeparationQuotient.instNormedAlgebra : NormedAlgebra 𝕜 (SeparationQuotient E) where
  __ : NormedSpace 𝕜 (SeparationQuotient E) := inferInstance
  __ : Algebra 𝕜 (SeparationQuotient E) := inferInstance
/-
**MulOpposite.instNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNormedAlgebra {E : Type*} [SeminormedRing E] [NormedAlgebr
a 𝕜 E] : NormedAlgebra 𝕜 Eᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNormedAlgebra {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ where
  __ := instAlgebra
  __ := instNormedSpace

end NormedAlgebra

/-- A non-unital algebra homomorphism from an `Algebra` to a `NormedAlgebra` induces a
`NormedAlgebra` structure on the domain, using the `SeminormedRing.induced` norm.

See note [reducible non-instances] -/
/-
**NormedAlgebra.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedAlgebra.induced {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R]
 [Algebra 𝕜 R] [SeminormedRing S] [NormedAlgebra 𝕜 S] [FunLike F R S] [NonUnital
AlgHomClass F 𝕜 R S] (f : F) : @NormedAlgebra 𝕜 R _ (SeminormedRing.induced R S 
f)
参数：𝕜 R S : Type*；f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital algebra homomorphism from an `Algebra` to a `NormedAlgebra` induces
 a
`NormedAlgebra` structure on the domain, using the `SeminormedRing.induced` norm
.

See note [reducible non-instances]
-/
abbrev NormedAlgebra.induced {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R] [Algebra 𝕜 R]
    [SeminormedRing S] [NormedAlgebra 𝕜 S] [FunLike F R S] [NonUnitalAlgHomClass F 𝕜 R S]
    (f : F) :
    @NormedAlgebra 𝕜 R _ (SeminormedRing.induced R S f) :=
  letI := SeminormedRing.induced R S f
  ⟨fun a b ↦ show ‖f (a • b)‖ ≤ ‖a‖ * ‖f b‖ from (map_smul f a b).symm ▸ norm_smul_le a (f b)⟩
/-
**Subalgebra.toNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subalgebra.toNormedAlgebra {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜
] [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S
参数：S : Subalgebra 𝕜 A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subalgebra.toNormedAlgebra {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  fast_instance% NormedAlgebra.induced 𝕜 S A S.val

section SubalgebraClass

variable {S 𝕜 E : Type*} [NormedField 𝕜] [SeminormedRing E] [NormedAlgebra 𝕜 E]
variable [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E] (s : S)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) SubalgebraClass.toNormedAlgebra : NormedAlgebra 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SubalgebraClass

section RestrictScalars

section NormInstances

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NormedAddCommGroup E] :
    NormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NonUnitalSeminormedRing E] :
    NonUnitalSeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NonUnitalNormedRing E] :
    NonUnitalNormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : SeminormedRing E] :
    SeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NormedRing E] :
    NormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NonUnitalSeminormedCommRing E] :
    NonUnitalSeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NonUnitalNormedCommRing E] :
    NonUnitalNormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : SeminormedCommRing E] :
    SeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : NormedCommRing E] :
    NormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

end NormInstances

section NormedSpace

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[instance_reducible]
/-
**NormedSpace.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedSpace.restrictScalars : NormedSpace 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put dire
ctly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both beca
use `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { Module.restrictScalars 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebraMap'] }
/-
**NormedSpace.restrictScalars_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedSpace.restrictScalars_eq {E : Type*} [SeminormedAddCommGroup E] [h :
 NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] : NormedSpace.restri
ctScalars 𝕜 𝕜' E = h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.ext`：∀ {𝕜 : Type u_6} {E : Type u_7} {inst : NormedField 𝕜} 
{inst_1 : SeminormedAddCommGroup E} {x y : NormedSpace 𝕜 E},   SMul.smul = SMul.
smul …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem NormedSpace.restrictScalars_eq {E : Type*} [SeminormedAddCommGroup E]
    [h : NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    NormedSpace.restrictScalars 𝕜 𝕜' E = h := by
  ext
  apply algebraMap_smul

/-- If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedSpace`. -/
/-
**RestrictScalars.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedSpace`.
-/
instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  fast_instance% NormedSpace.restrictScalars 𝕜 𝕜' E

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[instance_reducible]
/-
**Module.RestrictScalars.normedSpaceOrig** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.RestrictScalars.normedSpaceOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*
} [NormedField 𝕜'] [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpa
ce 𝕜' (RestrictScalars 𝕜 𝕜' E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScala
rs`.
-/
def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

end NormedSpace

section NormedAlgebra

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedRing E] [NormedAlgebra 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedAlgebra` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[instance_reducible]
/-
**NormedAlgebra.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedAlgebra.restrictScalars : NormedAlgebra 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedAlgebra` instance to be put di
rectly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both beca
use `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
def NormedAlgebra.restrictScalars : NormedAlgebra 𝕜 E :=
  { NormedSpace.restrictScalars 𝕜 𝕜' E, Algebra.restrictScalars 𝕜 𝕜' E with }

/-- If `E` is a normed algebra over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedAlgebra`. -/
/-
**RestrictScalars.normedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RestrictScalars.normedAlgebra : NormedAlgebra 𝕜 (RestrictScalars 𝕜 𝕜' E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a normed algebra over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedAlgebra`.
-/
instance RestrictScalars.normedAlgebra : NormedAlgebra 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  fast_instance% NormedAlgebra.restrictScalars 𝕜 𝕜' E

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[instance_reducible]
/-
**Module.RestrictScalars.normedAlgebraOrig** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.RestrictScalars.normedAlgebraOrig {𝕜 : Type*} {𝕜' : Type*} {E : Typ
e*} [NormedField 𝕜'] [SeminormedRing E] [I : NormedAlgebra 𝕜' E] : NormedAlgebra
 𝕜' (RestrictScalars 𝕜 𝕜' E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScala
rs`.
-/
def Module.RestrictScalars.normedAlgebraOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedRing E] [I : NormedAlgebra 𝕜' E] : NormedAlgebra 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I
end NormedAlgebra

end RestrictScalars

section Core
/-!
### Structures for constructing new normed spaces

This section contains tools meant for constructing new normed spaces. These allow one to easily
construct all the relevant instances (distances measures, etc) while proving only a minimal
set of axioms. Furthermore, tools are provided to add a norm structure to a type that already
has a preexisting uniformity or bornology: in such cases, it is necessary to keep the preexisting
instances, while ensuring that the norm induces the same uniformity/bornology.
-/

open scoped Uniformity Bornology

/-- A structure encapsulating minimal axioms needed to defined a seminormed vector space, as found
in textbooks. This is meant to be used to easily define `SeminormedSpace E` instances from
scratch on a type with no preexisting distance or topology. -/
/-
**SeminormedSpace.Core** 是 Mathlib 中的一个归纳类型，位于命名空间 `SeminormedSpace`。
形式化陈述：(𝕜 : Type u_6) →   (E : Type u_7) → [inst : NormedField 𝕜] → [inst_1 : Add
CommGroup E] → [Norm E] → [_root_.Module 𝕜 E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure encapsulating minimal axioms needed to defined a seminormed vector s
pace, as found
in textbooks. This is meant to be used to easily define `SeminormedSpace E` inst
ances from
scratch on a type with no preexisting distance or topology.
-/
structure SeminormedSpace.Core (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] : Prop where
  norm_nonneg (x : E) : 0 ≤ ‖x‖
  norm_smul (c : 𝕜) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖
  norm_triangle (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖

/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new uniformity and
topology on the type. See note [reducible non-instances]. -/
/-
**PseudoMetricSpace.ofSeminormedSpaceCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜] [Add
CommGroup E] [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) : PseudoMet
ricSpace E where dist x y
参数：core : SeminormedSpace.Core 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core`. Note th
at
if this is used to define an instance on a type, it also provides a new uniformi
ty and
topology on the type. See note [reducible non-instances].
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) :
    PseudoMetricSpace E where
  dist x y := ‖-x + y‖
  dist_self x := by
    show ‖-x + x‖ = 0
    simp only [add_comm, ← sub_eq_add_neg, sub_self]
    have : (0 : E) = (0 : 𝕜) • (0 : E) := by simp
    rw [this, core.norm_smul]
    simp
  dist_comm x y := by
    show ‖-x + y‖ = ‖-y + x‖
    have : -y + x = (-1 : 𝕜) • (-x + y) := by simp; abel
    rw [this, core.norm_smul]
    simp
  dist_triangle x y z := by
    show ‖-x + z‖ ≤ ‖-x + y‖ + ‖-y + z‖
    have : -x + z = (-x + y) + (-y + z) := by abel
    rw [this]
    exact core.norm_triangle _ _
  edist_dist x y := by exact (ENNReal.ofReal_eq_coe_nnreal _).symm

/-- Produces a `PseudoEMetricSpace E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new uniformity and
topology on the type. See note [reducible non-instances]. -/
/-
**PseudoEMetricSpace.ofSeminormedSpaceCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜] [Ad
dCommGroup E] [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) : PseudoEM
etricSpace E
参数：core : SeminormedSpace.Core 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `PseudoEMetricSpace E` instance from a `SeminormedSpace.Core`. Note t
hat
if this is used to define an instance on a type, it also provides a new uniformi
ty and
topology on the type. See note [reducible non-instances].
-/
abbrev PseudoEMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E]
    (core : SeminormedSpace.Core 𝕜 E) : PseudoEMetricSpace E :=
  (PseudoMetricSpace.ofSeminormedSpaceCore core).toPseudoEMetricSpace

/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a type that
already has an existing uniform space structure. This requires a proof that the uniformity induced
by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
/-
**PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity** 是 Mathlib 中的一个缩写定义，
位于命名空间 ``。
形式化陈述：PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity {𝕜 E : Type*} [No
rmedField 𝕜] [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] (core :
 SeminormedSpace.Core 𝕜 E) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace (self
参数：core : SeminormedSpace.Core 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a typ
e that
already has an existing uniform space structure. This requires a proof that the 
uniformity induced
by the norm is equal to the preexisting uniformity. See note [reducible non-inst
ances].
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
        (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    PseudoMetricSpace E :=
  .replaceUniformity (.ofSeminormedSpaceCore core) H

/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a type that
already has an existing topology. This requires a proof that the topology induced
by the norm is equal to the preexisting topology. See note [reducible non-instances]. -/
/-
**PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology** 是 Mathlib 中的一个缩写定义，位于
命名空间 ``。
形式化陈述：PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology {𝕜 E : Type*} [Norm
edField 𝕜] [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E] (core
 : SeminormedSpace.Core 𝕜 E) (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore 
core).toUniformSpace.toTopologicalSpace) : PseudoMetricSpace E
参数：core : SeminormedSpace.Core 𝕜 E；H : T = (PseudoEMetricSpace.ofSeminormedSpace
Core core).toUniformSpace.toTopologicalSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a typ
e that
already has an existing topology. This requires a proof that the topology induce
d
by the norm is equal to the preexisting topology. See note [reducible non-instan
ces].
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    PseudoMetricSpace E :=
  .replaceTopology (.ofSeminormedSpaceCore core) H

open Bornology in
/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a type that
already has a preexisting uniform space structure and a preexisting bornology. This requires proofs
that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise for
the bornology. See note [reducible non-instances]. -/
/-
**PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll** 是 Mathlib 中的一个缩写定义，位于命名空间 
``。
形式化陈述：PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll {𝕜 E : Type*} [NormedFie
ld 𝕜] [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology
 E] (core : SeminormedSpace.Core 𝕜 E) (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUnifor
mSpace (self
参数：core : SeminormedSpace.Core 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a typ
e that
already has a preexisting uniform space structure and a preexisting bornology. T
his requires proofs
that the uniformity induced by the norm is equal to the preexisting uniformity, 
and likewise for
the bornology. See note [reducible non-instances].
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    PseudoMetricSpace E :=
  .replaceBornology (.replaceUniformity (.ofSeminormedSpaceCore core) HU) HB

/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new distance measure from the
norm.  it must therefore not be used on a type with a preexisting distance measure or topology.
See note [reducible non-instances]. -/
/-
**SeminormedAddCommGroup.ofCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedAddCommGroup.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [Add
CommGroup E] [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) : Seminorme
dAddCommGroup E
参数：core : SeminormedSpace.Core 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core`. No
te that
if this is used to define an instance on a type, it also provides a new distance
 measure from the
norm.  it must therefore not be used on a type with a preexisting distance measu
re or topology.
See note [reducible non-instances].
-/
abbrev SeminormedAddCommGroup.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) : SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCore core with }

/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on a type
that already has an existing uniform space structure. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
/-
**SeminormedAddCommGroup.ofCoreReplaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedAddCommGroup.ofCoreReplaceUniformity {𝕜 : Type*} {E : Type*} [No
rmedField 𝕜] [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] (core :
 SeminormedSpace.Core 𝕜 E) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace (self
参数：core : SeminormedSpace.Core 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on 
a type
that already has an existing uniform space structure. This requires a proof that
 the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible 
non-instances].
-/
abbrev SeminormedAddCommGroup.ofCoreReplaceUniformity {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity core H with }

/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
/-
**SeminormedAddCommGroup.ofCoreReplaceTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedAddCommGroup.ofCoreReplaceTopology {𝕜 : Type*} {E : Type*} [Norm
edField 𝕜] [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E] (core
 : SeminormedSpace.Core 𝕜 E) (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore 
core).toUniformSpace.toTopologicalSpace) : SeminormedAddCommGroup E
参数：core : SeminormedSpace.Core 𝕜 E；H : T = (PseudoEMetricSpace.ofSeminormedSpace
Core core).toUniformSpace.toTopologicalSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on 
a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible 
non-instances].
-/
abbrev SeminormedAddCommGroup.ofCoreReplaceTopology {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology core H with }

open Bornology in
/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on a type
that already has a preexisting uniform space structure and a preexisting bornology. This requires
proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
for the bornology. See note [reducible non-instances]. -/
/-
**SeminormedAddCommGroup.ofCoreReplaceAll** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedAddCommGroup.ofCoreReplaceAll {𝕜 : Type*} {E : Type*} [NormedFie
ld 𝕜] [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology
 E] (core : SeminormedSpace.Core 𝕜 E) (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUnifor
mSpace (self
参数：core : SeminormedSpace.Core 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on 
a type
that already has a preexisting uniform space structure and a preexisting bornolo
gy. This requires
proofs that the uniformity induced by the norm is equal to the preexisting unifo
rmity, and likewise
for the bornology. See note [reducible non-instances].
-/
abbrev SeminormedAddCommGroup.ofCoreReplaceAll {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll core HU HB with }

/-- A structure encapsulating minimal axioms needed to defined a normed vector space, as found
in textbooks. This is meant to be used to easily define `NormedAddCommGroup E` and `NormedSpace E`
instances from scratch on a type with no preexisting distance or topology. -/
/-
**NormedSpace.Core** 是 Mathlib 中的一个归纳类型，位于命名空间 `NormedSpace`。
形式化陈述：(𝕜 : Type u_6) →   (E : Type u_7) → [inst : NormedField 𝕜] → [inst_1 : Add
CommGroup E] → [_root_.Module 𝕜 E] → [Norm E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure encapsulating minimal axioms needed to defined a normed vector space
, as found
in textbooks. This is meant to be used to easily define `NormedAddCommGroup E` a
nd `NormedSpace E`
instances from scratch on a type with no preexisting distance or topology.
-/
structure NormedSpace.Core (𝕜 : Type*) (E : Type*)
    [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E] : Prop
    extends SeminormedSpace.Core 𝕜 E where
  norm_eq_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0

variable {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E]

/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core`. Note that if this is
used to define an instance on a type, it also provides a new distance measure from the norm.
it must therefore not be used on a type with a preexisting distance measure.
See note [reducible non-instances]. -/
/-
**NormedAddCommGroup.ofCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.ofCore (core : NormedSpace.Core 𝕜 E) : NormedAddCommGro
up E
参数：core : NormedSpace.Core 𝕜 E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.Core.toCore`：∀ {𝕜 : Type u_6} {E : Type u_7} [inst : NormedF
ield 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : Norm 
E], NormedSpa…
· 使用定理 `SeminormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedAddCo
mmGroup E] (x y : E), dist x y = ‖-x + y‖

--- 原说明 ---
Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core`. Note that 
if this is
used to define an instance on a type, it also provides a new distance measure fr
om the norm.
it must therefore not be used on a type with a preexisting distance measure.
See note [reducible non-instances].
-/
abbrev NormedAddCommGroup.ofCore (core : NormedSpace.Core 𝕜 E) : NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCore core.toCore with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has an existing uniform space structure. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
/-
**NormedAddCommGroup.ofCoreReplaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.ofCoreReplaceUniformity [U : UniformSpace E] (core : No
rmedSpace.Core 𝕜 E) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace (self
参数：core : NormedSpace.Core 𝕜 E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.Core.toCore`：∀ {𝕜 : Type u_6} {E : Type u_7} [inst : NormedF
ield 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : Norm 
E], NormedSpa…
· 使用定理 `SeminormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedAddCo
mmGroup E] (x y : E), dist x y = ‖-x + y‖

--- 原说明 ---
Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has an existing uniform space structure. This requires a proof that
 the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible 
non-instances].
-/
abbrev NormedAddCommGroup.ofCoreReplaceUniformity [U : UniformSpace E] (core : NormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)]) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceUniformity core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
/-
**NormedAddCommGroup.ofCoreReplaceTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.ofCoreReplaceTopology [T : TopologicalSpace E] (core : 
NormedSpace.Core 𝕜 E) (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore core.to
Core).toUniformSpace.toTopologicalSpace) : NormedAddCommGroup E
参数：core : NormedSpace.Core 𝕜 E；H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
 core.toCore).toUniformSpace.toTopologicalSpace。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.Core.toCore`：∀ {𝕜 : Type u_6} {E : Type u_7} [inst : NormedF
ield 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : Norm 
E], NormedSpa…
· 使用定理 `SeminormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedAddCo
mmGroup E] (x y : E), dist x y = ‖-x + y‖

--- 原说明 ---
Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible 
non-instances].
-/
abbrev NormedAddCommGroup.ofCoreReplaceTopology [T : TopologicalSpace E]
    (core : NormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core.toCore).toUniformSpace.toTopologicalSpace) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceTopology core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

open Bornology in
/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has a preexisting uniform space structure and a preexisting bornology. This requires
proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
for the bornology. See note [reducible non-instances]. -/
/-
**NormedAddCommGroup.ofCoreReplaceAll** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.ofCoreReplaceAll [U : UniformSpace E] [B : Bornology E]
 (core : NormedSpace.Core 𝕜 E) (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace 
(self
参数：core : NormedSpace.Core 𝕜 E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.Core.toCore`：∀ {𝕜 : Type u_6} {E : Type u_7} [inst : NormedF
ield 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : Norm 
E], NormedSpa…
· 使用定理 `SeminormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedAddCo
mmGroup E] (x y : E), dist x y = ‖-x + y‖

--- 原说明 ---
Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has a preexisting uniform space structure and a preexisting bornolo
gy. This requires
proofs that the uniformity induced by the norm is equal to the preexisting unifo
rmity, and likewise
for the bornology. See note [reducible non-instances].
-/
abbrev NormedAddCommGroup.ofCoreReplaceAll [U : UniformSpace E] [B : Bornology E]
    (core : NormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core.toCore).toBornology s) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceAll core.toCore HU HB with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

/-- Produces a `NormedSpace 𝕜 E` instance from a `NormedSpace.Core`. This is meant to be used
on types where the `NormedAddCommGroup E` instance has also been defined using `core`.
See note [reducible non-instances]. -/
/-
**NormedSpace.ofCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedSpace.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [SeminormedAddC
ommGroup E] [Module 𝕜 E] (core : NormedSpace.Core 𝕜 E) : NormedSpace 𝕜 E where n
orm_smul_le r x
参数：core : NormedSpace.Core 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a `NormedSpace 𝕜 E` instance from a `NormedSpace.Core`. This is meant t
o be used
on types where the `NormedAddCommGroup E` instance has also been defined using `
core`.
See note [reducible non-instances].
-/
abbrev NormedSpace.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] (core : NormedSpace.Core 𝕜 E) : NormedSpace 𝕜 E where
  norm_smul_le r x := by rw [core.norm_smul r x]

end Core

variable {G H : Type*} [SeminormedAddCommGroup G] [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  {s : Set G}

/-- A group homomorphism from a normed group to a real normed space,
bounded on a neighborhood of `0`, must be continuous. -/
/-
**AddMonoidHom.continuous_of_isBounded_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.continuous_of_isBounded_nhds_zero (f : G ->+ H) (hs : s in 𝓝 
(0 : G)) (hbounded : IsBounded (f '' s)) : Continuous f
参数：f : G ->+ H；hs : s in 𝓝 (0 : G)；hbounded : IsBounded (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `Metric.isBounded_iff_subset_ball`：isBounded_iff_subset_ball (c : α) : Is
Bounded s ↔ exists r, s subseteq ball c r
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `continuous_of_continuousAt_zero`：∀ {G : Type w} [inst : TopologicalSpace
 G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {M : Type u_1}   {hom : Type
 u_2} [inst_3 : AddZe…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.continuousAt_iff`：continuousAt_iff [PseudoMetricSpace β] {f : α -
> β} {a : α} : ContinuousAt f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, di
st x a < δ ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
A group homomorphism from a normed group to a real normed space,
bounded on a neighborhood of `0`, must be continuous.
-/
lemma AddMonoidHom.continuous_of_isBounded_nhds_zero (f : G →+ H) (hs : s ∈ 𝓝 (0 : G))
    (hbounded : IsBounded (f '' s)) : Continuous f := by
  obtain ⟨δ, hδ, hUε⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (isBounded_iff_subset_ball 0).1 (hbounded.subset <| image_mono hUε)
  refine continuous_of_continuousAt_zero _ (continuousAt_iff.2 fun ε (hε : _ < _) => ?_)
  simp only [dist_zero_right, map_zero]
  simp only [subset_def, mem_image, mem_ball, dist_zero_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hC
  have hC₀ : 0 < C := (norm_nonneg _).trans_lt <| hC 0 (by simpa)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hnpos : 0 < (n : ℝ) := (div_pos hC₀ hε).trans hn
  have hn₀ : n ≠ 0 := by rintro rfl; simp at hnpos
  refine ⟨δ / n, div_pos hδ hnpos, fun {x} hxδ => ?_⟩
  calc
    ‖f x‖
    _ = ‖(n : ℝ)⁻¹ • f (n • x)‖ := by simp [← Nat.cast_smul_eq_nsmul ℝ, hn₀]
    _ ≤ ‖(n : ℝ)⁻¹‖ * ‖f (n • x)‖ := norm_smul_le ..
    _ < ‖(n : ℝ)⁻¹‖ * C := by
      gcongr
      · simpa [pos_iff_ne_zero]
      · refine hC _ <| norm_nsmul_le.trans_lt ?_
        simpa only [norm_mul, Real.norm_natCast, lt_div_iff₀ hnpos, mul_comm] using hxδ
    _ = (n : ℝ)⁻¹ * C := by simp
    _ < (C / ε : ℝ)⁻¹ * C := by gcongr
    _ = ε := by simp [hC₀.ne']
