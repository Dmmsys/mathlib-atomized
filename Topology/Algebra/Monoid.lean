/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Mitchell Lee
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Theory of topological monoids

In this file we define mixin classes `ContinuousMul` and `ContinuousAdd`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

@[expose] public section

universe u v

open Set Filter TopologicalSpace Topology
open scoped Topology Pointwise

variable {ι α M N X : Type*} [TopologicalSpace X]

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1

namespace MulOpposite

/-- If multiplication is separately continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is separately continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If multiplication is separately continuous in `α`, then it also is in `αᵐᵒᵖ`.
-/
instance [TopologicalSpace α] [Mul α] [SeparatelyContinuousMul α] :
    SeparatelyContinuousMul αᵐᵒᵖ where
  continuous_mul_const := continuous_op.comp (continuous_unop.const_mul (unop _))
  continuous_const_mul := continuous_op.comp (continuous_unop.mul_const (unop _))

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`.
-/
instance [TopologicalSpace α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ :=
  ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end MulOpposite

section SeparatelyContinuousMul

variable [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SeparatelyContinuousMul Mᵒᵈ :=
  ‹SeparatelyContinuousMul M›

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SeparatelyContinuousMul (ULift.{u} M) :=
  ⟨continuous_uliftUp.comp (by fun_prop), continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]
/-
**SeparatelyContinuousMul.to_continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparatelyContinuousMul.to_continuousSMul : ContinuousConstSMul M M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatelyContinuousMul.continuous_const_mul`：∀ {M : Type u_1} {inst : T
opologicalSpace M} {inst_1 : Mul M} [self : SeparatelyContinuousMul M] {a : M}, 
  Continuous fun x => a * x
-/
instance SeparatelyContinuousMul.to_continuousSMul : ContinuousConstSMul M M :=
  ⟨fun _ ↦ continuous_const_mul⟩

@[to_additive]
/-
**SeparatelyContinuousMul.to_continuousSMul_op** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparatelyContinuousMul.to_continuousSMul_op : ContinuousConstSMul Mᵐᵒᵖ M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatelyContinuousMul.continuous_mul_const`：∀ {M : Type u_1} {inst : T
opologicalSpace M} {inst_1 : Mul M} [self : SeparatelyContinuousMul M] {a : M}, 
  Continuous fun x => x * a
-/
instance SeparatelyContinuousMul.to_continuousSMul_op : ContinuousConstSMul Mᵐᵒᵖ M :=
  ⟨fun _ ↦ continuous_mul_const⟩

end SeparatelyContinuousMul

section ContinuousMul

variable [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMul Mᵒᵈ :=
  ‹ContinuousMul M›

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMul (ULift.{u} M) := ⟨continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]
/-
**ContinuousMul.to_continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMul.to_continuousSMul : ContinuousSMul M M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMul.continuous_mul`：∀ {M : Type u_1} {inst : TopologicalSpace 
M} {inst_1 : Mul M} [self : ContinuousMul M], Continuous fun p => p.1 * p.2
-/
instance ContinuousMul.to_continuousSMul : ContinuousSMul M M :=
  ⟨continuous_mul⟩

@[to_additive]
/-
**ContinuousMul.to_continuousSMul_op** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMul.to_continuousSMul_op : ContinuousSMul Mᵐᵒᵖ M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g 
: X → M}…
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
-/
instance ContinuousMul.to_continuousSMul_op : ContinuousSMul Mᵐᵒᵖ M :=
  ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) by
    fun_prop⟩

@[to_additive]
/-
**ContinuousMul.induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMul.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] 
[Mul α] [Mul β] [MulHomClass F α β] [tβ : TopologicalSpace β] [ContinuousMul β] 
(f : F) : @ContinuousMul α (tβ.induced f) _
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Continuous.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g 
: X → M}…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem ContinuousMul.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Mul α]
    [Mul β] [MulHomClass F α β] [tβ : TopologicalSpace β] [ContinuousMul β] (f : F) :
    @ContinuousMul α (tβ.induced f) _ := by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_mul]
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_add_left := continuous_const_add
@[deprecated (since := "2026-02-20")] alias continuous_add_right := continuous_add_const
@[to_additive existing, deprecated (since := "2026-02-20")]
alias continuous_mul_left := continuous_const_mul
@[to_additive existing, deprecated (since := "2026-02-20")]
alias continuous_mul_right := continuous_mul_const

@[to_additive]
/-
**tendsto_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)
) (𝓝 (a * b))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousMul.continuous_mul`：∀ {M : Type u_1} {inst : TopologicalSpace 
M} {inst_1 : Mul M} [self : ContinuousMul M], Continuous fun p => p.1 * p.2
-/
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)

@[to_additive]
/-
**le_nhds_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b <= 𝓝 (a * b)
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map₂_mul`：map₂_mul : map₂ (· * ·) f g = f * g
· 使用定理 `Filter.map_uncurry_prod`：map_uncurry_prod (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : (f ×ˢ g).map (uncurry m) = map₂ m f g
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
theorem le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b ≤ 𝓝 (a * b) := by
  rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq]
  exact continuous_mul.tendsto _

@[to_additive (attr := simp)]
/-
**nhds_one_mul_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul 
M] (a : M) : 𝓝 (1 : M) * 𝓝 a = 𝓝 a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_nhds_mul`：le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b <= 𝓝 (a * b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm <|
    le_mul_of_one_le_left' <| pure_le_nhds 1

@[to_additive (attr := simp)]
/-
**nhds_mul_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul 
M] (a : M) : 𝓝 a * 𝓝 1 = 𝓝 a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_nhds_mul`：le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b <= 𝓝 (a * b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 a * 𝓝 1 = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm <|
    le_mul_of_one_le_right' <| pure_le_nhds 1

/-- This lemma exists to ensure that we can still do the simplification `pure_le_nhds_iff`
after simplifying with `pure_one`. -/
@[to_additive (attr := simp) /-- This lemma exists to ensure that we can still do the simplification
`pure_le_nhds_iff` after simplifying with `pure_zero`. -/]
/-
**one_le_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_nhds_iff [T1Space X] [One X] {b : X} : 1 <= 𝓝 b ↔ 1 = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pure_le_nhds_iff`：pure_le_nhds_iff [T1Space X] {a b : X} : pure a <= 𝓝 b
 ↔ a = b
-/
theorem one_le_nhds_iff [T1Space X] [One X] {b : X} : 1 ≤ 𝓝 b ↔ 1 = b :=
  pure_le_nhds_iff

section tendsto_nhds

variable {𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [Mul 𝕜] [TopologicalSpace 𝕜] [SeparatelyContinuousMul 𝕜]
  {l : Filter α} {f : α → 𝕜} {b c : 𝕜} (hb : 0 < b)
include hb

/-
**Filter.TendstoNhdsWithinIoi.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f 
l (𝓝[>] c)) : Tendsto (fun a => b * f a) l (𝓝[>] (b * c))
参数：h : Tendsto f l (𝓝[>] c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `tendsto_nhds_of_tendsto_nhdsWithin`：tendsto_nhds_of_tendsto_nhdsWithin {
f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : Tend
sto f l (𝓝 a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
    Tendsto (fun a => b * f a) l (𝓝[>] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr
/-
**Filter.TendstoNhdsWithinIio.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f 
l (𝓝[<] c)) : Tendsto (fun a => b * f a) l (𝓝[<] (b * c))
参数：h : Tendsto f l (𝓝[<] c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `tendsto_nhds_of_tendsto_nhdsWithin`：tendsto_nhds_of_tendsto_nhdsWithin {
f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : Tend
sto f l (𝓝 a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
    Tendsto (fun a => b * f a) l (𝓝[<] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr
/-
**Filter.TendstoNhdsWithinIoi.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f 
l (𝓝[>] c)) : Tendsto (fun a => f a * b) l (𝓝[>] (c * b))
参数：h : Tendsto f l (𝓝[>] c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `tendsto_nhds_of_tendsto_nhdsWithin`：tendsto_nhds_of_tendsto_nhdsWithin {
f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : Tend
sto f l (𝓝 a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
    Tendsto (fun a => f a * b) l (𝓝[>] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr
/-
**Filter.TendstoNhdsWithinIio.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f 
l (𝓝[<] c)) : Tendsto (fun a => f a * b) l (𝓝[<] (c * b))
参数：h : Tendsto f l (𝓝[<] c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `tendsto_nhds_of_tendsto_nhdsWithin`：tendsto_nhds_of_tendsto_nhdsWithin {
f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : Tend
sto f l (𝓝 a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
    Tendsto (fun a => f a * b) l (𝓝[<] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

end tendsto_nhds

@[to_additive]
/-
**Specializes.mul** 是 Mathlib 中的一个定理，位于命名空间 `Specializes`。
形式化陈述：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : Mul M] [ContinuousM
ul M] {a b c d : M},   a ⤳ b → c ⤳ d → (a * c) ⤳ (b * d)
参数：a * c；b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.smul`：∀ {M : Type u_1} {X : Type u_2} [inst : TopologicalSpa
ce M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [ContinuousSMul M X] {
a b : …
-/
protected theorem Specializes.mul {a b c d : M} (hab : a ⤳ b) (hcd : c ⤳ d) : (a * c) ⤳ (b * d) :=
  hab.smul hcd

@[to_additive]
/-
**Inseparable.mul** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : Mul M] [ContinuousM
ul M] {a b c d : M},   Inseparable a b → Inseparable c d → Inseparable (a * c) (
b * d)
参数：a * c；b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.smul`：∀ {M : Type u_1} {X : Type u_2} [inst : TopologicalSpa
ce M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [ContinuousSMul M X] {
a b : …
-/
protected theorem Inseparable.mul {a b c d : M} (hab : Inseparable a b) (hcd : Inseparable c d) :
    Inseparable (a * c) (b * d) :=
  hab.smul hcd

@[to_additive]
/-
**Specializes.pow** 是 Mathlib 中的一个定理，位于命名空间 `Specializes`。
形式化陈述：∀ {M : Type u_6} [inst : Monoid M] [inst_1 : TopologicalSpace M] [Continuo
usMul M] {a b : M},   a ⤳ b → ∀ (n : ℕ), (a ^ n) ⤳ (b ^ n)
参数：n : ℕ；a ^ n；b ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Specializes.mul`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : 
Mul M] [ContinuousMul M] {a b c d : M},   a ⤳ b → c ⤳ d → (a * c) ⤳ (b * d)
-/
protected theorem Specializes.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {a b : M} (h : a ⤳ b) (n : ℕ) : (a ^ n) ⤳ (b ^ n) :=
  Nat.recOn n (by simp only [pow_zero, specializes_rfl]) fun _ ihn ↦ by
    simpa only [pow_succ] using ihn.mul h

@[to_additive]
/-
**Inseparable.pow** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：∀ {M : Type u_6} [inst : Monoid M] [inst_1 : TopologicalSpace M] [Continuo
usMul M] {a b : M},   Inseparable a b → ∀ (n : ℕ), Inseparable (a ^ n) (b ^ n)
参数：n : ℕ；a ^ n；b ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.antisymm`：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x
 ~ᵢ y
· 使用定理 `Specializes.pow`：∀ {M : Type u_6} [inst : Monoid M] [inst_1 : Topologica
lSpace M] [ContinuousMul M] {a b : M},   a ⤳ b → ∀ (n : ℕ), (a ^ n) ⤳ (b ^ n)
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.specializes'`：Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x
-/
protected theorem Inseparable.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {a b : M} (h : Inseparable a b) (n : ℕ) : Inseparable (a ^ n) (b ^ n) :=
  (h.specializes.pow n).antisymm (h.specializes'.pow n)

/-- Construct a unit from limits of units and their inverses. -/
@[to_additive (attr := simps)
  /-- Construct an additive unit from limits of additive units and their negatives. -/]
/-
**Filter.Tendsto.units** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Filter.Tendsto.units [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2
Space N] {f : ι -> Nˣ} {r₁ r₂ : N} {l : Filter ι} [l.NeBot] (h₁ : Tendsto (fun x
 => ↑(f x)) l (𝓝 r₁)) (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ where val
参数：h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁)；h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝
 r₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Filter.Tendsto.units [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2Space N]
    {f : ι → Nˣ} {r₁ r₂ : N} {l : Filter ι} [l.NeBot] (h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁))
    (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ where
  val := r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁

@[to_additive]
/-
**Prod.continuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.continuousMul [TopologicalSpace N] [Mul N] [ContinuousMul N] : Contin
uousMul (M × N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g 
: X → M}…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
instance Prod.continuousMul [TopologicalSpace N] [Mul N] [ContinuousMul N] :
    ContinuousMul (M × N) :=
  ⟨by apply Continuous.prodMk <;> fun_prop⟩

@[to_additive]
/-
**Prod.separatelyContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.separatelyContinuousMul {M N : Type*} [TopologicalSpace M] [Mul M] [S
eparatelyContinuousMul M] [TopologicalSpace N] [Mul N] [SeparatelyContinuousMul 
N] : SeparatelyContinuousMul (M × N) where continuous_const_mul {_}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
-/
instance Prod.separatelyContinuousMul {M N : Type*}
    [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M]
    [TopologicalSpace N] [Mul N] [SeparatelyContinuousMul N] :
    SeparatelyContinuousMul (M × N) where
  continuous_const_mul {_} := by apply Continuous.prodMk <;> fun_prop
  continuous_mul_const {_} := by apply Continuous.prodMk <;> fun_prop

@[to_additive]
/-
**Pi.continuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.continuousMul {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [fora
ll i, Mul (C i)] [forall i, ContinuousMul (C i)] : ContinuousMul (forall i, C i)
 where continuous_mul
参数：C i；C i；C i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.snd'`：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.snd
-/
instance Pi.continuousMul {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, ContinuousMul (C i)] : ContinuousMul (∀ i, C i) where
  continuous_mul :=
    continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'

@[to_additive]
/-
**Pi.separatelyContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.separatelyContinuousMul {C : ι -> Type*} [forall i, TopologicalSpace (C
 i)] [forall i, Mul (C i)] [forall i, SeparatelyContinuousMul (C i)] : Separatel
yContinuousMul (forall i, C i) where continuous_mul_const {_}
参数：C i；C i；C i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
-/
instance Pi.separatelyContinuousMul {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, SeparatelyContinuousMul (C i)] : SeparatelyContinuousMul (∀ i, C i) where
  continuous_mul_const {_} := continuous_pi fun i ↦ (continuous_apply i).mul_const _
  continuous_const_mul {_} := continuous_pi fun i ↦ (continuous_apply i).const_mul _

/-- A version of `Pi.continuousMul` for non-dependent functions. It is needed because sometimes
Lean 3 fails to use `Pi.continuousMul` for non-dependent functions. -/
@[to_additive /-- A version of `Pi.continuousAdd` for non-dependent functions. It is needed
because sometimes Lean fails to use `Pi.continuousAdd` for non-dependent functions. -/]
/-
**Pi.continuousMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.continuousMul' : ContinuousMul (ι -> M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.continuousMul' : ContinuousMul (ι → M) :=
  Pi.continuousMul

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousMul_of_discreteTopology [TopologicalSpace N] [Mul N]
    [DiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousMul_of_indiscreteTopology [TopologicalSpace N] [Mul N]
    [IndiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_indiscreteTopology⟩

open Filter

open Function

@[to_additive]
/-
**ContinuousMul.of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMul.of_nhds_one {M : Type u} [Monoid M] [TopologicalSpace M] (hm
ul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1 ×ˢ 𝓝 1) <| 𝓝 1) (hleft : for
all x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) (hright : forall x₀ : M, 𝓝 x₀ = 
map (fun x => x * x₀) (𝓝 1)) : ContinuousMul M
参数：hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1 ×ˢ 𝓝 1) <| 𝓝 1；hleft : 
forall x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)；hright : forall x₀ : M, 𝓝 x₀ =
 map (fun x => x * x₀) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem ContinuousMul.of_nhds_one {M : Type u} [Monoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ˢ 𝓝 1) <| 𝓝 1)
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : ContinuousMul M :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key : (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) := by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x := by
      ext x
      simp [mul_assoc]
    calc
      map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ˢ 𝓝 y₀) := by
        rw [nhds_prod_eq]
      _ = map (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ˢ 𝓝 1) := by
        unfold uncurry
        rw [hleft x₀, hright y₀, prod_map_map_eq, Filter.map_map, Function.comp_def]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ˢ 𝓝 1)) := by
        rw [key, ← Filter.map_map]
      _ ≤ map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) := map_mono hmul
      _ = 𝓝 (x₀ * y₀) := by
        rw [← Filter.map_map, ← hright, hleft y₀, Filter.map_map, key₂, ← hleft]⟩

@[to_additive]
/-
**continuousMul_of_comm_of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [Topological
Space M] (hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)) (
hleft : forall x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : ContinuousMul M
参数：M : Type u；hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1
)；hleft : forall x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMul.of_nhds_one`：ContinuousMul.of_nhds_one {M : Type u} [Monoi
d M] [TopologicalSpace M] (hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1
 ×ˢ 𝓝 1) <| 𝓝 1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem continuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : ContinuousMul M := by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]

end ContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type*) [TopologicalSpace M₂] [T2Space M₂]

@[to_additive]
/-
**isClosed_setOfPred_map_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_map_one [One M₁] [One M₂] : IsClosed { f : M₁ -> M₂ | f
 1 = 1 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem isClosed_setOfPred_map_one [One M₁] [One M₂] : IsClosed { f : M₁ → M₂ | f 1 = 1 } :=
  isClosed_eq (continuous_apply 1) continuous_const

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_one := isClosed_setOfPred_map_one

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_zero := isClosed_setOfPred_map_zero

@[to_additive]
/-
**isClosed_setOfPred_map_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_map_mul [Mul M₁] [Mul M₂] [ContinuousMul M₂] : IsClosed
 { f : M₁ -> M₂ | forall x y, f (x * y) = f x * f y }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g 
: X → M}…
-/
theorem isClosed_setOfPred_map_mul [Mul M₁] [Mul M₂] [ContinuousMul M₂] :
    IsClosed { f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y } := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_eq (continuous_apply _) (by fun_prop)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_mul := isClosed_setOfPred_map_mul
@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_add := isClosed_setOfPred_map_add

section Semigroup

variable {M₁ M₂} [Mul M₁] [Mul M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MulHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled semigroup homomorphism `M₁ →ₙ* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →ₙ* M₂` (or another type of bundled
homomorphisms that has a `MulHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Construct a bundled additive semigroup homomorphism `M₁ →ₙ+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →ₙ+ M₂` (or another
type of bundled homomorphisms that has an `AddHomClass` instance) to `M₁ → M₂`. -/]
/-
**mulHomOfMemClosureRangeCoe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulHomOfMemClosureRangeCoe (f : M₁ -> M₂) (hf : f in closure (range fun (f
 : F) (x : M₁) => f x)) : M₁ ->ₙ* M₂ where toFun
参数：f : M₁ -> M₂；hf : f in closure (range fun (f : F) (x : M₁) => f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →ₙ* M₂ where
  toFun := f
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf

/-- Construct a bundled semigroup homomorphism from a pointwise limit of semigroup homomorphisms. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Construct a bundled additive semigroup homomorphism from a pointwise limit of additive
semigroup homomorphisms -/]
/-
**mulHomOfTendsto** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulHomOfTendsto (f : M₁ -> M₂) (g : α -> F) [l.NeBot] (h : Tendsto (fun a 
x => g a x) l (𝓝 f)) : M₁ ->ₙ* M₂
参数：f : M₁ -> M₂；g : α -> F；h : Tendsto (fun a x => g a x) l (𝓝 f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₙ* M₂ :=
  mulHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => mem_range_self _

variable (M₁ M₂)

@[to_additive]
/-
**MulHom.isClosed_range_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ ->ₙ* M₂) -> M₁ 
-> M₂))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
-/
theorem MulHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →ₙ* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨mulHomOfMemClosureRangeCoe f hf, rfl⟩

end Semigroup

section Monoid

variable {M₁ M₂} [MulOneClass M₁] [MulOneClass M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `MonoidHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another
type of bundled homomorphisms that has an `AddMonoidHomClass` instance) to `M₁ → M₂`. -/]
/-
**monoidHomOfMemClosureRangeCoe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monoidHomOfMemClosureRangeCoe (f : M₁ -> M₂) (hf : f in closure (range fun
 (f : F) (x : M₁) => f x)) : M₁ ->* M₂ where toFun
参数：f : M₁ -> M₂；hf : f in closure (range fun (f : F) (x : M₁) => f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →* M₂ where
  toFun := f
  map_one' := (isClosed_setOfPred_map_one M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOfPred_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Construct a bundled additive monoid homomorphism from a pointwise limit of additive
monoid homomorphisms -/]
/-
**monoidHomOfTendsto** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monoidHomOfTendsto (f : M₁ -> M₂) (g : α -> F) [l.NeBot] (h : Tendsto (fun
 a x => g a x) l (𝓝 f)) : M₁ ->* M₂
参数：f : M₁ -> M₂；g : α -> F；h : Tendsto (fun a x => g a x) l (𝓝 f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →* M₂ :=
  monoidHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => mem_range_self _

variable (M₁ M₂)

@[to_additive]
/-
**MonoidHom.isClosed_range_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ ->* M₂) -> M
₁ -> M₂))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
-/
theorem MonoidHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩

end Monoid

end PointwiseLimits

@[to_additive]
/-
**Topology.IsInducing.continuousMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike
 F M N] [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [Continuou
sMul N] (f : F) (hf : IsInducing f) : ContinuousMul M
参数：f : F；hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用引理 `Topology.IsInducing.continuousSMul`：Topology.IsInducing.continuousSMul {
N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M} (hg : IsInducing g) (hf 
: Continuous f) (hsmul :…
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
theorem Topology.IsInducing.continuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [ContinuousMul N] (f : F)
    (hf : IsInducing f) : ContinuousMul M :=
  ⟨(hf.continuousSMul hf.continuous (map_mul f _ _)).1⟩

@[to_additive]
/-
**continuousMul_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [Mul
HomClass F M N] [TopologicalSpace N] [ContinuousMul N] (f : F) : @ContinuousMul 
M (induced f ‹_›) _
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuousMul`：Topology.IsInducing.continuousMul {M 
N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] [TopologicalSpa
ce M] [TopologicalSpace…
-/
theorem continuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [TopologicalSpace N] [ContinuousMul N] (f : F) : @ContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.continuousMul f ⟨rfl⟩

@[to_additive]
/-
**Subsemigroup.continuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subsemigroup.continuousMul [TopologicalSpace M] [Semigroup M] [ContinuousM
ul M] (S : Subsemigroup M) : ContinuousMul S
参数：S : Subsemigroup M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuousMul`：Topology.IsInducing.continuousMul {M 
N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] [TopologicalSpa
ce M] [TopologicalSpace…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
instance Subsemigroup.continuousMul [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
    (S : Subsemigroup M) : ContinuousMul S :=
  IsInducing.continuousMul ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]
/-
**Submonoid.continuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.continuousMul [TopologicalSpace M] [Monoid M] [ContinuousMul M] 
(S : Submonoid M) : ContinuousMul S
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Submonoid.continuousMul [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    (S : Submonoid M) : ContinuousMul S :=
  S.toSubsemigroup.continuousMul

open MulOpposite in
@[to_additive]
/-
**Topology.IsInducing.separatelyContinuousMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.separatelyContinuousMul {M N F : Type*} [Mul M] [Mul N
] [FunLike F M N] [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] 
[SeparatelyContinuousMul N] (f : F) (hf : IsInducing f) : SeparatelyContinuousMu
l M where continuous_const_mul
参数：f : F；hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `Topology.IsInducing.continuousConstSMul`：Topology.IsInducing.continuousC
onstSMul {N β : Type*} [SMul N β] [TopologicalSpace β] {g : β -> α} (hg : IsIndu
cing g) (f : N -> M) (hf : fo…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulOpposite.opHomeomorph_symm_apply`：∀ {M : Type u_1} [inst : Topologica
lSpace M] (a : Mᵐᵒᵖ), MulOpposite.opHomeomorph.symm a = MulOpposite.unop a
· 使用定理 `MulOpposite.opHomeomorph_apply`：∀ {M : Type u_1} [inst : TopologicalSpac
e M] (a : M), MulOpposite.opHomeomorph a = MulOpposite.op a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
-/
theorem Topology.IsInducing.separatelyContinuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [SeparatelyContinuousMul N]
    (f : F) (hf : IsInducing f) : SeparatelyContinuousMul M where
  continuous_const_mul := (hf.continuousConstSMul f (map_mul f _ _)).1 _
  continuous_mul_const {m} :=
    have := ((opHomeomorph.isInducing.comp hf).comp (opHomeomorph.symm.isInducing)
      |>.continuousConstSMul (fun x ↦ op (f (unop x))) (by simp)).1 (op m)
    continuous_unop.comp <| this.comp continuous_op

@[to_additive]
/-
**separatelyContinuousMul_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separatelyContinuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F
 M N] [MulHomClass F M N] [TopologicalSpace N] [SeparatelyContinuousMul N] (f : 
F) : @SeparatelyContinuousMul M (induced f ‹_›) _
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.separatelyContinuousMul`：Topology.IsInducing.separat
elyContinuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F 
M N] [TopologicalSpace M] [Topolo…
-/
theorem separatelyContinuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace N] [SeparatelyContinuousMul N] (f : F) :
    @SeparatelyContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.separatelyContinuousMul f ⟨rfl⟩

@[to_additive]
/-
**Subsemigroup.separatelyContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subsemigroup.separatelyContinuousMul [TopologicalSpace M] [Semigroup M] [S
eparatelyContinuousMul M] (S : Subsemigroup M) : SeparatelyContinuousMul S
参数：S : Subsemigroup M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.separatelyContinuousMul`：Topology.IsInducing.separat
elyContinuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F 
M N] [TopologicalSpace M] [Topolo…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
instance Subsemigroup.separatelyContinuousMul [TopologicalSpace M] [Semigroup M]
    [SeparatelyContinuousMul M] (S : Subsemigroup M) : SeparatelyContinuousMul S :=
  IsInducing.separatelyContinuousMul
    ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]
/-
**Submonoid.separatelyContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.separatelyContinuousMul [TopologicalSpace M] [Monoid M] [Separat
elyContinuousMul M] (S : Submonoid M) : SeparatelyContinuousMul S
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Submonoid.separatelyContinuousMul [TopologicalSpace M] [Monoid M]
    [SeparatelyContinuousMul M] (S : Submonoid M) : SeparatelyContinuousMul S :=
  S.toSubsemigroup.separatelyContinuousMul
section MulZeroClass

open Filter

variable {α β : Type*}
variable [TopologicalSpace M] [MulZeroClass M] [ContinuousMul M]

/-
**exists_mem_nhds_zero_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_nhds_zero_mul_subset {K U : Set M} (hK : IsCompact K) (hU : U i
n 𝓝 0) : exists V in 𝓝 0, K * V subseteq U
参数：hK : IsCompact K；hU : U in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_mul`：empty_mul : ∅ * s = ∅
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.union_mul`：union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Set.image_mul_prod`：image_mul_prod : (fun x : α × α => x.fst * x.snd) ''
 s ×ˢ t = s * t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem exists_mem_nhds_zero_mul_subset
    {K U : Set M} (hK : IsCompact K) (hU : U ∈ 𝓝 0) : ∃ V ∈ 𝓝 0, K * V ⊆ U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 0) by simpa using hU)
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M` which is disjoint from the cocompact filter. Then, the multiplication map
`M × M → M` tends to zero on the filter product `𝓝 0 ×ˢ l`. -/
/-
**tendsto_mul_nhds_zero_prod_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul_nhds_zero_prod_of_disjoint_cocompact {l : Filter M} (hl : Disj
oint l (cocompact M)) : Tendsto (fun x : M × M => x.1 * x.2) (𝓝 0 ×ˢ l) (𝓝 0)
参数：hl : Disjoint l (cocompact M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `nhds_prod_le_of_disjoint_cocompact`：nhds_prod_le_of_disjoint_cocompact {
f : Filter Y} (x : X) (hf : Disjoint f (Filter.cocompact Y)) : 𝓝 x ×ˢ f <= 𝓝ˢ ({
x} ×ˢ Set.univ)
· 使用引理 `Continuous.tendsto_nhdsSet_nhds`：Continuous.tendsto_nhdsSet_nhds {b : β}
 {f : α -> β} (h : Continuous f) (h' : EqOn f (fun _ => b) s) : Tendsto f (𝓝ˢ s)
 (𝓝 b)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0

--- 原说明 ---
Let `M` be a topological space with a continuous multiplication operation and a 
`0`.
Let `l` be a filter on `M` which is disjoint from the cocompact filter. Then, th
e multiplication map
`M × M → M` tends to zero on the filter product `𝓝 0 ×ˢ l`.
-/
theorem tendsto_mul_nhds_zero_prod_of_disjoint_cocompact {l : Filter M}
    (hl : Disjoint l (cocompact M)) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) (𝓝 0 ×ˢ l) (𝓝 0) := calc
  map (fun x : M × M ↦ x.1 * x.2) (𝓝 0 ×ˢ l)
  _ ≤ map (fun x : M × M ↦ x.1 * x.2) (𝓝ˢ ({0} ×ˢ Set.univ)) :=
    map_mono <| nhds_prod_le_of_disjoint_cocompact 0 hl
  _ ≤ 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨hx, _⟩ ↦ mul_eq_zero_of_left hx _

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M` which is disjoint from the cocompact filter. Then, the multiplication map
`M × M → M` tends to zero on the filter product `l ×ˢ 𝓝 0`. -/
/-
**tendsto_mul_prod_nhds_zero_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul_prod_nhds_zero_of_disjoint_cocompact {l : Filter M} (hl : Disj
oint l (cocompact M)) : Tendsto (fun x : M × M => x.1 * x.2) (l ×ˢ 𝓝 0) (𝓝 0)
参数：hl : Disjoint l (cocompact M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `prod_nhds_le_of_disjoint_cocompact`：prod_nhds_le_of_disjoint_cocompact {
f : Filter X} (y : Y) (hf : Disjoint f (Filter.cocompact X)) : f ×ˢ 𝓝 y <= 𝓝ˢ (S
et.univ ×ˢ {y})
· 使用引理 `Continuous.tendsto_nhdsSet_nhds`：Continuous.tendsto_nhdsSet_nhds {b : β}
 {f : α -> β} (h : Continuous f) (h' : EqOn f (fun _ => b) s) : Tendsto f (𝓝ˢ s)
 (𝓝 b)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0

--- 原说明 ---
Let `M` be a topological space with a continuous multiplication operation and a 
`0`.
Let `l` be a filter on `M` which is disjoint from the cocompact filter. Then, th
e multiplication map
`M × M → M` tends to zero on the filter product `l ×ˢ 𝓝 0`.
-/
theorem tendsto_mul_prod_nhds_zero_of_disjoint_cocompact {l : Filter M}
    (hl : Disjoint l (cocompact M)) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) (l ×ˢ 𝓝 0) (𝓝 0) := calc
  map (fun x : M × M ↦ x.1 * x.2) (l ×ˢ 𝓝 0)
  _ ≤ map (fun x : M × M ↦ x.1 * x.2) (𝓝ˢ (Set.univ ×ˢ {0})) :=
    map_mono <| prod_nhds_le_of_disjoint_cocompact 0 hl
  _ ≤ 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨_, hx⟩ ↦ mul_eq_zero_of_right _ hx

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M × M` which is disjoint from the cocompact filter. Then, the multiplication
map `M × M → M` tends to zero on `(𝓝 0).coprod (𝓝 0) ⊓ l`. -/
/-
**tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact {l : Filter (M × M)
} (hl : Disjoint l (cocompact (M × M))) : Tendsto (fun x : M × M => x.1 * x.2) (
(𝓝 0).coprod (𝓝 0) ⊓ l) (𝓝 0)
参数：M × M；hl : Disjoint l (cocompact (M × M))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Filter.le_prod_map_fst_snd`：le_prod_map_fst_snd {f : Filter (α × β)} : f
 <= map Prod.fst f ×ˢ map Prod.snd f
· 使用定理 `Filter.coprod_inf_prod_le`：coprod_inf_prod_le (f₁ f₂ : Filter α) (g₁ g₂ 
: Filter β) : f₁.coprod g₁ ⊓ f₂ ×ˢ g₂ <= f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.sup`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y : Filter β},   Filter.Tendsto f x₁ y → Filter.Tendsto f x₂ y → Fil
ter.Tend…
· 使用定理 `tendsto_mul_nhds_zero_prod_of_disjoint_cocompact`：tendsto_mul_nhds_zero_
prod_of_disjoint_cocompact {l : Filter M} (hl : Disjoint l (cocompact M)) : Tend
sto (fun x : M × M => x.1 * x.2) (𝓝 0 …
· 使用定理 `disjoint_map_cocompact`：disjoint_map_cocompact {g : X -> Y} {f : Filter 
X} (hg : Continuous g) (hf : Disjoint f (Filter.cocompact X)) : Disjoint (map g 
f) (Filter.c…
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `tendsto_mul_prod_nhds_zero_of_disjoint_cocompact`：tendsto_mul_prod_nhds_
zero_of_disjoint_cocompact {l : Filter M} (hl : Disjoint l (cocompact M)) : Tend
sto (fun x : M × M => x.1 * x.2) (l ×ˢ…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
Let `M` be a topological space with a continuous multiplication operation and a 
`0`.
Let `l` be a filter on `M × M` which is disjoint from the cocompact filter. Then
, the multiplication
map `M × M → M` tends to zero on `(𝓝 0).coprod (𝓝 0) ⊓ l`.
-/
theorem tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact {l : Filter (M × M)}
    (hl : Disjoint l (cocompact (M × M))) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) ((𝓝 0).coprod (𝓝 0) ⊓ l) (𝓝 0) := by
  have := calc
    (𝓝 0).coprod (𝓝 0) ⊓ l
    _ ≤ (𝓝 0).coprod (𝓝 0) ⊓ map Prod.fst l ×ˢ map Prod.snd l :=
      inf_le_inf_left _ le_prod_map_fst_snd
    _ ≤ 𝓝 0 ×ˢ map Prod.snd l ⊔ map Prod.fst l ×ˢ 𝓝 0 :=
      coprod_inf_prod_le _ _ _ _
  apply (Tendsto.sup _ _).mono_left this
  · apply tendsto_mul_nhds_zero_prod_of_disjoint_cocompact
    exact disjoint_map_cocompact continuous_snd hl
  · apply tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
    exact disjoint_map_cocompact continuous_fst hl

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M × M` which is both disjoint from the cocompact filter and less than or
equal to `(𝓝 0).coprod (𝓝 0)`. Then the multiplication map `M × M → M` tends to zero on `l`. -/
/-
**tendsto_mul_nhds_zero_of_disjoint_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul_nhds_zero_of_disjoint_cocompact {l : Filter (M × M)} (hl : Dis
joint l (cocompact (M × M))) (h'l : l <= (𝓝 0).coprod (𝓝 0)) : Tendsto (fun x : 
M × M => x.1 * x.2) l (𝓝 0)
参数：M × M；hl : Disjoint l (cocompact (M × M))；h'l : l <= (𝓝 0).coprod (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact`：tendsto_mul_copr
od_nhds_zero_inf_of_disjoint_cocompact {l : Filter (M × M)} (hl : Disjoint l (co
compact (M × M))) : Tendsto (fun x : M × M =…

--- 原说明 ---
Let `M` be a topological space with a continuous multiplication operation and a 
`0`.
Let `l` be a filter on `M × M` which is both disjoint from the cocompact filter 
and less than or
equal to `(𝓝 0).coprod (𝓝 0)`. Then the multiplication map `M × M → M` tends to 
zero on `l`.
-/
theorem tendsto_mul_nhds_zero_of_disjoint_cocompact {l : Filter (M × M)}
    (hl : Disjoint l (cocompact (M × M))) (h'l : l ≤ (𝓝 0).coprod (𝓝 0)) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) l (𝓝 0) := by
  simpa [inf_eq_right.mpr h'l] using tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact hl

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `f : α → M` and `g : α → M` be functions. If `f` tends to zero on a filter `l`
and the image of `l` under `g` is disjoint from the cocompact filter on `M`, then
`fun x : α ↦ f x * g x` also tends to zero on `l`. -/
/-
**Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right {f g : α -> M} {l : F
ilter α} (hf : Tendsto f l (𝓝 0)) (hg : Disjoint (map g l) (cocompact M)) : Tend
sto (fun x => f x * g x) l (𝓝 0)
参数：hf : Tendsto f l (𝓝 0)；hg : Disjoint (map g l) (cocompact M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_mul_nhds_zero_prod_of_disjoint_cocompact`：tendsto_mul_nhds_zero_
prod_of_disjoint_cocompact {l : Filter M} (hl : Disjoint l (cocompact M)) : Tend
sto (fun x : M × M => x.1 * x.2) (𝓝 0 …
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
Let `M` be a topological space with a continuous multiplication operation and a 
`0`.
Let `f : α → M` and `g : α → M` be functions. If `f` tends to zero on a filter `
l`
and the image of `l` under `g` is disjoint from the cocompact filter on `M`, the
n
`fun x : α ↦ f x * g x` also tends to zero on `l`.
-/
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right {f g : α → M} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : Disjoint (map g l) (cocompact M)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) :=
  tendsto_mul_nhds_zero_prod_of_disjoint_cocompact hg |>.comp (hf.prodMk tendsto_map)

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `f : α → M` and `g : α → M` be functions. If `g` tends to zero on a filter `l`
and the image of `l` under `f` is disjoint from the cocompact filter on `M`, then
`fun x : α ↦ f x * g x` also tends to zero on `l`. -/
/-
**Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left {f g : α -> M} {l : Fi
lter α} (hf : Disjoint (map f l) (cocompact M)) (hg : Tendsto g l (𝓝 0)) : Tends
to (fun x => f x * g x) l (𝓝 0)
参数：hf : Disjoint (map f l) (cocompact M)；hg : Tendsto g l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_mul_prod_nhds_zero_of_disjoint_cocompact`：tendsto_mul_prod_nhds_
zero_of_disjoint_cocompact {l : Filter M} (hl : Disjoint l (cocompact M)) : Tend
sto (fun x : M × M => x.1 * x.2) (l ×ˢ…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
Let `M` be a topological space with a continuous multiplication operation and a 
`0`.
Let `f : α → M` and `g : α → M` be functions. If `g` tends to zero on a filter `
l`
and the image of `l` under `f` is disjoint from the cocompact filter on `M`, the
n
`fun x : α ↦ f x * g x` also tends to zero on `l`.
-/
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left {f g : α → M} {l : Filter α}
    (hf : Disjoint (map f l) (cocompact M)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) :=
  tendsto_mul_prod_nhds_zero_of_disjoint_cocompact hf |>.comp (tendsto_map.prodMk hg)

/-- If `f : α → M` and `g : β → M` are continuous and both tend to zero on the cocompact filter,
then `fun i : α × β ↦ f i.1 * g i.2` also tends to zero on the cocompact filter. -/
/-
**tendsto_mul_cocompact_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul_cocompact_nhds_zero [TopologicalSpace α] [TopologicalSpace β] 
{f : α -> M} {g : β -> M} (f_cont : Continuous f) (g_cont : Continuous g) (hf : 
Tendsto f (cocompact α) (𝓝 0)) (hg : Tendsto g (cocompact β) (𝓝 0)) : Tendsto (f
un i : α × β => f i.1 * g i.2) (cocompact (α × β)) (𝓝 0)
参数：f_cont : Continuous f；g_cont : Continuous g；hf : Tendsto f (cocompact α) (𝓝 0
)；hg : Tendsto g (cocompact β) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `Filter.Tendsto.isCompact_insert_range_of_cocompact`：∀ {X : Type u} {Y : 
Type v} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {y
 : Y},   Filter.Tendsto f (Filter.cocomp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.disjoint_cocompact_right`：disjoint_cocompact_right (f : Filter X)
 : Disjoint f (Filter.cocompact X) ↔ exists K in f, IsCompact K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.coprod_cocompact`：Filter.coprod_cocompact : (Filter.cocompact X).
coprod (Filter.cocompact Y) = Filter.cocompact (X × Y)
· 使用定理 `Filter.Tendsto.prodMap_coprod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c 
: Filter γ} {d : Fi…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_mul_nhds_zero_of_disjoint_cocompact`：tendsto_mul_nhds_zero_of_di
sjoint_cocompact {l : Filter (M × M)} (hl : Disjoint l (cocompact (M × M))) (h'l
 : l <= (𝓝 0).coprod (𝓝 0)) : Ten…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
If `f : α → M` and `g : β → M` are continuous and both tend to zero on the cocom
pact filter,
then `fun i : α × β ↦ f i.1 * g i.2` also tends to zero on the cocompact filter.
-/
theorem tendsto_mul_cocompact_nhds_zero [TopologicalSpace α] [TopologicalSpace β]
    {f : α → M} {g : β → M} (f_cont : Continuous f) (g_cont : Continuous g)
    (hf : Tendsto f (cocompact α) (𝓝 0)) (hg : Tendsto g (cocompact β) (𝓝 0)) :
    Tendsto (fun i : α × β ↦ f i.1 * g i.2) (cocompact (α × β)) (𝓝 0) := by
  set l : Filter (M × M) := map (Prod.map f g) (cocompact (α × β)) with l_def
  set K : Set (M × M) := (insert 0 (range f)) ×ˢ (insert 0 (range g))
  have K_compact : IsCompact K := .prod (hf.isCompact_insert_range_of_cocompact f_cont)
    (hg.isCompact_insert_range_of_cocompact g_cont)
  have K_mem_l : K ∈ l := eventually_map.mpr <| .of_forall fun ⟨x, y⟩ ↦
    ⟨mem_insert_of_mem _ (mem_range_self _), mem_insert_of_mem _ (mem_range_self _)⟩
  have l_compact : Disjoint l (cocompact (M × M)) := by
    rw [disjoint_cocompact_right]
    exact ⟨K, K_mem_l, K_compact⟩
  have l_le_coprod : l ≤ (𝓝 0).coprod (𝓝 0) := by
    rw [l_def, ← coprod_cocompact]
    exact hf.prodMap_coprod hg
  exact tendsto_mul_nhds_zero_of_disjoint_cocompact l_compact l_le_coprod |>.comp tendsto_map

/-- If `f : α → M` and `g : β → M` both tend to zero on the cofinite filter, then so does
`fun i : α × β ↦ f i.1 * g i.2`. -/
/-
**tendsto_mul_cofinite_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul_cofinite_nhds_zero {f : α -> M} {g : β -> M} (hf : Tendsto f c
ofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) : Tendsto (fun i : α × β => f i.1
 * g i.2) cofinite (𝓝 0)
参数：hf : Tendsto f cofinite (𝓝 0)；hg : Tendsto g cofinite (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `discreteTopology_bot`：discreteTopology_bot (α : Type*) : @DiscreteTopolo
gy α ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.cocompact_eq_cofinite`：cocompact_eq_cofinite (X : Type*) [Topolog
icalSpace X] [DiscreteTopology X] : cocompact X = cofinite
· 使用定理 `instDiscreteTopologyProd`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   [DiscreteTopology
 Y], DiscreteT…
· 使用定理 `tendsto_mul_cocompact_nhds_zero`：tendsto_mul_cocompact_nhds_zero [Topolo
gicalSpace α] [TopologicalSpace β] {f : α -> M} {g : β -> M} (f_cont : Continuou
s f) (g_cont : Contin…
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f

--- 原说明 ---
If `f : α → M` and `g : β → M` both tend to zero on the cofinite filter, then so
 does
`fun i : α × β ↦ f i.1 * g i.2`.
-/
theorem tendsto_mul_cofinite_nhds_zero {f : α → M} {g : β → M}
    (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun i : α × β ↦ f i.1 * g i.2) cofinite (𝓝 0) := by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := discreteTopology_bot α
  let : TopologicalSpace β := ⊥
  have : DiscreteTopology β := discreteTopology_bot β
  rw [← cocompact_eq_cofinite] at *
  exact tendsto_mul_cocompact_nhds_zero
    continuous_of_discreteTopology continuous_of_discreteTopology hf hg

end MulZeroClass

section GroupWithZero

/-
**GroupWithZero.isOpen_singleton_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupWithZero.isOpen_singleton_zero [GroupWithZero M] [TopologicalSpace M]
 [ContinuousMul M] [CompactSpace M] [T1Space M] : IsOpen {(0 : M)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t1Space_iff_exists_open`：t1Space_iff_exists_open : T1Space X ↔ Pairwise 
fun x y => exists U : Set X, IsOpen U ∧ x in U ∧ y ∉ U
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `exists_mem_nhds_zero_mul_subset`：exists_mem_nhds_zero_mul_subset {K U : 
Set M} (hK : IsCompact K) (hU : U in 𝓝 0) : exists V in 𝓝 0, K * V subseteq U
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma GroupWithZero.isOpen_singleton_zero [GroupWithZero M] [TopologicalSpace M]
    [ContinuousMul M] [CompactSpace M] [T1Space M] :
    IsOpen {(0 : M)} := by
  obtain ⟨U, hU, h0U, h1U⟩ := t1Space_iff_exists_open.mp ‹_› zero_ne_one
  obtain ⟨W, hW, hW'⟩ := exists_mem_nhds_zero_mul_subset isCompact_univ (hU.mem_nhds h0U)
  by_cases H : ∃ x ≠ 0, x ∈ W
  · obtain ⟨x, hx, hxW⟩ := H
    cases h1U (hW' (by simpa [hx] using Set.mul_mem_mul (Set.mem_univ x⁻¹) hxW))
  · obtain rfl : W = {0} := subset_antisymm
      (by simpa [not_imp_not] using H) (by simpa using mem_of_mem_nhds hW)
    simpa [isOpen_iff_mem_nhds]

end GroupWithZero

section MulOneClass

variable [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

@[to_additive exists_open_nhds_zero_half]
/-
**exists_open_nhds_one_split** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_nhds_one_split {s : Set M} (hs : s in 𝓝 (1 : M)) : exists V : 
Set M, IsOpen V ∧ (1 : M) in V ∧ forall v in V, forall w in V, v * w in s
参数：hs : s in 𝓝 (1 : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_nhds_square`：exists_nhds_square {s : Set (X × X)} {x : X} (hx : s
 in 𝓝 (x, x)) : exists U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subseteq s
-/
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s := by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s ∈ 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using! hs)
  simpa only [prod_subset_iff] using! exists_nhds_square this

@[to_additive exists_nhds_zero_half]
/-
**exists_nhds_one_split** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_one_split {s : Set M} (hs : s in 𝓝 (1 : M)) : exists V in 𝓝 (1
 : M), forall v in V, forall w in V, v * w in s
参数：hs : s in 𝓝 (1 : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_nhds_one_split`：exists_open_nhds_one_split {s : Set M} (hs :
 s in 𝓝 (1 : M)) : exists V : Set M, IsOpen V ∧ (1 : M) in V ∧ forall v in V, fo
rall w in V, v *…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem exists_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `V * V ⊆ U`. -/
@[to_additive /-- Given an open neighborhood `U` of `0` there is an open neighborhood `V` of `0`
  such that `V + V ⊆ U`. -/]
/-
**exists_open_nhds_one_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_nhds_one_mul_subset {U : Set M} (hU : U in 𝓝 (1 : M)) : exists
 V : Set M, IsOpen V ∧ (1 : M) in V ∧ V * V subseteq U
参数：hU : U in 𝓝 (1 : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_open_nhds_one_split`：exists_open_nhds_one_split {s : Set M} (hs :
 s in 𝓝 (1 : M)) : exists V : Set M, IsOpen V ∧ (1 : M) in V ∧ forall v in V, fo
rall w in V, v *…
-/
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ V * V ⊆ U := by
  simpa only [mul_subset_iff] using exists_open_nhds_one_split hU

@[to_additive]
/-
**Filter.HasBasis.mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.mul_self {p : ι -> Prop} {s : ι -> Set M} (h : (𝓝 1).HasBa
sis p s) : (𝓝 1).HasBasis p fun i => s i * s i
参数：h : (𝓝 1).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_mul_nhds_one`：nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpa
ce M] [ContinuousMul M] (a : M) : 𝓝 a * 𝓝 1 = 𝓝 a
· 使用定理 `Filter.map₂_mul`：map₂_mul : map₂ (· * ·) f g = f * g
· 使用定理 `Filter.map_uncurry_prod`：map_uncurry_prod (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : (f ×ˢ g).map (uncurry m) = map₂ m f g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
-/
theorem Filter.HasBasis.mul_self {p : ι → Prop} {s : ι → Set M} (h : (𝓝 1).HasBasis p s) :
    (𝓝 1).HasBasis p fun i => s i * s i := by
  rw [← nhds_mul_nhds_one, ← map₂_mul, ← map_uncurry_prod]
  simpa only [← image_mul_prod] using! h.prod_self.map _

end MulOneClass

section ContinuousMul

section Semigroup

variable [TopologicalSpace M] [Semigroup M] [SeparatelyContinuousMul M]

@[to_additive]
/-
**Subsemigroup.top_closure_mul_self_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.top_closure_mul_self_subset (s : Subsemigroup M) : _root_.clo
sure (s : Set M) * _root_.closure s subseteq _root_.closure s
参数：s : Subsemigroup M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `map_mem_closure₂'`：map_mem_closure₂' {f : X -> Y -> Z} {x : X} {y : Y} {
s : Set X} {t : Set Y} {u : Set Z} (hf₁ : forall x, Continuous (f x)) (hf₂ : for
all y, …
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `Subsemigroup.mul_mem`：∀ {M : Type u_1} [inst : Mul M] (S : Subsemigroup 
M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
-/
theorem Subsemigroup.top_closure_mul_self_subset (s : Subsemigroup M) :
    _root_.closure (s : Set M) * _root_.closure s ⊆ _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const
      hx hy fun _ ha _ hb => s.mul_mem ha hb

/-- The (topological-space) closure of a subsemigroup of a space `M` with `ContinuousMul` is
itself a subsemigroup. -/
@[to_additive /-- The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid. -/]
/-
**Subsemigroup.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemigroup.topologicalClosure (s : Subsemigroup M) : Subsemigroup M wher
e carrier
参数：s : Subsemigroup M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subsemigroup.topologicalClosure (s : Subsemigroup M) : Subsemigroup M where
  carrier := _root_.closure (s : Set M)
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]
/-
**Subsemigroup.coe_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.coe_topologicalClosure (s : Subsemigroup M) : (s.topologicalC
losure : Set M) = _root_.closure (s : Set M)
参数：s : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subsemigroup.coe_topologicalClosure (s : Subsemigroup M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
/-
**Subsemigroup.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.le_topologicalClosure (s : Subsemigroup M) : s <= s.topologic
alClosure
参数：s : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subsemigroup.le_topologicalClosure (s : Subsemigroup M) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
/-
**Subsemigroup.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.isClosed_topologicalClosure (s : Subsemigroup M) : IsClosed (
s.topologicalClosure : Set M)
参数：s : Subsemigroup M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Subsemigroup.isClosed_topologicalClosure (s : Subsemigroup M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

@[to_additive]
/-
**Subsemigroup.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.topologicalClosure_minimal (s : Subsemigroup M) {t : Subsemig
roup M} (h : s <= t) (ht : IsClosed (t : Set M)) : s.topologicalClosure <= t
参数：s : Subsemigroup M；h : s <= t；ht : IsClosed (t : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Subsemigroup.topologicalClosure_minimal (s : Subsemigroup M) {t : Subsemigroup M}
    (h : s ≤ t) (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t := closure_minimal h ht

@[to_additive (attr := gcongr)]
/-
**Subsemigroup.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.topologicalClosure_mono {s t : Subsemigroup M} (h : s <= t) :
 s.topologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Subsemigroup.topologicalClosure_mono {s t : Subsemigroup M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a subsemigroup of a topological semigroup is commutative, then so is its topological
closure.

See note [reducible non-instances] -/
@[to_additive /-- If a submonoid of an additive topological monoid is commutative, then so is its
topological closure.

See note [reducible non-instances] -/]
/-
**Subsemigroup.commSemigroupTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subsemigroup.commSemigroupTopologicalClosure [T2Space M] (s : Subsemigroup
 M) (hs : forall x y : s, x * y = y * x) : CommSemigroup s.topologicalClosure
参数：s : Subsemigroup M；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Subsemigroup.commSemigroupTopologicalClosure [T2Space M] (s : Subsemigroup M)
    (hs : ∀ x y : s, x * y = y * x) : CommSemigroup s.topologicalClosure :=
  { MulMemClass.toSemigroup s.topologicalClosure with
    mul_comm :=
      have : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      Subtype.ext <| by
        refine eqOn_closure₂' this ?_ ?_ ?_ ?_ x hx y hy
        all_goals fun_prop }

@[to_additive]
/-
**IsCompact.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mul [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
 (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t)
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_mul_prod`：image_mul_prod : (fun x : α × α => x.fst * x.snd) ''
 s ×ˢ t = s * t
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
theorem IsCompact.mul [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul

end Semigroup

variable [TopologicalSpace M] [Monoid M]

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul M]

@[to_additive]
/-
**Submonoid.top_closure_mul_self_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.top_closure_mul_self_subset (s : Submonoid M) : _root_.closure (
s : Set M) * _root_.closure s subseteq _root_.closure s
参数：s : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `map_mem_closure₂'`：map_mem_closure₂' {f : X -> Y -> Z} {x : X} {y : Y} {
s : Set X} {t : Set Y} {u : Set Z} (hf₁ : forall x, Continuous (f x)) (hf₂ : for
all y, …
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
-/
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s ⊆ _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const hx hy
      fun _ ha _ hb ↦ s.mul_mem ha hb

@[to_additive]
/-
**Submonoid.top_closure_mul_self_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.top_closure_mul_self_eq (s : Submonoid M) : _root_.closure (s : 
Set M) * _root_.closure s = _root_.closure s
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Submonoid.top_closure_mul_self_subset`：Submonoid.top_closure_mul_self_su
bset (s : Submonoid M) : _root_.closure (s : Set M) * _root_.closure s subseteq 
_root_.closure s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s = _root_.closure s :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, hx, 1, _root_.subset_closure s.one_mem, mul_one _⟩

/-- The (topological-space) closure of a submonoid of a space `M` with `ContinuousMul` is
itself a submonoid. -/
@[to_additive /-- The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid. -/]
/-
**Submonoid.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M where carrier
参数：s : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M where
  carrier := _root_.closure (s : Set M)
  one_mem' := _root_.subset_closure s.one_mem
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]
/-
**Submonoid.coe_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.coe_topologicalClosure (s : Submonoid M) : (s.topologicalClosure
 : Set M) = _root_.closure (s : Set M)
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Submonoid.coe_topologicalClosure (s : Submonoid M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
/-
**Submonoid.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.le_topologicalClosure (s : Submonoid M) : s <= s.topologicalClos
ure
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Submonoid.le_topologicalClosure (s : Submonoid M) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
/-
**Submonoid.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.isClosed_topologicalClosure (s : Submonoid M) : IsClosed (s.topo
logicalClosure : Set M)
参数：s : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Submonoid.isClosed_topologicalClosure (s : Submonoid M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

@[to_additive]
/-
**Submonoid.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (
h : s <= t) (ht : IsClosed (t : Set M)) : s.topologicalClosure <= t
参数：s : Submonoid M；h : s <= t；ht : IsClosed (t : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t := closure_minimal h ht

@[to_additive (attr := gcongr)]
/-
**Submonoid.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.topologicalClosure_mono {s t : Submonoid M} (h : s <= t) : s.top
ologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Submonoid.topologicalClosure_mono {s t : Submonoid M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive /-- If a submonoid of an additive topological monoid is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/]
/-
**Submonoid.commMonoidTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M) (hs :
 forall x y : s, x * y = y * x) : CommMonoid s.topologicalClosure
参数：s : Submonoid M；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M)
    (hs : ∀ x y : s, x * y = y * x) : CommMonoid s.topologicalClosure :=
  { s.topologicalClosure.toMonoid, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

/-- Left-multiplication by a left-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
/-
**Filter.tendsto_cocompact_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) : Filter.Tend
sto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M)
参数：ha : b * a = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_tendsto_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ},   F
ilter.Tendsto (g ∘ f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)

--- 原说明 ---
Left-multiplication by a left-invertible element of a topological monoid is prop
er, i.e.,
inverse images of compact sets are compact.
-/
theorem Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
    Filter.Tendsto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_const_mul b))
  convert! Filter.tendsto_id
  ext x
  simp [← mul_assoc, ha]

/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
/-
**Filter.tendsto_cocompact_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) : Filter.Ten
dsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M)
参数：ha : a * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_tendsto_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ},   F
ilter.Tendsto (g ∘ f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `comp_mul_right`：comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y *
 x))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)

--- 原说明 ---
Right-multiplication by a right-invertible element of a topological monoid is pr
oper, i.e.,
inverse images of compact sets are compact.
-/
theorem Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
    Filter.Tendsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_const b))
  simp only [comp_mul_right, ha, mul_one]
  exact Filter.tendsto_id

end SeparatelyContinuousMul

variable [ContinuousMul M]

@[to_additive exists_nhds_zero_quarter]
/-
**exists_nhds_one_split4** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_one_split4 {u : Set M} (hu : u in 𝓝 (1 : M)) : exists V in 𝓝 (
1 : M), forall {v w s t}, v in V -> w in V -> s in V -> t in V -> v * w * s * t 
in u
参数：hu : u in 𝓝 (1 : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nhds_one_split`：exists_nhds_one_split {s : Set M} (hs : s in 𝓝 (1
 : M)) : exists V in 𝓝 (1 : M), forall v in V, forall w in V, v * w in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u := by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

@[to_additive]
/-
**tendsto_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : Monoid M] [ContinuousMul M]   {f : ι → α → M} {x : Filter α} {a : ι →
 M} (l : List ι),   (∀ i ∈ l, Filter.Tendsto (f i) x (nhds (a i))) →     Filter.
Tendsto (fun b => (List.map (fun c => f c b) l).prod) x (nhds (List.map a l).pro
d)
参数：l : List ι；∀ i ∈ l, Filter.Tendsto (f i) x (nhds (a i))；fun b => (List.map (f
un c => f c b) l).prod；nhds (List.map a l).prod。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
    ∀ l : List ι,
      (∀ i ∈ l, Tendsto (f i) x (𝓝 (a i))) →
        Tendsto (fun b => (l.map fun c => f c b).prod) x (𝓝 (l.map a).prod)
  | [], _ => by simp [tendsto_const_nhds]
  | f::l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact
      (h f List.mem_cons_self).mul
        (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_mem _ hc))

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_list_prod {f : ι -> X -> M} (l : List ι) (h : forall i in l, Co
ntinuous (f i)) : Continuous fun a => (l.map fun i => f i a).prod
参数：l : List ι；h : forall i in l, Continuous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `tendsto_list_prod`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : Monoid M] [ContinuousMul M]   {f : ι → α → M} {x
 : Filt…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i ∈ l, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).prod :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x

@[to_additive]
/-
**continuousOn_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_list_prod {f : ι -> X -> M} (l : List ι) {t : Set X} (h : for
all i in l, ContinuousOn (f i) t) : ContinuousOn (fun a => (l.map fun i => f i a
).prod) t
参数：l : List ι；h : forall i in l, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_iff_continuousAt_domRestrict`：continuousWithinAt_iff_
continuousAt_domRestrict (f : α -> β) {x : α} {s : Set α} (h : x in s) : Continu
ousWithinAt f s x ↔ ContinuousAt (s.d…
· 使用定理 `tendsto_list_prod`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : Monoid M] [ContinuousMul M]   {f : ι → α → M} {x
 : Filt…
-/
theorem continuousOn_list_prod {f : ι → X → M} (l : List ι) {t : Set X}
    (h : ∀ i ∈ l, ContinuousOn (f i) t) :
    ContinuousOn (fun a => (l.map fun i => f i a).prod) t := by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx]
  refine tendsto_list_prod _ fun i hi => ?_
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hx] at h
  exact h

@[to_additive (attr := continuity)]
/-
**continuous_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : Monoid M] [Continuo
usMul M] (n : ℕ), Continuous fun a => a ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
  | 0 => by simpa using continuous_const
  | k + 1 => by
    simp only [pow_succ']
    exact continuous_id.mul (continuous_pow _)
/-
**AddMonoid.continuousConstSMul_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A] [
ContinuousAdd A] : ContinuousConstSMul Nat A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_nsmul`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 :
 AddMonoid M] [ContinuousAdd M] (n : ℕ), Continuous fun a => n • a
-/
instance AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousConstSMul ℕ A :=
  ⟨continuous_nsmul⟩
/-
**AddMonoid.continuousSMul_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.continuousSMul_nat {A} [AddMonoid A] [TopologicalSpace A] [Conti
nuousAdd A] : ContinuousSMul Nat A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_prod_of_discrete_left`：continuous_prod_of_discrete_left [Disc
reteTopology α] {f : α × β -> γ} : Continuous f ↔ forall a, Continuous (f ⟨a, ·⟩
)
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `continuous_nsmul`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 :
 AddMonoid M] [ContinuousAdd M] (n : ℕ), Continuous fun a => n • a
-/
instance AddMonoid.continuousSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousSMul ℕ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_nsmul⟩

-- We register `Continuous.pow` as a `continuity` lemma with low penalty (so
-- `continuity` will try it before other `continuity` lemmas). This is a
-- workaround for goals of the form `Continuous fun x => x ^ 2`, where
-- `continuity` applies `Continuous.mul` since the goal is defeq to
-- `Continuous fun x => x * x`.
--
-- To properly fix this, we should make sure that `continuity` applies its
-- lemmas with reducible transparency, preventing the unfolding of `^`. But this
-- is quite an invasive change.
@[to_fun (attr := to_additive (attr := aesop safe -100 (rule_sets := [Continuous]), fun_prop))]
/-
**Continuous.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.pow {f : X -> M} (h : Continuous f) (n : Nat) : Continuous (f ^
 n)
参数：h : Continuous f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
-/
theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous (f ^ n) :=
  (continuous_pow n).comp h

@[to_additive]
/-
**continuousOn_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_pow {s : Set M} (n : Nat) : ContinuousOn (fun (x : M) => x ^ 
n) s
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
-/
theorem continuousOn_pow {s : Set M} (n : ℕ) : ContinuousOn (fun (x : M) => x ^ n) s :=
  (continuous_pow n).continuousOn

@[to_additive]
/-
**continuousAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_pow (x : M) (n : Nat) : ContinuousAt (fun (x : M) => x ^ n) x
参数：x : M；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
-/
theorem continuousAt_pow (x : M) (n : ℕ) : ContinuousAt (fun (x : M) => x ^ n) x :=
  (continuous_pow n).continuousAt

@[to_additive]
/-
**Filter.Tendsto.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : M} (hf : Tendsto f l (
𝓝 x)) (n : Nat) : Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n))
参数：hf : Tendsto f l (𝓝 x)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_pow`：continuousAt_pow (x : M) (n : Nat) : ContinuousAt (fun
 (x : M) => x ^ n) x
-/
theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuousAt_pow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.pow {f : X -> M} {x : X} {s : Set X} (hf : ContinuousWi
thinAt f s x) (n : Nat) : ContinuousWithinAt (f ^ n) s x
参数：hf : ContinuousWithinAt f s x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.pow`：Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : 
M} (hf : Tendsto f l (𝓝 x)) (n : Nat) : Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n))
-/
theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
    (n : ℕ) : ContinuousWithinAt (f ^ n) s x :=
  Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.pow {f : X -> M} {x : X} (hf : ContinuousAt f x) (n : Nat) : 
ContinuousAt (f ^ n) x
参数：hf : ContinuousAt f x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.pow`：Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : 
M} (hf : Tendsto f l (𝓝 x)) (n : Nat) : Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n))
-/
theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) :
    ContinuousAt (f ^ n) x :=
  Filter.Tendsto.pow hf n

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousOn.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.pow {f : X -> M} {s : Set X} (hf : ContinuousOn f s) (n : Nat
) : ContinuousOn (f ^ n) s
参数：hf : ContinuousOn f s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.pow`：ContinuousWithinAt.pow {f : X -> M} {x : X} {s :
 Set X} (hf : ContinuousWithinAt f s x) (n : Nat) : ContinuousWithinAt (f ^ n) s
 x
-/
theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (f ^ n) s := fun x hx => (hf x hx).pow n

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instance applies when `R = A`, or when `[Algebra R A]` is available. -/
@[to_additive /-- If `R` acts on `A` via `A`, then continuous addition implies
continuous affine addition by constants. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsScalarTower.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [SeparatelyContinuousMul A] :
    ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp +singlePass only [← smul_one_mul q (_ : A)]
    fun_prop

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instance applies when `R = Aᵐᵒᵖ`. -/
@[to_additive /-- If the action of `R` on `A` commutes with left-addition, then
continuous addition implies continuous affine addition by constants.

Notably, this instance applies when `R = Aᵃᵒᵖ`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SMulCommClass.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [SMulCommClass R A A] [TopologicalSpace A] [SeparatelyContinuousMul A] :
    ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp +singlePass only [← mul_smul_one q (_ : A)]
    fun_prop

end ContinuousMul

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoid α] [ContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `Topology.Algebra.Group`,
because the predicate `ContinuousInv` has not yet been defined. -/
@[to_additive /-- If addition on an additive monoid is continuous, then addition on the additive
units of the monoid, with respect to the induced topology, is continuous.

Negation is also continuous, but we register this in a later file, `Topology.Algebra.Group`, because
the predicate `ContinuousNeg` has not yet been defined. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMul αˣ := isInducing_embedProduct.continuousMul (embedProduct α)

end Units

@[to_additive (attr := fun_prop)]
/-
**Continuous.units_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [Topologic
alSpace N] (f : M ->* N) (hf : Continuous f) : Continuous (Units.map f)
参数：f : M ->* N；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.continuous_iff`：∀ {M : Type u_1} {X : Type u_3} [inst : Topologica
lSpace M] [inst_1 : Monoid M] [inst_2 : TopologicalSpace X]   {f : X → Mˣ}, Cont
inuous f ↔…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `Units.continuous_coe_inv`：continuous_coe_inv : Continuous (fun u => ↑u⁻¹
 : Mˣ -> M)
-/
theorem Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →* N) (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

section

variable [TopologicalSpace M] [CommMonoid M]

@[to_additive]
/-
**Submonoid.mem_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) : (S : 
Set M) in 𝓝 (1 : M)
参数：S : Submonoid M；oS : IsOpen (S : Set M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
-/
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) :
    (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem

variable [ContinuousMul M]

@[to_additive]
/-
**tendsto_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_multiset_prod {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : M
ultiset ι) : (forall i in s, Tendsto (f i) x (𝓝 (a i))) -> Tendsto (fun b => (s.
map fun c => f c b).prod) x (𝓝 (s.map a).prod)
参数：s : Multiset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `tendsto_list_prod`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : Monoid M] [ContinuousMul M]   {f : ι → α → M} {x
 : Filt…
-/
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => (s.map fun c => f c b).prod) x (𝓝 (s.map a).prod) := by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l

@[to_additive]
/-
**tendsto_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_finsetProd {f : ι -> α -> M} {x : Filter α} {a : ι -> M} (s : Fins
et ι) : (forall i in s, Tendsto (f i) x (𝓝 (a i))) -> Tendsto (fun b => ∏ c in s
, f c b) x (𝓝 (∏ c in s, a c))
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_multiset_prod`：tendsto_multiset_prod {f : ι -> α -> M} {x : Filt
er α} {a : ι -> M} (s : Multiset ι) : (forall i in s, Tendsto (f i) x (𝓝 (a i)))
 -> Tendsto…
-/
theorem tendsto_finsetProd {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c)) :=
  tendsto_multiset_prod _

@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias tendsto_finset_prod := tendsto_finsetProd

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_multiset_prod {f : ι -> X -> M} (s : Multiset ι) : (forall i in
 s, Continuous (f i)) -> Continuous fun a => (s.map fun i => f i a).prod
参数：s : Multiset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `continuous_list_prod`：continuous_list_prod {f : ι -> X -> M} (l : List ι
) (h : forall i in l, Continuous (f i)) : Continuous fun a => (l.map fun i => f 
i a).prod
-/
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).prod := by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l

@[to_additive]
/-
**continuousOn_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_multiset_prod {f : ι -> X -> M} (s : Multiset ι) {t : Set X} 
: (forall i in s, ContinuousOn (f i) t) -> ContinuousOn (fun a => (s.map fun i =
> f i a).prod) t
参数：s : Multiset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `continuousOn_list_prod`：continuousOn_list_prod {f : ι -> X -> M} (l : Li
st ι) {t : Set X} (h : forall i in l, ContinuousOn (f i) t) : ContinuousOn (fun 
a => (l.map …
-/
theorem continuousOn_multiset_prod {f : ι → X → M} (s : Multiset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => (s.map fun i => f i a).prod) t := by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_finsetProd {f : ι -> X -> M} (s : Finset ι) : (forall i in s, C
ontinuous (f i)) -> Continuous fun a => ∏ i in s, f i a
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_multiset_prod`：continuous_multiset_prod {f : ι -> X -> M} (s 
: Multiset ι) : (forall i in s, Continuous (f i)) -> Continuous fun a => (s.map 
fun i => f i a…
-/
theorem continuous_finsetProd {f : ι → X → M} (s : Finset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => ∏ i ∈ s, f i a :=
  continuous_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuous_finset_sum := continuous_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuous_finset_prod := continuous_finsetProd

@[to_additive]
/-
**continuousOn_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_finsetProd {f : ι -> X -> M} (s : Finset ι) {t : Set X} : (fo
rall i in s, ContinuousOn (f i) t) -> ContinuousOn (fun a => ∏ i in s, f i a) t
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_multiset_prod`：continuousOn_multiset_prod {f : ι -> X -> M}
 (s : Multiset ι) {t : Set X} : (forall i in s, ContinuousOn (f i) t) -> Continu
ousOn (fun a => …
-/
theorem continuousOn_finsetProd {f : ι → X → M} (s : Finset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => ∏ i ∈ s, f i a) t :=
  continuousOn_multiset_prod _

@[deprecated (since := "2026-04-08")] alias continuousOn_finset_sum := continuousOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias continuousOn_finset_prod := continuousOn_finsetProd

@[to_additive]
/-
**eventuallyEq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyEq_prod {X M : Type*} [CommMonoid M] {s : Finset ι} {l : Filter 
X} {f g : ι -> X -> M} (hs : forall i in s, f i =ᶠ[l] g i) : ∏ i in s, f i =ᶠ[l]
 ∏ i in s, g i
参数：hs : forall i in s, f i =ᶠ[l] g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eventuallyEq_prod {X M : Type*} [CommMonoid M] {s : Finset ι} {l : Filter X}
    {f g : ι → X → M} (hs : ∀ i ∈ s, f i =ᶠ[l] g i) : ∏ i ∈ s, f i =ᶠ[l] ∏ i ∈ s, g i := by
  replace hs : ∀ᶠ x in l, ∀ i ∈ s, f i x = g i x := by rwa [eventually_all_finset]
  filter_upwards [hs] with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]

open Function

@[to_additive]
/-
**LocallyFinite.exists_finset_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.exists_finset_mulSupport {M : Type*} [One M] {f : ι -> X -> 
M} (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) : exists I : Finset 
ι, forallᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) subseteq I
参数：hf : LocallyFinite fun i => mulSupport <| f i；x₀ : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem LocallyFinite.exists_finset_mulSupport {M : Type*} [One M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) ⊆ I := by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine ⟨hUf.toFinset, mem_of_superset hxU fun y hy i hi => ?_⟩
  rw [hUf.coe_toFinset]
  exact ⟨y, hi, hy⟩

@[to_additive]
/-
**finprod_eventually_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finprod_eventually_eq_prod {M : Type*} [CommMonoid M] {f : ι -> X -> M} (h
f : LocallyFinite fun i => mulSupport (f i)) (x : X) : exists s : Finset ι, fora
llᶠ y in 𝓝 x, ∏ᶠ i, f i y = ∏ i in s, f i y
参数：hf : LocallyFinite fun i => mulSupport (f i)；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.exists_finset_mulSupport`：LocallyFinite.exists_finset_mulS
upport {M : Type*} [One M] {f : ι -> X -> M} (hf : LocallyFinite fun i => mulSup
port <| f i) (x₀ : X) : exis…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
-/
theorem finprod_eventually_eq_prod {M : Type*} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport (f i)) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, ∏ᶠ i, f i y = ∏ i ∈ s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun _ hy => finprod_eq_prod_of_mulSupport_subset _ fun _ hi => hy hi⟩

@[to_additive]
/-
**continuous_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_finprod {f : ι -> X -> M} (hc : forall i, Continuous (f i)) (hf
 : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x
参数：hc : forall i, Continuous (f i)；hf : LocallyFinite fun i => mulSupport (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `finprod_eventually_eq_prod`：finprod_eventually_eq_prod {M : Type*} [Comm
Monoid M] {f : ι -> X -> M} (hf : LocallyFinite fun i => mulSupport (f i)) (x : 
X) : exists s : …
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `tendsto_finsetProd`：tendsto_finsetProd {f : ι -> α -> M} {x : Filter α} 
{a : ι -> M} (s : Finset ι) : (forall i in s, Tendsto (f i) x (𝓝 (a i))) -> Tend
sto (fun…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem continuous_finprod {f : ι → X → M} (hc : ∀ i, Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine ContinuousAt.congr ?_ (EventuallyEq.symm hs)
  exact tendsto_finsetProd _ fun i _ => (hc i).continuousAt

@[to_additive]
/-
**continuous_finprod_cond** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_finprod_cond {f : ι -> X -> M} {p : ι -> Prop} (hc : forall i, 
p i -> Continuous (f i)) (hf : LocallyFinite fun i => mulSupport (f i)) : Contin
uous fun x => ∏ᶠ (i) (_ : p i), f i x
参数：hc : forall i, p i -> Continuous (f i)；hf : LocallyFinite fun i => mulSupport
 (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `continuous_finprod`：continuous_finprod {f : ι -> X -> M} (hc : forall i,
 Continuous (f i)) (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous f
un x => …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LocallyFinite.comp_injective`：comp_injective {g : ι' -> ι} (hf : Locally
Finite f) (hg : Injective g) : LocallyFinite (f ∘ g)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Continuous fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M) where
  continuous_add := @continuous_mul M _ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M) where
  continuous_mul := @continuous_add M _ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M] :
    SeparatelyContinuousAdd (Additive M) where
  continuous_const_add := @continuous_const_mul M _ _ _
  continuous_add_const := @continuous_mul_const M _ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace M] [Add M] [SeparatelyContinuousAdd M] :
    SeparatelyContinuousMul (Multiplicative M) where
  continuous_const_mul := @continuous_const_add M _ _ _
  continuous_mul_const := @continuous_add_const M _ _ _

section LatticeOps

variable {ι' : Sort*} [Mul M]

@[to_additive]
/-
**continuousMul_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMul_sInf {ts : Set (TopologicalSpace M)} (h : forall t in ts, @C
ontinuousMul M t _) : @ContinuousMul M (sInf ts) _
参数：TopologicalSpace M；h : forall t in ts, @ContinuousMul M t _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sInf_rng`：continuous_sInf_rng {t₁ : TopologicalSpace α} {T : 
Set (TopologicalSpace β)} : Continuous[t₁, sInf T] f ↔ forall t in T, Continuous
[t₁, t] f
· 使用定理 `continuous_sInf_dom₂`：continuous_sInf_dom₂ {X Y Z} {f : X -> Y -> Z} {ta
s : Set (TopologicalSpace X)} {tbs : Set (TopologicalSpace Y)} {tX : Topological
Space X} {…
· 使用定理 `ContinuousMul.continuous_mul`：∀ {M : Type u_1} {inst : TopologicalSpace 
M} {inst_1 : Mul M} [self : ContinuousMul M], Continuous fun p => p.1 * p.2
-/
theorem continuousMul_sInf {ts : Set (TopologicalSpace M)}
    (h : ∀ t ∈ ts, @ContinuousMul M t _) : @ContinuousMul M (sInf ts) _ :=
  letI := sInf ts
  { continuous_mul :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }

@[to_additive]
/-
**continuousMul_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMul_iInf {ts : ι' -> TopologicalSpace M} (h' : forall i, @Contin
uousMul M (ts i) _) : @ContinuousMul M (⨅ i, ts i) _
参数：h' : forall i, @ContinuousMul M (ts i) _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `continuousMul_sInf`：continuousMul_sInf {ts : Set (TopologicalSpace M)} (
h : forall t in ts, @ContinuousMul M t _) : @ContinuousMul M (sInf ts) _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem continuousMul_iInf {ts : ι' → TopologicalSpace M}
    (h' : ∀ i, @ContinuousMul M (ts i) _) : @ContinuousMul M (⨅ i, ts i) _ := by
  rw [← sInf_range]
  exact continuousMul_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/-
**continuousMul_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _
) (h₂ : @ContinuousMul M t₂ _) : @ContinuousMul M (t₁ ⊓ t₂) _
参数：h₁ : @ContinuousMul M t₁ _；h₂ : @ContinuousMul M t₂ _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `continuousMul_iInf`：continuousMul_iInf {ts : ι' -> TopologicalSpace M} (
h' : forall i, @ContinuousMul M (ts i) _) : @ContinuousMul M (⨅ i, ts i) _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem continuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
    (h₂ : @ContinuousMul M t₂ _) : @ContinuousMul M (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousMul_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

namespace ContinuousMap

variable [Mul X] [SeparatelyContinuousMul X]

/-- The continuous map `fun y => y * x` -/
@[to_additive /-- The continuous map `fun y => y + x` -/]
/-
**ContinuousMap.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u_5} → [inst : TopologicalSpace X] → [inst_1 : Mul X] → [Separat
elyContinuousMul X] → X → C(X, X)
参数：X, X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)

--- 原说明 ---
The continuous map `fun y => y * x`
-/
protected def mulRight (x : X) : C(X, X) :=
  mk _ (continuous_mul_const x)

@[to_additive (attr := simp)]
/-
**ContinuousMap.coe_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_mulRight (x : X) : ⇑(ContinuousMap.mulRight x) = fun y => y * x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulRight (x : X) : ⇑(ContinuousMap.mulRight x) = fun y => y * x :=
  rfl

@[to_additive]
/-
**ContinuousMap.mulRight_mul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mulRight_mul {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyCon
tinuousMul X] (x y : X) : ContinuousMap.mulRight (x * y) = (ContinuousMap.mulRig
ht y).comp (ContinuousMap.mulRight x)
参数：x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulRight_mul {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
    (x y : X) : ContinuousMap.mulRight (x * y) =
    (ContinuousMap.mulRight y).comp (ContinuousMap.mulRight x) := by
  ext; simp [mul_assoc]

/-- The continuous map `fun y => x * y` -/
@[to_additive /-- The continuous map `fun y => x + y` -/]
/-
**ContinuousMap.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u_5} → [inst : TopologicalSpace X] → [inst_1 : Mul X] → [Separat
elyContinuousMul X] → X → C(X, X)
参数：X, X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)

--- 原说明 ---
The continuous map `fun y => x * y`
-/
protected def mulLeft (x : X) : C(X, X) :=
  mk _ (continuous_const_mul x)

@[to_additive (attr := simp)]
/-
**ContinuousMap.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_mulLeft (x : X) : ⇑(ContinuousMap.mulLeft x) = fun y => x * y
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulLeft (x : X) : ⇑(ContinuousMap.mulLeft x) = fun y => x * y :=
  rfl

@[to_additive]
/-
**ContinuousMap.mulLeft_mul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mulLeft_mul {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyCont
inuousMul X] (x y : X) : ContinuousMap.mulLeft (x * y) = (ContinuousMap.mulLeft 
x).comp (ContinuousMap.mulLeft y)
参数：x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulLeft_mul {X : Type*} [Semigroup X] [TopologicalSpace X] [SeparatelyContinuousMul X]
    (x y : X) : ContinuousMap.mulLeft (x * y) =
    (ContinuousMap.mulLeft x).comp (ContinuousMap.mulLeft y) := by
  ext; simp [mul_assoc]

end ContinuousMap

