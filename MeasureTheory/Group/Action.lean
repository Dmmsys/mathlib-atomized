/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Dynamics.Minimal
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Group.Defs

/-!
# Measures invariant under group actions

A measure `μ : Measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure-preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/

public section


open scoped ENNReal NNReal Pointwise Topology symmDiff
open MeasureTheory.Measure Set Function Filter

namespace MeasureTheory

universe u v w

variable {G : Type u} {M : Type v} {α : Type w}

namespace SMulInvariantMeasure

@[to_additive]
/-
**MeasureTheory.SMulInvariantMeasure.zero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.SMulInvariantMeasure`。
形式化陈述：zero [MeasurableSpace α] [SMul M α] : SMulInvariantMeasure M α (0 : Measur
e α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zero [MeasurableSpace α] [SMul M α] : SMulInvariantMeasure M α (0 : Measure α) :=
  ⟨fun _ _ _ => rfl⟩

variable [SMul M α] {m : MeasurableSpace α} {μ ν : Measure α}

@[to_additive]
/-
**MeasureTheory.SMulInvariantMeasure.add** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.SMulInvariantMeasure`。
形式化陈述：add [SMulInvariantMeasure M α μ] [SMulInvariantMeasure M α ν] : SMulInvari
antMeasure M α (μ + ν)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
-/
instance add [SMulInvariantMeasure M α μ] [SMulInvariantMeasure M α ν] :
    SMulInvariantMeasure M α (μ + ν) :=
  ⟨fun c _s hs =>
    show _ + _ = _ + _ from
      congr_arg₂ (· + ·) (measure_preimage_smul c hs) (measure_preimage_smul c hs)⟩

@[to_additive]
/-
**MeasureTheory.SMulInvariantMeasure.smul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.SMulInvariantMeasure`。
形式化陈述：smul [SMulInvariantMeasure M α μ] (c : Real>=0∞) : SMulInvariantMeasure M 
α (c • μ)
参数：c : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
-/
instance smul [SMulInvariantMeasure M α μ] (c : ℝ≥0∞) : SMulInvariantMeasure M α (c • μ) :=
  ⟨fun a _s hs => show c • _ = c • _ from congr_arg (c • ·) (measure_preimage_smul a hs)⟩

@[to_additive]
/-
**MeasureTheory.SMulInvariantMeasure.smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.SMulInvariantMeasure`。
形式化陈述：smul_nnreal [SMulInvariantMeasure M α μ] (c : Real>=0) : SMulInvariantMeas
ure M α (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul_nnreal [SMulInvariantMeasure M α μ] (c : ℝ≥0) : SMulInvariantMeasure M α (c • μ) :=
  SMulInvariantMeasure.smul c

end SMulInvariantMeasure

section AE_smul

variable {m : MeasurableSpace α} [SMul G α]
  (μ : Measure α) [SMulInvariantMeasure G α μ] {s : Set α}

/-- See also `measure_preimage_smul_of_nullMeasurableSet` and `measure_preimage_smul`. -/
@[to_additive
/-- See also `measure_preimage_smul_of_nullMeasurableSet` and `measure_preimage_smul`. -/]
/-
**MeasureTheory.measure_preimage_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_preimage_smul_le (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) <= μ s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.outerMeasure_le_iff`：outerMeasure_le_iff {m : Oute
rMeasure α} : m <= μ.1 ↔ forall s, MeasurableSet s -> m s <= μ s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
-/
theorem measure_preimage_smul_le (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) ≤ μ s :=
  (outerMeasure_le_iff (m := .map (c • ·) μ.1)).2
    (fun _s hs ↦ (SMulInvariantMeasure.measure_preimage_smul _ hs).le) _

/-- See also `smul_ae`. -/
@[to_additive /-- See also `vadd_ae`. -/]
/-
**MeasureTheory.tendsto_smul_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_smul_ae (c : G) : Filter.Tendsto (c • ·) (ae μ) (ae μ)
参数：c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `MeasureTheory.measure_preimage_smul_le`：measure_preimage_smul_le (c : G)
 (s : Set α) : μ ((c • ·) ⁻¹' s) <= μ s

--- 原说明 ---
See also `smul_ae`.
-/
theorem tendsto_smul_ae (c : G) : Filter.Tendsto (c • ·) (ae μ) (ae μ) := fun _s hs ↦
  eq_bot_mono (measure_preimage_smul_le μ c _) hs

variable {μ}

@[to_additive]
/-
**MeasureTheory.measure_preimage_smul_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_preimage_smul_null (h : μ s = 0) (c : G) : μ ((c • ·) ⁻¹' s) = 0
参数：h : μ s = 0；c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `MeasureTheory.measure_preimage_smul_le`：measure_preimage_smul_le (c : G)
 (s : Set α) : μ ((c • ·) ⁻¹' s) <= μ s
-/
theorem measure_preimage_smul_null (h : μ s = 0) (c : G) : μ ((c • ·) ⁻¹' s) = 0 :=
  eq_bot_mono (measure_preimage_smul_le μ c _) h

@[to_additive]
/-
**MeasureTheory.measure_preimage_smul_of_nullMeasurableSet** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：measure_preimage_smul_of_nullMeasurableSet (hs : NullMeasurableSet s μ) (c
 : G) : μ ((c • ·) ⁻¹' s) = μ s
参数：hs : NullMeasurableSet s μ；c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_smul_ae`：tendsto_smul_ae (c : G) : Filter.Tendsto 
(c • ·) (ae μ) (ae μ)
· 使用定理 `MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq`：toMeasurable_ae_eq (
h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s
-/
theorem measure_preimage_smul_of_nullMeasurableSet (hs : NullMeasurableSet s μ) (c : G) :
    μ ((c • ·) ⁻¹' s) = μ s := by
  rw [← measure_toMeasurable s,
    ← SMulInvariantMeasure.measure_preimage_smul c (measurableSet_toMeasurable μ s)]
  exact measure_congr (tendsto_smul_ae μ c hs.toMeasurable_ae_eq) |>.symm

end AE_smul

section AE

variable {m : MeasurableSpace α} [Group G] [MulAction G α]
  (μ : Measure α) [SMulInvariantMeasure G α μ]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_preimage_smul (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) = μ s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MeasureTheory.measure_preimage_smul_le`：measure_preimage_smul_le (c : G)
 (s : Set α) : μ ((c • ·) ⁻¹' s) <= μ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem measure_preimage_smul (c : G) (s : Set α) : μ ((c • ·) ⁻¹' s) = μ s :=
  (measure_preimage_smul_le μ c s).antisymm <| by
    simpa [preimage_preimage] using measure_preimage_smul_le μ c⁻¹ ((c • ·) ⁻¹' s)

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_smul (c : G) (s : Set α) : μ (c • s) = μ s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `MeasureTheory.measure_preimage_smul`：measure_preimage_smul (c : G) (s : 
Set α) : μ ((c • ·) ⁻¹' s) = μ s
-/
theorem measure_smul (c : G) (s : Set α) : μ (c • s) = μ s := by
  simpa only [preimage_smul_inv] using measure_preimage_smul μ c⁻¹ s

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_inter_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_inter_inv_smul (c : G) (s t : Set α) : μ (s inter c⁻¹ • t) = μ (c 
• s inter t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem measure_inter_inv_smul (c : G) (s t : Set α) : μ (s ∩ c⁻¹ • t) = μ (c • s ∩ t) := by
  rw [← measure_smul _ c, smul_set_inter, smul_smul, mul_inv_cancel, one_smul]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_inv_smul_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_inv_smul_inter (c : G) (s t : Set α) : μ (c⁻¹ • s inter t) = μ (s 
inter c • t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_inv_smul`：measure_inter_inv_smul (c : G) (s 
t : Set α) : μ (s inter c⁻¹ • t) = μ (c • s inter t)
-/
theorem measure_inv_smul_inter (c : G) (s t : Set α) : μ (c⁻¹ • s ∩ t) = μ (s ∩ c • t) := by
  simpa [inv_inv] using (measure_inter_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_union_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_union_inv_smul (c : G) (s t : Set α) : μ (s union c⁻¹ • t) = μ (c 
• s union t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用引理 `Set.smul_set_union`：smul_set_union : a • (t₁ union t₂) = a • t₁ union a 
• t₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem measure_union_inv_smul (c : G) (s t : Set α) : μ (s ∪ c⁻¹ • t) = μ (c • s ∪ t) := by
  rw [← measure_smul _ c, smul_set_union, smul_smul, mul_inv_cancel, one_smul]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_inv_smul_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_inv_smul_union (c : G) (s t : Set α) : μ (c⁻¹ • s union t) = μ (s 
union c • t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_union_inv_smul`：measure_union_inv_smul (c : G) (s 
t : Set α) : μ (s union c⁻¹ • t) = μ (c • s union t)
-/
theorem measure_inv_smul_union (c : G) (s t : Set α) : μ (c⁻¹ • s ∪ t) = μ (s ∪ c • t) := by
  simpa [inv_inv] using (measure_union_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_sdiff_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_sdiff_inv_smul (c : G) (s t : Set α) : μ (s \ c⁻¹ • t) = μ (c • s 
\ t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `Set.smul_set_sdiff`：smul_set_sdiff : a • (s \ t) = a • s \ a • t
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem measure_sdiff_inv_smul (c : G) (s t : Set α) : μ (s \ c⁻¹ • t) = μ (c • s \ t) := by
  rw [← measure_smul _ c, smul_set_sdiff, smul_smul, mul_inv_cancel, one_smul]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_inv_smul_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_inv_smul_sdiff (c : G) (s t : Set α) : μ (c⁻¹ • s \ t) = μ (s \ c 
• t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_sdiff_inv_smul`：measure_sdiff_inv_smul (c : G) (s 
t : Set α) : μ (s \ c⁻¹ • t) = μ (c • s \ t)
-/
theorem measure_inv_smul_sdiff (c : G) (s t : Set α) : μ (c⁻¹ • s \ t) = μ (s \ c • t) := by
  simpa [inv_inv] using (measure_sdiff_inv_smul _ c⁻¹ _ _).symm

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_symmDiff_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_symmDiff_inv_smul (c : G) (s t : Set α) : μ (s ∆ (c⁻¹ • t)) = μ ((
c • s) ∆ t)
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `Set.smul_set_symmDiff`：smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem measure_symmDiff_inv_smul (c : G) (s t : Set α) : μ (s ∆ (c⁻¹ • t)) = μ ((c • s) ∆ t) := by
  rw [← measure_smul _ c, smul_set_symmDiff, smul_smul, mul_inv_cancel, one_smul]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_inv_smul_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_inv_smul_symmDiff (c : G) (s t : Set α) : μ ((c⁻¹ • s) ∆ t) = μ (s
 ∆ (c • t))
参数：c : G；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_symmDiff_inv_smul`：measure_symmDiff_inv_smul (c : 
G) (s t : Set α) : μ (s ∆ (c⁻¹ • t)) = μ ((c • s) ∆ t)
-/
theorem measure_inv_smul_symmDiff (c : G) (s t : Set α) : μ ((c⁻¹ • s) ∆ t) = μ (s ∆ (c • t)) := by
  simpa [inv_inv] using (measure_symmDiff_inv_smul _ c⁻¹ _ _).symm

variable {μ}

@[to_additive]
/-
**MeasureTheory.measure_smul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_smul_eq_zero_iff {s} (c : G) : μ (c • s) = 0 ↔ μ s = 0
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measure_smul_eq_zero_iff {s} (c : G) : μ (c • s) = 0 ↔ μ s = 0 := by
  rw [measure_smul]

@[to_additive]
/-
**MeasureTheory.measure_smul_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_smul_null {s} (h : μ s = 0) (c : G) : μ (c • s) = 0
参数：h : μ s = 0；c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_smul_eq_zero_iff`：measure_smul_eq_zero_iff {s} (c 
: G) : μ (c • s) = 0 ↔ μ s = 0
-/
theorem measure_smul_null {s} (h : μ s = 0) (c : G) : μ (c • s) = 0 :=
  (measure_smul_eq_zero_iff _).2 h

@[to_additive (attr := simp)]
/-
**MeasureTheory.smul_mem_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：smul_mem_ae (c : G) {s : Set α} : c • s in ae μ ↔ s in ae μ
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_mem_ae (c : G) {s : Set α} : c • s ∈ ae μ ↔ s ∈ ae μ := by
  simp only [mem_ae_iff, ← smul_set_compl, measure_smul_eq_zero_iff]

@[to_additive (attr := simp)]
/-
**MeasureTheory.smul_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：smul_ae (c : G) : c • ae μ = ae μ
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_ae (c : G) : c • ae μ = ae μ := by
  ext s
  simp only [mem_smul_filter, preimage_smul, smul_mem_ae]

@[to_additive (attr := simp)]
/-
**MeasureTheory.eventuallyConst_smul_set_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eventuallyConst_smul_set_ae (c : G) {s : Set α} : EventuallyConst (c • s :
 Set α) (ae μ) ↔ EventuallyConst s (ae μ)
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `Filter.eventuallyConst_preimage`：eventuallyConst_preimage {s : Set β} {f
 : α -> β} : EventuallyConst (f ⁻¹' s) l ↔ EventuallyConst s (map f l)
· 使用定理 `Filter.map_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {f : 
Filter β} {a : α}, Filter.map (fun b => a • b) f = a • f
· 使用定理 `MeasureTheory.smul_ae`：smul_ae (c : G) : c • ae μ = ae μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyConst_smul_set_ae (c : G) {s : Set α} :
    EventuallyConst (c • s : Set α) (ae μ) ↔ EventuallyConst s (ae μ) := by
  rw [← preimage_smul_inv, eventuallyConst_preimage, Filter.map_smul, smul_ae]

@[to_additive (attr := simp)]
/-
**MeasureTheory.smul_set_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：smul_set_ae_le (c : G) {s t : Set α} : c • s <=ᵐ[μ] c • t ↔ s <=ᵐ[μ] t
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_set_ae_le (c : G) {s t : Set α} : c • s ≤ᵐ[μ] c • t ↔ s ≤ᵐ[μ] t := by
  simp only [ae_le_set, ← smul_set_sdiff, measure_smul_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MeasureTheory.smul_set_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：smul_set_ae_eq (c : G) {s t : Set α} : c • s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_set_ae_eq (c : G) {s t : Set α} : c • s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t := by
  simp only [Filter.eventuallyLE_antisymm_iff, smul_set_ae_le]

end AE

section MeasurableConstSMul

variable {m : MeasurableSpace α} [SMul M α] [MeasurableConstSMul M α] (c : M)
  (μ : Measure α) [SMulInvariantMeasure M α μ]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measurePreserving_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measurePreserving_smul : MeasurePreserving (c • ·) μ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
-/
theorem measurePreserving_smul : MeasurePreserving (c • ·) μ μ :=
  { measurable := measurable_const_smul c
    map_eq := by
      ext1 s hs
      rw [map_apply (measurable_const_smul c) hs]
      exact SMulInvariantMeasure.measure_preimage_smul c hs }

@[to_additive (attr := simp)]
/-
**MeasureTheory.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {M : Type v} {α : Type w} {m : MeasurableSpace α} [inst : SMul M α] [Mea
surableConstSMul M α] (c : M)   (μ : MeasureTheory.Measure α) [MeasureTheory.SMu
lInvariantMeasure M α μ],   MeasureTheory.Measure.map (fun x => c • x) μ = μ
参数：c : M；μ : MeasureTheory.Measure α；fun x => c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
-/
protected theorem map_smul : map (c • ·) μ = μ :=
  (measurePreserving_smul c μ).map_eq

end MeasurableConstSMul

@[to_additive]
/-
**MeasureTheory.MeasurePreserving.smulInvariantMeasure_iterateMulAct** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type w} {f : α → α} {x : MeasurableSpace α} {μ : MeasureTheory.Meas
ure α},   MeasureTheory.MeasurePreserving f μ μ → MeasureTheory.SMulInvariantMea
sure (IterateMulAct f) α μ
参数：IterateMulAct f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasureTheory.MeasurePreserving.iterate`：∀ {α : Type u_1} [inst : Measur
ableSpace α] {μ : MeasureTheory.Measure α} {f : α → α},   MeasureTheory.MeasureP
reserving f μ μ → ∀ (n : ℕ), …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem MeasurePreserving.smulInvariantMeasure_iterateMulAct
    {f : α → α} {_ : MeasurableSpace α} {μ : Measure α} (hf : MeasurePreserving f μ μ) :
    SMulInvariantMeasure (IterateMulAct f) α μ :=
  ⟨fun n _s hs ↦ (hf.iterate n.val).measure_preimage hs.nullMeasurableSet⟩

@[to_additive]
/-
**MeasureTheory.smulInvariantMeasure_iterateMulAct** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：smulInvariantMeasure_iterateMulAct {f : α -> α} {_ : MeasurableSpace α} {μ
 : Measure α} (hf : Measurable f) : SMulInvariantMeasure (IterateMulAct f) α μ ↔
 MeasurePreserving f μ μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.measurableSMul₂_iterateMulAct`：Measurable.measurableSMul₂_ite
rateMulAct (h : Measurable f) : MeasurableSMul₂ (IterateMulAct f) α where measur
able_smul
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `MeasurableSMul₂.toMeasurableSMul`：∀ {M : Type u_2} {X : Type u_3} [inst 
: MeasurableSpace X] [inst_1 : SMul M X] [inst_2 : MeasurableSpace M]   [Measura
bleSMul₂ M X], Measura…
· 使用定理 `MeasureTheory.MeasurePreserving.smulInvariantMeasure_iterateMulAct`：∀ {α
 : Type w} {f : α → α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α},   
MeasureTheory.MeasurePreserving f μ μ → MeasureTheory.SM…
-/
theorem smulInvariantMeasure_iterateMulAct
    {f : α → α} {_ : MeasurableSpace α} {μ : Measure α} (hf : Measurable f) :
    SMulInvariantMeasure (IterateMulAct f) α μ ↔ MeasurePreserving f μ μ :=
  ⟨fun _ ↦
    have := hf.measurableSMul₂_iterateMulAct
    measurePreserving_smul (IterateMulAct.mk (f := f) 1) μ,
    MeasurePreserving.smulInvariantMeasure_iterateMulAct⟩

section SMulHomClass

universe uM uN uα uβ
variable {M : Type uM} {N : Type uN} {α : Type uα} {β : Type uβ}
  [MeasurableSpace α] [MeasurableSpace β]

@[to_additive]
/-
**MeasureTheory.smulInvariantMeasure_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：smulInvariantMeasure_map [SMul M α] [SMul M β] [MeasurableConstSMul M β] (
μ : Measure α) [SMulInvariantMeasure M α μ] (f : α -> β) (hsmul : forall (m : M)
 a, f (m • a) = m • f a) (hf : Measurable f) : SMulInvariantMeasure M β (map f μ
) where measure_preimage_smul m S hS
参数：μ : Measure α；f : α -> β；hsmul : forall (m : M) a, f (m • a) = m • f a；hf : M
easurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
-/
theorem smulInvariantMeasure_map [SMul M α] [SMul M β]
    [MeasurableConstSMul M β]
    (μ : Measure α) [SMulInvariantMeasure M α μ] (f : α → β)
    (hsmul : ∀ (m : M) a, f (m • a) = m • f a) (hf : Measurable f) :
    SMulInvariantMeasure M β (map f μ) where
  measure_preimage_smul m S hS := calc
    map f μ ((m • ·) ⁻¹' S)
    _ = μ (f ⁻¹' (m • ·) ⁻¹' S) := map_apply hf <| hS.preimage (measurable_const_smul _)
    _ = μ ((m • f ·) ⁻¹' S) := by rw [preimage_preimage]
    _ = μ ((f <| m • ·) ⁻¹' S) := by simp_rw [hsmul]
    _ = μ ((m • ·) ⁻¹' f ⁻¹' S) := by rw [← preimage_preimage]
    _ = μ (f ⁻¹' S) := by rw [SMulInvariantMeasure.measure_preimage_smul m (hS.preimage hf)]
    _ = map f μ S := (map_apply hf hS).symm

@[to_additive]
/-
**MeasureTheory.smulInvariantMeasure_map_smul** 是 Mathlib 中的一个实例，位于命名空间 `Measure
Theory`。
形式化陈述：smulInvariantMeasure_map_smul [SMul M α] [SMul N α] [SMulCommClass N M α] 
[MeasurableConstSMul M α] [MeasurableConstSMul N α] (μ : Measure α) [SMulInvaria
ntMeasure M α μ] (n : N) : SMulInvariantMeasure M α (map (n • ·) μ)
参数：μ : Measure α；n : N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.smulInvariantMeasure_map`：smulInvariantMeasure_map [SMul M
 α] [SMul M β] [MeasurableConstSMul M β] (μ : Measure α) [SMulInvariantMeasure M
 α μ] (f : α -> β) (hsmul : …
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
-/
instance smulInvariantMeasure_map_smul [SMul M α] [SMul N α] [SMulCommClass N M α]
    [MeasurableConstSMul M α] [MeasurableConstSMul N α]
    (μ : Measure α) [SMulInvariantMeasure M α μ] (n : N) :
    SMulInvariantMeasure M α (map (n • ·) μ) :=
  smulInvariantMeasure_map μ _ (smul_comm n) <| measurable_const_smul _

end SMulHomClass

variable (G) {m : MeasurableSpace α} [Group G] [MulAction G α] (μ : Measure α)

variable [MeasurableConstSMul G α] in
/-- Equivalent definitions of a measure invariant under a multiplicative action of a group.

0. `SMulInvariantMeasure G α μ`;

1. for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
  multiplication by `c` is equal to the measure of `s`;

2. for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
  scalar multiplication by `c` is equal to the measure of `s`;

3. property 1 for any set, including non-measurable ones;
4. property 2 for any set, including non-measurable ones;

5. for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

6. for any `c : G`, scalar multiplication by `c` is a measure-preserving map. -/
@[to_additive]
/-
**MeasureTheory.smulInvariantMeasure_tfae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：smulInvariantMeasure_tfae : List.TFAE [SMulInvariantMeasure G α μ, forall 
(c : G) (s), MeasurableSet s -> μ ((c • ·) ⁻¹' s) = μ s, forall (c : G) (s), Mea
surableSet s -> μ (c • s) = μ s, forall (c : G) (s), μ ((c • ·) ⁻¹' s) = μ s, fo
rall (c : G) (s), μ (c • s) = μ s, forall c : G, Measure.map (c • ·) μ = μ, fora
ll c : G, MeasurePreserving (c • ·) μ μ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage_emb`：measure_preimage_e
mb {f : α -> β} (hf : MeasurePreserving f μa μb) (hfe : MeasurableEmbedding f) (
s : Set β) : μa (f ⁻¹' s) = μb s
· 使用定理 `measurableEmbedding_const_smul`：∀ {G : Type u_1} {α : Type u_3} [inst : 
MeasurableSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [MeasurableCons
tSMul G α] (c : G), …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Equivalent definitions of a measure invariant under a multiplicative action of a
 group.

0. `SMulInvariantMeasure G α μ`;

1. for every `c : G` and a measurable set `s`, the measure of the preimage of `s
` under scalar
  multiplication by `c` is equal to the measure of `s`;

2. for every `c : G` and a measurable set `s`, the measure of the image `c • s` 
of `s` under
  scalar multiplication by `c` is equal to the measure of `s`;

3. property 1 for any set, including non-measurable ones;
4. property 2 for any set, including non-measurable ones;

5. for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

6. for any `c : G`, scalar multiplication by `c` is a measure-preserving map.
-/
theorem smulInvariantMeasure_tfae :
    List.TFAE
      [SMulInvariantMeasure G α μ,
        ∀ (c : G) (s), MeasurableSet s → μ ((c • ·) ⁻¹' s) = μ s,
        ∀ (c : G) (s), MeasurableSet s → μ (c • s) = μ s,
        ∀ (c : G) (s), μ ((c • ·) ⁻¹' s) = μ s,
        ∀ (c : G) (s), μ (c • s) = μ s,
        ∀ c : G, Measure.map (c • ·) μ = μ,
        ∀ c : G, MeasurePreserving (c • ·) μ μ] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 1 → 6 := fun h c => (measurePreserving_smul c μ).map_eq
  tfae_have 6 → 7 := fun H c => ⟨measurable_const_smul c, H c⟩
  tfae_have 7 → 4 := fun H c => (H c).measure_preimage_emb (measurableEmbedding_const_smul c)
  tfae_have 4 → 5
  | H, c, s => by
    rw [← preimage_smul_inv]
    apply H
  tfae_have 5 → 3 := fun H c s _ => H c s
  tfae_have 3 → 2
  | H, c, s, hs => by
    rw [preimage_smul]
    exact H c⁻¹ s hs
  tfae_finish

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `VAddInvariantMeasure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(c +ᵥ ·)` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(c +ᵥ ·)` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure-preserving map. -/
add_decl_doc vaddInvariantMeasure_tfae

variable {G}
variable [SMulInvariantMeasure G α μ]

variable {μ}
variable [MeasurableConstSMul G α] in
@[to_additive]
/-
**MeasureTheory.NullMeasurableSet.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
NullMeasurableSet`。
形式化陈述：∀ {G : Type u} {α : Type w} {m : MeasurableSpace α} [inst : Group G] [inst
_1 : MulAction G α]   {μ : MeasureTheory.Measure α} [MeasureTheory.SMulInvariant
Measure G α μ] [MeasurableConstSMul G α] {s : Set α},   MeasureTheory.NullMeasur
ableSet s μ → ∀ (c : G), MeasureTheory.NullMeasurableSet (c • s) μ
参数：c : G；c • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
-/
theorem NullMeasurableSet.smul {s} (hs : NullMeasurableSet s μ) (c : G) :
    NullMeasurableSet (c • s) μ := by
  simpa only [← preimage_smul_inv] using
    hs.preimage (measurePreserving_smul _ _).quasiMeasurePreserving

section IsMinimal

variable (G)
variable [TopologicalSpace α] [ContinuousConstSMul G α] [MulAction.IsMinimal G α] {K U : Set α}

include G in
/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_ne_zero`. -/
@[to_additive]
/-
**MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero (hK : IsCompact K) 
(hμK : μ K != 0) (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U
参数：hK : IsCompact K；hμK : μ K != 0；hU : IsOpen U；hne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_finite_cover_smul`：IsCompact.exists_finite_cover_smul [
IsMinimal G α] [ContinuousConstSMul G α] {K U : Set α} (hK : IsCompact K) (hUo :
 IsOpen U) (hne : U.None…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_biUnion_null_iff`：measure_biUnion_null_iff {I : Se
t ι} (hI : I.Countable) {s : ι -> Set α} : μ (⋃ i in I, s i) = 0 ↔ forall i in I
, μ (s i) = 0
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s

--- 原说明 ---
If measure `μ` is invariant under a group action and is nonzero on a compact set
 `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume 
`μ ≠ 0` instead of
`μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_ne_zero`.
-/
theorem measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ K ≠ 0)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
  pos_iff_ne_zero.2 fun hμU =>
    hμK <|
      measure_mono_null ht <|
        (measure_biUnion_null_iff t.countable_toSet).2 fun _ _ => by rwa [measure_smul]

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `MeasureTheory.measure_isOpen_pos_of_vaddInvariant_of_ne_zero`. -/
add_decl_doc measure_isOpen_pos_of_vaddInvariant_of_compact_ne_zero

include G

@[to_additive]
/-
**MeasureTheory.isLocallyFiniteMeasure_of_smulInvariant** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：isLocallyFiniteMeasure_of_smulInvariant (hU : IsOpen U) (hne : U.Nonempty)
 (hμU : μ U != ∞) : IsLocallyFiniteMeasure μ
参数：hU : IsOpen U；hne : U.Nonempty；hμU : μ U != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.exists_smul_mem`：IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {
U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) : exists c : M, c • x in U
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_preimage_smul`：measure_preimage_smul (c : G) (s : 
Set α) : μ ((c • ·) ⁻¹' s) = μ s
-/
theorem isLocallyFiniteMeasure_of_smulInvariant (hU : IsOpen U) (hne : U.Nonempty) (hμU : μ U ≠ ∞) :
    IsLocallyFiniteMeasure μ :=
  ⟨fun x =>
    let ⟨g, hg⟩ := hU.exists_smul_mem G x hne
    ⟨(g • ·) ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg,
      Ne.lt_top <| by rwa [measure_preimage_smul]⟩⟩

variable [Measure.Regular μ]

@[to_additive]
/-
**MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_ne_zero** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_isOpen_pos_of_smulInvariant_of_ne_zero (hμ : μ != 0) (hU : IsOpen 
U) (hne : U.Nonempty) : 0 < μ U
参数：hμ : μ != 0；hU : IsOpen U；hne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.Regular.exists_isCompact_not_null`：exists_isCompac
t_not_null [Regular μ] : (exists K, IsCompact K ∧ μ K != 0) ↔ μ != 0
· 使用定理 `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero`：me
asure_isOpen_pos_of_smulInvariant_of_compact_ne_zero (hK : IsCompact K) (hμK : μ
 K != 0) (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U
-/
theorem measure_isOpen_pos_of_smulInvariant_of_ne_zero (hμ : μ ≠ 0) (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μ U :=
  let ⟨_K, hK, hμK⟩ := Regular.exists_isCompact_not_null.mpr hμ
  measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive]
/-
**MeasureTheory.measure_pos_iff_nonempty_of_smulInvariant** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：measure_pos_iff_nonempty_of_smulInvariant (hμ : μ != 0) (hU : IsOpen U) : 
0 < μ U ↔ U.Nonempty
参数：hμ : μ != 0；hU : IsOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_ne_zero`：measure_is
Open_pos_of_smulInvariant_of_ne_zero (hμ : μ != 0) (hU : IsOpen U) (hne : U.None
mpty) : 0 < μ U
-/
theorem measure_pos_iff_nonempty_of_smulInvariant (hμ : μ ≠ 0) (hU : IsOpen U) :
    0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_of_measure_ne_zero h.ne',
    measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ hU⟩

@[to_additive]
/-
**MeasureTheory.measure_eq_zero_iff_eq_empty_of_smulInvariant** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_zero_iff_eq_empty_of_smulInvariant (hμ : μ != 0) (hU : IsOpen U
) : μ U = 0 ↔ U = ∅
参数：hμ : μ != 0；hU : IsOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_pos_iff_nonempty_of_smulInvariant`：measure_pos_iff
_nonempty_of_smulInvariant (hμ : μ != 0) (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measure_eq_zero_iff_eq_empty_of_smulInvariant (hμ : μ ≠ 0) (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ := by
  rw [← not_iff_not, ← Ne, ← pos_iff_ne_zero,
    measure_pos_iff_nonempty_of_smulInvariant G hμ hU, nonempty_iff_ne_empty]

end IsMinimal

end MeasureTheory

