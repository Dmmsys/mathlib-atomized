/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `PMF` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : PMF β` is the distribution given by sampling `a : α` from `pa : PMF α`,
and then sampling from `pb a : PMF β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/

@[expose] public section


noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal

open MeasureTheory

namespace PMF

section Pure

open scoped Classical in
/-- The pure `PMF` is the `PMF` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
/-
**PMF.pure** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：pure (a : α) : PMF α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pure `PMF` is the `PMF` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere.
-/
def pure (a : α) : PMF α :=
  ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

variable (a a' : α)

open scoped Classical in
@[simp]
/-
**PMF.pure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：pure_apply : pure a a' = if a' = a then 1 else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl

@[simp]
/-
**PMF.support_pure** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_pure : (pure a).support = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]
/-
**PMF.mem_support_pure_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_pure_iff : a' in (pure a).support ↔ a' = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_pure`：support_pure : (pure a).support = {a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_pure_iff : a' ∈ (pure a).support ↔ a' = a := by simp
/-
**PMF.pure_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：pure_apply_self : pure a a = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem pure_apply_self : pure a a = 1 :=
  if_pos rfl
/-
**PMF.pure_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：pure_apply_of_ne (h : a' != a) : pure a a' = 0
参数：h : a' != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 :=
  if_neg h
/-
**PMF.** 是 Mathlib 中的一个实例，位于命名空间 `PMF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (PMF α) :=
  ⟨pure default⟩

section Measure

variable (s : Set α)

open scoped Classical in
@[simp]
/-
**PMF.toOuterMeasure_pure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a in s then 1 e
lse 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y :
 α}, (if p then x else y) = x ↔ ¬p → y = x
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
-/
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a ∈ s then 1 else 0 := by
  refine (toOuterMeasure_apply (pure a) s).trans ?_
  split_ifs with ha
  · refine (tsum_congr fun b => ?_).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb =>
      symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine (tsum_congr fun b => ?_).trans tsum_zero
    exact ite_eq_right_iff.2 fun hb =>
      ite_eq_right_iff.2 fun h => (ha <| h ▸ hb).elim

variable [MeasurableSpace α]

open scoped Classical in
/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise. -/
@[simp]
/-
**PMF.toMeasure_pure_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_pure_apply (hs : MeasurableSet s) : (pure a).toMeasure s = if a 
in s then 1 else 0
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_pure_apply`：toOuterMeasure_pure_apply : (pure a).toOu
terMeasure s = if a in s then 1 else 0

--- 原说明 ---
The measure of a set under `pure a` is `1` for sets containing `a` and `0` other
wise.
-/
theorem toMeasure_pure_apply (hs : MeasurableSet s) :
    (pure a).toMeasure s = if a ∈ s then 1 else 0 :=
  (toMeasure_apply_eq_toOuterMeasure_apply (pure a) hs).trans (toOuterMeasure_pure_apply a s)
/-
**PMF.toMeasure_pure** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_pure : (pure a).toMeasure = Measure.dirac a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_pure_apply`：toMeasure_pure_apply (hs : MeasurableSet s) : 
(pure a).toMeasure s = if a in s then 1 else 0
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
-/
theorem toMeasure_pure : (pure a).toMeasure = Measure.dirac a :=
  Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl

@[simp]
/-
**PMF.toPMF_dirac** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toPMF_dirac [Countable α] [h : MeasurableSingletonClass α] : (Measure.dira
c a).toPMF = pure a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toPMF_eq_iff_toMeasure_eq`：toPMF_eq_iff_toMeasure_eq (μ : Measure α)
 [IsProbabilityMeasure μ] : μ.toPMF = p ↔ μ = p.toMeasure
· 使用定理 `PMF.toMeasure_pure`：toMeasure_pure : (pure a).toMeasure = Measure.dirac 
a
-/
theorem toPMF_dirac [Countable α] [h : MeasurableSingletonClass α] :
    (Measure.dirac a).toPMF = pure a := by
  rw [toPMF_eq_iff_toMeasure_eq, toMeasure_pure]

end Measure

end Pure

section Bind

/-- The monadic bind operation for `PMF`. -/
/-
**PMF.bind** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：bind (p : PMF α) (f : α -> PMF β) : PMF β
参数：p : PMF α；f : α -> PMF β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monadic bind operation for `PMF`.
-/
def bind (p : PMF α) (f : α → PMF β) : PMF β :=
  ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩

variable (p : PMF α) (f : α → PMF β) (g : β → PMF γ)

@[simp]
/-
**PMF.bind_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b
参数：b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl

@[simp]
/-
**PMF.support_bind** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_bind : (p.bind f).support = ⋃ a in p.support, (f a).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_bind : (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
  Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]
/-
**PMF.mem_support_bind_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_bind_iff (b : β) : b in (p.bind f).support ↔ exists a in p.sup
port, b in (f a).support
参数：b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_bind`：support_bind : (p.bind f).support = ⋃ a in p.support, 
(f a).support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_bind_iff (b : β) :
    b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support := by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

@[simp]
/-
**PMF.pure_bind** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：pure_bind (a : α) (f : α -> PMF β) : (pure a).bind f = f a
参数：a : α；f : α -> PMF β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pure_bind (a : α) (f : α → PMF β) : (pure a).bind f = f a := by
  ext
  simp

@[simp]
/-
**PMF.bind_pure** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_pure : p.bind pure = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.bind_apply`：bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.pure_apply_of_ne`：pure_apply_of_ne (h : a' != a) : pure a a' = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PMF.pure_apply_self`：pure_apply_self : pure a a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem bind_pure : p.bind pure = p :=
  PMF.ext fun x => (bind_apply _ _ _).trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one])

@[simp]
/-
**PMF.bind_const** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_const (p : PMF α) (q : PMF β) : (p.bind fun _ => q) = q
参数：p : PMF α；q : PMF β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.bind_apply`：bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b
· 使用定理 `ENNReal.tsum_mul_right`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal}
, ∑' (i : α), f i * a = (∑' (i : α), f i) * a
· 使用定理 `PMF.tsum_coe`：tsum_coe (p : PMF α) : ∑' a, p a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem bind_const (p : PMF α) (q : PMF β) : (p.bind fun _ => q) = q :=
  PMF.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]

@[simp]
/-
**PMF.bind_bind** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_mul_right`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal}
, ∑' (i : α), f i * a = (∑' (i : α), f i) * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
-/
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g :=
  PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm
/-
**PMF.bind_comm** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_comm (p : PMF α) (q : PMF β) (f : α -> β -> PMF γ) : (p.bind fun a =>
 q.bind (f a)) = q.bind fun b => p.bind fun a => f a b
参数：p : PMF α；q : PMF β；f : α -> β -> PMF γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
-/
theorem bind_comm (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

section Measure

variable (s : Set β)

@[simp]
/-
**PMF.toOuterMeasure_bind_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_bind_apply : (p.bind f).toOuterMeasure s = ∑' a, p a * (f a
).toOuterMeasure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s := by
  classical
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b ∈ s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b ∈ s then f a b else 0 := tsum_congr fun b => by split_ifs <;> simp
    _ = ∑' (a) (b), p a * if b ∈ s then f a b else 0 := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 := tsum_congr fun _ => ENNReal.tsum_mul_left
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 :=
      (tsum_congr fun a => (congr_arg fun x => p a * x) <| tsum_congr fun b => by split_ifs <;> rfl)
    _ = ∑' a, p a * (f a).toOuterMeasure s :=
      tsum_congr fun a => by simp only [toOuterMeasure_apply, Set.indicator_apply]

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/
@[simp]
/-
**PMF.toMeasure_bind_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) : (p.bind 
f).toMeasure s = ∑' a, p a * (f a).toMeasure s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_bind_apply`：toOuterMeasure_bind_apply : (p.bind f).to
OuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`.
-/
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) hs).symm))

end Measure

end Bind

/-
**PMF.** 是 Mathlib 中的一个实例，位于命名空间 `PMF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad PMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnSupport

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bindOnSupport (fun a _ ↦ f a)`, see `bindOnSupport_eq_bind`. -/
/-
**PMF.bindOnSupport** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：bindOnSupport (p : PMF α) (f : forall a in p.support, PMF β) : PMF β
参数：p : PMF α；f : forall a in p.support, PMF β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generalized version of `bind` allowing `f` to only be defined on the support of 
`p`.
  `p.bind f` is equivalent to `p.bindOnSupport (fun a _ ↦ f a)`, see `bindOnSupp
ort_eq_bind`.
-/
def bindOnSupport (p : PMF α) (f : ∀ a ∈ p.support, PMF β) : PMF β :=
  ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b, ENNReal.summable.hasSum_iff.2 (by
    refine ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => ?_) p.tsum_coe)
    simp_rw [ENNReal.tsum_mul_left]
    split_ifs with h
    · simp only [h, zero_mul]
    · rw [(f a h).tsum_coe, mul_one])⟩

variable {p : PMF α} (f : ∀ a ∈ p.support, PMF β)

@[simp]
/-
**PMF.bindOnSupport_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bindOnSupport_apply (b : β) : p.bindOnSupport f b = ∑' a, p a * if h : p a
 = 0 then 0 else f a h b
参数：b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bindOnSupport_apply (b : β) :
    p.bindOnSupport f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl

@[simp]
/-
**PMF.support_bindOnSupport** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_bindOnSupport : (p.bindOnSupport f).support = ⋃ (a : α) (h : a in 
p.support), (f a h).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_bindOnSupport :
    (p.bindOnSupport f).support = ⋃ (a : α) (h : a ∈ p.support), (f a h).support := by
  ext
  -- `simp` suffices; squeezed for performance
  simp only [mem_support_iff, bindOnSupport_apply, ne_eq, ENNReal.tsum_eq_zero,
    dite_eq_left_iff, mul_eq_zero, not_forall, not_or, and_exists_self,
    Set.mem_iUnion]
/-
**PMF.mem_support_bindOnSupport_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_bindOnSupport_iff (b : β) : b in (p.bindOnSupport f).support ↔
 exists (a : α) (h : a in p.support), b in (f a h).support
参数：b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_bindOnSupport`：support_bindOnSupport : (p.bindOnSupport f).s
upport = ⋃ (a : α) (h : a in p.support), (f a h).support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_bindOnSupport_iff (b : β) :
    b ∈ (p.bindOnSupport f).support ↔ ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support := by
  simp only [support_bindOnSupport, Set.mem_iUnion]

/-- `bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypothesis. -/
@[simp]
/-
**PMF.bindOnSupport_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bindOnSupport_eq_bind (p : PMF α) (f : α -> PMF β) : (p.bindOnSupport fun 
a _ => f a) = p.bind f
参数：p : PMF α；f : α -> PMF β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.bindOnSupport_apply`：bindOnSupport_apply (b : β) : p.bindOnSupport f
 b = ∑' a, p a * if h : p a = 0 then 0 else f a h b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypoth
esis.
-/
theorem bindOnSupport_eq_bind (p : PMF α) (f : α → PMF β) :
    (p.bindOnSupport fun a _ => f a) = p.bind f := by
  ext b
  have : ∀ a, ite (p a = 0) 0 (p a * f a b) = p a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]
/-
**PMF.bindOnSupport_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bindOnSupport_eq_zero_iff (b : β) : p.bindOnSupport f b = 0 ↔ forall (a) (
ha : p a != 0), f a ha b = 0
参数：b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem bindOnSupport_eq_zero_iff (b : β) :
    p.bindOnSupport f b = 0 ↔ ∀ (a) (ha : p a ≠ 0), f a ha b = 0 := by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
/-
**PMF.pure_bindOnSupport** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：pure_bindOnSupport (a : α) (f : forall (a' : α) (_ : a' in (pure a).suppor
t), PMF β) : (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl)
参数：a : α；f : forall (a' : α) (_ : a' in (pure a).support), PMF β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PMF.mem_support_pure_iff`：mem_support_pure_iff : a' in (pure a).support 
↔ a' = a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tsum_ite_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (b : β)   [inst_2 : DecidablePred fun x => x = b] (a
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem pure_bindOnSupport (a : α) (f : ∀ (a' : α) (_ : a' ∈ (pure a).support), PMF β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine PMF.ext fun b => ?_
  simp only [bindOnSupport_apply, pure_apply]
  classical
  refine _root_.trans (tsum_congr fun a' => ?_) (tsum_ite_eq a (fun _ ↦ _))
  by_cases h : a' = a <;> simp [h]
/-
**PMF.bindOnSupport_pure** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bindOnSupport_pure (p : PMF α) : (p.bindOnSupport fun a _ => pure a) = p
参数：p : PMF α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.bindOnSupport_eq_bind`：bindOnSupport_eq_bind (p : PMF α) (f : α -> P
MF β) : (p.bindOnSupport fun a _ => f a) = p.bind f
· 使用定理 `PMF.bind_pure`：bind_pure : p.bind pure = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bindOnSupport_pure (p : PMF α) : (p.bindOnSupport fun a _ => pure a) = p := by
  simp only [PMF.bind_pure, PMF.bindOnSupport_eq_bind]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PMF.bindOnSupport_bindOnSupport** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bindOnSupport_bindOnSupport (p : PMF α) (f : forall a in p.support, PMF β)
 (g : forall b in (p.bindOnSupport f).support, PMF γ) : (p.bindOnSupport f).bind
OnSupport g = p.bindOnSupport fun a ha => (f a ha).bindOnSupport fun b hb => g b
 ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩)
参数：p : PMF α；f : forall a in p.support, PMF β；g : forall b in (p.bindOnSupport f
).support, PMF γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PMF.mem_support_bindOnSupport_iff`：mem_support_bindOnSupport_iff (b : β)
 : b in (p.bindOnSupport f).support ↔ exists (a : α) (h : a in p.support), b in 
(f a h).support
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_mul_right`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal}
, ∑' (i : α), f i * a = (∑' (i : α), f i) * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 43 条，此处仅展示前 30 条）
-/
theorem bindOnSupport_bindOnSupport (p : PMF α) (f : ∀ a ∈ p.support, PMF β)
    (g : ∀ b ∈ (p.bindOnSupport f).support, PMF γ) :
    (p.bindOnSupport f).bindOnSupport g =
      p.bindOnSupport fun a ha =>
        (f a ha).bindOnSupport fun b hb =>
          g b ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩) := by
  refine PMF.ext fun a => ?_
  dsimp only [bindOnSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  classical
  simp only [ENNReal.tsum_eq_zero]
  refine ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => ?_)
  split_ifs with h _ h_1 H h_2
  any_goals ring1
  · absurd H
    simpa [h] using h_1 a'
  · simp [h_2]
/-
**PMF.bindOnSupport_comm** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bindOnSupport_comm (p : PMF α) (q : PMF β) (f : forall a in p.support, for
all b in q.support, PMF γ) : (p.bindOnSupport fun a ha => q.bindOnSupport (f a h
a)) = q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb
参数：p : PMF α；q : PMF β；f : forall a in p.support, forall b in q.support, PMF γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 34 条，此处仅展示前 30 条）
-/
theorem bindOnSupport_comm (p : PMF α) (q : PMF β) (f : ∀ a ∈ p.support, ∀ b ∈ q.support, PMF γ) :
    (p.bindOnSupport fun a ha => q.bindOnSupport (f a ha)) =
      q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb := by
  apply PMF.ext; rintro c
  simp only [bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm]
  refine _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => ?_)
  split_ifs with h1 h2 h2 <;> ring

section Measure

variable (s : Set β)

@[simp]
/-
**PMF.toOuterMeasure_bindOnSupport_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_bindOnSupport_apply : (p.bindOnSupport f).toOuterMeasure s 
= ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem toOuterMeasure_bindOnSupport_apply :
    (p.bindOnSupport f).toOuterMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s := by
  simp only [toOuterMeasure_apply]
  classical
  calc
    (∑' b, ite (b ∈ s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [tsum_zero]
    _ = ∑' (a) (b), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, ite (b ∈ s) (dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      (tsum_congr fun a => by simp only [← ENNReal.tsum_mul_left, mul_ite, mul_zero])
    _ = ∑' a, p a * dite (p a = 0) (fun h => 0) fun h => ∑' b, ite (b ∈ s) (f a h b) 0 :=
      tsum_congr fun a => by split_ifs with ha <;> simp only [ite_self, tsum_zero]

/-- The measure of a set under `p.bindOnSupport f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function. -/
@[simp]
/-
**PMF.toMeasure_bindOnSupport_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
 (p.bindOnSupport f).toMeasure s = ∑' a, p a * if h : p a = 0 then 0 else (f a h
).toMeasure s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_bindOnSupport_apply`：toOuterMeasure_bindOnSupport_app
ly : (p.bindOnSupport f).toOuterMeasure s = ∑' a, p a * if h : p a = 0 then 0 el
se (f a h).toOuterMeasure s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The measure of a set under `p.bindOnSupport f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`
.
  The additional if statement is needed since `f` is only a partial function.
-/
theorem toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bindOnSupport f).toMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toMeasure s := by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_bindOnSupport_apply]

end Measure

end BindOnSupport

end PMF

