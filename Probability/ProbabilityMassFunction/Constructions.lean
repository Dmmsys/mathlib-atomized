/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Control.ULiftable

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `PMF` constructions for common probability distributions.

`map` and `seq` allow pushing a `PMF α` along a function `f : α → β` (or distribution of
functions `f : PMF (α → β)`) to get a `PMF β`.

`ofFinset` and `ofFintype` simplify the construction of a `PMF α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `Finset.sum` instead of `tsum`.

`normalize` constructs a `PMF α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `PMF` and re-normalize the new distribution.

`bernoulli` represents the Bernoulli distribution on `Bool`.

-/

@[expose] public section

universe u v

namespace PMF

noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal Finset MeasureTheory

section Map

/-- The functorial action of a function on a `PMF`. -/
/-
**PMF.map** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：map (f : α -> β) (p : PMF α) : PMF β
参数：f : α -> β；p : PMF α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial action of a function on a `PMF`.
-/
def map (f : α → β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)

variable (f : α → β) (p : PMF α) (b : β)
/-
**PMF.monad_map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：monad_map_eq_map {α β : Type u} (f : α -> β) (p : PMF α) : f < > p = p.map
 f
参数：f : α -> β；p : PMF α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monad_map_eq_map {α β : Type u} (f : α → β) (p : PMF α) : f <$> p = p.map f := rfl

open scoped Classical in
@[simp]
/-
**PMF.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：map_apply : (map f p) b = ∑' a, if b = f a then p a else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]

@[simp]
/-
**PMF.support_map** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_map : (map f p).support = f '' p.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.support_bind`：support_bind : (p.bind f).support = ⋃ a in p.support, 
(f a).support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PMF.support_pure`：support_pure : (pure a).support = {a}
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_map : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]
/-
**PMF.mem_support_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_map_iff : b in (map f p).support ↔ exists a in p.support, f a 
= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.support_map`：support_map : (map f p).support = f '' p.support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_map_iff : b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp
/-
**PMF.bind_pure_comp** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_pure_comp : bind p (pure ∘ f) = map f p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_pure_comp : bind p (pure ∘ f) = map f p := rfl
/-
**PMF.map_id** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：map_id : map id p = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.bind_pure`：bind_pure : p.bind pure = p
-/
theorem map_id : map id p = p :=
  bind_pure _
/-
**PMF.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：map_comp (g : β -> γ) : (p.map f).map g = p.map (g ∘ f)
参数：g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.bind_bind`：bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bin
d g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PMF.pure_bind`：pure_bind (a : α) (f : α -> PMF β) : (pure a).bind f = f 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map, Function.comp_def]
/-
**PMF.pure_map** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：pure_map (a : α) : (pure a).map f = pure (f a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.pure_bind`：pure_bind (a : α) (f : α -> PMF β) : (pure a).bind f = f 
a
-/
theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _
/-
**PMF.map_bind** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：map_bind (q : α -> PMF β) (f : β -> γ) : (p.bind q).map f = p.bind fun a =
> (q a).map f
参数：q : α -> PMF β；f : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.bind_bind`：bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bin
d g
-/
theorem map_bind (q : α → PMF β) (f : β → γ) : (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _

@[simp]
/-
**PMF.bind_map** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bind_map (p : PMF α) (f : α -> β) (q : β -> PMF γ) : (p.map f).bind q = p.
bind (q ∘ f)
参数：p : PMF α；f : α -> β；q : β -> PMF γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.bind_bind`：bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bin
d g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PMF.pure_bind`：pure_bind (a : α) (f : α -> PMF β) : (pure a).bind f = f 
a
-/
theorem bind_map (p : PMF α) (f : α → β) (q : β → PMF γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[simp]
/-
**PMF.map_const** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：map_const : p.map (Function.const α b) = pure b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.bind_const`：bind_const (p : PMF α) (q : PMF β) : (p.bind fun _ => q)
 = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_const : p.map (Function.const α b) = pure b := by
  simp only [map, Function.comp_def, bind_const, Function.const]

section Measure

variable (s : Set β)

@[simp]
/-
**PMF.toOuterMeasure_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (
f ⁻¹' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toOuterMeasure_bind_apply`：toOuterMeasure_bind_apply : (p.bind f).to
OuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PMF.toOuterMeasure_pure_apply`：toOuterMeasure_pure_apply : (pure a).toOu
terMeasure s = if a in s then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
-/
theorem toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
  rfl

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

@[simp]
/-
**PMF.toMeasure_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_map_apply (hf : Measurable f) (hs : MeasurableSet s) : (p.map f)
.toMeasure s = p.toMeasure (f ⁻¹' s)
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `measurableSet_preimage`：measurableSet_preimage {t : Set β} (hf : Measura
ble f) (ht : MeasurableSet t) : MeasurableSet (f ⁻¹' t)
· 使用定理 `PMF.toOuterMeasure_map_apply`：toOuterMeasure_map_apply : (p.map f).toOut
erMeasure s = p.toOuterMeasure (f ⁻¹' s)
-/
theorem toMeasure_map_apply (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs,
    toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s

@[simp]
/-
**PMF.toMeasure_map** 是 Mathlib 中的一个引理，位于命名空间 `PMF`。
形式化陈述：toMeasure_map (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map
 f).toMeasure
参数：p : PMF α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_map_apply`：toMeasure_map_apply (hf : Measurable f) (hs : M
easurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
lemma toMeasure_map (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure := by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

end Measure

end Map

section Seq

/-- The monadic sequencing operation for `PMF`. -/
/-
**PMF.seq** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：seq (q : PMF (α -> β)) (p : PMF α) : PMF β
参数：q : PMF (α -> β)；p : PMF α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monadic sequencing operation for `PMF`.
-/
def seq (q : PMF (α → β)) (p : PMF α) : PMF β :=
  q.bind fun m => p.bind fun a => pure (m a)

variable (q : PMF (α → β)) (p : PMF α) (b : β)
/-
**PMF.monad_seq_eq_seq** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：monad_seq_eq_seq {α β : Type u} (q : PMF (α -> β)) (p : PMF α) : q <*> p =
 q.seq p
参数：q : PMF (α -> β)；p : PMF α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monad_seq_eq_seq {α β : Type u} (q : PMF (α → β)) (p : PMF α) : q <*> p = q.seq p := rfl

open scoped Classical in
@[simp]
/-
**PMF.seq_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：seq_apply : (seq q p) b = ∑' (f : α -> β) (a : α), if b = f a then q f * p
 a else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
-/
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => ?_)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]
/-
**PMF.support_seq** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_seq : (seq q p).support = ⋃ f in q.support, f '' p.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.support_bind`：support_bind : (p.bind f).support = ⋃ a in p.support, 
(f a).support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PMF.support_pure`：support_pure : (pure a).support = {a}
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_seq : (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]
/-
**PMF.mem_support_seq_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_seq_iff : b in (seq q p).support ↔ exists f in q.support, b in
 f '' p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.support_seq`：support_seq : (seq q p).support = ⋃ f in q.support, f '
' p.support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_seq_iff : b ∈ (seq q p).support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by simp

end Seq

/-
**PMF.** 是 Mathlib 中的一个实例，位于命名空间 `PMF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor PMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm
/-
**PMF.** 是 Mathlib 中的一个实例，位于命名空间 `PMF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

/--
This instance allows `do` notation for `PMF` to be used across universes, for instance as
```lean4
example {R : Type u} [Ring R] (x : PMF ℕ) : PMF R := do
  let ⟨n⟩ ← ULiftable.up x
  pure n
```
where `x` is in universe `0`, but the return value is in universe `u`.
-/
/-
**PMF.** 是 Mathlib 中的一个实例，位于命名空间 `PMF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance allows `do` notation for `PMF` to be used across universes, for in
stance as
```lean4
example {R : Type u} [Ring R] (x : PMF ℕ) : PMF R := do
  let ⟨n⟩ ← ULiftable.up x
  pure n
```
where `x` is in universe `0`, but the return value is in universe `u`.
-/
instance : ULiftable PMF.{u} PMF.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by simp [map_comp, map_id]
      right_inv := fun a => by simp [map_comp, map_id] }

section OfFinset

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `PMF`. -/
/-
**PMF.ofFinset** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：ofFinset (f : α -> Real>=0∞) (s : Finset α) (h : ∑ a in s, f a = 1) (h' : 
forall (a) (_ : a ∉ s), f a = 0) : PMF α
参数：f : α -> Real>=0∞；s : Finset α；h : ∑ a in s, f a = 1；h' : forall (a) (_ : a ∉
 s), f a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `PMF`.
-/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a ∈ s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a ∈ s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
/-
**PMF.ofFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：ofFinset_apply (a : α) : ofFinset f s h h' a = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
/-
**PMF.support_ofFinset** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_ofFinset : (ofFinset f s h h').support = ↑s inter Function.support
 f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem support_ofFinset : (ofFinset f s h h').support = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)
/-
**PMF.mem_support_ofFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_ofFinset_iff (a : α) : a in (ofFinset f s h h').support ↔ a in
 s ∧ f a != 0
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_ofFinset`：support_ofFinset : (ofFinset f s h h').support = ↑
s inter Function.support f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp
/-
**PMF.ofFinset_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：ofFinset_apply_of_notMem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFinset_apply_of_notMem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

section Measure

variable (t : Set α)

@[simp]
/-
**PMF.toOuterMeasure_ofFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_ofFinset_apply : (ofFinset f s h h').toOuterMeasure t = ∑' 
x, t.indicator f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
-/
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t

@[simp]
/-
**PMF.toMeasure_ofFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) : (ofF
inset f s h h').toMeasure t = ∑' x, t.indicator f x
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_ofFinset_apply`：toOuterMeasure_ofFinset_apply : (ofFi
nset f s h h').toOuterMeasure t = ∑' x, t.indicator f x
-/
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofFinset_apply h h' t)

end Measure

end OfFinset

section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `PMF`. -/
/-
**PMF.ofFintype** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：ofFintype [Fintype α] (f : α -> Real>=0∞) (h : ∑ a, f a = 1) : PMF α
参数：f : α -> Real>=0∞；h : ∑ a, f a = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `PMF`
.
-/
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[simp]
/-
**PMF.ofFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：ofFintype_apply (a : α) : ofFintype f h a = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
/-
**PMF.support_ofFintype** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_ofFintype : (ofFintype f h).support = Function.support f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_ofFintype : (ofFintype f h).support = Function.support f := rfl
/-
**PMF.mem_support_ofFintype_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_ofFintype_iff (a : α) : a in (ofFintype f h).support ↔ f a != 
0
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 := Iff.rfl

open scoped Classical in
@[simp]
/-
**PMF.map_ofFintype** 是 Mathlib 中的一个引理，位于命名空间 `PMF`。
形式化陈述：map_ofFintype [Fintype β] (f : α -> Real>=0∞) (h : ∑ a, f a = 1) (g : α ->
 β) : (ofFintype f h).map g = ofFintype (fun b => ∑ a with g a = b, f a) (by sim
pa [Finset.sum_fiberwise_eq_sum_filter univ univ g f])
参数：f : α -> Real>=0∞；h : ∑ a, f a = 1；g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.map_apply`：map_apply : (map f p) b = ∑' a, if b = f a then p a else 
0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `PMF.ofFintype.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] (f f_1 : α
 → ENNReal) (e_f : f = f_1) (h : ∑ a, f a = 1),   PMF.ofFintype f h = PMF.ofFint
ype f_1 ⋯
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma map_ofFintype [Fintype β] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) (g : α → β) :
    (ofFintype f h).map g = ofFintype (fun b ↦ ∑ a with g a = b, f a)
      (by simpa [Finset.sum_fiberwise_eq_sum_filter univ univ g f]) := by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h ↦ (h <| mem_univ _).elim

section Measure

variable (s : Set α)

@[simp high]
/-
**PMF.toOuterMeasure_ofFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, 
s.indicator f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
-/
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s

@[simp]
/-
**PMF.toMeasure_ofFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) : (of
Fintype f h).toMeasure s = ∑' x, s.indicator f x
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_ofFintype_apply`：toOuterMeasure_ofFintype_apply : (of
Fintype f h).toOuterMeasure s = ∑' x, s.indicator f x
-/
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ hs).trans (toOuterMeasure_ofFintype_apply h s)

end Measure

end OfFintype

section normalize

/-- Given an `f` with non-zero and non-infinite sum, get a `PMF` by normalizing `f` by its `tsum`.
-/
/-
**PMF.normalize** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：normalize (f : α -> Real>=0∞) (hf0 : tsum f != 0) (hf : tsum f != ∞) : PMF
 α
参数：f : α -> Real>=0∞；hf0 : tsum f != 0；hf : tsum f != ∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `f` with non-zero and non-infinite sum, get a `PMF` by normalizing `f` 
by its `tsum`.
-/
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : PMF α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩

variable {f : α → ℝ≥0∞} (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)

@[simp]
/-
**PMF.normalize_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ := rfl

@[simp]
/-
**PMF.support_normalize** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_normalize : (normalize f hf0 hf).support = Function.support f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff]
/-
**PMF.mem_support_normalize_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_normalize_iff (a : α) : a in (normalize f hf0 hf).support ↔ f 
a != 0
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_normalize`：support_normalize : (normalize f hf0 hf).support 
= Function.support f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0 hf).support ↔ f a ≠ 0 := by simp

end normalize

section Filter

/-- Create new `PMF` by filtering on a set with non-zero measure and normalizing. -/
/-
**PMF.filter** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：filter (p : PMF α) (s : Set α) (h : exists a in s, a in p.support) : PMF α
参数：p : PMF α；s : Set α；h : exists a in s, a in p.support。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.tsum_coe_indicator_ne_top`：tsum_coe_indicator_ne_top (p : PMF α) (s 
: Set α) : ∑' a, s.indicator p a != ∞

--- 原说明 ---
Create new `PMF` by filtering on a set with non-zero measure and normalizing.
-/
def filter (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : PMF α :=
  PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)

variable {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support)

@[simp]
/-
**PMF.filter_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：filter_apply (a : α) : (p.filter s h) a = s.indicator p a * (∑' a', (s.ind
icator p) a')⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.tsum_coe_indicator_ne_top`：tsum_coe_indicator_ne_top (p : PMF α) (s 
: Set α) : ∑' a, s.indicator p a != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.filter.eq_1`：∀ {α : Type u_1} (p : PMF α) (s : Set α) (h : ∃ a ∈ s, 
a ∈ p.support), p.filter s h = PMF.normalize (s.indicator ⇑p) ⋯ ⋯
· 使用定理 `PMF.normalize_apply`：normalize_apply (a : α) : (normalize f hf0 hf) a = 
f a * (∑' x, f x)⁻¹
-/
theorem filter_apply (a : α) :
    (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [filter, normalize_apply]
/-
**PMF.filter_apply_eq_zero_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：filter_apply_eq_zero_of_notMem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.filter_apply`：filter_apply (a : α) : (p.filter s h) a = s.indicator 
p a * (∑' a', (s.indicator p) a')⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_apply_eq_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Zer
o M] {s : Set α} {f : α → M} {a : α}, s.indicator f a = 0 ↔ a ∈ s → f a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem filter_apply_eq_zero_of_notMem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply, Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]
/-
**PMF.mem_support_filter_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_filter_iff {a : α} : a in (p.filter s h).support ↔ a in s ∧ a 
in p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PMF.tsum_coe_indicator_ne_top`：tsum_coe_indicator_ne_top (p : PMF α) (s 
: Set α) : ∑' a, s.indicator p a != ∞
· 使用定理 `PMF.mem_support_normalize_iff`：mem_support_normalize_iff (a : α) : a in 
(normalize f hf0 hf).support ↔ f a != 0
· 使用定理 `Set.indicator_apply_ne_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Zer
o M] {s : Set α} {f : α → M} {a : α},   s.indicator f a ≠ 0 ↔ a ∈ s ∩ Function.s
upport f
-/
theorem mem_support_filter_iff {a : α} : a ∈ (p.filter s h).support ↔ a ∈ s ∧ a ∈ p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero

@[simp]
/-
**PMF.support_filter** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_filter : (p.filter s h).support = s inter p.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PMF.mem_support_filter_iff`：mem_support_filter_iff {a : α} : a in (p.fil
ter s h).support ↔ a in s ∧ a in p.support
-/
theorem support_filter : (p.filter s h).support = s ∩ p.support :=
  Set.ext fun _ => mem_support_filter_iff _
/-
**PMF.filter_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.su
pport
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.apply_eq_zero_iff`：apply_eq_zero_iff (p : PMF α) (a : α) : p a = 0 ↔
 a ∉ p.support
· 使用定理 `PMF.support_filter`：support_filter : (p.filter s h).support = s inter p.
support
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  rw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_or]
/-
**PMF.filter_apply_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：filter_apply_ne_zero_iff (a : α) : (p.filter s h) a != 0 ↔ a in s ∧ a in p
.support
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `PMF.filter_apply_eq_zero_iff`：filter_apply_eq_zero_iff (a : α) : (p.filt
er s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem filter_apply_ne_zero_iff (a : α) : (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

section bernoulli

/-- A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
@[deprecated ProbabilityTheory.bernoulliMeasure (since := "2026-04-07")]
/-
**PMF.bernoulli** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：bernoulli (p : Real>=0) (h : p <= 1) : PMF Bool
参数：p : Real>=0；h : p <= 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`.
-/
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0} (h : p ≤ 1) (b : Bool)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply (since := "2026-04-07")]
/-
**PMF.bernoulli_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bernoulli_apply : bernoulli p h b = cond b p (1 - p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.apply_cond`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {b : Bool} 
{a a' : α}, f (bif b then a else a') = bif b then f a else f a'
-/
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := by
  simp only [bernoulli, ofFintype_apply]
  exact Eq.symm (Bool.apply_cond ofNNReal)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]
/-
**PMF.support_bernoulli** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_bernoulli : (bernoulli p h).support = { b | cond b (p != 0) (p != 
1) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.bernoulli_apply`：bernoulli_apply : bernoulli p h b = cond b p (1 - p
)
· 使用定理 `Bool.cond_false`：∀ {α : Sort u} {a b : α}, (bif false then a else b) = b
· 使用定理 `ENNReal.coe_sub`：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bool.cond_true`：∀ {α : Sort u} {a b : α}, (bif true then a else b) = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine Set.ext fun b => ?_
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, ENNReal.coe_sub,
      ENNReal.coe_one, Bool.cond_prop, Set.mem_ofPred_eq, Bool.false_eq_true, ite_false,
      not_iff_not]
    constructor
    · intro h'
      simp only [tsub_eq_zero_iff_le, one_le_coe_iff] at h'
      exact eq_of_le_of_ge h h'
    · intro h'
      simp only [h', ENNReal.coe_one, tsub_self]
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_ofPred_eq, ne_eq,
      ENNReal.coe_eq_zero]

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]
/-
**PMF.mem_support_bernoulli_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_bernoulli_iff : b in (bernoulli p h).support ↔ cond b (p != 0)
 (p != 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.support_bernoulli`：support_bernoulli : (bernoulli p h).support = { b
 | cond b (p != 0) (p != 1) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by
  simp [support_bernoulli]

end bernoulli

end

end PMF

