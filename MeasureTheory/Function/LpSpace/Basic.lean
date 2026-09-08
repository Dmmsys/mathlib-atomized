/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E`
(see `MeasureTheory.AEEqFun`) such that `eLpNorm f p μ` is finite.
For `1 ≤ p`, `eLpNorm` defines a norm and `Lp` is a complete metric space
(the latter is proved at `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`).

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` such that `eLpNorm f p μ` is finite.
  Defined as an `AddSubgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `ContinuousLinearMap.compLp` defines the action on `Lp` of a continuous linear map.
* `Lp.posPart` is the positive part of an `Lp` function.
* `Lp.negPart` is the negative part of an `Lp` function.

## Notation

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `AddSubgroup`, dot notation does not work. Use `Lp.Measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.Measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) := by
  ext1
  filter_upwards [coeFn_add (f + g) h, coeFn_add f g, coeFn_add f (g + h), coeFn_add g h]
    with _ ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, add_assoc]
```
The lemma `coeFn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coeFn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace MeasureTheory

/-!
### Lp space

The space of equivalence classes of measurable functions for which `eLpNorm f p μ < ∞`.
-/

@[simp]
/-
**MeasureTheory.eLpNorm_aeeqFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_aeeqFun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedA
ddCommGroup E] {p : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) : eLp
Norm (AEEqFun.mk f hf) p μ = eLpNorm f p μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f

--- 原说明 ---
### Lp space

The space of equivalence classes of measurable functions for which `eLpNorm f p 
μ < ∞`.
-/
theorem eLpNorm_aeeqFun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (AEEqFun.mk f hf) p μ = eLpNorm f p μ :=
  eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)
/-
**MeasureTheory.MemLp.eLpNorm_mk_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.MemLp`。
形式化陈述：∀ {α : Type u_6} {E : Type u_7} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : NormedAddCommGroup E]   {p : ENNReal} {f : α → E} (hfp 
: MeasureTheory.MemLp f p μ),   MeasureTheory.eLpNorm (↑(MeasureTheory.AEEqFun.m
k f ⋯)) p μ < ⊤
参数：hfp : MeasureTheory.MemLp f p μ；↑(MeasureTheory.AEEqFun.mk f ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_aeeqFun`：eLpNorm_aeeqFun {α E : Type*} [Measurable
Space α] {μ : Measure α} [NormedAddCommGroup E] {p : Real>=0∞} {f : α -> E} (hf 
: AEStronglyMeasura…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.eLpNorm_mk_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {f : α → E} (hfp : MemLp f p μ) :
    eLpNorm (AEEqFun.mk f hfp.1) p μ < ∞ := by simp [hfp.2]

/-- Lp space -/
/-
**MeasureTheory.Lp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : Rea
l>=0∞) (μ : Measure α
参数：E : Type*；p : Real>=0∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lp space
-/
def Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | eLpNorm f p μ < ∞ }
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLpNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.mem_ofPred_eq, eLpNorm_congr_ae (AEEqFun.coeFn_neg f), eLpNorm_neg]

/-- `α →₁[μ] E` is the type of `L¹` or integrable functions from `α` to `E`. -/
scoped notation:25 α' " →₁[" μ "] " E => MeasureTheory.Lp (α := α') E 1 μ
/-- `α →₂[μ] E` is the type of `L²` or square-integrable functions from `α` to `E`. -/
scoped notation:25 α' " →₂[" μ "] " E => MeasureTheory.Lp (α := α') E 2 μ

namespace MemLp

/-- make an element of Lp from a function verifying `MemLp` -/
/-
**MeasureTheory.MemLp.toLp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：toLp (f : α -> E) (h_mem_ℒp : MemLp f p μ) : Lp E p μ
参数：f : α -> E；h_mem_ℒp : MemLp f p μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.eLpNorm_mk_lt_top`：∀ {α : Type u_6} {E : Type u_7} [
inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : NormedAddCommG
roup E]   {p : ENNReal} {f …

--- 原说明 ---
make an element of Lp from a function verifying `MemLp`
-/
def toLp (f : α → E) (h_mem_ℒp : MemLp f p μ) : Lp E p μ :=
  ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.eLpNorm_mk_lt_top⟩
/-
**MeasureTheory.MemLp.toLp_val** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：toLp_val {f : α -> E} (h : MemLp f p μ) : (toLp f h).1 = AEEqFun.mk f h.1
参数：h : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toLp_val {f : α → E} (h : MemLp f p μ) : (toLp f h).1 = AEEqFun.mk f h.1 := rfl
/-
**MeasureTheory.MemLp.coeFn_toLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：coeFn_toLp {f : α -> E} (hf : MemLp f p μ) : hf.toLp f =ᵐ[μ] f
参数：hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_toLp {f : α → E} (hf : MemLp f p μ) : hf.toLp f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.MemLp.toLp_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：toLp_congr {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) (hfg : f =
ᵐ[μ] g) : hf.toLp f = hg.toLp g
参数：hf : MemLp f p μ；hg : MemLp g p μ；hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.MemLp.eLpNorm_mk_lt_top`：∀ {α : Type u_6} {E : Type u_7} [
inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : NormedAddCommG
roup E]   {p : ENNReal} {f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem toLp_congr {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) :
    hf.toLp f = hg.toLp g := by simp [toLp, hfg]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.MemLp.toLp_eq_toLp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
MemLp`。
形式化陈述：toLp_eq_toLp_iff {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) : hf
.toLp f = hg.toLp g ↔ f =ᵐ[μ] g
参数：hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.eLpNorm_mk_lt_top`：∀ {α : Type u_6} {E : Type u_7} [
inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : NormedAddCommG
roup E]   {p : ENNReal} {f …
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toLp_eq_toLp_iff {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by simp [toLp]

@[simp]
/-
**MeasureTheory.MemLp.toLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：toLp_zero (h : MemLp (0 : α -> E) p μ) : h.toLp 0 = 0
参数：h : MemLp (0 : α -> E) p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toLp_zero (h : MemLp (0 : α → E) p μ) : h.toLp 0 = 0 :=
  rfl
/-
**MeasureTheory.MemLp.toLp_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：toLp_add {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) : (hf.add hg
).toLp (f + g) = hf.toLp f + hg.toLp g
参数：hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem toLp_add {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g :=
  rfl
/-
**MeasureTheory.MemLp.toLp_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：toLp_neg {f : α -> E} (hf : MemLp f p μ) : hf.neg.toLp (-f) = -hf.toLp f
参数：hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
-/
theorem toLp_neg {f : α → E} (hf : MemLp f p μ) : hf.neg.toLp (-f) = -hf.toLp f :=
  rfl
/-
**MeasureTheory.MemLp.toLp_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：toLp_sub {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) : (hf.sub hg
).toLp (f - g) = hf.toLp f - hg.toLp g
参数：hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
-/
theorem toLp_sub {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g :=
  rfl

end MemLp

namespace Lp

/-
**MeasureTheory.Lp.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instCoeFun : CoeFun (Lp E p μ) (fun _ => α -> E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeFun : CoeFun (Lp E p μ) (fun _ => α → E) :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

@[ext high]
/-
**MeasureTheory.Lp.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MeasureTheory.AEEqFun.ext`：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = 
g
-/
theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g := by
  ext
  exact h
/-
**MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Lp`。
形式化陈述：mem_Lp_iff_eLpNorm_lt_top {f : α ->ₘ[μ] E} : f in Lp E p μ ↔ eLpNorm f p μ
 < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem mem_Lp_iff_eLpNorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ eLpNorm f p μ < ∞ := Iff.rfl
/-
**MeasureTheory.Lp.mem_Lp_iff_memLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`
。
形式化陈述：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f in Lp E p μ ↔ MemLp f p μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.AEEqFun.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topological
Space β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_Lp_iff_memLp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ MemLp f p μ := by
  simp [mem_Lp_iff_eLpNorm_lt_top, MemLp, f.stronglyMeasurable.aestronglyMeasurable]
/-
**MeasureTheory.Lp.antitone** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup E]   [MeasureTheory.IsFiniteMeasure μ] {p
 q : ENNReal}, p ≤ q → MeasureTheory.Lp E q μ ≤ MeasureTheory.Lp E p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
protected theorem antitone [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
  fun f hf => (MemLp.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]
/-
**MeasureTheory.Lp.coeFn_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_mk {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ)
 : α -> E) = f
参数：hf : eLpNorm f p μ < ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coeFn_mk {f : α →ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α → E) = f :=
  rfl

-- not @[simp] because dsimp can prove this
/-
**MeasureTheory.Lp.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coe_mk {f : α ->ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) :
 α ->ₘ[μ] E) = f
参数：hf : eLpNorm f p μ < ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_mk {f : α →ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f :=
  rfl

@[simp]
/-
**MeasureTheory.Lp.toLp_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ) : hf.toLp f = f
参数：f : Lp E p μ；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.eLpNorm_mk_lt_top`：∀ {α : Type u_6} {E : Type u_7} [
inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : NormedAddCommG
roup E]   {p : ENNReal} {f …
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ) : hf.toLp f = f := by
  simp [MemLp.toLp]
/-
**MeasureTheory.Lp.eLpNorm_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：eLpNorm_lt_top (f : Lp E p μ) : eLpNorm f p μ < ∞
参数：f : Lp E p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem eLpNorm_lt_top (f : Lp E p μ) : eLpNorm f p μ < ∞ :=
  f.prop

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**MeasureTheory.Lp.eLpNorm_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm f p μ != ∞
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Lp.eLpNorm_lt_top`：eLpNorm_lt_top (f : Lp E p μ) : eLpNorm
 f p μ < ∞
-/
theorem eLpNorm_ne_top (f : Lp E p μ) : eLpNorm f p μ ≠ ∞ :=
  (eLpNorm_lt_top f).ne

@[fun_prop]
/-
**MeasureTheory.Lp.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] (f : ↥(MeasureTheory.L
p E p μ)), MeasureTheory.StronglyMeasurable ↑↑f
参数：f : ↥(MeasureTheory.Lp E p μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topological
Space β]   (f : α →ₘ[μ] β), Me…
-/
protected theorem stronglyMeasurable (f : Lp E p μ) : StronglyMeasurable f :=
  f.val.stronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.Lp.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] (f : ↥(MeasureTheory.L
p E p μ)), MeasureTheory.AEStronglyMeasurable (↑↑f) μ
参数：f : ↥(MeasureTheory.Lp E p μ)；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
  f.val.aestronglyMeasurable
/-
**MeasureTheory.Lp.memLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] (f : ↥(MeasureTheory.L
p E p μ)), MeasureTheory.MemLp (↑↑f) p μ
参数：f : ↥(MeasureTheory.Lp E p μ)；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
protected theorem memLp (f : Lp E p μ) : MemLp f p μ :=
  ⟨Lp.aestronglyMeasurable f, f.prop⟩

variable (E p μ)
/-
**MeasureTheory.Lp.coeFn_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_zero`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace β]
   [inst_2 : Zero β], …
-/
theorem coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 :=
  AEEqFun.coeFn_zero

variable {E p μ}
/-
**MeasureTheory.Lp.coeFn_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_neg`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : AddGroup …
-/
theorem coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f :=
  AEEqFun.coeFn_neg _
/-
**MeasureTheory.Lp.coeFn_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_add`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : Add γ] [i…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g :=
  AEEqFun.coeFn_add _ _
/-
**MeasureTheory.Lp.coeFn_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_sub`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : AddGroup …
-/
theorem coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g :=
  AEEqFun.coeFn_sub _ _
/-
**MeasureTheory.Lp.coeFn_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_finsetSum {ι : Type*} (s : Finset ι) (f : ι -> Lp E p μ) : ⇑(∑ i in 
s, f i) =ᵐ[μ] ∑ i in s, ⇑(f i)
参数：s : Finset ι；f : ι -> Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.val_finsetSum`：∀ {ι : Type u_3} {G : Type u_4} [inst : AddCo
mmGroup G] (H : AddSubgroup G) (f : ι → ↥H) (s : Finset ι),   ↑(∑ i ∈ s, f i) = 
∑ i ∈ s, ↑(f i)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem coeFn_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] ∑ i ∈ s, ⇑(f i) := by
  simp [AEEqFun.coeFn_finsetSum]
/-
**MeasureTheory.Lp.coeFn_fun_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp`。
形式化陈述：coeFn_fun_finsetSum {ι : Type*} (s : Finset ι) (f : ι -> Lp E p μ) : ⇑(∑ i
 in s, f i) =ᵐ[μ] fun x => ∑ i in s, f i x
参数：s : Finset ι；f : ι -> Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.Lp.coeFn_finsetSum`：coeFn_finsetSum {ι : Type*} (s : Finse
t ι) (f : ι -> Lp E p μ) : ⇑(∑ i in s, f i) =ᵐ[μ] ∑ i in s, ⇑(f i)
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeFn_fun_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x ↦ ∑ i ∈ s, f i x := by
  grw [coeFn_finsetSum]
  filter_upwards with x using by simp
/-
**MeasureTheory.Lp.const_mem_Lp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：const_mem_Lp (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFinite
Measure μ] : @AEEqFun.const α _ _ μ _ c in Lp E p μ
参数：α；μ : Measure α；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.eLpNorm_mk_lt_top`：∀ {α : Type u_6} {E : Type u_7} [
inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : NormedAddCommG
roup E]   {p : ENNReal} {f …
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
-/
theorem const_mem_Lp (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ] :
    @AEEqFun.const α _ _ μ _ c ∈ Lp E p μ :=
  (memLp_const c).eLpNorm_mk_lt_top
/-
**MeasureTheory.Lp.instNorm** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instNorm : Norm (Lp E p μ) where norm f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNorm : Norm (Lp E p μ) where norm f := ENNReal.toReal (eLpNorm f p μ)

-- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- can't use `ENNReal.toNNReal (eLpNorm f p μ)`
/-
**MeasureTheory.Lp.instNNNorm** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instNNNorm : NNNorm (Lp E p μ) where nnnorm f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNNorm : NNNorm (Lp E p μ) where nnnorm f := .mk ‖f‖ ENNReal.toReal_nonneg
/-
**MeasureTheory.Lp.instDist** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instDist : Dist (Lp E p μ) where dist f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDist : Dist (Lp E p μ) where dist f g := ‖-f + g‖
/-
**MeasureTheory.Lp.instEDist** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instEDist : EDist (Lp E p μ) where edist f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instEDist : EDist (Lp E p μ) where edist f g := eLpNorm (-⇑f + ⇑g) p μ
/-
**MeasureTheory.Lp.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm f p μ)
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm f p μ) :=
  rfl
/-
**MeasureTheory.Lp.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (eLpNorm f p μ)
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.Lp.coe_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] (f : ↥(MeasureTheory.L
p E p μ)), ↑‖f‖₊ = ‖f‖
参数：f : ↥(MeasureTheory.Lp E p μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
protected theorem coe_nnnorm (f : Lp E p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
  rfl
/-
**MeasureTheory.Lp.enorm_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f p μ
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
-/
theorem enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f p μ :=
  ENNReal.coe_toNNReal <| Lp.eLpNorm_ne_top f

@[simp]
/-
**MeasureTheory.Lp.norm_toLp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：norm_toLp (f : α -> E) (hf : MemLp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (
eLpNorm f p μ)
参数：f : α -> E；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
-/
lemma norm_toLp (f : α → E) (hf : MemLp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]

@[simp]
/-
**MeasureTheory.Lp.nnnorm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：nnnorm_toLp (f : α -> E) (hf : MemLp f p μ) : ‖hf.toLp f‖₊ = ENNReal.toNNR
eal (eLpNorm f p μ)
参数：f : α -> E；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.Lp.norm_toLp`：norm_toLp (f : α -> E) (hf : MemLp f p μ) : 
‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
-/
theorem nnnorm_toLp (f : α → E) (hf : MemLp f p μ) :
    ‖hf.toLp f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
  NNReal.eq <| norm_toLp f hf

@[simp]
/-
**MeasureTheory.Lp.enorm_toLp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：enorm_toLp {f : α -> E} (hf : MemLp f p μ) : ‖hf.toLp f‖ₑ = eLpNorm f p μ
参数：hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.nnnorm_toLp`：nnnorm_toLp (f : α -> E) (hf : MemLp f p μ
) : ‖hf.toLp f‖₊ = ENNReal.toNNReal (eLpNorm f p μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_toLp {f : α → E} (hf : MemLp f p μ) : ‖hf.toLp f‖ₑ = eLpNorm f p μ := by
  simp_rw [enorm, nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]
/-
**MeasureTheory.Lp.dist_eq_eLpNorm_neg_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp`。
形式化陈述：dist_eq_eLpNorm_neg_add (f g : Lp E p μ) : dist f g = (eLpNorm (-⇑f + ⇑g) 
p μ).toReal
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `MeasureTheory.Lp.coeFn_neg`：coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f
· 使用引理 `MeasureTheory.ae_eq_rfl`：ae_eq_rfl {f : α -> β} : f =ᵐ[μ] f
-/
theorem dist_eq_eLpNorm_neg_add (f g : Lp E p μ) : dist f g = (eLpNorm (-⇑f + ⇑g) p μ).toReal := by
  simp_rw [dist, norm_def]
  congr 1
  apply eLpNorm_congr_ae
  exact (coeFn_add _ _).trans ((coeFn_neg f).add ae_eq_rfl)
/-
**MeasureTheory.Lp.dist_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：dist_def (f g : Lp E p μ) : dist f g = (eLpNorm (⇑f - ⇑g) p μ).toReal
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.dist_eq_eLpNorm_neg_add`：dist_eq_eLpNorm_neg_add (f g :
 Lp E p μ) : dist f g = (eLpNorm (-⇑f + ⇑g) p μ).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem dist_def (f g : Lp E p μ) : dist f g = (eLpNorm (⇑f - ⇑g) p μ).toReal := by
  rw [dist_eq_eLpNorm_neg_add, ← eLpNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
/-
**MeasureTheory.Lp.edist_eq_eLpNorm_neg_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：edist_eq_eLpNorm_neg_add (f g : Lp E p μ) : edist f g = eLpNorm (-⇑f + ⇑g)
 p μ
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem edist_eq_eLpNorm_neg_add (f g : Lp E p μ) : edist f g = eLpNorm (-⇑f + ⇑g) p μ := rfl
/-
**MeasureTheory.Lp.edist_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：edist_def (f g : Lp E p μ) : edist f g = eLpNorm (⇑f - ⇑g) p μ
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.edist_eq_eLpNorm_neg_add`：edist_eq_eLpNorm_neg_add (f g
 : Lp E p μ) : edist f g = eLpNorm (-⇑f + ⇑g) p μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem edist_def (f g : Lp E p μ) : edist f g = eLpNorm (⇑f - ⇑g) p μ := by
  rw [edist_eq_eLpNorm_neg_add, ← eLpNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
/-
**MeasureTheory.Lp.edist_dist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] (f g : ↥(MeasureTheory
.Lp E p μ)), edist f g = ENNReal.ofReal (dist f g)
参数：f g : ↥(MeasureTheory.Lp E p μ)；dist f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.edist_def`：edist_def (f g : Lp E p μ) : edist f g = eLp
Norm (⇑f - ⇑g) p μ
· 使用定理 `MeasureTheory.Lp.dist_def`：dist_def (f g : Lp E p μ) : dist f g = (eLpNo
rm (⇑f - ⇑g) p μ).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
-/
protected theorem edist_dist (f g : Lp E p μ) : edist f g = .ofReal (dist f g) := by
  rw [edist_def, dist_def, ← eLpNorm_congr_ae (coeFn_sub _ _),
    ENNReal.ofReal_toReal (eLpNorm_ne_top (f - g))]
/-
**MeasureTheory.Lp.dist_edist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] (f g : ↥(MeasureTheory
.Lp E p μ)), dist f g = (edist f g).toReal
参数：f g : ↥(MeasureTheory.Lp E p μ)；edist f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.dist_eq_eLpNorm_neg_add`：dist_eq_eLpNorm_neg_add (f g :
 Lp E p μ) : dist f g = (eLpNorm (-⇑f + ⇑g) p μ).toReal
-/
protected theorem dist_edist (f g : Lp E p μ) : dist f g = (edist f g).toReal :=
  MeasureTheory.Lp.dist_eq_eLpNorm_neg_add ..
/-
**MeasureTheory.Lp.dist_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：dist_eq_norm (f g : Lp E p μ) : dist f g = ‖-f + g‖
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem dist_eq_norm (f g : Lp E p μ) : dist f g = ‖-f + g‖ := rfl

@[simp]
/-
**MeasureTheory.Lp.edist_toLp_toLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：edist_toLp_toLp (f g : α -> E) (hf : MemLp f p μ) (hg : MemLp g p μ) : edi
st (hf.toLp f) (hg.toLp g) = eLpNorm (f - g) p μ
参数：f g : α -> E；hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.edist_def`：edist_def (f g : Lp E p μ) : edist f g = eLp
Norm (⇑f - ⇑g) p μ
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
-/
theorem edist_toLp_toLp (f g : α → E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g) p μ := by
  rw [edist_def]
  exact eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)

@[simp]
/-
**MeasureTheory.Lp.edist_toLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：edist_toLp_zero (f : α -> E) (hf : MemLp f p μ) : edist (hf.toLp f) 0 = eL
pNorm f p μ
参数：f : α -> E；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.Lp.edist_toLp_toLp`：edist_toLp_toLp (f g : α -> E) (hf : M
emLp f p μ) (hg : MemLp g p μ) : edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g)
 p μ
-/
theorem edist_toLp_zero (f : α → E) (hf : MemLp f p μ) : edist (hf.toLp f) 0 = eLpNorm f p μ := by
  simpa using edist_toLp_toLp f 0 hf .zero

@[simp]
/-
**MeasureTheory.Lp.nnnorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.nnnorm_def`：nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.
toNNReal (eLpNorm f p μ)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_zero`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace β]
   [inst_2 : Zero β], …
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0 := by
  rw [nnnorm_def, ZeroMemClass.coe_zero]
  simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]

@[simp]
/-
**MeasureTheory.Lp.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：norm_zero : ‖(0 : Lp E p μ)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.nnnorm_zero`：nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0
-/
theorem norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
  congr_arg ((↑) : ℝ≥0 → ℝ) nnnorm_zero

@[simp]
/-
**MeasureTheory.Lp.norm_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0
参数：f : Lp E p (0 : MeasureTheory.Measure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0 := by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_measure_zero, ENNReal.toReal_zero]
/-
**MeasureTheory.Lp.norm_exponent_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup E]   (f : ↥(MeasureTheory.Lp E 0 μ)), ‖f‖
 = 0
参数：f : ↥(MeasureTheory.Lp E 0 μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem norm_exponent_zero (f : Lp E 0 μ) : ‖f‖ = 0 := by
  -- Squeezed for performance reasons
  simp_rw [norm_def, eLpNorm_exponent_zero, ENNReal.toReal_zero]
/-
**MeasureTheory.Lp.eq_zero_iff_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Lp`。
形式化陈述：eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.ext_iff`：∀ {α : Type u_1} {E : Type u_4} {m : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f g : ↥…
· 使用定理 `Filter.EventuallyEq.congr_right`：∀ {α : Type u} {β : Type v} {l : Filter
 α} {f g h : α → β}, g =ᶠ[l] h → (f =ᶠ[l] g ↔ f =ᶠ[l] h)
· 使用定理 `MeasureTheory.AEEqFun.coeFn_zero`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace β]
   [inst_2 : Zero β], …
-/
theorem eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [Lp.ext_iff]
  exact EventuallyEq.congr_right AEEqFun.coeFn_zero
/-
**MeasureTheory.Lp.nnnorm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_iff`：eLpNorm_eq_zero_iff {f : α -> ε} (hf 
: AEStronglyMeasurable f μ) (h0 : p != 0) : eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Lp.nnnorm_zero`：nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0
-/
theorem nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 := by
  refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
  simp_rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff, eLpNorm_ne_top, or_false] at hf
  simp_rw [eq_zero_iff_ae_eq_zero, ← eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm, hf]
/-
**MeasureTheory.Lp.norm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`
。
形式化陈述：norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `MeasureTheory.Lp.nnnorm_eq_zero_iff`：nnnorm_eq_zero_iff {f : Lp E p μ} (
hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0
-/
theorem norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
  NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

@[simp]
/-
**MeasureTheory.Lp.nnnorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.nnnorm_def`：nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.
toNNReal (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.Lp.coeFn_neg`：coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
-/
theorem nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊ := by
  rw [nnnorm_def, nnnorm_def, eLpNorm_congr_ae (coeFn_neg _), eLpNorm_neg]

@[simp]
/-
**MeasureTheory.Lp.norm_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.nnnorm_neg`：nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊
-/
theorem norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) (nnnorm_neg f)
/-
**MeasureTheory.Lp.nnnorm_le_mul_nnnorm_of_ae_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Lp`。
形式化陈述：nnnorm_le_mul_nnnorm_of_ae_le_mul {c : Real>=0} {f : Lp E p μ} {g : Lp F p
 μ} (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : ‖f‖₊ <= c * ‖g‖₊
参数：h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul`：eLpNorm_le_nn
real_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0} (h : fora
llᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toNNReal_le_toNNReal`：toNNReal_le_toNNReal (ha : a != ∞) (hb : b
 != ∞) : a.toNNReal <= b.toNNReal ↔ a <= b
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : ‖f‖₊ ≤ c * ‖g‖₊ := by
  simp only [nnnorm_def]
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h p
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · finiteness
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)
/-
**MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：norm_le_mul_norm_of_ae_le_mul {c : Real} {f : Lp E p μ} {g : Lp F p μ} (h 
: forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) : ‖f‖ <= c * ‖g‖
参数：h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `MeasureTheory.Lp.nnnorm_le_mul_nnnorm_of_ae_le_mul`：nnnorm_le_mul_nnnorm
_of_ae_le_mul {c : Real>=0} {f : Lp E p μ} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f 
x‖₊ <= c * ‖g x‖₊) : ‖f‖₊ <= c * ‖g‖₊
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg`：eLpNorm_eq_zero
_and_zero_of_ae_le_mul_neg {f : α -> F} {g : α -> G} {c : Real} (h : forallᵐ x ∂
μ, ‖f x‖ <= c * ‖g x‖) (hc : c < 0) (p : Real…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ := by
  rcases le_or_gt 0 c with hc | hc
  · lift c to ℝ≥0 using hc
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]
/-
**MeasureTheory.Lp.norm_le_norm_of_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f 
x‖ <= ‖g x‖) : ‖f‖ <= ‖g‖
参数：h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `MeasureTheory.eLpNorm_mono_ae`：eLpNorm_mono_ae {f : α -> F} {g : α -> G}
 (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
-/
theorem norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    ‖f‖ ≤ ‖g‖ := by
  rw [norm_def, norm_def]
  exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae h)
/-
**MeasureTheory.Lp.mem_Lp_of_nnnorm_ae_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Lp`。
形式化陈述：mem_Lp_of_nnnorm_ae_le_mul {c : Real>=0} {f : α ->ₘ[μ] E} {g : Lp F p μ} (
h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : f in Lp E p μ
参数：h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `MeasureTheory.MemLp.of_nnnorm_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}
   [inst : NormedAddCommGr…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
theorem mem_Lp_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : α →ₘ[μ] E} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_nnnorm_le_mul (Lp.memLp g) f.aestronglyMeasurable h
/-
**MeasureTheory.Lp.mem_Lp_of_ae_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp`。
形式化陈述：mem_Lp_of_ae_le_mul {c : Real} {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forall
ᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) : f in Lp E p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
theorem mem_Lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_le_mul (Lp.memLp g) f.aestronglyMeasurable h
/-
**MeasureTheory.Lp.mem_Lp_of_nnnorm_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Lp`。
形式化陈述：mem_Lp_of_nnnorm_ae_le {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, 
‖f x‖₊ <= ‖g x‖₊) : f in Lp E p μ
参数：h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `MeasureTheory.MemLp.of_le`：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5
} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst :
 NormedAddCommG…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
theorem mem_Lp_of_nnnorm_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_le (Lp.memLp g) f.aestronglyMeasurable h
/-
**MeasureTheory.Lp.mem_Lp_of_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：mem_Lp_of_ae_le {f : α ->ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖ <
= ‖g x‖) : f in Lp E p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.mem_Lp_of_nnnorm_ae_le`：mem_Lp_of_nnnorm_ae_le {f : α -
>ₘ[μ] E} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) : f in Lp E p μ
-/
theorem mem_Lp_of_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    f ∈ Lp E p μ :=
  mem_Lp_of_nnnorm_ae_le h
/-
**MeasureTheory.Lp.mem_Lp_of_ae_nnnorm_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Lp`。
形式化陈述：mem_Lp_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : Real>=
0) (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : f in Lp E p μ
参数：C : Real>=0；hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `MeasureTheory.MemLp.of_bound`：∀ {α : Type u_1} {E : Type u_4} {m0 : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [Measur…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
theorem mem_Lp_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_bound f.aestronglyMeasurable _ hfC
/-
**MeasureTheory.Lp.mem_Lp_of_ae_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：mem_Lp_of_ae_bound [IsFiniteMeasure μ] {f : α ->ₘ[μ] E} (C : Real) (hfC : 
forallᵐ x ∂μ, ‖f x‖ <= C) : f in Lp E p μ
参数：C : Real；hfC : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `MeasureTheory.MemLp.of_bound`：∀ {α : Type u_1} {E : Type u_4} {m0 : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [Measur…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
theorem mem_Lp_of_ae_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_bound f.aestronglyMeasurable _ hfC
/-
**MeasureTheory.Lp.nnnorm_le_of_ae_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : Real>=0} (hf
C : forallᵐ x ∂μ, ‖f x‖₊ <= C) : ‖f‖₊ <= measureUnivNNReal μ ^ p.toReal⁻¹ * C
参数：hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `MeasureTheory.Lp.nnnorm_def`：nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.
toNNReal (eLpNorm f p μ)
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_le_of_ae_nnnorm_bound`：eLpNorm_le_of_ae_nnnorm_bou
nd {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : eLpNorm f p μ 
<= C • μ Set.univ ^ p.toReal⁻¹
· 使用定理 `MeasureTheory.coe_measureUnivNNReal`：coe_measureUnivNNReal (μ : Measure 
α) [IsFiniteMeasure μ] : ↑(measureUnivNNReal μ) = μ univ
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measureUnivNNReal_pos`：measureUnivNNReal_pos [IsFiniteMeas
ure μ] (hμ : μ != 0) : 0 < measureUnivNNReal μ
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ≥0}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  by_cases hμ : μ = 0
  · simp [hμ, nnnorm_def]
  rw [← ENNReal.coe_le_coe, nnnorm_def, ENNReal.coe_toNNReal (eLpNorm_ne_top _)]
  refine (eLpNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
  rw [← coe_measureUnivNNReal μ, ← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne',
    ENNReal.coe_mul, mul_comm, ENNReal.smul_def, smul_eq_mul]
/-
**MeasureTheory.Lp.norm_le_of_ae_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp`。
形式化陈述：norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : Real} (hC : 0 
<= C) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : ‖f‖ <= measureUnivNNReal μ ^ p.toReal⁻¹
 * C
参数：hC : 0 <= C；hfC : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `MeasureTheory.Lp.nnnorm_le_of_ae_bound`：nnnorm_le_of_ae_bound [IsFiniteM
easure μ] {f : Lp E p μ} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : ‖f‖₊ 
<= measureUnivNNReal μ ^ p.t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_rpow`：coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) 
: Real) = (x : Real) ^ y
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
-/
theorem norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  lift C to ℝ≥0 using hC
  have := nnnorm_le_of_ae_bound hfC
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this
/-
**MeasureTheory.Lp.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`
。
形式化陈述：instAddCommGroup : AddCommGroup (Lp E p μ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (Lp E p μ) := inferInstance
/-
**MeasureTheory.Lp.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Lp`。
形式化陈述：instNormedAddCommGroup [hp : Fact (1 <= p)] : NormedAddCommGroup (Lp E p μ
)
参数：1 <= p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.norm_zero`：norm_zero : ‖(0 : Lp E p μ)‖ = 0
-/
instance instNormedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (Lp E p μ) :=
  fast_instance%
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Lp E p μ → ℝ)
        map_zero' := norm_zero
        neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
        add_le' := fun f g => by
          suffices ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ by
            -- Squeezed for performance reasons
            simpa only [ge_iff_le, enorm, ← ENNReal.coe_add, ENNReal.coe_le_coe] using! this
          simp only [Lp.enorm_def]
          exact (eLpNorm_congr_ae (AEEqFun.coeFn_add _ _)).trans_le
            (eLpNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hp.out)
        eq_zero_of_map_eq_zero' _ := (norm_eq_zero_iff <| zero_lt_one.trans_le hp.1).1 } with
    edist := edist
    edist_dist := Lp.edist_dist }

-- check no diamond is created
/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个示例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Fact (1 ≤ p)] : PseudoEMetricSpace.toEDist = (Lp.instEDist : EDist (Lp E p μ)) := by
  with_reducible_and_instances rfl
/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个示例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Fact (1 ≤ p)] : SeminormedAddGroup.toNNNorm = (Lp.instNNNorm : NNNorm (Lp E p μ)) := by
  with_reducible_and_instances rfl

section IsBoundedSMul

variable [NormedRing 𝕜] [NormedRing 𝕜'] [Module 𝕜 E] [Module 𝕜' E]
variable [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜' E]

/-
**MeasureTheory.Lp.const_smul_mem_Lp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：const_smul_mem_Lp (c : 𝕜) (f : Lp E p μ) : c • (f : α ->ₘ[μ] E) in Lp E p 
μ
参数：c : 𝕜；f : Lp E p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top`：mem_Lp_iff_eLpNorm_lt_top {f
 : α ->ₘ[μ] E} : f in Lp E p μ ↔ eLpNorm f p μ < ∞
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_smul`：coeFn_smul (c : 𝕜) (f : α ->ₘ[μ] γ) : 
⇑(c • f) =ᵐ[μ] c • ⇑f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_const_smul_le`：eLpNorm_const_smul_le : eLpNorm (c 
• f) p μ <= ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
-/
theorem const_smul_mem_Lp (c : 𝕜) (f : Lp E p μ) : c • (f : α →ₘ[μ] E) ∈ Lp E p μ := by
  rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_congr_ae (AEEqFun.coeFn_smul _ _)]
  exact eLpNorm_const_smul_le.trans_lt <| (by finiteness)

variable (𝕜 E p μ)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
/-
**MeasureTheory.Lp.LpSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：LpSubmodule : Submodule 𝕜 (α ->ₘ[μ] E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is
 `Lp E p μ`,
with extra structure.
-/
def LpSubmodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }

variable {𝕜 E p μ}
/-
**MeasureTheory.Lp.coe_LpSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coe_LpSubmodule : (LpSubmodule 𝕜 E p μ).toAddSubgroup = Lp E p μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem coe_LpSubmodule : (LpSubmodule 𝕜 E p μ).toAddSubgroup = Lp E p μ :=
  rfl
/-
**MeasureTheory.Lp.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instModule : Module 𝕜 (Lp E p μ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module 𝕜 (Lp E p μ) :=
  fast_instance% (LpSubmodule 𝕜 E p μ).module
/-
**MeasureTheory.Lp.coeFn_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • ⇑f
参数：c : 𝕜；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_smul`：coeFn_smul (c : 𝕜) (f : α ->ₘ[μ] γ) : 
⇑(c • f) =ᵐ[μ] c • ⇑f
-/
theorem coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  AEEqFun.coeFn_smul _ _
/-
**MeasureTheory.Lp.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
Lp`。
形式化陈述：instIsCentralScalar [Module 𝕜ᵐᵒᵖ E] [IsBoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScala
r 𝕜 E] : IsCentralScalar 𝕜 (Lp E p μ) where op_smul_eq_smul k f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
instance instIsCentralScalar [Module 𝕜ᵐᵒᵖ E] [IsBoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E] :
    IsCentralScalar 𝕜 (Lp E p μ) where
  op_smul_eq_smul k f := Subtype.ext <| op_smul_eq_smul k (f : α →ₘ[μ] E)
/-
**MeasureTheory.Lp.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：instSMulCommClass [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (Lp E p μ) w
here smul_comm k k' f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (Lp E p μ) where
  smul_comm k k' f := Subtype.ext <| smul_comm k k' (f : α →ₘ[μ] E)
/-
**MeasureTheory.Lp.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' 
(Lp E p μ) where smul_assoc k k' f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' (Lp E p μ) where
  smul_assoc k k' f := Subtype.ext <| smul_assoc k k' (f : α →ₘ[μ] E)
/-
**MeasureTheory.Lp.instIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：instIsBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp E p μ)
参数：1 <= p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_enorm_smul_le`：IsBoundedSMul.of_enorm_smul_le (h : fora
ll (r : α) (x : β), ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ) : IsBoundedSMul α β
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Lp.enorm_def`：enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f 
p μ
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `MeasureTheory.eLpNorm_const_smul_le`：eLpNorm_const_smul_le : eLpNorm (c 
• f) p μ <= ‖c‖ₑ * eLpNorm f p μ
-/
instance instIsBoundedSMul [Fact (1 ≤ p)] : IsBoundedSMul 𝕜 (Lp E p μ) :=
  IsBoundedSMul.of_enorm_smul_le fun r f => by
    simpa only [eLpNorm_congr_ae (coeFn_smul _ _), enorm_def]
      using eLpNorm_const_smul_le (c := r) (f := f) (p := p)

end IsBoundedSMul

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/-
**MeasureTheory.Lp.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instNormedSpace [Fact (1 <= p)] : NormedSpace 𝕜 (Lp E p μ) where norm_smul
_le _ _
参数：1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedSpace [Fact (1 ≤ p)] : NormedSpace 𝕜 (Lp E p μ) where
  norm_smul_le _ _ := norm_smul_le _ _

end NormedSpace

end Lp

namespace MemLp

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-
**MeasureTheory.MemLp.toLp_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
emLp`。
形式化陈述：toLp_const_smul {f : α -> E} (c : 𝕜) (hf : MemLp f p μ) : (hf.const_smul c
).toLp (c • f) = c • hf.toLp f
参数：c : 𝕜；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
-/
theorem toLp_const_smul {f : α → E} (c : 𝕜) (hf : MemLp f p μ) :
    (hf.const_smul c).toLp (c • f) = c • hf.toLp f :=
  rfl

end MemLp

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/-
**MeasureTheory.MemLp.enorm_rpow_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
mLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {ε : Type u_6}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENor
m ε] {f : α → ε},   MeasureTheory.MemLp f p μ → ∀ (q : ENNReal), MeasureTheory.M
emLp (fun x => ‖f x‖ₑ ^ q.toReal) (p / q) μ
参数：q : ENNReal；fun x => ‖f x‖ₑ ^ q.toReal；p / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `ENNReal.div_zero`：div_zero (h : a != 0) : a / 0 = ∞
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.memLp_top_const_enorm`：memLp_top_const_enorm {c : ε'} (hc 
: ‖c‖ₑ != ⊤) : MemLp (fun _ : α => c) ∞ μ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.eLpNorm_enorm_rpow`：eLpNorm_enorm_rpow (f : α -> ε) (hq_po
s : 0 < q) : eLpNorm (‖f ·‖ₑ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 33 条，此处仅展示前 30 条）
-/
theorem MemLp.enorm_rpow_div {f : α → ε} (hf : MemLp f p μ) (q : ℝ≥0∞) :
    MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ := by
  refine ⟨(hf.1.enorm.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    simpa only [ENNReal.rpow_zero, eLpNorm_exponent_top] using (memLp_top_const_enorm (by simp)).2
  rw [eLpNorm_enorm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.ne
/-
**MeasureTheory.MemLp.norm_rpow_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mem
Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {f : α → E},   Measure
Theory.MemLp f p μ → ∀ (q : ENNReal), MeasureTheory.MemLp (fun x => ‖f x‖ ^ q.to
Real) (p / q) μ
参数：q : ENNReal；fun x => ‖f x‖ ^ q.toReal；p / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `ENNReal.div_zero`：div_zero (h : a != 0) : a / 0 = ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.memLp_top_const`：memLp_top_const (c : E) : MemLp (fun _ : 
α => c) ∞ μ
· 使用定理 `MeasureTheory.eLpNorm_norm_rpow`：eLpNorm_norm_rpow (f : α -> F) (hq_pos 
: 0 < q) : eLpNorm (fun x => ‖f x‖ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ
 ^ q
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 31 条，此处仅展示前 30 条）
-/
theorem MemLp.norm_rpow_div {f : α → E} (hf : MemLp f p μ) (q : ℝ≥0∞) :
    MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ := by
  refine ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero, Real.rpow_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exact (memLp_top_const (1 : ℝ)).2
  rw [eLpNorm_norm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.ne
/-
**MeasureTheory.memLp_enorm_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_enorm_rpow_iff {q : Real>=0∞} {f : α -> ε} (hf : AEStronglyMeasurabl
e f μ) (q_zero : q != 0) (q_top : q != ∞) : MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ 
↔ MemLp f p μ
参数：hf : AEStronglyMeasurable f μ；q_zero : q != 0；q_top : q != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_enorm_iff`：memLp_enorm_iff {f : α -> ε} (hf : AEStro
nglyMeasurable f μ) : MemLp (‖f ·‖ₑ) p μ ↔ MemLp f p μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CommGroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u_2} [self : CommGroupWit
hZero G₀] (a : G₀), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_ne_zero`：toReal_ne_zero : a.toReal != 0 ↔ a != 0 ∧ a != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.MemLp.enorm_rpow_div`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_6}   [inst : Topolo
gicalSpace ε] [inst_1 : …
-/
theorem memLp_enorm_rpow_iff {q : ℝ≥0∞} {f : α → ε} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.enorm_rpow_div q⟩
  apply (memLp_enorm_iff hf).1
  convert! h.enorm_rpow_div q⁻¹ using 1
  · ext x
    have : q.toReal * q.toReal⁻¹ = 1 :=
      CommGroupWithZero.mul_inv_cancel q.toReal <| ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩
    simp [← ENNReal.rpow_mul, this, ENNReal.rpow_one]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]
/-
**MeasureTheory.memLp_norm_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_norm_rpow_iff {q : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable
 f μ) (q_zero : q != 0) (q_top : q != ∞) : MemLp (fun x : α => ‖f x‖ ^ q.toReal)
 (p / q) μ ↔ MemLp f p μ
参数：hf : AEStronglyMeasurable f μ；q_zero : q != 0；q_top : q != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_norm_iff`：memLp_norm_iff {f : α -> E} (hf : AEStrong
lyMeasurable f μ) : MemLp (fun x => ‖f x‖) p μ ↔ MemLp f p μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.MemLp.norm_rpow_div`：∀ {α : Type u_1} {E : Type u_4} {m : 
MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedA
ddCommGroup E] {f : α →…
-/
theorem memLp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.norm_rpow_div q⟩
  apply (memLp_norm_iff hf).1
  convert! h.norm_rpow_div q⁻¹ using 1
  · ext x
    rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ENNReal.toReal_inv, mul_inv_cancel₀, abs_of_nonneg (norm_nonneg _), Real.rpow_one]
    simp [ENNReal.toReal_eq_zero_iff, q_zero, q_top]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]
/-
**MeasureTheory.MemLp.enorm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {ε : Type u_6}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENor
m ε] {f : α → ε},   MeasureTheory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → MeasureTheory.Me
mLp (fun x => ‖f x‖ₑ ^ p.toReal) 1 μ
参数：fun x => ‖f x‖ₑ ^ p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `MeasureTheory.MemLp.enorm_rpow_div`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_6}   [inst : Topolo
gicalSpace ε] [inst_1 : …
-/
theorem MemLp.enorm_rpow {f : α → ε} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun x : α => ‖f x‖ₑ ^ p.toReal) 1 μ := by
  convert! hf.enorm_rpow_div p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]
/-
**MeasureTheory.MemLp.norm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {f : α → E},   Measure
Theory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → MeasureTheory.MemLp (fun x => ‖f x‖ ^ p.toR
eal) 1 μ
参数：fun x => ‖f x‖ ^ p.toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `MeasureTheory.MemLp.norm_rpow_div`：∀ {α : Type u_1} {E : Type u_4} {m : 
MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedA
ddCommGroup E] {f : α →…
-/
theorem MemLp.norm_rpow {f : α → E} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun x : α => ‖f x‖ ^ p.toReal) 1 μ := by
  convert! hf.norm_rpow_div p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_mem_Lp** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.AEEqFun`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {β : Type u_7} [inst_1
 : MeasurableSpace β] {μb : MeasureTheory.Measure β}   {g : β →ₘ[μb] E},   g ∈ M
easureTheory.Lp E p μb →     ∀ {f : α → β} (hf : MeasureTheory.MeasurePreserving
 f μ μb), g.compMeasurePreserving f hf ∈ MeasureTheory.Lp E p μ
参数：hf : MeasureTheory.MeasurePreserving f μ μb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top`：mem_Lp_iff_eLpNorm_lt_top {f
 : α ->ₘ[μ] E} : f in Lp E p μ ↔ eLpNorm f p μ < ∞
· 使用定理 `MeasureTheory.AEEqFun.eLpNorm_compMeasurePreserving`：∀ {α : Type u_1} {E
 : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α
}   [inst : NormedAddCommGroup E] {β : Ty…
-/
theorem AEEqFun.compMeasurePreserving_mem_Lp {β : Type*} [MeasurableSpace β]
    {μb : MeasureTheory.Measure β} {g : β →ₘ[μb] E} (hg : g ∈ Lp E p μb) {f : α → β}
    (hf : MeasurePreserving f μ μb) :
    g.compMeasurePreserving f hf ∈ Lp E p μ := by
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top] at hg ⊢
  rwa [eLpNorm_compMeasurePreserving]

namespace Lp

/-! ### Composition with a measure-preserving function -/

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α → β}

/-- Composition of an `L^p` function with a measure-preserving function is an `L^p` function. -/
/-
**MeasureTheory.Lp.compMeasurePreserving** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：compMeasurePreserving (f : α -> β) (hf : MeasurePreserving f μ μb) : Lp E 
p μb ->+ Lp E p μ where toFun g
参数：f : α -> β；hf : MeasurePreserving f μ μb。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of an `L^p` function with a measure-preserving function is an `L^p` 
function.
-/
def compMeasurePreserving (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →+ Lp E p μ where
  toFun g := ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl

@[simp]
/-
**MeasureTheory.Lp.compMeasurePreserving_val** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Lp`。
形式化陈述：compMeasurePreserving_val (g : Lp E p μb) (hf : MeasurePreserving f μ μb) 
: (compMeasurePreserving f hf g).1 = g.1.compMeasurePreserving f hf
参数：g : Lp E p μb；hf : MeasurePreserving f μ μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem compMeasurePreserving_val (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    (compMeasurePreserving f hf g).1 = g.1.compMeasurePreserving f hf :=
  rfl
/-
**MeasureTheory.Lp.coeFn_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Lp`。
形式化陈述：coeFn_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb
) : compMeasurePreserving f hf g =ᵐ[μ] g ∘ f
参数：g : Lp E p μb；hf : MeasurePreserving f μ μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compMeasurePreserving`：coeFn_compMeasurePres
erving (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) : g.compMeasurePreserving
 f hf =ᵐ[μ] g ∘ f
-/
theorem coeFn_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf g =ᵐ[μ] g ∘ f :=
  g.1.coeFn_compMeasurePreserving hf

@[simp]
/-
**MeasureTheory.Lp.norm_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Lp`。
形式化陈述：norm_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb)
 : ‖compMeasurePreserving f hf g‖ = ‖g‖
参数：g : Lp E p μb；hf : MeasurePreserving f μ μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.eLpNorm_compMeasurePreserving`：∀ {α : Type u_1} {E
 : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α
}   [inst : NormedAddCommGroup E] {β : Ty…
-/
theorem norm_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    ‖compMeasurePreserving f hf g‖ = ‖g‖ :=
  congr_arg ENNReal.toReal <| g.1.eLpNorm_compMeasurePreserving hf
/-
**MeasureTheory.Lp.isometry_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
形式化陈述：isometry_compMeasurePreserving [Fact (1 <= p)] (hf : MeasurePreserving f μ
 μb) : Isometry (compMeasurePreserving f hf : Lp E p μb -> Lp E p μ)
参数：1 <= p；hf : MeasurePreserving f μ μb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MeasureTheory.Lp.norm_compMeasurePreserving`：norm_compMeasurePreserving 
(g : Lp E p μb) (hf : MeasurePreserving f μ μb) : ‖compMeasurePreserving f hf g‖
 = ‖g‖
-/
theorem isometry_compMeasurePreserving [Fact (1 ≤ p)] (hf : MeasurePreserving f μ μb) :
    Isometry (compMeasurePreserving f hf : Lp E p μb → Lp E p μ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_compMeasurePreserving · hf)
/-
**MeasureTheory.Lp.toLp_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Lp`。
形式化陈述：toLp_compMeasurePreserving {g : β -> E} (hg : MemLp g p μb) (hf : MeasureP
reserving f μ μb) : compMeasurePreserving f hf (hg.toLp g) = (hg.comp_measurePre
serving hf).toLp _
参数：hg : MemLp g p μb；hf : MeasurePreserving f μ μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toLp_compMeasurePreserving {g : β → E} (hg : MemLp g p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf (hg.toLp g) = (hg.comp_measurePreserving hf).toLp _ := rfl

@[simp]
/-
**MeasureTheory.Lp.compMeasurePreserving_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：compMeasurePreserving_id : compMeasurePreserving (E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.compMeasurePreserving_id`：compMeasurePreserving_id
 (g : β ->ₘ[ν] γ) : compMeasurePreserving g id (.id ν) = g
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
-/
theorem compMeasurePreserving_id :
    compMeasurePreserving (E := E) (p := p) id (.id μb) = AddMonoidHom.id _ := by
  ext
  simp
/-
**MeasureTheory.Lp.compMeasurePreserving_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
形式化陈述：compMeasurePreserving_id_apply (g : Lp E p μb) : compMeasurePreserving id 
(MeasurePreserving.id μb) g = g
参数：g : Lp E p μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.compMeasurePreserving_id`：compMeasurePreserving_id : co
mpMeasurePreserving (E
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compMeasurePreserving_id_apply (g : Lp E p μb) :
    compMeasurePreserving id (MeasurePreserving.id μb) g = g := by simp
/-
**MeasureTheory.Lp.compMeasurePreserving_comp** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Lp`。
形式化陈述：compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {μc : Meas
ure γ} {f : β -> γ} (hf : MeasurePreserving f μb μc) {f' : α -> β} (hf' : Measur
ePreserving f' μ μb) : compMeasurePreserving (E
参数：hf : MeasurePreserving f μb μc；hf' : MeasurePreserving f' μ μb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.compMeasurePreserving_comp`：compMeasurePreserving_
comp {γ : Type*} {mγ : MeasurableSpace γ} {ξ : Measure γ} (g : γ ->ₘ[ξ] δ) {f : 
β -> γ} (hf : MeasurePreserving f ν ξ)…
-/
theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
    {f : β → γ} (hf : MeasurePreserving f μb μc) {f' : α → β} (hf' : MeasurePreserving f' μ μb) :
    compMeasurePreserving (E := E) (p := p) (f ∘ f') (hf.comp hf') =
    (compMeasurePreserving f' hf').comp (compMeasurePreserving f hf) := by
  ext g
  simp [AEEqFun.compMeasurePreserving_comp _ hf hf']
/-
**MeasureTheory.Lp.compMeasurePreserving_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Lp`。
形式化陈述：compMeasurePreserving_comp_apply {γ : Type*} {mγ : MeasurableSpace γ} {μc 
: Measure γ} (g : Lp E p μc) {f : β -> γ} (hf : MeasurePreserving f μb μc) {f' :
 α -> β} (hf' : MeasurePreserving f' μ μb) : (compMeasurePreserving (f ∘ f') (hf
.comp hf')) g = (compMeasurePreserving f' hf') ((compMeasurePreserving f hf) g)
参数：g : Lp E p μc；hf : MeasurePreserving f μb μc；hf' : MeasurePreserving f' μ μb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.compMeasurePreserving_comp`：compMeasurePreserving_comp 
{γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ} {f : β -> γ} (hf : Measure
Preserving f μb μc) {f' : α -> β}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compMeasurePreserving_comp_apply {γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ}
    (g : Lp E p μc) {f : β → γ} (hf : MeasurePreserving f μb μc) {f' : α → β}
    (hf' : MeasurePreserving f' μ μb) :
    (compMeasurePreserving (f ∘ f') (hf.comp hf')) g =
    (compMeasurePreserving f' hf') ((compMeasurePreserving f hf) g) := by
  simp [compMeasurePreserving_comp hf hf']
/-
**MeasureTheory.Lp.compMeasurePreserving_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：compMeasurePreserving_iterate {f : α -> α} (hf : MeasurePreserving f μ μ) 
(n : Nat) : (compMeasurePreserving (E
参数：hf : MeasurePreserving f μ μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MeasurePreserving.iterate`：∀ {α : Type u_1} [inst : Measur
ableSpace α] {μ : MeasureTheory.Measure α} {f : α → α},   MeasureTheory.MeasureP
reserving f μ μ → ∀ (n : ℕ), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Lp.compMeasurePreserving_id`：compMeasurePreserving_id : co
mpMeasurePreserving (E
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `MeasureTheory.Lp.compMeasurePreserving_comp`：compMeasurePreserving_comp 
{γ : Type*} {mγ : MeasurableSpace γ} {μc : Measure γ} {f : β -> γ} (hf : Measure
Preserving f μb μc) {f' : α -> β}…
-/
theorem compMeasurePreserving_iterate {f : α → α} (hf : MeasurePreserving f μ μ) (n : ℕ) :
    (compMeasurePreserving (E := E) (p := p) f hf)^[n] =
    compMeasurePreserving f^[n] (MeasurePreserving.iterate hf n) := by
  funext
  induction n with
  | zero => simp
  | succ n h =>
    nth_rewrite 1 [add_comm n 1]
    simp [Function.iterate_add, h, compMeasurePreserving_comp (hf.iterate n) hf]

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear map. -/
@[simps]
/-
**MeasureTheory.Lp.compMeasurePreserving** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：compMeasurePreserving (f : α -> β) (hf : MeasurePreserving f μ μb) : Lp E 
p μb ->+ Lp E p μ where toFun g
参数：f : α -> β；hf : MeasurePreserving f μ μb。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MeasureTheory.Lp.compMeasurePreserving` as a linear map.
-/
def compMeasurePreservingₗ (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗ[𝕜] Lp E p μ where
  __ := compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear isometry. -/
@[simps!]
/-
**MeasureTheory.Lp.compMeasurePreserving** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：compMeasurePreserving (f : α -> β) (hf : MeasurePreserving f μ μb) : Lp E 
p μb ->+ Lp E p μ where toFun g
参数：f : α -> β；hf : MeasurePreserving f μ μb。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MeasureTheory.Lp.compMeasurePreserving` as a linear isometry.
-/
def compMeasurePreservingₗᵢ [Fact (1 ≤ p)] (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗᵢ[𝕜] Lp E p μ where
  toLinearMap := compMeasurePreservingₗ 𝕜 f hf
  norm_map' := (norm_compMeasurePreserving · hf)

end Lp

end MeasureTheory

open MeasureTheory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/


section Composition

variable {g : E → F} {c : ℝ≥0}

/-
**LipschitzWith.comp_memLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.comp_memLp {α E F} {K} [MeasurableSpace α] {μ : Measure α} [
NormedAddCommGroup E] [NormedAddCommGroup F] {f : α -> E} {g : E -> F} (hg : Lip
schitzWith K g) (g0 : g 0 = 0) (hL : MemLp f p μ) : MemLp (g ∘ f) p μ
参数：hg : LipschitzWith K g；g0 : g 0 = 0；hL : MemLp f p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LipschitzWith.norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Semin
ormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : NNRe
al}, LipschitzW…
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem LipschitzWith.comp_memLp {α E F} {K} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (g0 : g 0 = 0) (hL : MemLp f p μ) : MemLp (g ∘ f) p μ :=
  have : ∀ x, ‖g (f x)‖ ≤ K * ‖f x‖ := fun x ↦ by
    -- TODO: add `LipschitzWith.nnnorm_sub_le` and `LipschitzWith.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f x) 0
  hL.of_le_mul (hg.continuous.comp_aestronglyMeasurable hL.1) (Eventually.of_forall this)
/-
**MeasureTheory.MemLp.of_comp_antilipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.MemLp.of_comp_antilipschitzWith {α E F} {K'} [MeasurableSpac
e α] {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α -> E} 
{g : E -> F} (hL : MemLp (g ∘ f) p μ) (hg : UniformContinuous g) (hg' : Antilips
chitzWith K' g) (g0 : g 0 = 0) : MemLp f p μ
参数：hL : MemLp (g ∘ f) p μ；hg : UniformContinuous g；hg' : AntilipschitzWith K' g；
g0 : g 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `AntilipschitzWith.le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst : P
seudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   A
ntilipschitzWith K …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsEmbedding.aestronglyMeasurable_comp_iff`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpac
e γ]   {m₀ : MeasurableSpace α} {μ : Mea…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `AntilipschitzWith.isUniformEmbedding`：isUniformEmbedding {α β : Type*} [
EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : Antilips
chitzWith K f) (hfc : Unif…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem MeasureTheory.MemLp.of_comp_antilipschitzWith {α E F} {K'} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F}
    (hL : MemLp (g ∘ f) p μ) (hg : UniformContinuous g) (hg' : AntilipschitzWith K' g)
    (g0 : g 0 = 0) : MemLp f p μ := by
  have A : ∀ x, ‖f x‖ ≤ K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `AntilipschitzWith.le_mul_nnnorm_sub` and `AntilipschitzWith.le_mul_norm`
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    apply hg'.le_mul_dist
  have B : AEStronglyMeasurable f μ :=
    (hg'.isUniformEmbedding hg).isEmbedding.aestronglyMeasurable_comp_iff.1 hL.1
  exact hL.of_le_mul B (Filter.Eventually.of_forall A)
/-
**MeasureTheory.MemLp.continuousLinearMap_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.MemLp.continuousLinearMap_comp [NontriviallyNormedField 𝕜] [
NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {f : α -> E} (h_Lp : MemLp f p μ) (L : E ->L[
𝕜] F) : MemLp (fun x => L (f x)) p μ
参数：h_Lp : MemLp f p μ；L : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.comp_memLp`：LipschitzWith.comp_memLp {α E F} {K} [Measurab
leSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α 
-> E} {g : E -…
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MeasureTheory.MemLp.continuousLinearMap_comp [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {f : α → E}
    (h_Lp : MemLp f p μ) (L : E →L[𝕜] F) :
    MemLp (fun x ↦ L (f x)) p μ :=
  LipschitzWith.comp_memLp L.lipschitz (by simp) h_Lp

namespace LipschitzWith

/-
**LipschitzWith.memLp_comp_iff_of_antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Lipsc
hitzWith`。
形式化陈述：memLp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Me
asure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α -> E} {g : E -> F}
 (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : MemLp 
(g ∘ f) p μ ↔ MemLp f p μ
参数：hg : LipschitzWith K g；hg' : AntilipschitzWith K' g；g0 : g 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.of_comp_antilipschitzWith`：MeasureTheory.MemLp.of_co
mp_antilipschitzWith {α E F} {K'} [MeasurableSpace α] {μ : Measure α} [NormedAdd
CommGroup E] [NormedAddCommGroup F]…
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `LipschitzWith.comp_memLp`：LipschitzWith.comp_memLp {α E F} {K} [Measurab
leSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α 
-> E} {g : E -…
-/
theorem memLp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : MemLp (g ∘ f) p μ ↔ MemLp f p μ :=
  ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memLp g0 h⟩

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
/-
**LipschitzWith.compLp** 是 Mathlib 中的一个定义，位于命名空间 `LipschitzWith`。
形式化陈述：compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ
参数：hg : LipschitzWith c g；g0 : g 0 = 0；f : Lp E p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g 
∘ f` is well
defined as an element of `Lp`.
-/
def compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
  ⟨AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E), by
    rw [Lp.mem_Lp_iff_memLp]
    exact (hg.comp_memLp g0 (Lp.memLp f)).ae_eq (AEEqFun.coeFn_comp _ hg.continuous _).symm⟩
/-
**LipschitzWith.coeFn_compLp** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：coeFn_compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : hg.c
ompLp g0 f =ᵐ[μ] g ∘ f
参数：hg : LipschitzWith c g；g0 : g 0 = 0；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
-/
theorem coeFn_compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    hg.compLp g0 f =ᵐ[μ] g ∘ f :=
  AEEqFun.coeFn_comp _ hg.continuous _

@[simp]
/-
**LipschitzWith.compLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：compLp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.compLp g0 (0 : Lp
 E p μ) = 0
参数：hg : LipschitzWith c g；g0 : g 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.eq_zero_iff_ae_eq_zero`：eq_zero_iff_ae_eq_zero {f : Lp 
E p μ} : f = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `LipschitzWith.coeFn_compLp`：coeFn_compLp (hg : LipschitzWith c g) (g0 : 
g 0 = 0) (f : Lp E p μ) : hg.compLp g0 f =ᵐ[μ] g ∘ f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compLp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.compLp g0 (0 : Lp E p μ) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  apply (coeFn_compLp _ _ _).trans
  filter_upwards [Lp.coeFn_zero E p μ] with _ ha
  simp only [ha, g0, Function.comp_apply, Pi.zero_apply]
/-
**LipschitzWith.norm_compLp_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：norm_compLp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p 
μ) : ‖hg.compLp g0 f - hg.compLp g0 f'‖ <= c * ‖f - f'‖
参数：hg : LipschitzWith c g；g0 : g 0 = 0；f f' : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul`：norm_le_mul_norm_of_ae_l
e_mul {c : Real} {f : Lp E p μ} {g : Lp F p μ} (h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖
g x‖) : ‖f‖ <= c * ‖g‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `LipschitzWith.coeFn_compLp`：coeFn_compLp (hg : LipschitzWith c g) (g0 : 
g 0 = 0) (f : Lp E p μ) : hg.compLp g0 f =ᵐ[μ] g ∘ f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
-/
theorem norm_compLp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
    ‖hg.compLp g0 f - hg.compLp g0 f'‖ ≤ c * ‖f - f'‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg.coeFn_compLp g0 f, hg.coeFn_compLp g0 f',
    Lp.coeFn_sub (hg.compLp g0 f) (hg.compLp g0 f'), Lp.coeFn_sub f f'] with a ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, ← dist_eq_norm, Pi.sub_apply, Function.comp_apply]
  exact hg.dist_le_mul (f a) (f' a)
/-
**LipschitzWith.norm_compLp_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：norm_compLp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : ‖h
g.compLp g0 f‖ <= c * ‖f‖
参数：hg : LipschitzWith c g；g0 : g 0 = 0；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LipschitzWith.compLp_zero`：compLp_zero (hg : LipschitzWith c g) (g0 : g 
0 = 0) : hg.compLp g0 (0 : Lp E p μ) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LipschitzWith.norm_compLp_sub_le`：norm_compLp_sub_le (hg : LipschitzWith
 c g) (g0 : g 0 = 0) (f f' : Lp E p μ) : ‖hg.compLp g0 f - hg.compLp g0 f'‖ <= c
 * ‖f - f'‖
-/
theorem norm_compLp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    ‖hg.compLp g0 f‖ ≤ c * ‖f‖ := by
  -- squeezed for performance reasons
  simpa only [compLp_zero, sub_zero] using hg.norm_compLp_sub_le g0 f 0
/-
**LipschitzWith.lipschitzWith_compLp** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：lipschitzWith_compLp [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 
0) : LipschitzWith c (hg.compLp g0 : Lp E p μ -> Lp F p μ)
参数：1 <= p；hg : LipschitzWith c g；g0 : g 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
-/
theorem lipschitzWith_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    LipschitzWith c (hg.compLp g0 : Lp E p μ → Lp F p μ) :=
  -- squeezed for performance reasons
  LipschitzWith.of_dist_le_mul fun f g => by simp only [dist_eq_norm, norm_compLp_sub_le]
/-
**LipschitzWith.continuous_compLp** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：continuous_compLp [Fact (1 <= p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) 
: Continuous (hg.compLp g0 : Lp E p μ -> Lp F p μ)
参数：1 <= p；hg : LipschitzWith c g；g0 : g 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LipschitzWith.lipschitzWith_compLp`：lipschitzWith_compLp [Fact (1 <= p)]
 (hg : LipschitzWith c g) (g0 : g 0 = 0) : LipschitzWith c (hg.compLp g0 : Lp E 
p μ -> Lp F p μ)
-/
theorem continuous_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    Continuous (hg.compLp g0 : Lp E p μ → Lp F p μ) :=
  (lipschitzWith_compLp hg g0).continuous

end LipschitzWith

namespace ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜' F]
variable {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

/-- Composing `f : Lp` with `L : E →L[𝕜] F`. -/
/-
**ContinuousLinearMap.compLp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compLp (L : E ->SL[σ] F) (f : Lp E p μ) : Lp F p μ
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing `f : Lp` with `L : E →L[𝕜] F`.
-/
def compLp (L : E →SL[σ] F) (f : Lp E p μ) : Lp F p μ :=
  L.lipschitz.compLp (map_zero L) f
/-
**ContinuousLinearMap.coeFn_compLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：coeFn_compLp (L : E ->SL[σ] F) (f : Lp E p μ) : forallᵐ a ∂μ, (L.compLp f)
 a = L (f a)
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LipschitzWith.coeFn_compLp`：coeFn_compLp (hg : LipschitzWith c g) (g0 : 
g 0 = 0) (f : Lp E p μ) : hg.compLp g0 f =ᵐ[μ] g ∘ f
-/
theorem coeFn_compLp (L : E →SL[σ] F) (f : Lp E p μ) : ∀ᵐ a ∂μ, (L.compLp f) a = L (f a) :=
  LipschitzWith.coeFn_compLp _ _ _
/-
**ContinuousLinearMap.coeFn_compLp'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：coeFn_compLp' (L : E ->SL[σ] F) (f : Lp E p μ) : L.compLp f =ᵐ[μ] fun a =>
 L (f a)
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
-/
theorem coeFn_compLp' (L : E →SL[σ] F) (f : Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f
/-
**ContinuousLinearMap.comp_memLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：comp_memLp (L : E ->SL[σ] F) (f : Lp E p μ) : MemLp (L ∘ f) p μ
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `ContinuousLinearMap.coeFn_compLp'`：coeFn_compLp' (L : E ->SL[σ] F) (f : 
Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a)
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem comp_memLp (L : E →SL[σ] F) (f : Lp E p μ) : MemLp (L ∘ f) p μ :=
  (Lp.memLp (L.compLp f)).ae_eq (L.coeFn_compLp' f)
/-
**ContinuousLinearMap.comp_memLp'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：comp_memLp' (L : E ->SL[σ] F) {f : α -> E} (hf : MemLp f p μ) : MemLp (L ∘
 f) p μ
参数：L : E ->SL[σ] F；hf : MemLp f p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `ContinuousLinearMap.comp_memLp`：comp_memLp (L : E ->SL[σ] F) (f : Lp E p
 μ) : MemLp (L ∘ f) p μ
-/
theorem comp_memLp' (L : E →SL[σ] F) {f : α → E} (hf : MemLp f p μ) : MemLp (L ∘ f) p μ :=
  (L.comp_memLp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)

section RCLike

variable {K : Type*} [RCLike K]

/-
**ContinuousLinearMap._root_.MeasureTheory.MemLp.ofReal** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.MemLp.ofReal {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => (f x : K)) p μ :=
  (@RCLike.ofRealCLM K _).comp_memLp' hf
/-
**ContinuousLinearMap._root_.MeasureTheory.memLp_re_im_iff** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.memLp_re_im_iff {f : α → K} :
    MemLp (fun x ↦ RCLike.re (f x)) p μ ∧ MemLp (fun x ↦ RCLike.im (f x)) p μ ↔
      MemLp f p μ := by
  refine ⟨?_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert! MeasureTheory.MemLp.add (ε := K) hre.ofReal (him.ofReal.const_mul RCLike.I)
  ext1 x
  rw [Pi.add_apply, mul_comm, RCLike.re_add_im]

end RCLike

/-
**ContinuousLinearMap.add_compLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：add_compLp (L L' : E ->SL[σ] F) (f : Lp E p μ) : (L + L').compLp f = L.com
pLp f + L'.compLp f
参数：L L' : E ->SL[σ] F；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `ContinuousLinearMap.coeFn_compLp'`：coeFn_compLp' (L : E ->SL[σ] F) (f : 
Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a)
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
-/
theorem add_compLp (L L' : E →SL[σ] F) (f : Lp E p μ) :
    (L + L').compLp f = L.compLp f + L'.compLp f := by
  ext1
  grw [Lp.coeFn_add, coeFn_compLp', coeFn_compLp', coeFn_compLp']
  rfl
/-
**ContinuousLinearMap.smul_compLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：smul_compLp {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F] [S
MulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E ->SL[σ] F) (f : Lp E p μ) : (c • L).comp
Lp f = c • L.compLp f
参数：c : 𝕜''；L : E ->SL[σ] F；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `ContinuousLinearMap.coeFn_compLp'`：coeFn_compLp' (L : E ->SL[σ] F) (f : 
Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a)
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
-/
theorem smul_compLp {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
    [SMulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E →SL[σ] F) (f : Lp E p μ) :
    (c • L).compLp f = c • L.compLp f := by
  ext1
  grw [Lp.coeFn_smul, coeFn_compLp', coeFn_compLp']
  rfl
/-
**ContinuousLinearMap.norm_compLp_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：norm_compLp_le (L : E ->SL[σ] F) (f : Lp E p μ) : ‖L.compLp f‖ <= ‖L‖ * ‖f
‖
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LipschitzWith.norm_compLp_le`：norm_compLp_le (hg : LipschitzWith c g) (g
0 : g 0 = 0) (f : Lp E p μ) : ‖hg.compLp g0 f‖ <= c * ‖f‖
-/
theorem norm_compLp_le (L : E →SL[σ] F) (f : Lp E p μ) : ‖L.compLp f‖ ≤ ‖L‖ * ‖f‖ :=
  LipschitzWith.norm_compLp_le _ _ _

variable (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
/-
**ContinuousLinearMap.compLp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compLp (L : E ->SL[σ] F) (f : Lp E p μ) : Lp F p μ
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E
 p μ`.
-/
@[simps] def compLpₗ (L : E →SL[σ] F) : Lp E p μ →ₛₗ[σ] Lp F p μ where
  toFun f := L.compLp f
  map_add' f g := by
    ext1
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' c f := by
    ext1
    filter_upwards [Lp.coeFn_smul c f, coeFn_compLp L (c • f), Lp.coeFn_smul (σ c) (L.compLp f),
      coeFn_compLp L f] with _ ha1 ha2 ha3 ha4
    simp only [ha1, ha2, ha3, ha4, Pi.smul_apply, map_smulₛₗ]

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `LinearMap.compLeft` for functions,
* `ContinuousLinearMap.compLeftContinuous` for continuous functions,
* `ContinuousLinearMap.compLeftContinuousBounded` for bounded continuous functions,
* `ContinuousLinearMap.compLeftContinuousCompact` for continuous functions on compact spaces.
-/
/-
**ContinuousLinearMap.compLpL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compLpL [Fact (1 <= p)] (L : E ->SL[σ] F) : Lp E p μ ->SL[σ] Lp F p μ
参数：1 <= p；L : E ->SL[σ] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_compLp_le`：norm_compLp_le (L : E ->SL[σ] F) (f 
: Lp E p μ) : ‖L.compLp f‖ <= ‖L‖ * ‖f‖

--- 原说明 ---
Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear m
ap on
`Lp E p μ`. See also the similar
* `LinearMap.compLeft` for functions,
* `ContinuousLinearMap.compLeftContinuous` for continuous functions,
* `ContinuousLinearMap.compLeftContinuousBounded` for bounded continuous functio
ns,
* `ContinuousLinearMap.compLeftContinuousCompact` for continuous functions on co
mpact spaces.
-/
def compLpL [Fact (1 ≤ p)] (L : E →SL[σ] F) : Lp E p μ →SL[σ] Lp F p μ :=
  LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le

variable {μ p}
/-
**ContinuousLinearMap.coeFn_compLpL** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：coeFn_compLpL [Fact (1 <= p)] (L : E ->SL[σ] F) (f : Lp E p μ) : L.compLpL
 p μ f =ᵐ[μ] fun a => L (f a)
参数：1 <= p；L : E ->SL[σ] F；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
-/
theorem coeFn_compLpL [Fact (1 ≤ p)] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f
/-
**ContinuousLinearMap.add_compLpL** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：add_compLpL [Fact (1 <= p)] (L L' : E ->SL[σ] F) : (L + L').compLpL p μ = 
L.compLpL p μ + L'.compLpL p μ
参数：1 <= p；L L' : E ->SL[σ] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.add_compLp`：add_compLp (L L' : E ->SL[σ] F) (f : Lp 
E p μ) : (L + L').compLp f = L.compLp f + L'.compLp f
-/
theorem add_compLpL [Fact (1 ≤ p)] (L L' : E →SL[σ] F) :
    (L + L').compLpL p μ = L.compLpL p μ + L'.compLpL p μ := by ext1 f; exact add_compLp L L' f
/-
**ContinuousLinearMap.smul_compLpL** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：smul_compLpL [Fact (1 <= p)] {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoun
dedSMul 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E ->SL[σ] F) : (c • L).co
mpLpL p μ = c • L.compLpL p μ
参数：1 <= p；c : 𝕜''；L : E ->SL[σ] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.smul_compLp`：smul_compLp {𝕜''} [NormedRing 𝕜''] [Mod
ule 𝕜'' F] [IsBoundedSMul 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E ->SL[
σ] F) (f : Lp E p μ) …
-/
theorem smul_compLpL [Fact (1 ≤ p)] {𝕜''} [NormedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F]
    [SMulCommClass 𝕜' 𝕜'' F] (c : 𝕜'') (L : E →SL[σ] F) :
    (c • L).compLpL p μ = c • L.compLpL p μ := by
  ext1 f; exact smul_compLp c L f
/-
**ContinuousLinearMap.norm_compLpL_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：norm_compLpL_le [Fact (1 <= p)] (L : E ->SL[σ] F) : ‖L.compLpL p μ‖ <= ‖L‖
参数：1 <= p；L : E ->SL[σ] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.norm_compLp_le`：norm_compLp_le (L : E ->SL[σ] F) (f 
: Lp E p μ) : ‖L.compLp f‖ <= ‖L‖ * ‖f‖
-/
theorem norm_compLpL_le [Fact (1 ≤ p)] (L : E →SL[σ] F) : ‖L.compLpL p μ‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

section Bilinear

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (μ p) in
/-- Given a continuous bilinear map `G → E → F`, construct the associated bilinear map
`G → Lp E p μ → Lp F p μ`. -/
/-
**ContinuousLinearMap.compLp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compLp (L : E ->SL[σ] F) (f : Lp E p μ) : Lp F p μ
参数：L : E ->SL[σ] F；f : Lp E p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous bilinear map `G → E → F`, construct the associated bilinear m
ap
`G → Lp E p μ → Lp F p μ`.
-/
@[simps] def compLpₗ₂ (B : G →L[𝕜] E →L[𝕜] F) : G →ₗ[𝕜] Lp E p μ →ₗ[𝕜] Lp F p μ where
  toFun g := (B g).compLpₗ p μ
  map_add' g h := by
    ext f
    filter_upwards [(B (g + h)).coeFn_compLp f, (B g).coeFn_compLp f, (B h).coeFn_compLp f,
      Lp.coeFn_add ((B g).compLp f) ((B h).compLp f)] with x hx hg hh hadd
    simp only [compLpₗ_apply, LinearMap.add_apply, hx, hadd]
    simp only [map_add, add_apply, Pi.add_apply, hg, hh]
  map_smul' c g := by
    ext f
    filter_upwards [(c • B g).coeFn_compLp f, (B g).coeFn_compLp f,
      Lp.coeFn_smul c ((B g).compLp f)] with x hx hg hsmul
    simp [hx, hsmul, hg]

variable (μ p) in
/-- Given a continuous bilinear map `G → E → F`, construct the associated continuous bilinear map
`G → Lp E p μ → Lp F p μ`. -/
/-
**ContinuousLinearMap.compLpL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compLpL [Fact (1 <= p)] (L : E ->SL[σ] F) : Lp E p μ ->SL[σ] Lp F p μ
参数：1 <= p；L : E ->SL[σ] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_compLp_le`：norm_compLp_le (L : E ->SL[σ] F) (f 
: Lp E p μ) : ‖L.compLp f‖ <= ‖L‖ * ‖f‖

--- 原说明 ---
Given a continuous bilinear map `G → E → F`, construct the associated continuous
 bilinear map
`G → Lp E p μ → Lp F p μ`.
-/
def compLpL₂ [Fact (1 ≤ p)] (B : G →L[𝕜] E →L[𝕜] F) :
    G →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ :=
  (B.compLpₗ₂ p μ).mkContinuous₂ ‖B‖ (fun c f ↦ by
    simp only [compLpₗ₂_apply, compLpₗ_apply]
    grw [norm_compLp_le, le_opNorm])
/-
**ContinuousLinearMap.compLpL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compLpL [Fact (1 <= p)] (L : E ->SL[σ] F) : Lp E p μ ->SL[σ] Lp F p μ
参数：1 <= p；L : E ->SL[σ] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_compLp_le`：norm_compLp_le (L : E ->SL[σ] F) (f 
: Lp E p μ) : ‖L.compLp f‖ <= ‖L‖ * ‖f‖
-/
@[simp] theorem compLpL₂_apply_apply [Fact (1 ≤ p)] (B : G →L[𝕜] E →L[𝕜] F) (g : G) (f : Lp E p μ) :
    compLpL₂ p μ B g f = (B g).compLp f := rfl
/-
**ContinuousLinearMap.norm_compLpL** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_compLpL₂_le [Fact (1 ≤ p)] (B : G →L[𝕜] E →L[𝕜] F) :
    ‖B.compLpL₂ p μ‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg _) _

end Bilinear

end ContinuousLinearMap

namespace MeasureTheory.Lp

section LpToLpOfMeasureLeSMul

variable [NormedSpace ℝ E] {ν : Measure α} {c : ℝ≥0∞}

/-- The canonical map from `Lᵖ ν` to `Lᵖ μ` when `μ` is bounded by a finite multiple of `ν`.
This is the linear map version. Use instead the continuous linear map
version `LpToLpOfMeasureLeSMul` -/
/-
**MeasureTheory.Lp.LpToLpOfMeasureLeSMul** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：LpToLpOfMeasureLeSMul [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) : Lp 
E p ν ->L[Real] Lp E p μ
参数：1 <= p；hc : c != ∞；h : μ <= c • ν。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Basic.0.MeasureTheory.Lp
.norm_LpToLpOfMeasureLeSMulₗ_apply_le`：∀ {α : Type u_1} {E : Type u_4} {m : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [inst_1 …

--- 原说明 ---
The canonical map from `Lᵖ ν` to `Lᵖ μ` when `μ` is bounded by a finite multiple
 of `ν`.
This is the linear map version. Use instead the continuous linear map
version `LpToLpOfMeasureLeSMul`
-/
private noncomputable def LpToLpOfMeasureLeSMulₗ (hc : c ≠ ∞) (h : μ ≤ c • ν) :
    Lp E p ν →ₗ[ℝ] Lp E p μ where
  toFun f := ((Lp.memLp f).of_measure_le_smul hc h).toLp f
  map_add' f g := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    have : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
    apply this.ae_eq
    grw [Lp.coeFn_add]
  map_smul' c f := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    have : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
    apply this.ae_eq
    grw [Lp.coeFn_smul]
    rfl
/-
**MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Lp`。
形式化陈述：coeFn_LpToLpOfMeasureLeSMul [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν)
 (f : Lp E p ν) : LpToLpOfMeasureLeSMul hc h f =ᵐ[μ] f
参数：1 <= p；hc : c != ∞；h : μ <= c • ν；f : Lp E p ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Basic.0.MeasureTheory.Lp
.coeFn_LpToLpOfMeasureLeSMulₗ`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSp
ace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup 
E] [inst_1 …
-/
private lemma coeFn_LpToLpOfMeasureLeSMulₗ (hc : c ≠ ∞) (h : μ ≤ c • ν) (f : Lp E p ν) :
    LpToLpOfMeasureLeSMulₗ hc h f =ᵐ[μ] f := by
  simp [LpToLpOfMeasureLeSMulₗ, MemLp.coeFn_toLp]
/-
**MeasureTheory.Lp.enorm_LpToLpOfMeasureLeSMul** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma enorm_LpToLpOfMeasureLeSMulₗ_apply_le
    (hc : c ≠ ∞) (h : μ ≤ c • ν) [Fact (1 ≤ p)] {f : Lp E p ν} :
    ‖LpToLpOfMeasureLeSMulₗ hc h f‖ₑ ≤ c ^ (1 / p).toReal * ‖f‖ₑ := by
  simp only [Lp.enorm_def]
  rw [eLpNorm_congr_ae (coeFn_LpToLpOfMeasureLeSMulₗ hc h f)]
  exact eLpNorm_le_of_measure_le_smul h
/-
**MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma norm_LpToLpOfMeasureLeSMulₗ_apply_le
    (hc : c ≠ ∞) (h : μ ≤ c • ν) [Fact (1 ≤ p)] {f : Lp E p ν} :
    ‖LpToLpOfMeasureLeSMulₗ hc h f‖ ≤ c.toReal ^ (1 / p).toReal * ‖f‖ := by
  simp only [← toReal_enorm]
  rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  grw [enorm_LpToLpOfMeasureLeSMulₗ_apply_le]
  simp [ENNReal.mul_eq_top, hc]

/-- The canonical map from `Lᵖ ν` to `Lᵖ μ` when `μ` is bounded by a finite multiple of `ν`. -/
@[no_expose]
/-
**MeasureTheory.Lp.LpToLpOfMeasureLeSMul** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：LpToLpOfMeasureLeSMul [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν) : Lp 
E p ν ->L[Real] Lp E p μ
参数：1 <= p；hc : c != ∞；h : μ <= c • ν。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Basic.0.MeasureTheory.Lp
.norm_LpToLpOfMeasureLeSMulₗ_apply_le`：∀ {α : Type u_1} {E : Type u_4} {m : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [inst_1 …

--- 原说明 ---
The canonical map from `Lᵖ ν` to `Lᵖ μ` when `μ` is bounded by a finite multiple
 of `ν`.
-/
noncomputable def LpToLpOfMeasureLeSMul [Fact (1 ≤ p)] (hc : c ≠ ∞) (h : μ ≤ c • ν) :
    Lp E p ν →L[ℝ] Lp E p μ :=
  LinearMap.mkContinuous (LpToLpOfMeasureLeSMulₗ hc h) (c.toReal ^ (1 / p).toReal)
    (fun _ ↦ norm_LpToLpOfMeasureLeSMulₗ_apply_le hc h)
/-
**MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Lp`。
形式化陈述：coeFn_LpToLpOfMeasureLeSMul [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • ν)
 (f : Lp E p ν) : LpToLpOfMeasureLeSMul hc h f =ᵐ[μ] f
参数：1 <= p；hc : c != ∞；h : μ <= c • ν；f : Lp E p ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Basic.0.MeasureTheory.Lp
.coeFn_LpToLpOfMeasureLeSMulₗ`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableSp
ace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup 
E] [inst_1 …
-/
lemma coeFn_LpToLpOfMeasureLeSMul [Fact (1 ≤ p)] (hc : c ≠ ∞) (h : μ ≤ c • ν) (f : Lp E p ν) :
    LpToLpOfMeasureLeSMul hc h f =ᵐ[μ] f :=
  coeFn_LpToLpOfMeasureLeSMulₗ hc h f
/-
**MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul_le** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：norm_LpToLpOfMeasureLeSMul_le [Fact (1 <= p)] (hc : c != ∞) (h : μ <= c • 
ν) : ‖(LpToLpOfMeasureLeSMul hc h : Lp E p ν ->L[Real] Lp E p μ)‖ <= c.toReal ^ 
(1 / p).toReal
参数：1 <= p；hc : c != ∞；h : μ <= c • ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Basic.0.MeasureTheory.Lp
.norm_LpToLpOfMeasureLeSMulₗ_apply_le`：∀ {α : Type u_1} {E : Type u_4} {m : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [inst_1 …
-/
lemma norm_LpToLpOfMeasureLeSMul_le [Fact (1 ≤ p)] (hc : c ≠ ∞) (h : μ ≤ c • ν) :
    ‖(LpToLpOfMeasureLeSMul hc h : Lp E p ν →L[ℝ] Lp E p μ)‖ ≤ c.toReal ^ (1 / p).toReal :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by simp) _) _

end LpToLpOfMeasureLeSMul

section PosPart

/-
**MeasureTheory.Lp.lipschitzWith_pos_part** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Lp`。
形式化陈述：lipschitzWith_pos_part : LipschitzWith 1 fun x : Real => max x 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.max_const`：max_const (hf : LipschitzWith Kf f) (a : Real) 
: LipschitzWith Kf fun x => max (f x) a
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
-/
theorem lipschitzWith_pos_part : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.id.max_const _
/-
**MeasureTheory.Lp._root_.MeasureTheory.MemLp.pos_part** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.MemLp.pos_part {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf
/-
**MeasureTheory.Lp._root_.MeasureTheory.MemLp.neg_part** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.MemLp.neg_part {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (-f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf.neg

/-- Positive part of a function in `L^p`. -/
/-
**MeasureTheory.Lp.posPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：posPart (f : Lp Real p μ) : Lp Real p μ
参数：f : Lp Real p μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.lipschitzWith_pos_part`：lipschitzWith_pos_part : Lipsch
itzWith 1 fun x : Real => max x 0

--- 原说明 ---
Positive part of a function in `L^p`.
-/
def posPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f

/-- Negative part of a function in `L^p`. -/
/-
**MeasureTheory.Lp.negPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：negPart (f : Lp Real p μ) : Lp Real p μ
参数：f : Lp Real p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negative part of a function in `L^p`.
-/
def negPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  posPart (-f)

@[norm_cast]
/-
**MeasureTheory.Lp.coe_posPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coe_posPart (f : Lp Real p μ) : (posPart f : α ->ₘ[μ] Real) = (f : α ->ₘ[μ
] Real).posPart
参数：f : Lp Real p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_posPart (f : Lp ℝ p μ) : (posPart f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).posPart :=
  rfl
/-
**MeasureTheory.Lp.coeFn_posPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_posPart (f : Lp Real p μ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0
参数：f : Lp Real p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_posPart`：coeFn_posPart (f : α ->ₘ[μ] γ) : ⇑(
posPart f) =ᵐ[μ] fun a => max (f a) 0
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem coeFn_posPart (f : Lp ℝ p μ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  AEEqFun.coeFn_posPart _
/-
**MeasureTheory.Lp.coeFn_negPart_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Lp`。
形式化陈述：coeFn_negPart_eq_max (f : Lp Real p μ) : forallᵐ a ∂μ, negPart f a = max (
-f a) 0
参数：f : Lp Real p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.negPart.eq_1`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} (f : ↥(MeasureTheory.Lp ℝ p μ)),   M
easureTheory.Lp.neg…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Lp.coeFn_neg`：coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f
· 使用定理 `MeasureTheory.Lp.coeFn_posPart`：coeFn_posPart (f : Lp Real p μ) : ⇑(posP
art f) =ᵐ[μ] fun a => max (f a) 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
-/
theorem coeFn_negPart_eq_max (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = max (-f a) 0 := by
  rw [negPart]
  filter_upwards [coeFn_posPart (-f), coeFn_neg f] with _ h₁ h₂
  rw [h₁, h₂, Pi.neg_apply]
/-
**MeasureTheory.Lp.coeFn_negPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_negPart (f : Lp Real p μ) : forallᵐ a ∂μ, negPart f a = -min (f a) 0
参数：f : Lp Real p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_negPart_eq_max`：coeFn_negPart_eq_max (f : Lp Real
 p μ) : forallᵐ a ∂μ, negPart f a = max (-f a) 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_neg_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOr
der α] [IsOrderedAddMonoid α] (a b : α),   max (-a) (-b) = -min a b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem coeFn_negPart (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = -min (f a) 0 :=
  (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]
/-
**MeasureTheory.Lp.continuous_posPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：continuous_posPart [Fact (1 <= p)] : Continuous fun f : Lp Real p μ => pos
Part f
参数：1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous_compLp`：continuous_compLp [Fact (1 <= p)] (hg :
 LipschitzWith c g) (g0 : g 0 = 0) : Continuous (hg.compLp g0 : Lp E p μ -> Lp F
 p μ)
· 使用定理 `MeasureTheory.Lp.lipschitzWith_pos_part`：lipschitzWith_pos_part : Lipsch
itzWith 1 fun x : Real => max x 0
-/
theorem continuous_posPart [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => posPart f :=
  LipschitzWith.continuous_compLp _ _
/-
**MeasureTheory.Lp.continuous_negPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：continuous_negPart [Fact (1 <= p)] : Continuous fun f : Lp Real p μ => neg
Part f
参数：1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.Lp.continuous_posPart`：continuous_posPart [Fact (1 <= p)] 
: Continuous fun f : Lp Real p μ => posPart f
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
theorem continuous_negPart [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => negPart f := by
  unfold negPart
  exact continuous_posPart.comp continuous_neg

end PosPart

end MeasureTheory.Lp

end Composition

namespace MeasureTheory.Lp

/-- A version of **Markov's inequality** with elements of Lp. -/
/-
**MeasureTheory.Lp.pow_mul_meas_ge_le_enorm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：pow_mul_meas_ge_le_enorm (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top :
 p != ∞) (ε : Real>=0∞) : (ε * μ {x | ε <= ‖f x‖ₑ ^ p.toReal}) ^ (1 / p.toReal) 
<= ENNReal.ofReal ‖f‖
参数：f : Lp E p μ；hp_ne_zero : p != 0；hp_ne_top : p != ∞；ε : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.pow_mul_meas_ge_le_eLpNorm`：pow_mul_meas_ge_le_eLpNorm (hp
_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurable
 f μ) (ε : Real>=0∞) : (ε * μ …
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞

--- 原说明 ---
A version of **Markov's inequality** with elements of Lp.
-/
lemma pow_mul_meas_ge_le_enorm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    (ε * μ {x | ε ≤ ‖f x‖ₑ ^ p.toReal}) ^ (1 / p.toReal) ≤ ENNReal.ofReal ‖f‖ :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/-- A version of **Markov's inequality** with elements of Lp. -/
/-
**MeasureTheory.Lp.mul_meas_ge_le_pow_enorm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：mul_meas_ge_le_pow_enorm (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top :
 p != ∞) (ε : Real>=0∞) : ε * μ {x | ε <= ‖f x‖ₑ ^ p.toReal} <= ENNReal.ofReal ‖
f‖ ^ p.toReal
参数：f : Lp E p μ；hp_ne_zero : p != 0；hp_ne_top : p != ∞；ε : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.mul_meas_ge_le_pow_eLpNorm`：mul_meas_ge_le_pow_eLpNorm (hp
_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurable
 f μ) (ε : Real>=0∞) : ε * μ {…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞

--- 原说明 ---
A version of **Markov's inequality** with elements of Lp.
-/
lemma mul_meas_ge_le_pow_enorm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    ε * μ {x | ε ≤ ‖f x‖ₑ ^ p.toReal} ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/-- A version of **Markov's inequality** with elements of Lp. -/
/-
**MeasureTheory.Lp.mul_meas_ge_le_pow_enorm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Lp`。
形式化陈述：mul_meas_ge_le_pow_enorm' (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top 
: p != ∞) (ε : Real>=0∞) : ε ^ p.toReal * μ {x | ε <= ‖f x‖₊ } <= ENNReal.ofReal
 ‖f‖ ^ p.toReal
参数：f : Lp E p μ；hp_ne_zero : p != 0；hp_ne_top : p != ∞；ε : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.mul_meas_ge_le_pow_eLpNorm'`：mul_meas_ge_le_pow_eLpNorm' (
hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurab
le f μ) (ε : Real>=0∞) : ε ^ p.…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞

--- 原说明 ---
A version of **Markov's inequality** with elements of Lp.
-/
theorem mul_meas_ge_le_pow_enorm' (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (ε : ℝ≥0∞) : ε ^ p.toReal * μ {x | ε ≤ ‖f x‖₊ } ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/-- A version of **Markov's inequality** with elements of Lp. -/
/-
**MeasureTheory.Lp.meas_ge_le_mul_pow_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：meas_ge_le_mul_pow_enorm (f : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top :
 p != ∞) {ε : Real>=0∞} (hε : ε != 0) : μ {x | ε <= ‖f x‖₊} <= ε⁻¹ ^ p.toReal * 
ENNReal.ofReal ‖f‖ ^ p.toReal
参数：f : Lp E p μ；hp_ne_zero : p != 0；hp_ne_top : p != ∞；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm`：meas_ge_le_mul_pow_eLpNo
rm_enorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStrong
lyMeasurable f μ) {ε : Real>=0∞} (hε…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞

--- 原说明 ---
A version of **Markov's inequality** with elements of Lp.
-/
theorem meas_ge_le_mul_pow_enorm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : μ {x | ε ≤ ‖f x‖₊} ≤ ε⁻¹ ^ p.toReal * ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε (by simp)

section Star

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable instance {p : ℝ≥0∞} : Star (Lp R p μ) where
  star f := ⟨star (f : α →ₘ[μ] R),
    by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩
/-
**MeasureTheory.Lp.coeFn_star** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_star {p : Real>=0∞} (f : Lp R p μ) : (star f : Lp R p μ) =ᵐ[μ] star 
f
参数：f : Lp R p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.AEEqFun.coeFn_star`：coeFn_star [Star R] [ContinuousStar R]
 (f : α ->ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α -> R)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
-/
lemma coeFn_star {p : ℝ≥0∞} (f : Lp R p μ) : (star f : Lp R p μ) =ᵐ[μ] star f :=
    (f : α →ₘ[μ] R).coeFn_star
/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {p : ℝ≥0∞} : InvolutiveStar (Lp R p μ) where
  star_involutive _ := Subtype.ext <| star_involutive _
/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [TrivialStar R] {p : ℝ≥0∞} : TrivialStar (Lp R p μ) where
  star_trivial _ := Subtype.ext <| star_trivial _

end Star

end MeasureTheory.Lp

