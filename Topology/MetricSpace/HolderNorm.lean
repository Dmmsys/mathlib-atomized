/-
Copyright (c) 2024 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder norm

This file defines the Hölder (semi-)norm for Hölder functions alongside some basic properties.
The `r`-Hölder norm of a function `f : X → Y` between two metric spaces is the least non-negative
real number `C` for which `f` is `r`-Hölder continuous with constant `C`, i.e. it is the least `C`
for which `WithHolder C r f` is true.

## Main definitions

* `eHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f`.
* `nnHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0` of a function `f`.
* `MemHolder r f`: Predicate for a function `f` being `r`-Hölder continuous.

## Main results

* `eHolderNorm_eq_zero`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHolder.holderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

## Tags

Hölder norm, Hoelder norm, Holder norm

-/

@[expose] public section

variable {X Y : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0} {f : X → Y}

/-- The `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f` is the least non-negative real
number `C` for which `f` is `r`-Hölder continuous with constant `C`. This is `∞` if no such
non-negative real exists. -/
noncomputable
/-
**eHolderNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：eHolderNorm (r : Real>=0) (f : X -> Y) : Real>=0∞
参数：r : Real>=0；f : X -> Y。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith C r f), C

/-- The `r`-Hölder (semi)norm in `ℝ≥0`. -/
noncomputable
/-
**nnHolderNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nnHolderNorm (r : Real>=0) (f : X -> Y) : Real>=0
参数：r : Real>=0；f : X -> Y。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def nnHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHolderNorm r f).toNNReal

/-- A function `f` is `MemHolder r f` if it is Hölder continuous. Namely, `f` has a finite
`r`-Hölder constant. This is equivalent to `f` having finite Hölder norm.
c.f. `memHolder_iff`. -/
/-
**MemHolder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MemHolder (r : Real>=0) (f : X -> Y) : Prop
参数：r : Real>=0；f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is `MemHolder r f` if it is Hölder continuous. Namely, `f` has a 
finite
`r`-Hölder constant. This is equivalent to `f` having finite Hölder norm.
c.f. `memHolder_iff`.
-/
def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C, HolderWith C r f
/-
**HolderWith.memHolder** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HolderWith.memHolder {C : Real>=0} (hf : HolderWith C r f) : MemHolder r f
参数：hf : HolderWith C r f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HolderWith.memHolder {C : ℝ≥0} (hf : HolderWith C r f) : MemHolder r f := ⟨C, hf⟩
/-
**eHolderNorm_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {r : NNReal} {f : X → Y},   eHolderNorm r f < ⊤ ↔ MemHolder 
r f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_lt_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{s : ι → α}, ⨅ i, s i < ⊤ ↔ ∃ i, s i < ⊤
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
@[simp] lemma eHolderNorm_lt_top : eHolderNorm r f < ∞ ↔ MemHolder r f := by
  refine ⟨fun h => ?_,
    fun hf => let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩⟩
  simp_rw [eHolderNorm, iInf_lt_top] at h
  let ⟨C, hC, _⟩ := h
  exact ⟨C, hC⟩
/-
**eHolderNorm_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_ne_top : eHolderNorm r f != ∞ ↔ MemHolder r f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eHolderNorm_lt_top`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetri
cSpace X] [inst_1 : PseudoEMetricSpace Y] {r : NNReal} {f : X → Y},   eHolderNor
m r f < …
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eHolderNorm_ne_top : eHolderNorm r f ≠ ∞ ↔ MemHolder r f := by
  rw [← eHolderNorm_lt_top, lt_top_iff_ne_top]
/-
**eHolderNorm_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {r : NNReal} {f : X → Y},   eHolderNorm r f = ⊤ ↔ ¬MemHolder
 r f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `eHolderNorm_ne_top`：eHolderNorm_ne_top : eHolderNorm r f != ∞ ↔ MemHolde
r r f
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma eHolderNorm_eq_top : eHolderNorm r f = ∞ ↔ ¬ MemHolder r f := by
  rw [← eHolderNorm_ne_top, not_not]

protected alias ⟨_, MemHolder.eHolderNorm_lt_top⟩ := eHolderNorm_lt_top
protected alias ⟨_, MemHolder.eHolderNorm_ne_top⟩ := eHolderNorm_ne_top
/-
**coe_nnHolderNorm_le_eHolderNorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_nnHolderNorm_le_eHolderNorm {r : Real>=0} {f : X -> Y} : (nnHolderNorm
 r f : Real>=0∞) <= eHolderNorm r f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_toNNReal_le_self`：∀ {a : ENNReal}, ↑a.toNNReal ≤ a
-/
lemma coe_nnHolderNorm_le_eHolderNorm {r : ℝ≥0} {f : X → Y} :
    (nnHolderNorm r f : ℝ≥0∞) ≤ eHolderNorm r f :=
  coe_toNNReal_le_self

variable (X) in
@[simp]
/-
**eHolderNorm_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_const (r : Real>=0) (c : Y) : eHolderNorm r (Function.const X 
c) = 0
参数：r : Real>=0；c : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eHolderNorm.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricS
pace X] [inst_1 : PseudoEMetricSpace Y] (r : NNReal) (f : X → Y),   eHolderNorm 
r f = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.bot_eq_zero`：bot_eq_zero : (⊥ : Real>=0∞) = 0
· 使用定理 `iInf₂_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLinearOrder α] (f : (i : ι) → κ i → α),   ⨅ i, ⨅ j, f i j = ⊥ ↔ ∀ (b : 
α)…
· 使用引理 `HolderWith.const`：const {y : Y} : HolderWith C r (Function.const X y)
-/
lemma eHolderNorm_const (r : ℝ≥0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

variable (X) in
@[simp]
/-
**eHolderNorm_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_zero [Zero Y] (r : Real>=0) : eHolderNorm r (0 : X -> Y) = 0
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eHolderNorm_const`：eHolderNorm_const (r : Real>=0) (c : Y) : eHolderNorm
 r (Function.const X c) = 0
-/
lemma eHolderNorm_zero [Zero Y] (r : ℝ≥0) : eHolderNorm r (0 : X → Y) = 0 :=
  eHolderNorm_const X r 0

variable (X) in
@[simp]
/-
**nnHolderNorm_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnHolderNorm_const (r : Real>=0) (c : Y) : nnHolderNorm r (Function.const 
X c) = 0
参数：r : Real>=0；c : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用引理 `eHolderNorm_const`：eHolderNorm_const (r : Real>=0) (c : Y) : eHolderNorm
 r (Function.const X c) = 0
· 使用引理 `coe_nnHolderNorm_le_eHolderNorm`：coe_nnHolderNorm_le_eHolderNorm {r : Re
al>=0} {f : X -> Y} : (nnHolderNorm r f : Real>=0∞) <= eHolderNorm r f
-/
lemma nnHolderNorm_const (r : ℝ≥0) (c : Y) : nnHolderNorm r (Function.const X c) = 0 := by
  rw [← nonpos_iff_eq_zero, ← ENNReal.coe_le_coe, ENNReal.coe_zero, ← eHolderNorm_const X r c]
  exact coe_nnHolderNorm_le_eHolderNorm

variable (X) in
@[simp]
/-
**nnHolderNorm_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnHolderNorm_zero [Zero Y] (r : Real>=0) : nnHolderNorm r (0 : X -> Y) = 0
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nnHolderNorm_const`：nnHolderNorm_const (r : Real>=0) (c : Y) : nnHolderN
orm r (Function.const X c) = 0
-/
lemma nnHolderNorm_zero [Zero Y] (r : ℝ≥0) : nnHolderNorm r (0 : X → Y) = 0 :=
  nnHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero
/-
**eHolderNorm_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_of_isEmpty [hX : IsEmpty X] : eHolderNorm r f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eHolderNorm.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricS
pace X] [inst_1 : PseudoEMetricSpace Y] (r : NNReal) (f : X → Y),   eHolderNorm 
r f = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.bot_eq_zero`：bot_eq_zero : (⊥ : Real>=0∞) = 0
· 使用定理 `iInf₂_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLinearOrder α] (f : (i : ι) → κ i → α),   ⨅ i, ⨅ j, f i j = ⊥ ↔ ∀ (b : 
α)…
· 使用引理 `HolderWith.of_isEmpty`：of_isEmpty [IsEmpty X] : HolderWith C r f
-/
lemma eHolderNorm_of_isEmpty [hX : IsEmpty X] :
    eHolderNorm r f = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩
/-
**HolderWith.eHolderNorm_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HolderWith.eHolderNorm_le {C : Real>=0} (hf : HolderWith C r f) : eHolderN
orm r f <= C
参数：hf : HolderWith C r f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma HolderWith.eHolderNorm_le {C : ℝ≥0} (hf : HolderWith C r f) :
    eHolderNorm r f ≤ C :=
  iInf₂_le C hf

/-- See also `memHolder_const` for the version with the spelling `fun _ ↦ c`. -/
@[simp]
/-
**memHolder_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memHolder_const {c : Y} : MemHolder r (Function.const X c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
· 使用引理 `HolderWith.const`：const {y : Y} : HolderWith C r (Function.const X y)

--- 原说明 ---
See also `memHolder_const` for the version with the spelling `fun _ ↦ c`.
-/
lemma memHolder_const {c : Y} : MemHolder r (Function.const X c) :=
  (HolderWith.const (C := 0)).memHolder

/-- Version of `memHolder_const` with the spelling `fun _ ↦ c` for the constant function. -/
@[simp]
/-
**memHolder_const'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memHolder_const' {c : Y} : MemHolder r (fun _ => c : X -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `memHolder_const`：memHolder_const {c : Y} : MemHolder r (Function.const X
 c)

--- 原说明 ---
Version of `memHolder_const` with the spelling `fun _ ↦ c` for the constant func
tion.
-/
lemma memHolder_const' {c : Y} : MemHolder r (fun _ ↦ c : X → Y) :=
  memHolder_const

@[simp]
/-
**memHolder_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memHolder_zero [Zero Y] : MemHolder r (0 : X -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `memHolder_const`：memHolder_const {c : Y} : MemHolder r (Function.const X
 c)
-/
lemma memHolder_zero [Zero Y] : MemHolder r (0 : X → Y) :=
  memHolder_const

section Monotonicity

open Bornology

/-- If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder when `s ≤ r`.
See `MemHolder.of_le'` for the version in a pseudoemetric space. -/
/-
**MemHolder.of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX : BoundedSpace X] {f
 : X -> Y} {s : Real>=0} (hf : MemHolder r f) (hs : s <= r) : MemHolder s f
参数：hf : MemHolder r f；hs : s <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Metric.boundedSpace_iff_edist`：boundedSpace_iff_edist : BoundedSpace α ↔
 exists C : Real>=0, forall a b : α, edist a b <= C
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用引理 `HolderOnWith.of_le`：of_le {C D s : Real>=0} {A : Set X} (hA : forall x i
n A, forall y in A, edist x y <= D) (hf : HolderOnWith C r f A) (hsr : s <= r) :
 HolderO…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder whe
n `s ≤ r`.
See `MemHolder.of_le'` for the version in a pseudoemetric space.
-/
lemma MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX : BoundedSpace X]
    {f : X → Y} {s : ℝ≥0} (hf : MemHolder r f) (hs : s ≤ r) :
    MemHolder s f := by
  obtain ⟨C, hf⟩ := hf
  obtain ⟨C', hC'⟩ := Metric.boundedSpace_iff_edist.1 hX
  exact ⟨C * C' ^ (r - s : ℝ),
    holderOnWith_univ.1 <| (holderOnWith_univ.2 hf).of_le (fun x _ y _ ↦ hC' x y) hs⟩

/-- If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder when `s ≤ r`.
See `MemHolder.of_le` for the version in a pseudometric space. -/
/-
**MemHolder.of_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.of_le' {s : Real>=0} (hf : MemHolder r f) (hs : s <= r) (hX : ex
ists C : Real>=0, forall x y : X, edist x y <= C) : MemHolder s f
参数：hf : MemHolder r f；hs : s <= r；hX : exists C : Real>=0, forall x y : X, edist
 x y <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Metric.boundedSpace_iff_edist`：boundedSpace_iff_edist : BoundedSpace α ↔
 exists C : Real>=0, forall a b : α, edist a b <= C
· 使用引理 `MemHolder.of_le`：MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX :
 BoundedSpace X] {f : X -> Y} {s : Real>=0} (hf : MemHolder r f) (hs : s <= r) :
 MemH…

--- 原说明 ---
If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder whe
n `s ≤ r`.
See `MemHolder.of_le` for the version in a pseudometric space.
-/
lemma MemHolder.of_le' {s : ℝ≥0} (hf : MemHolder r f) (hs : s ≤ r)
    (hX : ∃ C : ℝ≥0, ∀ x y : X, edist x y ≤ C) :
    MemHolder s f := by
  obtain ⟨C, hX⟩ := hX
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hX x y)
  have := Metric.boundedSpace_iff_edist.2 ⟨C, hX⟩
  exact hf.of_le hs

/-- If a function is `r`-Hölder over a bounded set, then it is also `s`-Hölder over this set
when `s ≤ r`. See `HolderOnWith.exists_holderOnWith_of_le'`
for the version in a pseudoemetric space. -/
/-
**HolderOnWith.exists_holderOnWith_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HolderOnWith.exists_holderOnWith_of_le {X : Type*} [PseudoMetricSpace X] {
f : X -> Y} {s : Real>=0} {A : Set X} (hf : exists C, HolderOnWith C r f A) (hs 
: s <= r) (hA : IsBounded A) : exists C, HolderOnWith C s f A
参数：hf : exists C, HolderOnWith C r f A；hs : s <= r；hA : IsBounded A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `boundedSpace_val_set_iff`：boundedSpace_val_set_iff {s : Set α} : Bounded
Space s ↔ IsBounded s
· 使用引理 `MemHolder.of_le`：MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX :
 BoundedSpace X] {f : X -> Y} {s : Real>=0} (hf : MemHolder r f) (hs : s <= r) :
 MemH…

--- 原说明 ---
If a function is `r`-Hölder over a bounded set, then it is also `s`-Hölder over 
this set
when `s ≤ r`. See `HolderOnWith.exists_holderOnWith_of_le'`
for the version in a pseudoemetric space.
-/
lemma HolderOnWith.exists_holderOnWith_of_le {X : Type*} [PseudoMetricSpace X]
    {f : X → Y} {s : ℝ≥0} {A : Set X} (hf : ∃ C, HolderOnWith C r f A) (hs : s ≤ r)
    (hA : IsBounded A) : ∃ C, HolderOnWith C s f A := by
  simp_rw [← HolderWith.restrict_iff] at *
  have : BoundedSpace A := boundedSpace_val_set_iff.2 hA
  exact MemHolder.of_le hf hs

/-- If a function is `r`-Hölder over a bounded set,
then it is also `s`-Hölder over this set when `s ≤ r`. See `HolderOnWith.exists_holderOnWith_of_le`
for the version in a pseudometric space. -/
/-
**HolderOnWith.exists_holderOnWith_of_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HolderOnWith.exists_holderOnWith_of_le' {D s : Real>=0} {A : Set X} (hf : 
exists C, HolderOnWith C r f A) (hs : s <= r) (hA : forall ⦃x⦄, x in A -> forall
 ⦃y⦄, y in A -> edist x y <= D) : exists C, HolderOnWith C s f A
参数：hf : exists C, HolderOnWith C r f A；hs : s <= r；hA : forall ⦃x⦄, x in A -> fo
rall ⦃y⦄, y in A -> edist x y <= D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Metric.boundedSpace_iff_edist`：boundedSpace_iff_edist : BoundedSpace α ↔
 exists C : Real>=0, forall a b : α, edist a b <= C
· 使用引理 `MemHolder.of_le`：MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX :
 BoundedSpace X] {f : X -> Y} {s : Real>=0} (hf : MemHolder r f) (hs : s <= r) :
 MemH…

--- 原说明 ---
If a function is `r`-Hölder over a bounded set,
then it is also `s`-Hölder over this set when `s ≤ r`. See `HolderOnWith.exists_
holderOnWith_of_le`
for the version in a pseudometric space.
-/
lemma HolderOnWith.exists_holderOnWith_of_le' {D s : ℝ≥0} {A : Set X}
    (hf : ∃ C, HolderOnWith C r f A) (hs : s ≤ r)
    (hA : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → edist x y ≤ D) :
    ∃ C, HolderOnWith C s f A := by
  simp_rw [← HolderWith.restrict_iff] at *
  let := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y : A ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hA x.2 y.2)
  have : BoundedSpace A := Metric.boundedSpace_iff_edist.2 ⟨D, fun x y ↦ hA x.2 y.2⟩
  exact MemHolder.of_le hf hs

/-- If a function is locally `r`-Hölder and locally `t`-Hölder,
then it is locally `s`-Hölder for `r ≤ s ≤ t`. -/
/-
**HolderOnWith.exists_holderOnWith_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HolderOnWith.exists_holderOnWith_of_le_of_le {s t : Real>=0} {A : Set X} (
hf₁ : exists C, HolderOnWith C r f A) (hf₂ : exists C, HolderOnWith C t f A) (hr
s : r <= s) (hst : s <= t) : exists C, HolderOnWith C s f A
参数：hf₁ : exists C, HolderOnWith C r f A；hf₂ : exists C, HolderOnWith C t f A；hrs
 : r <= s；hst : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderOnWith.of_le_of_le`：of_le_of_le {C₁ C₂ s t : Real>=0} {A : Set X} 
(hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (hrt : r <= t) (hts 
: t <= s) : Ho…

--- 原说明 ---
If a function is locally `r`-Hölder and locally `t`-Hölder,
then it is locally `s`-Hölder for `r ≤ s ≤ t`.
-/
lemma HolderOnWith.exists_holderOnWith_of_le_of_le {s t : ℝ≥0} {A : Set X}
    (hf₁ : ∃ C, HolderOnWith C r f A) (hf₂ : ∃ C, HolderOnWith C t f A)
    (hrs : r ≤ s) (hst : s ≤ t) : ∃ C, HolderOnWith C s f A := by
  obtain ⟨C₁, hf₁⟩ := hf₁
  obtain ⟨C₂, hf₂⟩ := hf₂
  exact ⟨max C₁ C₂, hf₁.of_le_of_le hf₂ hrs hst⟩

/-- If a function is `r`-Hölder and `t`-Hölder, then it is `s`-Hölder for `r ≤ s ≤ t`. -/
/-
**MemHolder.memHolder_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.memHolder_of_le_of_le {s t : Real>=0} (hf₁ : MemHolder r f) (hf₂
 : MemHolder t f) (hrs : r <= s) (hst : s <= t) : MemHolder s f
参数：hf₁ : MemHolder r f；hf₂ : MemHolder t f；hrs : r <= s；hst : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HolderOnWith.exists_holderOnWith_of_le_of_le`：HolderOnWith.exists_holder
OnWith_of_le_of_le {s t : Real>=0} {A : Set X} (hf₁ : exists C, HolderOnWith C r
 f A) (hf₂ : exists C, HolderOnWit…

--- 原说明 ---
If a function is `r`-Hölder and `t`-Hölder, then it is `s`-Hölder for `r ≤ s ≤ t
`.
-/
lemma MemHolder.memHolder_of_le_of_le {s t : ℝ≥0} (hf₁ : MemHolder r f) (hf₂ : MemHolder t f)
    (hrs : r ≤ s) (hst : s ≤ t) : MemHolder s f := by
  simp_rw [MemHolder, ← holderOnWith_univ] at *
  exact HolderOnWith.exists_holderOnWith_of_le_of_le hf₁ hf₂ hrs hst

end Monotonicity

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

/-
**eHolderNorm_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_eq_zero {r : Real>=0} {f : X -> Y} : eHolderNorm r f = 0 ↔ for
all x₁ x₂, f x₁ = f x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_eq_zero`：edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `iInf₂_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLinearOrder α] (f : (i : ι) → κ i → α),   ⨅ i, ⨅ j, f i j = ⊥ ↔ ∀ (b : 
α)…
· 使用定理 `ENNReal.bot_eq_zero`：bot_eq_zero : (⊥ : Real>=0∞) = 0
· 使用定理 `eHolderNorm.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricS
pace X] [inst_1 : PseudoEMetricSpace Y] (r : NNReal) (f : X → Y),   eHolderNorm 
r f = …
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.mul_lt_of_lt_div`：mul_lt_of_lt_div (h : a < b / c) : a * c < b
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用引理 `eHolderNorm_of_isEmpty`：eHolderNorm_of_isEmpty [hX : IsEmpty X] : eHolde
rNorm r f = 0
· 使用引理 `eHolderNorm_const`：eHolderNorm_const (r : Real>=0) (c : Y) : eHolderNorm
 r (Function.const X c) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma eHolderNorm_eq_zero {r : ℝ≥0} {f : X → Y} :
    eHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  constructor
  · intro h x₁ x₂
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero, ← nonpos_iff_eq_zero]
      refine le_of_forall_gt fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : ℝ))
        (ENNReal.div_pos hb.ne.symm (ENNReal.rpow_lt_top_of_nonneg zero_le_coe
          (edist_lt_top x₁ x₂).ne).ne)
      exact lt_of_le_of_lt (hC x₁ x₂) <| ENNReal.mul_lt_of_lt_div hC'
  · intro h
    rcases isEmpty_or_nonempty X with hX | hX
    · exact eHolderNorm_of_isEmpty
    · rw [← eHolderNorm_const X r (f hX.some)]
      congr
      simp [funext_iff, h _ hX.some]
/-
**MemHolder.holderWith** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) : Hol
derWith (nnHolderNorm r f) r f
参数：hf : MemHolder r f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `nnHolderNorm.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] (r : NNReal) (f : X → Y),   nnHolderNor
m r f =…
· 使用定理 `eHolderNorm.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricS
pace X] [inst_1 : PseudoEMetricSpace Y] (r : NNReal) (f : X → Y),   eHolderNorm 
r f = …
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MemHolder.eHolderNorm_lt_top`：∀ {X : Type u_1} {Y : Type u_2} [inst : Ps
eudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {r : NNReal} {f : X → Y},   
MemHolder r f → eH…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ENNReal.rpow_pos`：rpow_pos {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (h
x_ne_top : x != ⊤) : 0 < x ^ p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `edist_pos`：edist_pos {x y : γ} : 0 < edist x y ↔ x != y
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_le_iff`：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x 
≤ z * y)
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
-/
lemma MemHolder.holderWith {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    HolderWith (nnHolderNorm r f) r f := by
  intro x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHolderNorm, eHolderNorm, coe_toNNReal]
  on_goal 2 => exact hf.eHolderNorm_lt_top.ne
  have h₁ : edist x₁ x₂ ^ (r : ℝ) ≠ 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt_top x₁ x₂).ne)
  have h₂ : edist x₁ x₂ ^ (r : ℝ) ≠ ∞ := by
    simp [(edist_lt_top x₁ x₂).ne]
  rw [← ENNReal.div_le_iff h₁ h₂]
  refine le_iInf₂ fun C hC => ?_
  rw [ENNReal.div_le_iff h₁ h₂]
  exact hC x₁ x₂
/-
**memHolder_iff_holderWith** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memHolder_iff_holderWith {r : Real>=0} {f : X -> Y} : MemHolder r f ↔ Hold
erWith (nnHolderNorm r f) r f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
-/
lemma memHolder_iff_holderWith {r : ℝ≥0} {f : X → Y} :
    MemHolder r f ↔ HolderWith (nnHolderNorm r f) r f :=
  ⟨MemHolder.holderWith, HolderWith.memHolder⟩
/-
**MemHolder.coe_nnHolderNorm_eq_eHolderNorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.coe_nnHolderNorm_eq_eHolderNorm {r : Real>=0} {f : X -> Y} (hf :
 MemHolder r f) : (nnHolderNorm r f : Real>=0∞) = eHolderNorm r f
参数：hf : MemHolder r f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnHolderNorm.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] (r : NNReal) (f : X → Y),   nnHolderNor
m r f =…
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `HolderWith.eHolderNorm_le`：HolderWith.eHolderNorm_le {C : Real>=0} (hf :
 HolderWith C r f) : eHolderNorm r f <= C
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
lemma MemHolder.coe_nnHolderNorm_eq_eHolderNorm
    {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    (nnHolderNorm r f : ℝ≥0∞) = eHolderNorm r f := by
  rw [nnHolderNorm, coe_toNNReal]
  exact ne_of_lt <| lt_of_le_of_lt hf.holderWith.eHolderNorm_le <| coe_lt_top
/-
**HolderWith.nnholderNorm_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HolderWith.nnholderNorm_le {C r : Real>=0} {f : X -> Y} (hf : HolderWith C
 r f) : nnHolderNorm r f <= C
参数：hf : HolderWith C r f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `MemHolder.coe_nnHolderNorm_eq_eHolderNorm`：MemHolder.coe_nnHolderNorm_eq
_eHolderNorm {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) : (nnHolderNorm r f
 : Real>=0∞) = eHolderNorm r f
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
· 使用引理 `HolderWith.eHolderNorm_le`：HolderWith.eHolderNorm_le {C : Real>=0} (hf :
 HolderWith C r f) : eHolderNorm r f <= C
-/
lemma HolderWith.nnholderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    nnHolderNorm r f ≤ C := by
  rw [← ENNReal.coe_le_coe, hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le
/-
**MemHolder.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.comp {r s : Real>=0} {Z : Type*} [MetricSpace Z] {f : Z -> X} {g
 : X -> Y} (hf : MemHolder r f) (hg : MemHolder s g) : MemHolder (s * r) (g ∘ f)
参数：hf : MemHolder r f；hg : MemHolder s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
· 使用定理 `HolderWith.comp`：comp {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg
 rg g) {Cf rf : Real>=0} {f : X -> Y} (hf : HolderWith Cf rf f) : HolderWith (Cg
 * Cf…
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
-/
lemma MemHolder.comp {r s : ℝ≥0} {Z : Type*} [MetricSpace Z] {f : Z → X} {g : X → Y}
    (hf : MemHolder r f) (hg : MemHolder s g) : MemHolder (s * r) (g ∘ f) :=
  (hg.holderWith.comp hf.holderWith).memHolder
/-
**MemHolder.nnHolderNorm_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.nnHolderNorm_eq_zero {r : Real>=0} {f : X -> Y} (hf : MemHolder 
r f) : nnHolderNorm r f = 0 ↔ forall x₁ x₂, f x₁ = f x₂
参数：hf : MemHolder r f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用引理 `MemHolder.coe_nnHolderNorm_eq_eHolderNorm`：MemHolder.coe_nnHolderNorm_eq
_eHolderNorm {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) : (nnHolderNorm r f
 : Real>=0∞) = eHolderNorm r f
· 使用引理 `eHolderNorm_eq_zero`：eHolderNorm_eq_zero {r : Real>=0} {f : X -> Y} : eH
olderNorm r f = 0 ↔ forall x₁ x₂, f x₁ = f x₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma MemHolder.nnHolderNorm_eq_zero {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    nnHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  rw [← ENNReal.coe_eq_zero, hf.coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_eq_zero]

end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {r : ℝ≥0} {f g : X → Y}

/-
**MemHolder.add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f +
 g)
参数：hf : MemHolder r f；hg : MemHolder r g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
· 使用引理 `HolderWith.add`：add (hf : HolderWith C r f) (hg : HolderWith C' r g) : H
olderWith (C + C') r (f + g)
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
-/
lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) :=
  (hf.holderWith.add hg.holderWith).memHolder
/-
**MemHolder.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y] {c 
: 𝕜} (hf : MemHolder r f) : MemHolder r (c • f)
参数：hf : MemHolder r f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
· 使用引理 `HolderWith.smul`：smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y]
 [IsBoundedSMul α Y] (a : α) (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (
a • f…
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
-/
lemma MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]
    {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f) :=
  (hf.holderWith.smul c).memHolder
/-
**MemHolder.smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.smul_iff {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
 {c : 𝕜} (hc : ‖c‖₊ != 0) : MemHolder r (c • f) ↔ MemHolder r f
参数：hc : ‖c‖₊ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HolderWith.smul_iff`：smul_iff {α} [SeminormedRing α] [Module α Y] [NormS
MulClass α Y] (a : α) (ha : ‖a‖₊ != 0) : HolderWith (C * ‖a‖₊) r (a • f) ↔ Holde
rWith C r…
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用引理 `MemHolder.smul`：MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBo
undedSMul 𝕜 Y] {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f)
-/
lemma MemHolder.smul_iff {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
    {c : 𝕜} (hc : ‖c‖₊ ≠ 0) : MemHolder r (c • f) ↔ MemHolder r f := by
  refine ⟨fun ⟨h, hh⟩ => ⟨h * ‖c‖₊⁻¹, ?_⟩, .smul⟩
  rw [← HolderWith.smul_iff _ hc, inv_mul_cancel_right₀ hc]
  exact hh
/-
**MemHolder.nsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.nsmul [NormedSpace Real Y] (n : Nat) (hf : MemHolder r f) : MemH
older r (n • f)
参数：n : Nat；hf : MemHolder r f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MemHolder.smul`：MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBo
undedSMul 𝕜 Y] {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f)
-/
lemma MemHolder.nsmul [NormedSpace ℝ Y] (n : ℕ) (hf : MemHolder r f) :
    MemHolder r (n • f) := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), hf.smul]
/-
**MemHolder.nnHolderNorm_add_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.nnHolderNorm_add_le (hf : MemHolder r f) (hg : MemHolder r g) : 
nnHolderNorm r (f + g) <= nnHolderNorm r f + nnHolderNorm r g
参数：hf : MemHolder r f；hg : MemHolder r g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `HolderWith.nnholderNorm_le`：HolderWith.nnholderNorm_le {C r : Real>=0} {
f : X -> Y} (hf : HolderWith C r f) : nnHolderNorm r f <= C
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
· 使用引理 `MemHolder.add`：MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) :
 MemHolder r (f + g)
· 使用引理 `HolderWith.add`：add (hf : HolderWith C r f) (hg : HolderWith C' r g) : H
olderWith (C + C') r (f + g)
-/
lemma MemHolder.nnHolderNorm_add_le (hf : MemHolder r f) (hg : MemHolder r g) :
    nnHolderNorm r (f + g) ≤ nnHolderNorm r f + nnHolderNorm r g :=
  (hf.add hg).holderWith.nnholderNorm_le.trans (hf.holderWith.add hg.holderWith).nnholderNorm_le
/-
**eHolderNorm_add_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_add_le : eHolderNorm r (f + g) <= eHolderNorm r f + eHolderNor
m r g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MemHolder.coe_nnHolderNorm_eq_eHolderNorm`：MemHolder.coe_nnHolderNorm_eq
_eHolderNorm {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) : (nnHolderNorm r f
 : Real>=0∞) = eHolderNorm r f
· 使用引理 `MemHolder.add`：MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) :
 MemHolder r (f + g)
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `MemHolder.nnHolderNorm_add_le`：MemHolder.nnHolderNorm_add_le (hf : MemHo
lder r f) (hg : MemHolder r g) : nnHolderNorm r (f + g) <= nnHolderNorm r f + nn
HolderNorm r g
· 使用定理 `eHolderNorm_eq_top`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetri
cSpace X] [inst_1 : PseudoEMetricSpace Y] {r : NNReal} {f : X → Y},   eHolderNor
m r f = …
· 使用定理 `Classical.not_and_iff_not_or_not`：∀ {a b : Prop}, ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
-/
lemma eHolderNorm_add_le :
    eHolderNorm r (f + g) ≤ eHolderNorm r f + eHolderNorm r g := by
  by_cases hfg : MemHolder r f ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm, ← hg.coe_nnHolderNorm_eq_eHolderNorm,
      ← (hf.add hg).coe_nnHolderNorm_eq_eHolderNorm, ← coe_add, ENNReal.coe_le_coe]
    exact hf.nnHolderNorm_add_le hg
  · rw [Classical.not_and_iff_not_or_not, ← eHolderNorm_eq_top, ← eHolderNorm_eq_top] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]
/-
**eHolderNorm_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y] (c : 
α) : eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f
参数：c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖₊
 = 0 ↔ a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `eHolderNorm_zero`：eHolderNorm_zero [Zero Y] (r : Real>=0) : eHolderNorm 
r (0 : X -> Y) = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `HolderWith.eHolderNorm_le`：HolderWith.eHolderNorm_le {C : Real>=0} (hf :
 HolderWith C r f) : eHolderNorm r f <= C
· 使用引理 `HolderWith.smul`：smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y]
 [IsBoundedSMul α Y] (a : α) (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (
a • f…
· 使用引理 `MemHolder.holderWith`：MemHolder.holderWith {r : Real>=0} {f : X -> Y} (h
f : MemHolder r f) : HolderWith (nnHolderNorm r f) r f
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用引理 `MemHolder.coe_nnHolderNorm_eq_eHolderNorm`：MemHolder.coe_nnHolderNorm_eq
_eHolderNorm {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) : (nnHolderNorm r f
 : Real>=0∞) = eHolderNorm r f
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HolderWith.memHolder`：HolderWith.memHolder {C : Real>=0} (hf : HolderWit
h C r f) : MemHolder r f
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `ENNReal.mul_div_right_comm`：∀ {a b c : ENNReal}, a * b / c = a / c * b
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
（共 39 条，此处仅展示前 30 条）
-/
lemma eHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y] (c : α) :
    eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f := by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
  · refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) <| mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).memHolder.coe_nnHolderNorm_eq_eHolderNorm, ← coe_div hc]
      refine HolderWith.eHolderNorm_le fun x₁ x₂ => ?_
      rw [coe_div hc, ← ENNReal.mul_div_right_comm,
        ENNReal.le_div_iff_mul_le (Or.inl <| coe_ne_zero.2 hc) <| Or.inl coe_ne_top,
        mul_comm, ← smul_eq_mul, ← ENNReal.smul_def, ← edist_smul₀, ← Pi.smul_apply,
        ← Pi.smul_apply]
      exact hf.smul.holderWith x₁ x₂
  · rw [← eHolderNorm_eq_top] at hf
    rw [hf, mul_top <| coe_ne_zero.2 hc, eHolderNorm_eq_top, MemHolder.smul_iff hc]
    rw [nnnorm_eq_zero] at hc
    intro h
    exact h.eHolderNorm_lt_top.ne hf
/-
**MemHolder.nnHolderNorm_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.nnHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass
 α Y] (hf : MemHolder r f) (c : α) : nnHolderNorm r (c • f) = ‖c‖₊ * nnHolderNor
m r f
参数：hf : MemHolder r f；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用引理 `MemHolder.coe_nnHolderNorm_eq_eHolderNorm`：MemHolder.coe_nnHolderNorm_eq
_eHolderNorm {r : Real>=0} {f : X -> Y} (hf : MemHolder r f) : (nnHolderNorm r f
 : Real>=0∞) = eHolderNorm r f
· 使用引理 `MemHolder.smul`：MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBo
undedSMul 𝕜 Y] {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f)
· 使用引理 `eHolderNorm_smul`：eHolderNorm_smul {α} [NormedRing α] [Module α Y] [Norm
SMulClass α Y] (c : α) : eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f
-/
lemma MemHolder.nnHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y]
    (hf : MemHolder r f) (c : α) :
    nnHolderNorm r (c • f) = ‖c‖₊ * nnHolderNorm r f := by
  rw [← ENNReal.coe_inj, coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm,
    hf.smul.coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_smul]
/-
**eHolderNorm_nsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eHolderNorm_nsmul [NormedSpace Real Y] (n : Nat) : eHolderNorm r (n • f) =
 n • eHolderNorm r f
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `eHolderNorm_smul`：eHolderNorm_smul {α} [NormedRing α] [Module α Y] [Norm
SMulClass α Y] (c : α) : eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.nnnorm_natCast`：∀ (n : ℕ), ‖↑n‖₊ = ↑n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eHolderNorm_nsmul [NormedSpace ℝ Y] (n : ℕ) :
    eHolderNorm r (n • f) = n • eHolderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), eHolderNorm_smul]
/-
**MemHolder.nnHolderNorm_nsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MemHolder.nnHolderNorm_nsmul [NormedSpace Real Y] (n : Nat) (hf : MemHolde
r r f) : nnHolderNorm r (n • f) = n • nnHolderNorm r f
参数：n : Nat；hf : MemHolder r f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `MemHolder.nnHolderNorm_smul`：MemHolder.nnHolderNorm_smul {α} [NormedRing
 α] [Module α Y] [NormSMulClass α Y] (hf : MemHolder r f) (c : α) : nnHolderNorm
 r (c • f) = ‖c‖₊…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.nnnorm_natCast`：∀ (n : ℕ), ‖↑n‖₊ = ↑n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MemHolder.nnHolderNorm_nsmul [NormedSpace ℝ Y] (n : ℕ) (hf : MemHolder r f) :
    nnHolderNorm r (n • f) = n • nnHolderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), hf.nnHolderNorm_smul]

end SeminormedAddCommGroup

