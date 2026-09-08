/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.NNReal

/-!
# Hölder continuous functions

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `HolderOnWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `HolderWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `NNReal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotone in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

-/

@[expose] public section


variable {X Y Z : Type*}

open Filter Set Metric
open scoped NNReal ENNReal Topology

section EMetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- A function `f : X → Y` between two `PseudoEMetricSpace`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
/-
**HolderWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HolderWith (C r : Real>=0) (f : X -> Y) : Prop
参数：C r : Real>=0；f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` between two `PseudoEMetricSpace`s is Hölder continuous wi
th constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for
 all `x y : X`.
-/
def HolderWith (C r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x y, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

/-- A function `f : X → Y` between two `PseudoEMetricSpace`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0` on a set `s : Set X`, if `edist (f x) (f y) ≤ C * edist x y ^ r`
for all `x y ∈ s`. -/
/-
**HolderOnWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HolderOnWith (C r : Real>=0) (f : X -> Y) (s : Set X) : Prop
参数：C r : Real>=0；f : X -> Y；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` between two `PseudoEMetricSpace`s is Hölder continuous wi
th constant
`C : ℝ≥0` and exponent `r : ℝ≥0` on a set `s : Set X`, if `edist (f x) (f y) ≤ C
 * edist x y ^ r`
for all `x y ∈ s`.
-/
def HolderOnWith (C r : ℝ≥0) (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

@[simp]
/-
**holderOnWith_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：holderOnWith_empty (C r : Real>=0) (f : X -> Y) : HolderOnWith C r f ∅
参数：C r : Real>=0；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem holderOnWith_empty (C r : ℝ≥0) (f : X → Y) : HolderOnWith C r f ∅ := fun _ hx => hx.elim

@[simp]
/-
**holderOnWith_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：holderOnWith_singleton (C r : Real>=0) (f : X -> Y) (x : X) : HolderOnWith
 C r f {x}
参数：C r : Real>=0；f : X -> Y；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem holderOnWith_singleton (C r : ℝ≥0) (f : X → Y) (x : X) : HolderOnWith C r f {x} := by
  simp [HolderOnWith]
/-
**Set.Subsingleton.holderOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.holderOnWith {s : Set X} (hs : s.Subsingleton) (C r : Rea
l>=0) (f : X -> Y) : HolderOnWith C r f s
参数：hs : s.Subsingleton；C r : Real>=0；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `holderOnWith_empty`：holderOnWith_empty (C r : Real>=0) (f : X -> Y) : Ho
lderOnWith C r f ∅
· 使用定理 `holderOnWith_singleton`：holderOnWith_singleton (C r : Real>=0) (f : X ->
 Y) (x : X) : HolderOnWith C r f {x}
-/
theorem Set.Subsingleton.holderOnWith {s : Set X} (hs : s.Subsingleton) (C r : ℝ≥0) (f : X → Y) :
    HolderOnWith C r f s :=
  hs.induction_on (holderOnWith_empty C r f) (holderOnWith_singleton C r f)
/-
**holderOnWith_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : HolderOnWith C r f univ ↔
 HolderWith C r f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem holderOnWith_univ {C r : ℝ≥0} {f : X → Y} : HolderOnWith C r f univ ↔ HolderWith C r f := by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]

@[simp]
/-
**holderOnWith_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：holderOnWith_one {C : Real>=0} {f : X -> Y} {s : Set X} : HolderOnWith C 1
 f s ↔ LipschitzOnWith C f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem holderOnWith_one {C : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C 1 f s ↔ LipschitzOnWith C f s := by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]

alias ⟨_, LipschitzOnWith.holderOnWith⟩ := holderOnWith_one

@[simp]
/-
**holderWith_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：holderWith_one {C : Real>=0} {f : X -> Y} : HolderWith C 1 f ↔ LipschitzWi
th C f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用定理 `holderOnWith_one`：holderOnWith_one {C : Real>=0} {f : X -> Y} {s : Set X
} : HolderOnWith C 1 f s ↔ LipschitzOnWith C f s
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…
-/
theorem holderWith_one {C : ℝ≥0} {f : X → Y} : HolderWith C 1 f ↔ LipschitzWith C f :=
  holderOnWith_univ.symm.trans <| holderOnWith_one.trans lipschitzOnWith_univ

alias ⟨_, LipschitzWith.holderWith⟩ := holderWith_one
/-
**holderWith_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：holderWith_id : HolderWith 1 1 (id : X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.holderWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : Pseudo
EMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C : NNReal} {f : X → Y},   Lips
chitzWith C f …
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
-/
theorem holderWith_id : HolderWith 1 1 (id : X → X) :=
  LipschitzWith.id.holderWith
/-
**HolderWith.holderOnWith** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, HolderWith C r f → ∀ (s : Set 
X), HolderOnWith C r f s
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem HolderWith.holderOnWith {C r : ℝ≥0} {f : X → Y} (h : HolderWith C r f)
    (s : Set X) : HolderOnWith C r f s := fun x _ y _ => h x y

namespace HolderOnWith

variable {C r : ℝ≥0} {f : X → Y} {s t : Set X}

/-
**HolderOnWith.edist_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y in s) 
: edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r : Real)
参数：h : HolderOnWith C r f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ) :=
  h x hx y hy
/-
**HolderOnWith.edist_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x in s) (hy : y 
in s) {d : Real>=0∞} (hd : edist x y <= d) : edist (f x) (f y) <= (C : Real>=0∞)
 * d ^ (r : Real)
参数：h : HolderOnWith C r f s；hx : x in s；hy : y in s；hd : edist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HolderOnWith.edist_le`：edist_le (h : HolderOnWith C r f s) {x y : X} (hx
 : x in s) (hy : y in s) : edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r 
: Real)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) {d : ℝ≥0∞}
    (hd : edist x y ≤ d) : edist (f x) (f y) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (h.edist_le hx hy).trans <| by gcongr
/-
**HolderOnWith.comp** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：comp {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg : HolderOnWith Cg rg g
 t) {Cf rf : Real>=0} {f : X -> Y} (hf : HolderOnWith Cf rf f s) (hst : MapsTo f
 s t) : HolderOnWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f) s
参数：hg : HolderOnWith Cg rg g t；hf : HolderOnWith Cf rf f s；hst : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `HolderOnWith.edist_le_of_le`：edist_le_of_le (h : HolderOnWith C r f s) {
x y : X} (hx : x in s) (hy : y in s) {d : Real>=0∞} (hd : edist x y <= d) : edis
t (f x) (f y) <= …
· 使用定理 `HolderOnWith.edist_le`：edist_le (h : HolderOnWith C r f s) {x y : X} (hx
 : x in s) (hy : y in s) : edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r 
: Real)
-/
theorem comp {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : ℝ≥0}
    {f : X → Y} (hf : HolderOnWith Cf rf f s) (hst : MapsTo f s t) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s := by
  intro x hx y hy
  rw [ENNReal.coe_mul, mul_comm rg, NNReal.coe_mul, ENNReal.rpow_mul, mul_assoc,
    ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg, ← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)
/-
**HolderOnWith.comp_holderWith** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：comp_holderWith {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg : HolderOnW
ith Cg rg g t) {Cf rf : Real>=0} {f : X -> Y} (hf : HolderWith Cf rf f) (ht : fo
rall x, f x in t) : HolderWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f)
参数：hg : HolderOnWith Cg rg g t；hf : HolderWith Cf rf f；ht : forall x, f x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用定理 `HolderOnWith.comp`：comp {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg :
 HolderOnWith Cg rg g t) {Cf rf : Real>=0} {f : X -> Y} (hf : HolderOnWith Cf rf
 f s) (…
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…
-/
theorem comp_holderWith {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t)
    {Cf rf : ℝ≥0} {f : X → Y} (hf : HolderWith Cf rf f) (ht : ∀ x, f x ∈ t) :
    HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  holderOnWith_univ.mp <| hg.comp (hf.holderOnWith univ) fun x _ => ht x

/-- A Hölder continuous function is uniformly continuous -/
/-
**HolderOnWith.uniformContinuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {C r : NNReal} {f : X → Y}   {s : Set X}, HolderOnWith C r f
 s → 0 < r → UniformContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.uniformContinuousOn_iff`：uniformContinuousOn_iff [PseudoEMetricS
pace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s ↔ forall ε > 0, exist
s δ > 0, forall {a}, …
· 使用定理 `ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos`：tendsto_const_mul_rpow_
nhds_zero_of_pos {c : Real>=0∞} (hc : c != ∞) {y : Real} (hy : 0 < y) : Tendsto 
(fun x : Real>=0∞ => c * x ^ y) (𝓝 0)…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `ENNReal.nhds_zero_basis`：nhds_zero_basis : (𝓝 (0 : Real>=0∞)).HasBasis (
fun a : Real>=0∞ => 0 < a) fun a => Iio a
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `HolderOnWith.edist_le`：edist_le (h : HolderOnWith C r f s) {x y : X} (hx
 : x in s) (hy : y in s) : edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r 
: Real)

--- 原说明 ---
A Hölder continuous function is uniformly continuous
-/
protected theorem uniformContinuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) :
    UniformContinuousOn f s := by
  refine EMetric.uniformContinuousOn_iff.2 fun ε εpos => ?_
  have : Tendsto (fun d : ℝ≥0∞ => (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ENNReal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩
/-
**HolderOnWith.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {C r : NNReal} {f : X → Y}   {s : Set X}, HolderOnWith C r f
 s → 0 < r → ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousOn.continuousOn`：UniformContinuousOn.continuousOn [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} (h : UniformContinuousOn f
 s) : ContinuousOn f s
· 使用定理 `HolderOnWith.uniformContinuousOn`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal} {f : X → 
Y}   {s : Set X}, Hold…
-/
protected theorem continuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) : ContinuousOn f s :=
  (hf.uniformContinuousOn h0).continuousOn
/-
**HolderOnWith.mono** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {C r : NNReal} {f : X → Y}   {s t : Set X}, HolderOnWith C r
 f s → t ⊆ s → HolderOnWith C r f t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.edist_le`：edist_le (h : HolderOnWith C r f s) {x y : X} (hx
 : x in s) (hy : y in s) : edist (f x) (f y) <= (C : Real>=0∞) * edist x y ^ (r 
: Real)
-/
protected theorem mono (hf : HolderOnWith C r f s) (ht : t ⊆ s) : HolderOnWith C r f t :=
  fun _ hx _ hy => hf.edist_le (ht hx) (ht hy)
/-
**HolderOnWith.ediam_image_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : Real>=0∞} (hd : edia
m s <= d) : ediam (f '' s) <= (C : Real>=0∞) * d ^ (r : Real)
参数：hf : HolderOnWith C r f s；hd : ediam s <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ediam_image_le_iff`：ediam_image_le_iff {d : Real>=0∞} {f : α -> X
} {s : Set α} : ediam (f '' s) <= d ↔ forall x in s, forall y in s, edist (f x) 
(f y) <= d
· 使用定理 `HolderOnWith.edist_le_of_le`：edist_le_of_le (h : HolderOnWith C r f s) {
x y : X} (hx : x in s) (hy : y in s) {d : Real>=0∞} (hd : edist x y <= d) : edis
t (f x) (f y) <= …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
-/
theorem ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞} (hd : ediam s ≤ d) :
    ediam (f '' s) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  ediam_image_le_iff.2 fun _ hx _ hy =>
    hf.edist_le_of_le hx hy <| (edist_le_ediam_of_mem hx hy).trans hd
/-
**HolderOnWith.ediam_image_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：ediam_image_le (hf : HolderOnWith C r f s) : ediam (f '' s) <= (C : Real>=
0∞) * ediam s ^ (r : Real)
参数：hf : HolderOnWith C r f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.ediam_image_le_of_le`：ediam_image_le_of_le (hf : HolderOnWi
th C r f s) {d : Real>=0∞} (hd : ediam s <= d) : ediam (f '' s) <= (C : Real>=0∞
) * d ^ (r : Real)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ediam_image_le (hf : HolderOnWith C r f s) :
    ediam (f '' s) ≤ (C : ℝ≥0∞) * ediam s ^ (r : ℝ) :=
  hf.ediam_image_le_of_le le_rfl
/-
**HolderOnWith.ediam_image_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`
。
形式化陈述：ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t subseteq s) :
 ediam (f '' t) <= (C : Real>=0∞) * ediam t ^ (r : Real)
参数：hf : HolderOnWith C r f s；ht : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.ediam_image_le`：ediam_image_le (hf : HolderOnWith C r f s) 
: ediam (f '' s) <= (C : Real>=0∞) * ediam s ^ (r : Real)
· 使用定理 `HolderOnWith.mono`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal} {f : X → Y}   {s t : Set
 X}, Ho…
-/
theorem ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t ⊆ s) :
    ediam (f '' t) ≤ (C : ℝ≥0∞) * ediam t ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le
/-
**HolderOnWith.ediam_image_le_of_subset_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderO
nWith`。
形式化陈述：ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t subsete
q s) {d : Real>=0∞} (hd : ediam t <= d) : ediam (f '' t) <= (C : Real>=0∞) * d ^
 (r : Real)
参数：hf : HolderOnWith C r f s；ht : t subseteq s；hd : ediam t <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.ediam_image_le_of_le`：ediam_image_le_of_le (hf : HolderOnWi
th C r f s) {d : Real>=0∞} (hd : ediam s <= d) : ediam (f '' s) <= (C : Real>=0∞
) * d ^ (r : Real)
· 使用定理 `HolderOnWith.mono`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetric
Space X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal} {f : X → Y}   {s t : Set
 X}, Ho…
-/
theorem ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t ⊆ s) {d : ℝ≥0∞}
    (hd : ediam t ≤ d) : ediam (f '' t) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le_of_le hd
/-
**HolderOnWith.ediam_image_inter_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWit
h`。
形式化陈述：ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : Real>=0∞} (hd 
: ediam t <= d) : ediam (f '' (t inter s)) <= (C : Real>=0∞) * d ^ (r : Real)
参数：hf : HolderOnWith C r f s；hd : ediam t <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.ediam_image_le_of_subset_of_le`：ediam_image_le_of_subset_of
_le (hf : HolderOnWith C r f s) (ht : t subseteq s) {d : Real>=0∞} (hd : ediam t
 <= d) : ediam (f '' t) <= (C : R…
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞}
    (hd : ediam t ≤ d) : ediam (f '' (t ∩ s)) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  hf.ediam_image_le_of_subset_of_le inter_subset_right <|
    (ediam_mono inter_subset_left).trans hd
/-
**HolderOnWith.ediam_image_inter_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) : ediam (f ''
 (t inter s)) <= (C : Real>=0∞) * ediam t ^ (r : Real)
参数：hf : HolderOnWith C r f s；t : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.ediam_image_inter_le_of_le`：ediam_image_inter_le_of_le (hf 
: HolderOnWith C r f s) {d : Real>=0∞} (hd : ediam t <= d) : ediam (f '' (t inte
r s)) <= (C : Real>=0∞) * d ^…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) :
    ediam (f '' (t ∩ s)) ≤ (C : ℝ≥0∞) * ediam t ^ (r : ℝ) :=
  hf.ediam_image_inter_le_of_le le_rfl

/-- If a function is `(C₁, r)`-Hölder and `(C₂, s)`-Hölder, then it is
`(C₁ ^ t₁ * C₂ ^ t₂, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
/-
**HolderOnWith.interpolate** 是 Mathlib 中的一个引理，位于命名空间 `HolderOnWith`。
形式化陈述：interpolate {C₁ C₂ s t₁ t₂ : Real>=0} {A : Set X} (hf₁ : HolderOnWith C₁ r
 f A) (hf₂ : HolderOnWith C₂ s f A) (ht : t₁ + t₂ = 1) : HolderOnWith (C₁ ^ (t₁ 
: Real) * C₂ ^ (t₂ : Real)) (r * t₁ + s * t₂) f A
参数：hf₁ : HolderOnWith C₁ r f A；hf₂ : HolderOnWith C₂ s f A；ht : t₁ + t₂ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `ENNReal.rpow_add_of_nonneg`：rpow_add_of_nonneg {x : Real>=0∞} (y z : Rea
l) (hy : 0 <= y) (hz : 0 <= z) : x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is `(C₁, r)`-Hölder and `(C₂, s)`-Hölder, then it is
`(C₁ ^ t₁ * C₂ ^ t₂, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`.
-/
lemma interpolate {C₁ C₂ s t₁ t₂ : ℝ≥0} {A : Set X}
    (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (ht : t₁ + t₂ = 1) :
    HolderOnWith (C₁ ^ (t₁ : ℝ) * C₂ ^ (t₂ : ℝ)) (r * t₁ + s * t₂) f A := by
  intro x hx y hy
  calc edist (f x) (f y)
      = (edist (f x) (f y)) ^ (t₁ : ℝ) * (edist (f x) (f y)) ^ (t₂ : ℝ) := by
        simp [← ENNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]
    _ ≤ (C₁ * (edist x y) ^ (r : ℝ)) ^ (t₁ : ℝ) * (C₂ * (edist x y) ^ (s : ℝ)) ^ (t₂ : ℝ) := by
        nth_grw 1 [hf₁ x hx y hy, hf₂ x hx y hy]
    _ = ↑(C₁ ^ (t₁ : ℝ) * C₂ ^ (t₂ : ℝ)) * (edist x y) ^ (↑(r * t₁ + s * t₂) : ℝ) := by
        push_cast
        simp (discharger := positivity) only [ENNReal.mul_rpow_of_nonneg,
          ENNReal.rpow_add_of_nonneg, ENNReal.rpow_mul, ENNReal.coe_rpow_of_nonneg]
        ring

/-- If a function is Hölder over a bounded set, then it is bounded. -/
/-
**HolderOnWith.holderOnWith_zero_of_bounded** 是 Mathlib 中的一个引理，位于命名空间 `HolderOnW
ith`。
形式化陈述：holderOnWith_zero_of_bounded {C D : Real>=0} {A : Set X} (hA : forall x in
 A, forall y in A, edist x y <= D) (hf : HolderOnWith C r f A) : HolderOnWith (C
 * D ^ (r : Real)) 0 f A
参数：hA : forall x in A, forall y in A, edist x y <= D；hf : HolderOnWith C r f A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If a function is Hölder over a bounded set, then it is bounded.
-/
lemma holderOnWith_zero_of_bounded {C D : ℝ≥0} {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ D) (hf : HolderOnWith C r f A) :
    HolderOnWith (C * D ^ (r : ℝ)) 0 f A := by
  intro x hx y hy
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
  grw [hf x hx y hy, hA x hx y hy, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by simp)]

/-- If a function is `r`-Hölder over a bounded set, then it is also `s`-Hölder when `s ≤ r`. -/
/-
**HolderOnWith.of_le** 是 Mathlib 中的一个引理，位于命名空间 `HolderOnWith`。
形式化陈述：of_le {C D s : Real>=0} {A : Set X} (hA : forall x in A, forall y in A, ed
ist x y <= D) (hf : HolderOnWith C r f A) (hsr : s <= r) : HolderOnWith (C * D ^
 (r - s : Real)) s f A
参数：hA : forall x in A, forall y in A, edist x y <= D；hf : HolderOnWith C r f A；h
sr : s <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `HolderOnWith.holderOnWith_zero_of_bounded`：holderOnWith_zero_of_bounded 
{C D : Real>=0} {A : Set X} (hA : forall x in A, forall y in A, edist x y <= D) 
(hf : HolderOnWith C r f A) : H…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is `r`-Hölder over a bounded set, then it is also `s`-Hölder when 
`s ≤ r`.
-/
lemma of_le {C D s : ℝ≥0} {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ D) (hf : HolderOnWith C r f A) (hsr : s ≤ r) :
    HolderOnWith (C * D ^ (r - s : ℝ)) s f A := by
  obtain rfl | ht := eq_zero_or_pos s
  · simpa using hf.holderOnWith_zero_of_bounded hA
  have hr : 0 < r := ht.trans_le hsr
  rw [← NNReal.coe_le_coe] at hsr
  rw [← NNReal.coe_pos] at hr
  set θ₁ : ℝ≥0 := .mk (s / r) (by positivity)
  set θ₂ : ℝ≥0 := .mk (1 - s / r) (by simpa using div_le_one_of_le₀ hsr (by positivity))
  have hθ : θ₁ + θ₂ = 1 := by ext; simp [θ₁, θ₂]
  have hθt : r * θ₁ + 0 * θ₂ = s := by ext; simp [θ₁, mul_div_cancel₀ _ hr.ne']
  have hθC : C * D ^ (r - s : ℝ) = C ^ (θ₁ : ℝ) * (C * D ^ (r : ℝ)) ^ (θ₂ : ℝ) := by
    simp (discharger := positivity) only [NNReal.mul_rpow, ← mul_assoc,
      ← NNReal.rpow_add_of_nonneg, ← NNReal.rpow_mul, ← NNReal.coe_add, hθ, NNReal.coe_one,
      NNReal.rpow_one]
    congr
    simp [mul_sub, θ₂, mul_div_cancel₀ _ hr.ne']
  rw [hθC, ← hθt]
  exact hf.interpolate (hf.holderOnWith_zero_of_bounded hA) hθ
/-
**HolderOnWith.mono_const** 是 Mathlib 中的一个引理，位于命名空间 `HolderOnWith`。
形式化陈述：mono_const {C₁ C₂ : Real>=0} {A : Set X} (hf : HolderOnWith C₁ r f A) (hC 
: C₁ <= C₂) : HolderOnWith C₂ r f A
参数：hf : HolderOnWith C₁ r f A；hC : C₁ <= C₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
-/
lemma mono_const {C₁ C₂ : ℝ≥0} {A : Set X} (hf : HolderOnWith C₁ r f A)
    (hC : C₁ ≤ C₂) : HolderOnWith C₂ r f A := by
  intro x hx y hy
  grw [← hC]
  exact hf x hx y hy

/-- If a function is `(C, r)`-Hölder and `(C, s)`-Hölder,
then it is `(C, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
/-
**HolderOnWith.interpolate_const** 是 Mathlib 中的一个引理，位于命名空间 `HolderOnWith`。
形式化陈述：interpolate_const {C s t₁ t₂ : Real>=0} {A : Set X} (hf₁ : HolderOnWith C 
r f A) (hf₂ : HolderOnWith C s f A) (ht : t₁ + t₂ = 1) : HolderOnWith C (r * t₁ 
+ s * t₂) f A
参数：hf₁ : HolderOnWith C r f A；hf₂ : HolderOnWith C s f A；ht : t₁ + t₂ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HolderOnWith.interpolate`：interpolate {C₁ C₂ s t₁ t₂ : Real>=0} {A : Set
 X} (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (ht : t₁ + t₂ = 
1) : HolderOnW…

--- 原说明 ---
If a function is `(C, r)`-Hölder and `(C, s)`-Hölder,
then it is `(C, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`.
-/
lemma interpolate_const {C s t₁ t₂ : ℝ≥0} {A : Set X}
    (hf₁ : HolderOnWith C r f A) (hf₂ : HolderOnWith C s f A) (ht : t₁ + t₂ = 1) :
    HolderOnWith C (r * t₁ + s * t₂) f A := by
  convert! hf₁.interpolate hf₂ ht
  simp [← NNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]

variable (f) in
/-- For fixed `f : X → Y`, `A : Set X` and `C : ℝ≥0`, the set of all parameters `r : ℝ≥0` such that
`f` is `(C, r)`-Hölder on `A` is convex. -/
/-
**HolderOnWith._root_.convex_setOfPred_holderOnWith** 是 Mathlib 中的一个引理，位于命名空间 `H
olderOnWith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For fixed `f : X → Y`, `A : Set X` and `C : ℝ≥0`, the set of all parameters `r :
 ℝ≥0` such that
`f` is `(C, r)`-Hölder on `A` is convex.
-/
lemma _root_.convex_setOfPred_holderOnWith (C : ℝ≥0) (A : Set X) :
    Convex ℝ≥0 {r | HolderOnWith C r f A} := by
  intro r hr s hs _ _ _ _ ht
  rw [smul_eq_mul, smul_eq_mul, ← mul_comm r, ← mul_comm s]
  exact hr.interpolate_const hs ht

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderOnWith := _root_.convex_setOfPred_holderOnWith
/-
**HolderOnWith.of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `HolderOnWith`。
形式化陈述：of_le_of_le {C₁ C₂ s t : Real>=0} {A : Set X} (hf₁ : HolderOnWith C₁ r f A
) (hf₂ : HolderOnWith C₂ s f A) (hrt : r <= t) (hts : t <= s) : HolderOnWith (ma
x C₁ C₂) t f A
参数：hf₁ : HolderOnWith C₁ r f A；hf₂ : HolderOnWith C₂ s f A；hrt : r <= t；hts : t 
<= s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderOnWith.mono_const`：mono_const {C₁ C₂ : Real>=0} {A : Set X} (hf : 
HolderOnWith C₁ r f A) (hC : C₁ <= C₂) : HolderOnWith C₂ r f A
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `convex_setOfPred_holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : P
seudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] (f : X → Y) (C : NNReal)   
(A : Set X), Convex…
· 使用定理 `NNReal.Icc_subset_segment`：∀ {x y : NNReal}, Set.Icc x y ⊆ segment NNRea
l x y
-/
lemma of_le_of_le {C₁ C₂ s t : ℝ≥0} {A : Set X}
    (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (hrt : r ≤ t)
    (hts : t ≤ s) : HolderOnWith (max C₁ C₂) t f A := by
  replace hf₁ := hf₁.mono_const (le_max_left C₁ C₂)
  replace hf₂ := hf₂.mono_const (le_max_right C₁ C₂)
  exact convex_setOfPred_holderOnWith f (max C₁ C₂) A |>.segment_subset hf₁ hf₂
    (NNReal.Icc_subset_segment ⟨hrt, hts⟩)

end HolderOnWith

namespace HolderWith

variable {C r : ℝ≥0} {f : X → Y}

/-
**HolderWith.restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：restrict_iff {s : Set X} : HolderWith C r (s.domRestrict f) ↔ HolderOnWith
 C r f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrict_iff {s : Set X} : HolderWith C r (s.domRestrict f) ↔ HolderOnWith C r f s := by
  simp [HolderWith, HolderOnWith]

protected alias ⟨_, _root_.HolderOnWith.holderWith⟩ := restrict_iff
/-
**HolderWith.edist_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：edist_le (h : HolderWith C r f) (x y : X) : edist (f x) (f y) <= (C : Real
>=0∞) * edist x y ^ (r : Real)
参数：h : HolderWith C r f；x y : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_le (h : HolderWith C r f) (x y : X) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ) :=
  h x y
/-
**HolderWith.edist_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：edist_le_of_le (h : HolderWith C r f) {x y : X} {d : Real>=0∞} (hd : edist
 x y <= d) : edist (f x) (f y) <= (C : Real>=0∞) * d ^ (r : Real)
参数：h : HolderWith C r f；hd : edist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.edist_le_of_le`：edist_le_of_le (h : HolderOnWith C r f s) {
x y : X} (hx : x in s) (hy : y in s) {d : Real>=0∞} (hd : edist x y <= d) : edis
t (f x) (f y) <= …
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…
· 使用定理 `trivial`：True
-/
theorem edist_le_of_le (h : HolderWith C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (h.holderOnWith univ).edist_le_of_le trivial trivial hd
/-
**HolderWith.comp** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：comp {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg rg g) {Cf rf : Rea
l>=0} {f : X -> Y} (hf : HolderWith Cf rf f) : HolderWith (Cg * Cf ^ (rg : Real)
) (rg * rf) (g ∘ f)
参数：hg : HolderWith Cg rg g；hf : HolderWith Cf rf f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.comp_holderWith`：comp_holderWith {Cg rg : Real>=0} {g : Y -
> Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : Real>=0} {f : X -> Y} (h
f : HolderWith Cf …
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…
· 使用定理 `trivial`：True
-/
theorem comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0} {f : X → Y}
    (hf : HolderWith Cf rf f) : HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  (hg.holderOnWith univ).comp_holderWith hf fun _ => trivial
/-
**HolderWith.comp_holderOnWith** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：comp_holderOnWith {Cg rg : Real>=0} {g : Y -> Z} (hg : HolderWith Cg rg g)
 {Cf rf : Real>=0} {f : X -> Y} {s : Set X} (hf : HolderOnWith Cf rf f s) : Hold
erOnWith (Cg * Cf ^ (rg : Real)) (rg * rf) (g ∘ f) s
参数：hg : HolderWith Cg rg g；hf : HolderOnWith Cf rf f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.comp`：comp {Cg rg : Real>=0} {g : Y -> Z} {t : Set Y} (hg :
 HolderOnWith Cg rg g t) {Cf rf : Real>=0} {f : X -> Y} (hf : HolderOnWith Cf rf
 f s) (…
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…
· 使用定理 `trivial`：True
-/
theorem comp_holderOnWith {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0}
    {f : X → Y} {s : Set X} (hf : HolderOnWith Cf rf f s) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
  (hg.holderOnWith univ).comp hf fun _ _ => trivial

/-- A Hölder continuous function is uniformly continuous -/
/-
**HolderWith.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, HolderWith C r f → 0 < r → Uni
formContinuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuousOn_univ`：uniformContinuousOn_univ {f : α -> β} : Unifor
mContinuousOn f univ ↔ UniformContinuous f
· 使用定理 `HolderOnWith.uniformContinuousOn`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal} {f : X → 
Y}   {s : Set X}, Hold…
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…

--- 原说明 ---
A Hölder continuous function is uniformly continuous
-/
protected theorem uniformContinuous (hf : HolderWith C r f) (h0 : 0 < r) : UniformContinuous f :=
  uniformContinuousOn_univ.mp <| (hf.holderOnWith univ).uniformContinuousOn h0
/-
**HolderWith.continuous** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, HolderWith C r f → 0 < r → Con
tinuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `HolderWith.uniformContinuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Ps
eudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}
, HolderWith C r f…
-/
protected theorem continuous (hf : HolderWith C r f) (h0 : 0 < r) : Continuous f :=
  (hf.uniformContinuous h0).continuous
/-
**HolderWith.ediam_image_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：ediam_image_le (hf : HolderWith C r f) (s : Set X) : ediam (f '' s) <= (C 
: Real>=0∞) * ediam s ^ (r : Real)
参数：hf : HolderWith C r f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ediam_image_le_iff`：ediam_image_le_iff {d : Real>=0∞} {f : α -> X
} {s : Set α} : ediam (f '' s) <= d ↔ forall x in s, forall y in s, edist (f x) 
(f y) <= d
· 使用定理 `HolderWith.edist_le_of_le`：edist_le_of_le (h : HolderWith C r f) {x y : 
X} {d : Real>=0∞} (hd : edist x y <= d) : edist (f x) (f y) <= (C : Real>=0∞) * 
d ^ (r : Real)
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
-/
theorem ediam_image_le (hf : HolderWith C r f) (s : Set X) :
    ediam (f '' s) ≤ (C : ℝ≥0∞) * ediam s ^ (r : ℝ) :=
  ediam_image_le_iff.2 fun _ hx _ hy => hf.edist_le_of_le <| edist_le_ediam_of_mem hx hy
/-
**HolderWith.const** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：const {y : Y} : HolderWith C r (Function.const X y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma const {y : Y} :
    HolderWith C r (Function.const X y) := fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]
/-
**HolderWith.zero** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：zero [Zero Y] : HolderWith C r (0 : X -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HolderWith.const`：const {y : Y} : HolderWith C r (Function.const X y)
-/
lemma zero [Zero Y] : HolderWith C r (0 : X → Y) := .const
/-
**HolderWith.of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：of_isEmpty [IsEmpty X] : HolderWith C r f
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_isEmpty [IsEmpty X] : HolderWith C r f := isEmptyElim
/-
**HolderWith.mono** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：mono {C' : Real>=0} (hf : HolderWith C r f) (h : C <= C') : HolderWith C' 
r f
参数：hf : HolderWith C r f；h : C <= C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma mono {C' : ℝ≥0} (hf : HolderWith C r f) (h : C ≤ C') :
    HolderWith C' r f :=
  fun x₁ x₂ ↦ (hf x₁ x₂).trans (by gcongr)

/-- If a function is `(C₁, r)`-Hölder and `(C₂, s)`-Hölder, then it is
`(C₁ ^ t₁ * C₂ ^ t₂, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
/-
**HolderWith.interpolate** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：interpolate {C₁ C₂ s t₁ t₂ : Real>=0} (hf₁ : HolderWith C₁ r f) (hf₂ : Hol
derWith C₂ s f) (ht : t₁ + t₂ = 1) : HolderWith (C₁ ^ (t₁ : Real) * C₂ ^ (t₂ : R
eal)) (r * t₁ + s * t₂) f
参数：hf₁ : HolderWith C₁ r f；hf₂ : HolderWith C₂ s f；ht : t₁ + t₂ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用引理 `HolderOnWith.interpolate`：interpolate {C₁ C₂ s t₁ t₂ : Real>=0} {A : Set
 X} (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (ht : t₁ + t₂ = 
1) : HolderOnW…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a function is `(C₁, r)`-Hölder and `(C₂, s)`-Hölder, then it is
`(C₁ ^ t₁ * C₂ ^ t₂, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`.
-/
lemma interpolate {C₁ C₂ s t₁ t₂ : ℝ≥0}
    (hf₁ : HolderWith C₁ r f) (hf₂ : HolderWith C₂ s f) (ht : t₁ + t₂ = 1) :
    HolderWith (C₁ ^ (t₁ : ℝ) * C₂ ^ (t₂ : ℝ)) (r * t₁ + s * t₂) f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate (holderOnWith_univ.2 hf₂) ht)

/-- If a function is Hölder over a bounded space, then it is bounded. -/
/-
**HolderWith.holderWith_zero_of_bounded** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：holderWith_zero_of_bounded {C D : Real>=0} (h : forall x y : X, edist x y 
<= D) (hf : HolderWith C r f) : HolderWith (C * D ^ (r : Real)) 0 f
参数：h : forall x y : X, edist x y <= D；hf : HolderWith C r f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用引理 `HolderOnWith.holderOnWith_zero_of_bounded`：holderOnWith_zero_of_bounded 
{C D : Real>=0} {A : Set X} (hA : forall x in A, forall y in A, edist x y <= D) 
(hf : HolderOnWith C r f A) : H…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a function is Hölder over a bounded space, then it is bounded.
-/
lemma holderWith_zero_of_bounded {C D : ℝ≥0}
    (h : ∀ x y : X, edist x y ≤ D) (hf : HolderWith C r f) :
    HolderWith (C * D ^ (r : ℝ)) 0 f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf).holderOnWith_zero_of_bounded (fun x _ y _ ↦ h x y))

/-- If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder when `s ≤ r`. -/
/-
**HolderWith.of_le** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：of_le {C D s : Real>=0} (h : forall x y : X, edist x y <= D) (hf : HolderW
ith C r f) (hsr : s <= r) : HolderWith (C * D ^ (r - s : Real)) s f
参数：h : forall x y : X, edist x y <= D；hf : HolderWith C r f；hsr : s <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用引理 `HolderOnWith.of_le`：of_le {C D s : Real>=0} {A : Set X} (hA : forall x i
n A, forall y in A, edist x y <= D) (hf : HolderOnWith C r f A) (hsr : s <= r) :
 HolderO…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder whe
n `s ≤ r`.
-/
lemma of_le {C D s : ℝ≥0} (h : ∀ x y : X, edist x y ≤ D) (hf : HolderWith C r f) (hsr : s ≤ r) :
    HolderWith (C * D ^ (r - s : ℝ)) s f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf).of_le (fun x _ y _ ↦ h x y) hsr)

/-- If a function is `(C, r)`-Hölder and `(C, s)`-Hölder,
then it is `(C, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
/-
**HolderWith.interpolate_const** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：interpolate_const {C s t₁ t₂ : Real>=0} (hf₁ : HolderWith C r f) (hf₂ : Ho
lderWith C s f) (ht : t₁ + t₂ = 1) : HolderWith C (r * t₁ + s * t₂) f
参数：hf₁ : HolderWith C r f；hf₂ : HolderWith C s f；ht : t₁ + t₂ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用引理 `HolderOnWith.interpolate_const`：interpolate_const {C s t₁ t₂ : Real>=0} 
{A : Set X} (hf₁ : HolderOnWith C r f A) (hf₂ : HolderOnWith C s f A) (ht : t₁ +
 t₂ = 1) : HolderOnW…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a function is `(C, r)`-Hölder and `(C, s)`-Hölder,
then it is `(C, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`.
-/
lemma interpolate_const {C s t₁ t₂ : ℝ≥0}
    (hf₁ : HolderWith C r f) (hf₂ : HolderWith C s f) (ht : t₁ + t₂ = 1) :
    HolderWith C (r * t₁ + s * t₂) f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate_const (holderOnWith_univ.2 hf₂) ht)

variable (f) in
/-- For fixed `f : X → Y` and `C : ℝ≥0`, the set of all parameters `r : ℝ≥0` such that
`f` is `(C, r)`-Hölder is convex. -/
/-
**HolderWith._root_.convex_setOfPred_holderWith** 是 Mathlib 中的一个引理，位于命名空间 `Holde
rWith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For fixed `f : X → Y` and `C : ℝ≥0`, the set of all parameters `r : ℝ≥0` such th
at
`f` is `(C, r)`-Hölder is convex.
-/
lemma _root_.convex_setOfPred_holderWith (C : ℝ≥0) :
    Convex ℝ≥0 {r | HolderWith C r f} := by
  simp_rw [← holderOnWith_univ]
  exact convex_setOfPred_holderOnWith f C _

@[deprecated (since := "2026-07-09")]
alias _root_.convex_setOf_holderWith := _root_.convex_setOfPred_holderWith
/-
**HolderWith.of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：of_le_of_le {C₁ C₂ s t : Real>=0} (hf₁ : HolderWith C₁ r f) (hf₂ : HolderW
ith C₂ s f) (hrt : r <= t) (hts : t <= s) : HolderWith (max C₁ C₂) t f
参数：hf₁ : HolderWith C₁ r f；hf₂ : HolderWith C₂ s f；hrt : r <= t；hts : t <= s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `holderOnWith_univ`：holderOnWith_univ {C r : Real>=0} {f : X -> Y} : Hold
erOnWith C r f univ ↔ HolderWith C r f
· 使用引理 `HolderOnWith.of_le_of_le`：of_le_of_le {C₁ C₂ s t : Real>=0} {A : Set X} 
(hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (hrt : r <= t) (hts 
: t <= s) : Ho…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma of_le_of_le {C₁ C₂ s t : ℝ≥0}
    (hf₁ : HolderWith C₁ r f) (hf₂ : HolderWith C₂ s f) (hrt : r ≤ t)
    (hts : t ≤ s) : HolderWith (max C₁ C₂) t f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).of_le_of_le (holderOnWith_univ.2 hf₂) hrt hts)

end HolderWith

end EMetric

section PseudoMetric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {s : Set X} {x y : X}

namespace HolderOnWith

/-
**HolderOnWith.nndist_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：nndist_le_of_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s) {d
 : Real>=0} (hd : nndist x y <= d) : nndist (f x) (f y) <= C * d ^ (r : Real)
参数：hf : HolderOnWith C r f s；hx : x in s；hy : y in s；hd : nndist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `HolderOnWith.edist_le_of_le`：edist_le_of_le (h : HolderOnWith C r f s) {
x y : X} (hx : x in s) (hy : y in s) {d : Real>=0∞} (hd : edist x y <= d) : edis
t (f x) (f y) <= …
-/
theorem nndist_le_of_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ≥0} (hd : nndist x y ≤ d) : nndist (f x) (f y) ≤ C * d ^ (r : ℝ) := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le hx hy
  rwa [edist_nndist, ENNReal.coe_le_coe]
/-
**HolderOnWith.nndist_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：nndist_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s) : nndist
 (f x) (f y) <= C * nndist x y ^ (r : Real)
参数：hf : HolderOnWith C r f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.nndist_le_of_le`：nndist_le_of_le (hf : HolderOnWith C r f s
) (hx : x in s) (hy : y in s) {d : Real>=0} (hd : nndist x y <= d) : nndist (f x
) (f y) <= C * d ^…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem nndist_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s) :
    nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
  hf.nndist_le_of_le hx hy le_rfl
/-
**HolderOnWith.dist_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：dist_le_of_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s) {d :
 Real} (hd : dist x y <= d) : dist (f x) (f y) <= C * d ^ (r : Real)
参数：hf : HolderOnWith C r f s；hx : x in s；hy : y in s；hd : dist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `HolderOnWith.nndist_le_of_le`：nndist_le_of_le (hf : HolderOnWith C r f s
) (hx : x in s) (hy : y in s) {d : Real>=0} (hd : nndist x y <= d) : nndist (f x
) (f y) <= C * d ^…
-/
theorem dist_le_of_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ} (hd : dist x y ≤ d) : dist (f x) (f y) ≤ C * d ^ (r : ℝ) := by
  lift d to ℝ≥0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd ⊢
  norm_cast at hd ⊢
  exact hf.nndist_le_of_le hx hy hd
/-
**HolderOnWith.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderOnWith`。
形式化陈述：dist_le (hf : HolderOnWith C r f s) (hx : x in s) (hy : y in s) : dist (f 
x) (f y) <= C * dist x y ^ (r : Real)
参数：hf : HolderOnWith C r f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.dist_le_of_le`：dist_le_of_le (hf : HolderOnWith C r f s) (h
x : x in s) (hy : y in s) {d : Real} (hd : dist x y <= d) : dist (f x) (f y) <= 
C * d ^ (r : Rea…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem dist_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  hf.dist_le_of_le hx hy le_rfl

end HolderOnWith

namespace HolderWith

/-
**HolderWith.nndist_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d : Real>=0} (hd : nndi
st x y <= d) : nndist (f x) (f y) <= C * d ^ (r : Real)
参数：hf : HolderWith C r f；hd : nndist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.nndist_le_of_le`：nndist_le_of_le (hf : HolderOnWith C r f s
) (hx : x in s) (hy : y in s) {d : Real>=0} (hd : nndist x y <= d) : nndist (f x
) (f y) <= C * d ^…
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ≥0} (hd : nndist x y ≤ d) :
    nndist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  (hf.holderOnWith univ).nndist_le_of_le (mem_univ x) (mem_univ y) hd
/-
**HolderWith.nndist_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：nndist_le (hf : HolderWith C r f) (x y : X) : nndist (f x) (f y) <= C * nn
dist x y ^ (r : Real)
参数：hf : HolderWith C r f；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderWith.nndist_le_of_le`：nndist_le_of_le (hf : HolderWith C r f) {x y
 : X} {d : Real>=0} (hd : nndist x y <= d) : nndist (f x) (f y) <= C * d ^ (r : 
Real)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem nndist_le (hf : HolderWith C r f) (x y : X) :
    nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
  hf.nndist_le_of_le le_rfl
/-
**HolderWith.dist_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : Real} (hd : dist x y 
<= d) : dist (f x) (f y) <= C * d ^ (r : Real)
参数：hf : HolderWith C r f；hd : dist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderOnWith.dist_le_of_le`：dist_le_of_le (hf : HolderOnWith C r f s) (h
x : x in s) (hy : y in s) {d : Real} (hd : dist x y <= d) : dist (f x) (f y) <= 
C * d ^ (r : Rea…
· 使用定理 `HolderWith.holderOnWith`：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoE
MetricSpace X] [inst_1 : PseudoEMetricSpace Y] {C r : NNReal}   {f : X → Y}, Hol
derWith C r f…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ} (hd : dist x y ≤ d) :
    dist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  (hf.holderOnWith univ).dist_le_of_le (mem_univ x) (mem_univ y) hd
/-
**HolderWith.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `HolderWith`。
形式化陈述：dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) <= C * dist x
 y ^ (r : Real)
参数：hf : HolderWith C r f；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HolderWith.dist_le_of_le`：dist_le_of_le (hf : HolderWith C r f) {x y : X
} {d : Real} (hd : dist x y <= d) : dist (f x) (f y) <= C * d ^ (r : Real)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  hf.dist_le_of_le le_rfl

end HolderWith

end PseudoMetric

section Metric

variable [PseudoMetricSpace X] [MetricSpace Y] {r : ℝ≥0} {f : X → Y}

@[simp]
/-
**holderWith_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：holderWith_zero_iff : HolderWith 0 r f ↔ forall x₁ x₂, f x₁ = f x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
lemma holderWith_zero_iff : HolderWith 0 r f ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  refine ⟨fun h x₁ x₂ => ?_, fun h x₁ x₂ => h x₁ x₂ ▸ ?_⟩
  · specialize h x₁ x₂
    simp [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at h
    assumption
  · simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

end Metric

section SeminormedAddCommGroup

variable [PseudoMetricSpace X] [SeminormedAddCommGroup Y] {C C' r : ℝ≥0} {f g : X → Y}

namespace HolderWith

/-
**HolderWith.add** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：add (hf : HolderWith C r f) (hg : HolderWith C' r g) : HolderWith (C + C')
 r (f + g)
参数：hf : HolderWith C r f；hg : HolderWith C' r g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `edist_add_add_le`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] (a₁
 a₂ b₁ b₂ : E),   edist (a₁ + a₂) (b₁ + b₂) ≤ edist a₁ b₁ + edist a₂ b₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma add (hf : HolderWith C r f) (hg : HolderWith C' r g) :
    HolderWith (C + C') r (f + g) := by
  intro x₁ x₂
  simp only [Pi.add_apply, ENNReal.coe_add]
  grw [edist_add_add_le, hf x₁ x₂, hg x₁ x₂]
  rw [add_mul]
/-
**HolderWith.smul** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y] [IsBoundedSMul α Y
] (a : α) (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (a • f)
参数：a : α；hf : HolderWith C r f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `edist_smul_le`：edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) <
= ‖s‖₊ • edist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y] [IsBoundedSMul α Y] (a : α)
    (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (a • f) := fun x₁ x₂ => by
  refine edist_smul_le _ _ _ |>.trans ?_
  rw [ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul, mul_comm (C : ℝ≥0∞), mul_assoc]
  gcongr
  exact hf x₁ x₂
/-
**HolderWith.smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `HolderWith`。
形式化陈述：smul_iff {α} [SeminormedRing α] [Module α Y] [NormSMulClass α Y] (a : α) (
ha : ‖a‖₊ != 0) : HolderWith (C * ‖a‖₊) r (a • f) ↔ HolderWith C r f
参数：a : α；ha : ‖a‖₊ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `edist_smul₀`：edist_smul₀ (s : α) (x y : β) : edist (s • x) (s • y) = ‖s‖
₊ • edist x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_le_mul_iff_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * 
b ≤ a * c ↔ b ≤ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_iff {α} [SeminormedRing α] [Module α Y] [NormSMulClass α Y] (a : α)
    (ha : ‖a‖₊ ≠ 0) :
    HolderWith (C * ‖a‖₊) r (a • f) ↔ HolderWith C r f := by
  simp_rw [HolderWith, ENNReal.coe_mul, Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul,
    mul_comm (C : ℝ≥0∞), mul_assoc,
    ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top, mul_comm]

end HolderWith

end SeminormedAddCommGroup

