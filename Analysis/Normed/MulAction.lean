/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.ENNReal.Action
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Algebra

/-!
# Lemmas for `IsBoundedSMul` over normed additive groups

Lemmas which hold only in `NormedSpace α β` are provided in another file.

Notably we prove that `NonUnitalSeminormedRing`s have bounded actions by left- and right-
multiplication. This allows downstream files to write general results about `IsBoundedSMul`, and
then deduce `const_mul` and `mul_const` results as an immediate corollary.
-/

public section


variable {α β : Type*}

section SeminormedAddGroup

variable [SeminormedAddGroup α] [SeminormedAddGroup β] [SMulZeroClass α β]
variable [IsBoundedSMul α β] {r : α} {x : β}

@[bound]
/-
**norm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
参数：r : α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
-/
theorem norm_smul_le (r : α) (x : β) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ := by
  simpa [smul_zero] using dist_smul_pair r 0 x

@[bound]
/-
**nnnorm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
参数：r : α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
-/
theorem nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ ≤ ‖r‖₊ * ‖x‖₊ :=
  norm_smul_le _ _

@[bound]
/-
**enorm_smul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_smul_le : ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
-/
lemma enorm_smul_le : ‖r • x‖ₑ ≤ ‖r‖ₑ * ‖x‖ₑ := by
  simpa [enorm, ← ENNReal.coe_mul] using nnnorm_smul_le ..
/-
**dist_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) <= ‖s‖ * dist x y
参数：s : α；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_neg_add`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a 
b : E), dist a b = ‖-a + b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
-/
theorem dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) ≤ ‖s‖ * dist x y := by
  simpa only [dist_eq_norm_neg_add, add_zero, norm_neg] using dist_smul_pair s x y
/-
**nndist_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_smul_le (s : α) (x y : β) : nndist (s • x) (s • y) <= ‖s‖₊ * nndist
 x y
参数：s : α；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_smul_le`：dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) <= ‖
s‖ * dist x y
-/
theorem nndist_smul_le (s : α) (x y : β) : nndist (s • x) (s • y) ≤ ‖s‖₊ * nndist x y :=
  dist_smul_le s x y
/-
**lipschitzWith_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ (s • · : β -> β)
参数：s : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
· 使用定理 `dist_smul_le`：dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) <= ‖
s‖ * dist x y
-/
theorem lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ (s • · : β → β) :=
  lipschitzWith_iff_dist_le_mul.2 <| dist_smul_le _
/-
**edist_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) <= ‖s‖₊ • edist x 
y
参数：s : α；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzWith_smul`：lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ (s •
 · : β -> β)
-/
theorem edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) ≤ ‖s‖₊ • edist x y :=
  lipschitzWith_smul s x y

end SeminormedAddGroup

/-- Left multiplication is bounded. -/
/-
**NonUnitalSeminormedRing.isBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonUnitalSeminormedRing.isBoundedSMul [NonUnitalSeminormedRing α] : IsBoun
dedSMul α α where dist_smul_pair' x y₁ y₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c

--- 原说明 ---
Left multiplication is bounded.
-/
instance NonUnitalSeminormedRing.isBoundedSMul [NonUnitalSeminormedRing α] :
    IsBoundedSMul α α where
  dist_smul_pair' x y₁ y₂ := by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y

/-- Right multiplication is bounded. -/
/-
**NonUnitalSeminormedRing.isBoundedSMulOpposite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonUnitalSeminormedRing.isBoundedSMulOpposite [NonUnitalSeminormedRing α] 
: IsBoundedSMul αᵐᵒᵖ α where dist_smul_pair' x y₁ y₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c

--- 原说明 ---
Right multiplication is bounded.
-/
instance NonUnitalSeminormedRing.isBoundedSMulOpposite [NonUnitalSeminormedRing α] :
    IsBoundedSMul αᵐᵒᵖ α where
  dist_smul_pair' x y₁ y₂ := by
    simpa [sub_mul, dist_eq_norm, mul_comm] using! norm_mul_le (y₁ - y₂) x.unop
  dist_pair_smul' x₁ x₂ y := by
    simpa [mul_sub, dist_eq_norm, mul_comm] using! norm_mul_le y (x₁ - x₂).unop

section SeminormedRing

variable [SeminormedRing α] [SeminormedAddCommGroup β] [Module α β]

/-
**IsBoundedSMul.of_norm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedSMul.of_norm_smul_le (h : forall (r : α) (x : β), ‖r • x‖ <= ‖r‖ 
* ‖x‖) : IsBoundedSMul α β
参数：h : forall (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
theorem IsBoundedSMul.of_norm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖ ≤ ‖r‖ * ‖x‖) :
    IsBoundedSMul α β :=
  { dist_smul_pair' := fun a b₁ b₂ => by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂)
    dist_pair_smul' := fun a₁ a₂ b => by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }
/-
**IsBoundedSMul.of_enorm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedSMul.of_enorm_smul_le (h : forall (r : α) (x : β), ‖r • x‖ₑ <= ‖r
‖ₑ * ‖x‖ₑ) : IsBoundedSMul α β
参数：h : forall (r : α) (x : β), ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_norm_smul_le`：IsBoundedSMul.of_norm_smul_le (h : forall
 (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖) : IsBoundedSMul α β
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem IsBoundedSMul.of_enorm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖ₑ ≤ ‖r‖ₑ * ‖x‖ₑ) :
    IsBoundedSMul α β :=
  .of_norm_smul_le (by simpa [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using! h)
/-
**IsBoundedSMul.of_nnnorm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedSMul.of_nnnorm_smul_le (h : forall (r : α) (x : β), ‖r • x‖₊ <= ‖
r‖₊ * ‖x‖₊) : IsBoundedSMul α β
参数：h : forall (r : α) (x : β), ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_norm_smul_le`：IsBoundedSMul.of_norm_smul_le (h : forall
 (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖) : IsBoundedSMul α β
-/
theorem IsBoundedSMul.of_nnnorm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖₊ ≤ ‖r‖₊ * ‖x‖₊) :
    IsBoundedSMul α β := .of_norm_smul_le h

end SeminormedRing

section NormSMulClass

/-- Mixin class for scalar-multiplication actions with a strictly multiplicative norm, i.e.
`‖r • x‖ = ‖r‖ * ‖x‖`. -/
/-
**NormSMulClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → (β : Type u_4) → [Norm α] → [Norm β] → [SMul α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mixin class for scalar-multiplication actions with a strictly multiplicative nor
m, i.e.
`‖r • x‖ = ‖r‖ * ‖x‖`.
-/
class NormSMulClass (α β : Type*) [Norm α] [Norm β] [SMul α β] : Prop where
  protected norm_smul (r : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
/-
**norm_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r : α) (x : β)
 : ‖r • x‖ = ‖r‖ * ‖x‖
参数：r : α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormSMulClass.norm_smul`：∀ {α : Type u_3} {β : Type u_4} {inst : Norm α}
 {inst_1 : Norm β} {inst_2 : SMul α β} [self : NormSMulClass α β] (r : α)   (x :
 β), ‖r • x‖ …
-/
lemma norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r : α) (x : β) :
    ‖r • x‖ = ‖r‖ * ‖x‖ :=
  NormSMulClass.norm_smul r x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormMulClass.toNormSMulClass [Norm α] [Mul α] [NormMulClass α] :
    NormSMulClass α α where
  norm_smul := norm_mul
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormMulClass.toNormSMulClass_op [SeminormedRing α] [NormMulClass α] :
    NormSMulClass αᵐᵒᵖ α where
  norm_smul a b := mul_comm ‖b‖ ‖a‖ ▸ norm_mul b a.unop

/-- Mixin class for scalar-multiplication actions with a strictly multiplicative norm, i.e.
`‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ`. -/
/-
**ENormSMulClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → (β : Type u_4) → [ENorm α] → [ENorm β] → [SMul α β] → Pro
p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mixin class for scalar-multiplication actions with a strictly multiplicative nor
m, i.e.
`‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ`.
-/
class ENormSMulClass (α β : Type*) [ENorm α] [ENorm β] [SMul α β] : Prop where
  protected enorm_smul (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
/-
**enorm_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α β] (r : α) (x 
: β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
参数：r : α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENormSMulClass.enorm_smul`：∀ {α : Type u_3} {β : Type u_4} {inst : ENorm
 α} {inst_1 : ENorm β} {inst_2 : SMul α β} [self : ENormSMulClass α β]   (r : α)
 (x : β), ‖r • …
-/
lemma enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α β] (r : α) (x : β) :
    ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ :=
  ENormSMulClass.enorm_smul r x

variable [SeminormedRing α] [SeminormedAddGroup β] [SMul α β]
/-
**NormSMulClass.of_nnnorm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormSMulClass.of_nnnorm_smul (h : forall (r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ 
* ‖x‖₊) : NormSMulClass α β where norm_smul r b
参数：h : forall (r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem NormSMulClass.of_nnnorm_smul (h : ∀ (r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊) :
    NormSMulClass α β where
  norm_smul r b := congr_arg NNReal.toReal (h r b)

variable [NormSMulClass α β]
/-
**nnnorm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
参数：r : α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
-/
theorem nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊ :=
  NNReal.eq <| norm_smul r x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : ENormSMulClass α β where
  enorm_smul r x := by simp [enorm, nnnorm_smul]
/-
**Pi.instNormSMulClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instNormSMulClass {ι : Type*} {β : ι -> Type*} [Fintype ι] [forall i, S
eminormedAddGroup (β i)] [forall i, SMul α (β i)] [forall i, NormSMulClass α (β 
i)] : NormSMulClass α (Π i, β i) where norm_smul r x
参数：β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NNReal.mul_finset_sup`：mul_finset_sup {α} (r : Real>=0) (s : Finset α) (
f : α -> Real>=0) : r * s.sup f = s.sup fun a => r * f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Pi.instNormSMulClass {ι : Type*} {β : ι → Type*} [Fintype ι]
    [∀ i, SeminormedAddGroup (β i)] [∀ i, SMul α (β i)] [∀ i, NormSMulClass α (β i)] :
    NormSMulClass α (Π i, β i) where
  norm_smul r x := by
    simp [nnnorm_def, ← coe_nnnorm, nnnorm_smul, ← NNReal.coe_mul, NNReal.mul_finset_sup]
/-
**Prod.instNormSMulClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instNormSMulClass {γ : Type*} [SeminormedAddGroup γ] [SMul α γ] [Norm
SMulClass α γ] : NormSMulClass α (β × γ) where norm_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NNReal.mul_sup`：mul_sup (a b c : Real>=0) : a * (b ⊔ c) = a * b ⊔ a * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Prod.instNormSMulClass {γ : Type*} [SeminormedAddGroup γ] [SMul α γ] [NormSMulClass α γ] :
    NormSMulClass α (β × γ) where
  norm_smul := fun r ⟨v₁, v₂⟩ ↦ by simp only [smul_def, ← coe_nnnorm, nnnorm_def,
    nnnorm_smul r, ← NNReal.coe_mul, NNReal.mul_sup]
/-
**ULift.instNormSMulClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instNormSMulClass : NormSMulClass α (ULift β) where norm_smul r v
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
-/
instance ULift.instNormSMulClass : NormSMulClass α (ULift β) where
  norm_smul r v := norm_smul r v.down

end NormSMulClass

section NormSMulClassModule

variable [SeminormedRing α] [SeminormedAddCommGroup β] [Module α β] [NormSMulClass α β]

/-
**dist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (
x y : X) : dist (c • x) (c • y) = dist x y
参数：c : M；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * dist x y := by
  simp_rw [dist_eq_norm, (norm_smul s (x - y)).symm, smul_sub]
/-
**nndist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M)
 (x y : X) : nndist (c • x) (c • y) = nndist x y
参数：c : M；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem nndist_smul₀ (s : α) (x y : β) : nndist (s • x) (s • y) = ‖s‖₊ * nndist x y :=
  NNReal.eq <| dist_smul₀ s x y
/-
**edist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_smul₀ (s : α) (x y : β) : edist (s • x) (s • y) = ‖s‖₊ • edist x y := by
  simp only [edist_nndist, nndist_smul₀, ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]
/-
**NormSMulClass.toIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormSMulClass.toIsBoundedSMul : IsBoundedSMul α β
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_norm_smul_le`：IsBoundedSMul.of_norm_smul_le (h : forall
 (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖) : IsBoundedSMul α β
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
-/
instance NormSMulClass.toIsBoundedSMul : IsBoundedSMul α β :=
  .of_norm_smul_le fun r x ↦ (norm_smul r x).le

end NormSMulClassModule

section NormedDivisionRing

variable [NormedDivisionRing α] [SeminormedAddGroup β]
variable [MulActionWithZero α β] [IsBoundedSMul α β]

/-- For a normed division ring, a sub-multiplicative norm is actually strictly multiplicative.

This is not an instance as it forms a loop with `NormSMulClass.toIsBoundedSMul`. -/
/-
**NormedDivisionRing.toNormSMulClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NormedDivisionRing.toNormSMulClass : NormSMulClass α β where norm_smul r x
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
For a normed division ring, a sub-multiplicative norm is actually strictly multi
plicative.

This is not an instance as it forms a loop with `NormSMulClass.toIsBoundedSMul`.
-/
lemma NormedDivisionRing.toNormSMulClass : NormSMulClass α β where
  norm_smul r x := by
    by_cases h : r = 0
    · simp [h, zero_smul α x]
    · refine le_antisymm (norm_smul_le r x) ?_
      calc
      ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖ := by rw [inv_smul_smul₀ h]
      _ ≤ ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) := by gcongr; apply norm_smul_le
      _ = ‖r • x‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (mt norm_eq_zero.1 h), one_mul]

end NormedDivisionRing

section NormedDivisionRingModule
variable [NormedDivisionRing α] [SeminormedAddCommGroup β] [Module α β] [NormSMulClass α β]

/-
**Metric.smul_image_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.smul_image_ball {s : α} (hs : s != 0) (x : β) (ε : Real) : (s • ·) 
'' ball x ε = ball (s • x) (‖s‖ * ε)
参数：hs : s != 0；x : β；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `lt_of_mul_lt_mul_of_nonneg_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1
 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulReflectLT α],   a * b < a * 
c → 0 ≤ a → b < c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Metric.smul_image_ball {s : α} (hs : s ≠ 0) (x : β) (ε : ℝ) :
    (s • ·) '' ball x ε = ball (s • x) (‖s‖ * ε) := by
  ext p
  simp_rw [Set.mem_image, mem_ball]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_lt_mul_of_pos_left h1 (norm_pos_iff.mpr hs)
  · refine fun h ↦ ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine lt_of_mul_lt_mul_of_nonneg_left ?_ (norm_nonneg s)
    rw [← dist_smul₀]
    simpa [smul_smul, hs] using h
/-
**Metric.smul_image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.smul_image_closedBall {s : α} (hs : s != 0) (x : β) (ε : Real) : (s
 • ·) '' closedBall x ε = closedBall (s • x) (‖s‖ * ε)
参数：hs : s != 0；x : β；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_mul_le_mul_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : 
Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulReflectLE α],   a * b ≤ a * c →
 0 < a → b ≤ c
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Metric.smul_image_closedBall {s : α} (hs : s ≠ 0) (x : β) (ε : ℝ) :
    (s • ·) '' closedBall x ε = closedBall (s • x) (‖s‖ * ε) := by
  ext p
  simp_rw [Set.mem_image, mem_closedBall]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
  · refine fun h ↦ ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine le_of_mul_le_mul_of_pos_left ?_ (norm_pos_iff.mpr hs)
    rw [← dist_smul₀]
    simpa [smul_smul, hs] using h
/-
**Metric.smul_image_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.smul_image_sphere {s : α} (hs : s != 0) (x : β) (ε : Real) : (s • ·
) '' sphere x ε = sphere (s • x) (‖s‖ * ε)
参数：hs : s != 0；x : β；ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Metric.smul_image_ball`：Metric.smul_image_ball {s : α} (hs : s != 0) (x 
: β) (ε : Real) : (s • ·) '' ball x ε = ball (s • x) (‖s‖ * ε)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.smul_image_closedBall`：Metric.smul_image_closedBall {s : α} (hs :
 s != 0) (x : β) (ε : Real) : (s • ·) '' closedBall x ε = closedBall (s • x) (‖s
‖ * ε)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Metric.smul_image_sphere {s : α} (hs : s ≠ 0) (x : β) (ε : ℝ) :
    (s • ·) '' sphere x ε = sphere (s • x) (‖s‖ * ε) := by
  simp_rw [← Metric.closedBall_sdiff_ball, Set.image_sdiff (smul_right_injective β hs),
    smul_image_ball hs, smul_image_closedBall hs]

end NormedDivisionRingModule

