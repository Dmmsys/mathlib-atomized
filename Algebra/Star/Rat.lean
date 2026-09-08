/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Rat.Cast.Defs

/-!
# \*-ring structure on `ℚ` and `ℚ≥0`.
-/

public section

/-
**Rat.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instStarRing : StarRing Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Rat.instStarRing : StarRing ℚ := starRingOfComm
/-
**NNRat.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRat.instStarRing : StarRing Rat>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NNRat.instStarRing : StarRing ℚ≥0 := starRingOfComm
/-
**Rat.instTrivialStar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instTrivialStar : TrivialStar Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Rat.instTrivialStar : TrivialStar ℚ := ⟨fun _ ↦ rfl⟩
/-
**NNRat.instTrivialStar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRat.instTrivialStar : TrivialStar Rat>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NNRat.instTrivialStar : TrivialStar ℚ≥0 := ⟨fun _ ↦ rfl⟩

variable {R : Type*}

open MulOpposite

@[simp, norm_cast]
/-
**star_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：star_nnratCast [DivisionSemiring R] [StarRing R] (q : Rat>=0) : star (q : 
R) = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_nnratCast`：∀ {F : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Fu
nLike F α β] [inst_1 : DivisionSemiring α]   [inst_2 : DivisionSemiring β] [Ring
Hom…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `MulOpposite.unop_nnratCast`：unop_nnratCast [NNRatCast α] (q : Rat>=0) : 
unop (q : αᵐᵒᵖ) = q
-/
lemma star_nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) : star (q : R) = q :=
  (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]
/-
**star_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_ratCast [DivisionRing R] [StarRing R] (r : Rat) : star (r : R) = r
参数：r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `MulOpposite.unop_ratCast`：unop_ratCast [RatCast α] (q : Rat) : unop (q :
 αᵐᵒᵖ) = q
-/
theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)
