/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Basic Results about Star on Pi Types

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Pi/Defs.lean`.
-/

public section


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Star (f i)] [∀ i, TrivialStar (f i)] : TrivialStar (∀ i, f i) where
  star_trivial _ := funext fun _ => star_trivial _
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, InvolutiveStar (f i)] : InvolutiveStar (∀ i, f i) where
  star_involutive _ := funext fun _ => star_star _
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Mul (f i)] [∀ i, StarMul (f i)] : StarMul (∀ i, f i) where
  star_mul _ _ := funext fun _ => star_mul _ _
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] : StarAddMonoid (∀ i, f i) where
  star_add _ _ := funext fun _ => star_add _ _
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalSemiring (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i)
  where star_add _ _ := funext fun _ => star_add _ _
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type w} [∀ i, SMul R (f i)] [Star R] [∀ i, Star (f i)]
    [∀ i, StarModule R (f i)] : StarModule R (∀ i, f i) where
  star_smul r x := funext fun i => star_smul r (x i)
/-
**Pi.single_star** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：single_star [forall i, AddMonoid (f i)] [forall i, StarAddMonoid (f i)] [D
ecidableEq I] (i : I) (a : f i) : Pi.single i (star a) = star (Pi.single i a)
参数：f i；f i；i : I；a : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_op`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} [in
st : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decidable
Eq…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

open scoped ComplexConjugate

@[simp]
/-
**Pi.conj_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：conj_apply {ι : Type*} {α : ι -> Type*} [forall i, CommSemiring (α i)] [fo
rall i, StarRing (α i)] (f : forall i, α i) (i : ι) : conj f i = conj (f i)
参数：α i；α i；f : forall i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma conj_apply {ι : Type*} {α : ι → Type*} [∀ i, CommSemiring (α i)] [∀ i, StarRing (α i)]
    (f : ∀ i, α i) (i : ι) : conj f i = conj (f i) := rfl

end Pi

namespace Function

/-
**Function.update_star** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_star [forall i, Star (f i)] [DecidableEq I] (h : forall i : I, f i)
 (i : I) (a : f i) : Function.update (star h) i (star a) = star (Function.update
 h i a)
参数：f i；h : forall i : I, f i；i : I；a : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.apply_update`：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι
 -> Sort*} (f : forall i, α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j :
 ι) : f j (…
-/
theorem update_star [∀ i, Star (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun _ => star) h i a j).symm
/-
**Function.star_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：star_sumElim {I J α : Type*} (x : I -> α) (y : J -> α) [Star α] : star (Su
m.elim x y) = Sum.elim (star x) (star y)
参数：x : I -> α；y : J -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem star_sumElim {I J α : Type*} (x : I → α) (y : J → α) [Star α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

end Function

