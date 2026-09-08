/-
Copyright (c) 2024 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Algebra.Order.Archimedean.Hom  -- shake: keep (Subsingleton (ℝ →+*o ℝ)), cf. lean#13417
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.CompleteField

/-!
# Uniqueness of ring homomorphisms to the real numbers

This file contains results about ring homomorphisms to `ℝ`.

## Main results

* `Real.nonemptyOrderRingHom`: For any archimedean ordered field `α`, there exists
  a monotone ring homomorphism `α →+*o ℝ`.
* `Real.RingHom.unique`: There exists no nontrivial ring homomorphism `ℝ →+* ℝ`.
-/

public section

-- Note that we already know `Subsingleton (α →+*o ℝ)` here.
-- We intentionally do not define instance `Unique (α →+*o ℝ)` to avoid instance diamonds.
/-
**Real.nonemptyOrderRingHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.nonemptyOrderRingHom (α : Type*) [Field α] [LinearOrder α] [IsStrictO
rderedRing α] [Archimedean α] : Nonempty (α ->+*o Real)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Real.nonemptyOrderRingHom (α : Type*)
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] : Nonempty (α →+*o ℝ) :=
  ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingHom α ℝ⟩
/-
**ringHom_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringHom_monotone {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMono
id R] [Ring S] [LinearOrder S] [IsOrderedAddMonoid S] [PosMulMono S] (hR : foral
l r : R, 0 <= r -> IsSquare r) (f : R ->+* S) : Monotone f
参数：hR : forall r : R, 0 <= r -> IsSquare r；f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_iff_map_nonneg`：monotone_iff_map_nonneg [iamhc : AddMonoidHomCl
ass F α β] : Monotone (f : α -> β) ↔ forall a, 0 <= a -> 0 <= f a
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ringHom_monotone {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [Ring S] [LinearOrder S] [IsOrderedAddMonoid S] [PosMulMono S]
    (hR : ∀ r : R, 0 ≤ r → IsSquare r) (f : R →+* S) : Monotone f :=
  (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

/-- There exists no nontrivial ring homomorphism `ℝ →+* ℝ`. -/
/-
**Real.RingHom.unique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.RingHom.unique : Unique (Real ->+* Real) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There exists no nontrivial ring homomorphism `ℝ →+* ℝ`.
-/
instance Real.RingHom.unique : Unique (ℝ →+* ℝ) where
  default := RingHom.id ℝ
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (ℝ →+*o ℝ) _
      ⟨f, ringHom_monotone (fun _ ↦ Real.isSquare_iff.mpr) f⟩ default)

@[simp]
/-
**Real.ringHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.ringHom_apply {F : Type*} [FunLike F Real Real] [RingHomClass F Real 
Real] (f : F) (r : Real) : f r = r
参数：f : F；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem Real.ringHom_apply {F : Type*} [FunLike F ℝ ℝ] [RingHomClass F ℝ ℝ] (f : F) (r : ℝ) :
    f r = r :=
  DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r
