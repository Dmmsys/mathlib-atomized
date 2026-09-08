/-
Copyright (c) 2024 Jujian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Kernel of a ring homomorphism as a two-sided ideal

In this file we define the kernel of a ring homomorphism `f : R → S` as a two-sided ideal of `R`.

We put this in a separate file so that we could import it in
`Mathlib/RingTheory/SimpleRing/Basic.lean` without importing any finiteness result.
-/

@[expose] public section

namespace TwoSidedIdeal

section ker

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
variable (f : F)

/--
The kernel of a ring homomorphism, as a two-sided ideal.
-/
/-
**TwoSidedIdeal.ker** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ker : TwoSidedIdeal R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a ring homomorphism, as a two-sided ideal.
-/
def ker : TwoSidedIdeal R :=
  .ofRingCon
  -- TODO: use `RingCon.ker`
  { r := fun x y ↦ f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all
    add' := by intro; simp_all }

@[simp]
/-
**TwoSidedIdeal.ker_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ker_ringCon {x y : R} : (ker f).ringCon x y ↔ f x = f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ker_ringCon {x y : R} : (ker f).ringCon x y ↔ f x = f y := Iff.rfl
/-
**TwoSidedIdeal.mem_ker** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_ker {x : R} : x in ker f ↔ f x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用引理 `TwoSidedIdeal.ker_ringCon`：ker_ringCon {x y : R} : (ker f).ringCon x y ↔
 f x = f y
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ker {x : R} : x ∈ ker f ↔ f x = 0 := by
  rw [mem_iff, ker_ringCon, map_zero]
/-
**TwoSidedIdeal.ker_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ker_eq_bot : ker f = ⊥ ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
lemma ker_eq_bot : ker f = ⊥ ↔ Function.Injective f := by
  fconstructor
  · intro h x y hxy
    simpa [h, rel_iff, mem_bot, sub_eq_zero] using show (ker f).ringCon x y from hxy
  · exact fun h ↦ eq_bot_iff.2 fun x hx => h hx

section NonAssocRing

variable {R : Type*} [NonAssocRing R]

/--
The kernel of the ring homomorphism `R → R⧸I` is `I`.
-/
@[simp]
/-
**TwoSidedIdeal.ker_ringCon_mk'** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：ker_ringCon_mk' (I : TwoSidedIdeal R) : ker I.ringCon.mk' = I
参数：I : TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `TwoSidedIdeal.rel_iff`：rel_iff (x y : R) : I.ringCon x y ↔ x - y in I
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
The kernel of the ring homomorphism `R → R⧸I` is `I`.
-/
lemma ker_ringCon_mk' (I : TwoSidedIdeal R) : ker I.ringCon.mk' = I :=
  le_antisymm
    (fun _ h => by simpa using I.rel_iff _ _ |>.1 (Quotient.eq'.1 h))
    (fun _ h => Quotient.sound' <| I.rel_iff _ _ |>.2 (by simpa using h))

end NonAssocRing

end ker

end TwoSidedIdeal

