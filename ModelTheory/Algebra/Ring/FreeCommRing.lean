/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.RingTheory.FreeCommRing

/-!
# Making a term in the language of rings from an element of the FreeCommRing

This file defines the function `FirstOrder.Ring.termOfFreeCommRing` which constructs a
`Language.ring.Term α` from an element of `FreeCommRing α`.

The theorem `FirstOrder.Ring.realize_termOfFreeCommRing` shows that the term constructed when
realized in a ring `R` is equal to the lift of the element of `FreeCommRing α` to `R`.
-/

@[expose] public section

namespace FirstOrder

namespace Ring

open Language

variable {α : Type*}

section

attribute [local instance] compatibleRingOfRing

set_option backward.privateInPublic true in
/-
**FirstOrder.Ring.exists_term_realize_eq_freeCommRing** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing α) :
    ∃ t : Language.ring.Term α,
      (t.realize FreeCommRing.of : FreeCommRing α) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all⟩)

end

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Make a `Language.ring.Term α` from an element of `FreeCommRing α` -/
/-
**FirstOrder.Ring.termOfFreeCommRing** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Ring`
。
形式化陈述：termOfFreeCommRing (p : FreeCommRing α) : Language.ring.Term α
参数：p : FreeCommRing α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.ModelTheory.Algebra.Ring.FreeCommRing.0.FirstOrder.Ring
.exists_term_realize_eq_freeCommRing`：∀ {α : Type u_1} (p : FreeCommRing α), ∃ t
, FirstOrder.Language.Term.realize FreeCommRing.of t = p

--- 原说明 ---
Make a `Language.ring.Term α` from an element of `FreeCommRing α`
-/
noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.ring.Term α :=
  Classical.choose (exists_term_realize_eq_freeCommRing p)

variable {R : Type*} [CommRing R] [CompatibleRing R]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FirstOrder.Ring.realize_termOfFreeCommRing** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Ring`。
形式化陈述：realize_termOfFreeCommRing (p : FreeCommRing α) (v : α -> R) : (termOfFree
CommRing p).realize v = FreeCommRing.lift v p
参数：p : FreeCommRing α；v : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.ModelTheory.Algebra.Ring.FreeCommRing.0.FirstOrder.Ring
.exists_term_realize_eq_freeCommRing`：∀ {α : Type u_1} (p : FreeCommRing α), ∃ t
, FirstOrder.Language.Term.realize FreeCommRing.of t = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Ring.termOfFreeCommRing.eq_1`：∀ {α : Type u_1} (p : FreeCommR
ing α), FirstOrder.Ring.termOfFreeCommRing p = Classical.choose ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FreeCommRing.lift_of`：lift_of (x : α) : lift f (of x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Ring.CompatibleRing.funMap_add`：∀ {R : Type u_2} {inst : Add 
R} {inst_1 : Mul R} {inst_2 : Neg R} {inst_3 : One R} {inst_4 : Zero R}   [self 
: FirstOrder.Ring.CompatibleRin…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `FirstOrder.Ring.CompatibleRing.funMap_mul`：∀ {R : Type u_2} {inst : Add 
R} {inst_1 : Mul R} {inst_2 : Neg R} {inst_3 : One R} {inst_4 : Zero R}   [self 
: FirstOrder.Ring.CompatibleRin…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `FirstOrder.Ring.CompatibleRing.funMap_neg`：∀ {R : Type u_2} {inst : Add 
R} {inst_1 : Mul R} {inst_2 : Neg R} {inst_3 : One R} {inst_4 : Zero R}   [self 
: FirstOrder.Ring.CompatibleRin…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `FirstOrder.Ring.CompatibleRing.funMap_zero`：∀ {R : Type u_2} {inst : Add
 R} {inst_1 : Mul R} {inst_2 : Neg R} {inst_3 : One R} {inst_4 : Zero R}   [self
 : FirstOrder.Ring.CompatibleRin…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FirstOrder.Ring.CompatibleRing.funMap_one`：∀ {R : Type u_2} {inst : Add 
R} {inst_1 : Mul R} {inst_2 : Neg R} {inst_3 : One R} {inst_4 : Zero R}   [self 
: FirstOrder.Ring.CompatibleRin…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
（共 31 条，此处仅展示前 30 条）
-/
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → R) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  rw [termOfFreeCommRing]
  conv_rhs => rw [← Classical.choose_spec (exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (exists_term_realize_eq_freeCommRing p) with
  | var _ => simp
  | func f a ih =>
    cases f <;>
    simp [ih]

end Ring

end FirstOrder

