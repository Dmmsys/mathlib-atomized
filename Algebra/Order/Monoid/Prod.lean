/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Prod.Lex

/-! # Products of ordered monoids -/

public section

assert_not_exists MonoidWithZero

namespace Prod

variable {α β : Type*}

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
    [CommMonoid β] [Preorder β] [IsOrderedMonoid β] : IsOrderedMonoid (α × β) where
  mul_le_mul_left _ _ h _ := ⟨mul_le_mul_left h.1 _, mul_le_mul_left h.2 _⟩

@[to_additive]
/-
**Prod.instIsOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instIsOrderedCancelMonoid [CommMonoid α] [Preorder α] [IsOrderedCancelMono
id α] [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β] : IsOrderedCancelMon
oid (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.instIsOrderedMonoid`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMo
noid α] [inst_1 : Preorder α] [IsOrderedMonoid α] [inst_3 : CommMonoid β]   [ins
t_4 : Preorder…
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance instIsOrderedCancelMonoid
    [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α × β) :=
  { le_of_mul_le_mul_left :=
      fun _ _ _ h ↦ ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [LE β] [Mul α] [Mul β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
    ExistsMulOfLE (α × β) :=
  ⟨fun h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), Prod.ext hc hd⟩⟩

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [LE α] [CanonicallyOrderedMul α]
    [Mul β] [LE β] [CanonicallyOrderedMul β] : CanonicallyOrderedMul (α × β) where
  le_mul_self := fun _ _ ↦ le_def.mpr ⟨le_mul_self, le_mul_self⟩
  le_self_mul := fun _ _ ↦ le_def.mpr ⟨le_self_mul, le_self_mul⟩

namespace Lex

@[to_additive]
/-
**Prod.Lex.isOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：isOrderedMonoid [CommMonoid α] [Preorder α] [MulLeftStrictMono α] [CommMon
oid β] [Preorder β] [IsOrderedMonoid β] : IsOrderedMonoid (α ×ₗ β) where mul_le_
mul_left _ _ hxy z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Prod.Lex.le_iff`：le_iff [LT α] [LE β] {x y : α ×ₗ β} : x <= y ↔ (ofLex x
).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 <= (ofLex y).2
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance isOrderedMonoid [CommMonoid α] [Preorder α] [MulLeftStrictMono α]
    [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (α ×ₗ β) where
  mul_le_mul_left _ _ hxy z := (le_iff.1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left hxy _)
    (fun hxy => le_iff.2 <|
      Or.inr ⟨by simp only [ofLex_mul, fst_mul, hxy.1], mul_le_mul_left hxy.2 _⟩)

@[to_additive]
/-
**Prod.Lex.isOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Prod.Lex`。
形式化陈述：isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMono
id α] [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] : IsOrderedCance
lMonoid (α ×ₗ β) where le_of_mul_le_mul_left _ _ _ hxyz
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Prod.Lex.le_iff`：le_iff [LT α] [LE β] {x y : α ×ₗ β} : x <= y ↔ (ofLex x
).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 <= (ofLex y).2
· 使用定理 `lt_of_mul_lt_mul_left'`：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b
 c : α} (bc : a * b < a * c) : b < c
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α ×ₗ β) where
  le_of_mul_le_mul_left _ _ _ hxyz := (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

end Lex

end Prod

