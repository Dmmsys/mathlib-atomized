/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Ordered monoid instances on the space of germs of a function at a filter

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* `IsOrderedCancelMonoid` and `IsOrderedCancelAddMonoid`.

## Tags

filter, germ
-/

public section

namespace Filter.Germ

variable {α : Type*} {β : Type*} {l : Filter α}

@[to_additive]
/-
**Filter.Germ.instIsOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIsOrderedMonoid [CommMonoid β] [Preorder β] [IsOrderedMonoid β] : IsOr
deredMonoid (Germ l β) where mul_le_mul_left f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance instIsOrderedMonoid [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (Germ l β) where
  mul_le_mul_left f g := inductionOn₂ f g fun _ _ H h ↦ inductionOn h fun _ ↦ H.mono
    fun _ H ↦ by dsimp; gcongr

@[to_additive]
/-
**Filter.Germ.instIsOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIsOrderedCancelMonoid [CommMonoid β] [Preorder β] [IsOrderedCancelMono
id β] : IsOrderedCancelMonoid (Germ l β) where le_of_mul_le_mul_left f g h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Filter.Germ.inductionOn₃`：inductionOn₃ (f : Germ l β) (g : Germ l γ) (h 
: Germ l δ) {p : Germ l β -> Germ l γ -> Germ l δ -> Prop} (H : forall (f : α ->
 β) (g : α -> …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
-/
instance instIsOrderedCancelMonoid [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (Germ l β) where
  le_of_mul_le_mul_left f g h := inductionOn₃ f g h fun _ _ _ H ↦ H.mono
    fun _ ↦ le_of_mul_le_mul_left'

@[to_additive]
/-
**Filter.Germ.instCanonicallyOrderedMul** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instCanonicallyOrderedMul [Mul β] [LE β] [CanonicallyOrderedMul β] : Canon
icallyOrderedMul (Germ l β) where le_mul_self x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedMul.toExistsMulOfLE`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : LE α} [self : CanonicallyOrderedMul α], ExistsMulOfLE α
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_mul_self`：le_mul_self : a <= b * a
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
-/
instance instCanonicallyOrderedMul [Mul β] [LE β] [CanonicallyOrderedMul β] :
    CanonicallyOrderedMul (Germ l β) where
  le_mul_self x y := inductionOn₂ x y fun _ _ ↦ Eventually.of_forall fun _ ↦ le_mul_self
  le_self_mul x y := inductionOn₂ x y fun _ _ ↦ Eventually.of_forall fun _ ↦ le_self_mul

end Filter.Germ

