/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Complement

/-!

## HNN Extensions of Groups

This file defines the HNN extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`,
subgroups `A` and `B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such
that for any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the canonical map
from `G` into the `HNNExtension`. This construction is named after Graham Higman, Bernhard Neumann
and Hanna Neumann.

## Main definitions

- `HNNExtension G A B φ` : The HNN Extension of a group `G`, where `A` and `B` are subgroups and `φ`
  is an isomorphism between `A` and `B`.
- `HNNExtension.of` : The canonical embedding of `G` into `HNNExtension G A B φ`.
- `HNNExtension.t` : The stable letter of the HNN extension.
- `HNNExtension.lift` : Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t`
- `HNNExtension.of_injective` : The canonical embedding `G →* HNNExtension G A B φ` is injective.
- `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` : Britton's Lemma. If an element of
  `G` is represented by a reduced word, then this reduced word does not contain `t`.

-/

@[expose] public section

assert_not_exists Field

open Monoid Coprod Multiplicative Subgroup Function

/-- The relation we quotient the coproduct by to form an `HNNExtension`. -/
/-
**HNNExtension.con** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : C
on (G ∗ Multiplicative Int)
参数：G : Type*；A B : Subgroup G；φ : A ≃* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation we quotient the coproduct by to form an `HNNExtension`.
-/
def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) :
    Con (G ∗ Multiplicative ℤ) :=
  conGen (fun x y => ∃ (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

/-- The HNN Extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`, subgroups `A` and
`B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such that for
any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the canonical
map from `G` into the `HNNExtension`. -/
/-
**HNNExtension** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HNNExtension (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type 
_
参数：G : Type*；A B : Subgroup G；φ : A ≃* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The HNN Extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`, sub
groups `A` and
`B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such t
hat for
any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the can
onical
map from `G` into the `HNNExtension`.
-/
def HNNExtension (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*}
  [Group H] {M : Type*} [Monoid M]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (HNNExtension G A B φ) := by
  delta HNNExtension; infer_instance

namespace HNNExtension

/-- The canonical embedding `G →* HNNExtension G A B φ` -/
/-
**HNNExtension.of** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension`。
形式化陈述：of : G ->* HNNExtension G A B φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding `G →* HNNExtension G A B φ`
-/
def of : G →* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

/-- The stable letter of the `HNNExtension` -/
/-
**HNNExtension.t** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension`。
形式化陈述：t : HNNExtension G A B φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stable letter of the `HNNExtension`
-/
def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)
/-
**HNNExtension.t_mul_of** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：t_mul_of (a : A) : t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) 
* t
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Con.eq`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {a b : M}, ↑a = ↑b ↔
 c a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem t_mul_of (a : A) :
    t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) * t :=
  (Con.eq _).2 <| ConGen.Rel.of _ _ <| ⟨a, by simp⟩
/-
**HNNExtension.of_mul_t** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：of_mul_t (b : B) : (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.sym
m b : G)
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.t_mul_of`：t_mul_of (a : A) : t * (of (a : G) : HNNExtension
 G A B φ) = of (φ a : G) * t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_mul_t (b : B) :
    (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.symm b : G) := by
  rw [t_mul_of]; simp
/-
**HNNExtension.equiv_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：equiv_eq_conj (a : A) : (of (φ a : G) : HNNExtension G A B φ) = t * of (a 
: G) * t⁻¹
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.t_mul_of`：t_mul_of (a : A) : t * (of (a : G) : HNNExtension
 G A B φ) = of (φ a : G) * t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_eq_conj (a : A) :
    (of (φ a : G) : HNNExtension G A B φ) = t * of (a : G) * t⁻¹ := by
  rw [t_mul_of]; simp
/-
**HNNExtension.equiv_symm_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：equiv_symm_eq_conj (b : B) : (of (φ.symm b : G) : HNNExtension G A B φ) = 
t⁻¹ * of (b : G) * t
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `HNNExtension.of_mul_t`：of_mul_t (b : B) : (of (b : G) : HNNExtension G A
 B φ) * t = t * of (φ.symm b : G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_symm_eq_conj (b : B) :
    (of (φ.symm b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t := by
  rw [mul_assoc, of_mul_t]; simp
/-
**HNNExtension.inv_t_mul_of** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：inv_t_mul_of (b : B) : t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.s
ymm b : G) * t⁻¹
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.equiv_symm_eq_conj`：equiv_symm_eq_conj (b : B) : (of (φ.sym
m b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_t_mul_of (b : B) :
    t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.symm b : G) * t⁻¹ := by
  rw [equiv_symm_eq_conj]; simp
/-
**HNNExtension.of_mul_inv_t** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：of_mul_inv_t (a : A) : (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * o
f (φ a : G)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.equiv_eq_conj`：equiv_eq_conj (a : A) : (of (φ a : G) : HNNE
xtension G A B φ) = t * of (a : G) * t⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_mul_inv_t (a : A) :
    (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * of (φ a : G) := by
  rw [equiv_eq_conj]; simp [mul_assoc]

/-- Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t` -/
/-
**HNNExtension.lift** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension`。
形式化陈述：lift (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x)
 : HNNExtension G A B φ ->* H
参数：f : G ->* H；x : H；hx : forall a : A, x * f ↑a = f (φ a : G) * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t`
-/
def lift (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ →* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le.2 <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HNNExtension.lift_t** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：lift_t (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * 
x) : lift f x hx t = x
参数：f : G ->* H；x : H；hx : forall a : A, x * f ↑a = f (φ a : G) * x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_t (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    lift f x hx t = x := by
  delta HNNExtension; simp [lift, t]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HNNExtension.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：lift_of (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) *
 x) (g : G) : lift f x hx (of g) = f g
参数：f : G ->* H；x : H；hx : forall a : A, x * f ↑a = f (φ a : G) * x；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) (g : G) :
    lift f x hx (of g) = f g := by
  delta HNNExtension; simp [lift, of]

@[ext high]
/-
**HNNExtension.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：hom_ext {f g : HNNExtension G A B φ ->* M} (hg : f.comp of = g.comp of) (h
t : f t = g t) : f = g
参数：hg : f.comp of = g.comp of；ht : f t = g t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.cancel_right`：MonoidHom.cancel_right [MulOne M] [MulOne N] [Mu
lOne P] {g₁ g₂ : N ->* P} {f : M ->* N} (hf : Function.Surjective f) : g₁.comp f
 = g₂.comp f…
· 使用定理 `Con.mk'_surjective`：∀ {M : Type u_1} [inst : MulOneClass M] {c : Con M},
 Function.Surjective ⇑c.mk'
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
· 使用定理 `MonoidHom.ext_mint`：ext_mint {f g : Multiplicative Int ->* M} (h1 : f (o
fAdd 1) = g (ofAdd 1)) : f = g
-/
theorem hom_ext {f g : HNNExtension G A B φ →* M}
    (hg : f.comp of = g.comp of) (ht : f t = g t) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.hom_ext hg (MonoidHom.ext_mint ht)

set_option backward.isDefEq.respectTransparency false in
@[elab_as_elim]
/-
**HNNExtension.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：induction_on {motive : HNNExtension G A B φ -> Prop} (x : HNNExtension G A
 B φ) (of : forall g, motive (of g)) (t : motive t) (mul : forall x y, motive x 
-> motive y -> motive (x * y)) (inv : forall x, motive x -> motive x⁻¹) : motive
 x
参数：x : HNNExtension G A B φ；of : forall g, motive (of g)；t : motive t；mul : fora
ll x y, motive x -> motive y -> motive (x * y)；inv : forall x, motive x -> motiv
e x⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidHom.codRestrict_apply`：∀ {M : Type u_1} {N : Type u_2} [inst : Mul
OneClass M] [inst_1 : MulOneClass N] {S : Type u_5} [inst_2 : SetLike S N]   [in
st_3 : SubmonoidC…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `HNNExtension.equiv_eq_conj`：equiv_eq_conj (a : A) : (of (φ a : G) : HNNE
xtension G A B φ) = t * of (a : G) * t⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HNNExtension.hom_ext`：hom_ext {f g : HNNExtension G A B φ ->* M} (hg : f
.comp of = g.comp of) (ht : f t = g t) : f = g
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `HNNExtension.lift_of`：lift_of (f : G ->* H) (x : H) (hx : forall a : A, 
x * f ↑a = f (φ a : G) * x) (g : G) : lift f x hx (of g) = f g
· 使用定理 `MonoidHom.CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type 
u_3} {inst : Monoid M} {inst_1 : Monoid N} {inst_2 : Monoid P} {φ : M →* N}   {ψ
 : N →* P} {χ : ou…
· 使用定理 `HNNExtension.lift_t`：lift_t (f : G ->* H) (x : H) (hx : forall a : A, x 
* f ↑a = f (φ a : G) * x) : lift f x hx t = x
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem induction_on {motive : HNNExtension G A B φ → Prop}
    (x : HNNExtension G A B φ) (of : ∀ g, motive (of g))
    (t : motive t) (mul : ∀ x y, motive x → motive y → motive (x * y))
    (inv : ∀ x, motive x → motive x⁻¹) : motive x := by
  let S : Subgroup (HNNExtension G A B φ) :=
    { carrier := Set.ofPred motive
      one_mem' := by simpa using of 1
      mul_mem' := mul _ _
      inv_mem' := inv _ }
  let f : HNNExtension G A B φ →* S :=
    lift (HNNExtension.of.codRestrict S of)
      ⟨HNNExtension.t, t⟩ (by intro a; ext; simp [equiv_eq_conj, mul_assoc])
  have hf : S.subtype.comp f = MonoidHom.id _ :=
    hom_ext (by ext; simp [f]) (by simp [f])
  change motive (MonoidHom.id _ x)
  rw [← hf]
  exact (f x).2

variable (A B φ)

/-- To avoid duplicating code, we define `toSubgroup A B u` and `toSubgroupEquiv u`
where `u : ℤˣ` is `1` or `-1`. `toSubgroup A B u` is `A` when `u = 1` and `B` when `u = -1`,
and `toSubgroupEquiv` is `φ` when `u = 1` and `φ⁻¹` when `u = -1`. `toSubgroup u` is the subgroup
such that for any `a ∈ toSubgroup u`, `t ^ (u : ℤ) * a = toSubgroupEquiv a * t ^ (u : ℤ)`. -/
/-
**HNNExtension.toSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension`。
形式化陈述：toSubgroup (u : Intˣ) : Subgroup G
参数：u : Intˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To avoid duplicating code, we define `toSubgroup A B u` and `toSubgroupEquiv u`
where `u : ℤˣ` is `1` or `-1`. `toSubgroup A B u` is `A` when `u = 1` and `B` wh
en `u = -1`,
and `toSubgroupEquiv` is `φ` when `u = 1` and `φ⁻¹` when `u = -1`. `toSubgroup u
` is the subgroup
such that for any `a ∈ toSubgroup u`, `t ^ (u : ℤ) * a = toSubgroupEquiv a * t ^
 (u : ℤ)`.
-/
def toSubgroup (u : ℤˣ) : Subgroup G :=
  if u = 1 then A else B

@[simp]
/-
**HNNExtension.toSubgroup_one** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：toSubgroup_one : toSubgroup A B 1 = A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_one : toSubgroup A B 1 = A := rfl

@[simp]
/-
**HNNExtension.toSubgroup_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：toSubgroup_neg_one : toSubgroup A B (-1) = B
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_neg_one : toSubgroup A B (-1) = B := rfl

variable {A B}

/-- To avoid duplicating code, we define `toSubgroup A B u` and `toSubgroupEquiv u`
where `u : ℤˣ` is `1` or `-1`. `toSubgroup A B u` is `A` when `u = 1` and `B` when `u = -1`,
and `toSubgroupEquiv` is the group isomorphism from `toSubgroup A B u` to `toSubgroup A B (-u)`.
It is defined to be `φ` when `u = 1` and `φ⁻¹` when `u = -1`. -/
/-
**HNNExtension.toSubgroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension`。
形式化陈述：toSubgroupEquiv (u : Intˣ) : toSubgroup A B u ≃* toSubgroup A B (-u)
参数：u : Intˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To avoid duplicating code, we define `toSubgroup A B u` and `toSubgroupEquiv u`
where `u : ℤˣ` is `1` or `-1`. `toSubgroup A B u` is `A` when `u = 1` and `B` wh
en `u = -1`,
and `toSubgroupEquiv` is the group isomorphism from `toSubgroup A B u` to `toSub
group A B (-u)`.
It is defined to be `φ` when `u = 1` and `φ⁻¹` when `u = -1`.
-/
def toSubgroupEquiv (u : ℤˣ) : toSubgroup A B u ≃* toSubgroup A B (-u) :=
  if hu : u = 1 then hu ▸ φ else by
    convert! φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]
/-
**HNNExtension.toSubgroupEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：toSubgroupEquiv_one : toSubgroupEquiv φ 1 = φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroupEquiv_one : toSubgroupEquiv φ 1 = φ := rfl

@[simp]
/-
**HNNExtension.toSubgroupEquiv_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：toSubgroupEquiv_neg_one : toSubgroupEquiv φ (-1) = φ.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroupEquiv_neg_one : toSubgroupEquiv φ (-1) = φ.symm := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HNNExtension.toSubgroupEquiv_neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension
`。
形式化陈述：toSubgroupEquiv_neg_apply (u : Intˣ) (a : toSubgroup A B u) : (toSubgroupE
quiv φ (-u) (toSubgroupEquiv φ u a) : G) = a
参数：u : Intˣ；a : toSubgroup A B u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem toSubgroupEquiv_neg_apply (u : ℤˣ) (a : toSubgroup A B u) :
    (toSubgroupEquiv φ (-u) (toSubgroupEquiv φ u a) : G) = a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [toSubgroup]
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

namespace NormalWord

variable (G A B)
/-- To put a word in the HNN Extension into a normal form, we must choose an element of each right
coset of both `A` and `B`, such that the chosen element of the subgroup itself is `1`. -/
/-
**HNNExtension.NormalWord.TransversalPair** 是 Mathlib 中的一个归纳类型，位于命名空间 `HNNExtens
ion.NormalWord`。
形式化陈述：(G : Type u_1) → [inst : Group G] → Subgroup G → Subgroup G → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To put a word in the HNN Extension into a normal form, we must choose an element
 of each right
coset of both `A` and `B`, such that the chosen element of the subgroup itself i
s `1`.
-/
structure TransversalPair : Type _ where
  /-- The transversal of each subgroup -/
  set : ℤˣ → Set G
  /-- We have exactly one element of each coset of the subgroup -/
  compl : ∀ u, IsComplement (toSubgroup A B u : Subgroup G) (set u)
/-
**HNNExtension.NormalWord.TransversalPair.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `HN
NExtension.NormalWord.TransversalPair`。
形式化陈述：∀ (G : Type u_1) [inst : Group G] (A B : Subgroup G), Nonempty (HNNExtensi
on.NormalWord.TransversalPair G A B)
参数：G : Type u_1；A B : Subgroup G；HNNExtension.NormalWord.TransversalPair G A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Subgroup.exists_isComplement_right`：exists_isComplement_right (H : Subgr
oup G) (g : G) : exists T, IsComplement H T ∧ g in T
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance TransversalPair.nonempty : Nonempty (TransversalPair G A B) := by
  choose t ht using fun u ↦ (toSubgroup A B u).exists_isComplement_right 1
  exact ⟨⟨t, fun i ↦ (ht i).1⟩⟩

/-- A reduced word is a `head`, which is an element of `G`, followed by the product list of pairs.
There should also be no sequences of the form `t^u * g * t^-u`, where `g` is in
`toSubgroup A B u`. This is a less strict condition than required for `NormalWord`. -/
/-
**HNNExtension.NormalWord.ReducedWord** 是 Mathlib 中的一个归纳类型，位于命名空间 `HNNExtension.
NormalWord`。
形式化陈述：(G : Type u_1) → [inst : Group G] → Subgroup G → Subgroup G → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reduced word is a `head`, which is an element of `G`, followed by the product 
list of pairs.
There should also be no sequences of the form `t^u * g * t^-u`, where `g` is in
`toSubgroup A B u`. This is a less strict condition than required for `NormalWor
d`.
-/
structure ReducedWord : Type _ where
  /-- Every `ReducedWord` is the product of an element of the group and a word made up
  of letters each of which is in the transversal. `head` is that element of the base group. -/
  head : G
  /-- The list of pairs `(ℤˣ × G)`, where each pair `(u, g)` represents the element `t^u * g` of
  `HNNExtension G A B φ` -/
  toList : List (ℤˣ × G)
  /-- There are no sequences of the form `t^u * g * t^-u` where `g ∈ toSubgroup A B u`. -/
  chain : toList.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1)

/-- The empty reduced word. -/
@[simps]
/-
**HNNExtension.NormalWord.ReducedWord.empty** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtens
ion.NormalWord.ReducedWord`。
形式化陈述：(G : Type u_1) → [inst : Group G] → (A B : Subgroup G) → HNNExtension.Norm
alWord.ReducedWord G A B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty reduced word.
-/
def ReducedWord.empty : ReducedWord G A B :=
  { head := 1
    toList := []
    chain := List.isChain_nil }

variable {G A B}
/-- The product of a `ReducedWord` as an element of the `HNNExtension` -/
/-
**HNNExtension.NormalWord.ReducedWord.prod** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtensi
on.NormalWord.ReducedWord`。
形式化陈述：{G : Type u_1} →   [inst : Group G] →     {A B : Subgroup G} → (φ : ↥A ≃* 
↥B) → HNNExtension.NormalWord.ReducedWord G A B → HNNExtension G A B φ
参数：φ : ↥A ≃* ↥B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a `ReducedWord` as an element of the `HNNExtension`
-/
def ReducedWord.prod : ReducedWord G A B → HNNExtension G A B φ :=
  fun w => of w.head * (w.toList.map (fun x => t ^ (x.1 : ℤ) * of x.2)).prod

/-- Given a `TransversalPair`, we can make a normal form for words in the `HNNExtension G A B φ`.
The normal form is a `head`, which is an element of `G`, followed by the product list of pairs,
`t ^ u * g`, where `u` is `1` or `-1` and `g` is the chosen element of its right coset of
`toSubgroup A B u`. There should also be no sequences of the form `t^u * g * t^-u`
where `g ∈ toSubgroup A B u` -/
/-
**HNNExtension.NormalWord._root_.HNNExtension.NormalWord** 是 Mathlib 中的一个结构，位于命名
空间 `HNNExtension.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `TransversalPair`, we can make a normal form for words in the `HNNExtens
ion G A B φ`.
The normal form is a `head`, which is an element of `G`, followed by the product
 list of pairs,
`t ^ u * g`, where `u` is `1` or `-1` and `g` is the chosen element of its right
 coset of
`toSubgroup A B u`. There should also be no sequences of the form `t^u * g * t^-
u`
where `g ∈ toSubgroup A B u`
-/
structure _root_.HNNExtension.NormalWord (d : TransversalPair G A B) : Type _
    extends ReducedWord G A B where
  /-- Every element `g : G` in the list is the chosen element of its coset -/
  mem_set : ∀ (u : ℤˣ) (g : G), (u, g) ∈ toList → g ∈ d.set u

variable {d : TransversalPair G A B}

@[ext]
/-
**HNNExtension.NormalWord.ext** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.NormalWord
`。
形式化陈述：ext {w w' : NormalWord d} (h1 : w.head = w'.head) (h2 : w.toList = w'.toLi
st) : w = w'
参数：h1 : w.head = w'.head；h2 : w.toList = w'.toList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HNNExtension.NormalWord.ReducedWord.mk.congr_simp`：∀ {G : Type u_1} [ins
t : Group G] {A B : Subgroup G} (head head_1 : G),   head = head_1 →     ∀ (toLi
st toList_1 : List (ℤˣ × G)) (e_toList …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.NormalWord.mk.congr_simp`：∀ {G : Type u_1} [inst : Group G]
 {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B}   (toRed
ucedWord toReducedWord_1 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {w w' : NormalWord d}
    (h1 : w.head = w'.head) (h2 : w.toList = w'.toList) : w = w' := by
  rcases w with ⟨⟨⟩, _⟩; cases w'; simp_all

/-- The empty word -/
@[simps]
/-
**HNNExtension.NormalWord.empty** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.NormalWo
rd`。
形式化陈述：empty : NormalWord d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty word
-/
def empty : NormalWord d :=
  { head := 1
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

/-- The `NormalWord` representing an element `g` of the group `G`, which is just the element `g`
itself. -/
@[simps]
/-
**HNNExtension.NormalWord.ofGroup** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.Normal
Word`。
形式化陈述：ofGroup (g : G) : NormalWord d
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NormalWord` representing an element `g` of the group `G`, which is just the
 element `g`
itself.
-/
def ofGroup (g : G) : NormalWord d :=
  { head := g
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }
/-
**HNNExtension.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `HNNExtension.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NormalWord d) := ⟨empty⟩
/-
**HNNExtension.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `HNNExtension.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction G (NormalWord d) :=
  { smul := fun g w => { w with head := g * w.head }
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }
/-
**HNNExtension.NormalWord.group_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension
.NormalWord`。
形式化陈述：group_smul_def (g : G) (w : NormalWord d) : g • w = { w with head
参数：g : G；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem group_smul_def (g : G) (w : NormalWord d) :
    g • w = { w with head := g * w.head } := rfl

@[simp]
/-
**HNNExtension.NormalWord.group_smul_head** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtensio
n.NormalWord`。
形式化陈述：group_smul_head (g : G) (w : NormalWord d) : (g • w).head = g * w.head
参数：g : G；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem group_smul_head (g : G) (w : NormalWord d) : (g • w).head = g * w.head := rfl

@[simp]
/-
**HNNExtension.NormalWord.group_smul_toList** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtens
ion.NormalWord`。
形式化陈述：group_smul_toList (g : G) (w : NormalWord d) : (g • w).toList = w.toList
参数：g : G；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem group_smul_toList (g : G) (w : NormalWord d) : (g • w).toList = w.toList := rfl
/-
**HNNExtension.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `HNNExtension.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul G (NormalWord d) := ⟨by simp [group_smul_def]⟩

/-- A constructor to append an element `g` of `G` and `u : ℤˣ` to a word `w` with sufficient
hypotheses that no normalization or cancellation need take place for the result to be in normal form
-/
@[simps]
/-
**HNNExtension.NormalWord.cons** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.NormalWor
d`。
形式化陈述：cons (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u) (h2 : 
forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u
 = u') : NormalWord d
参数：g : G；u : Intˣ；w : NormalWord d；h1 : w.head in d.set u；h2 : forall u' in Opti
on.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor to append an element `g` of `G` and `u : ℤˣ` to a word `w` with su
fficient
hypotheses that no normalization or cancellation need take place for the result 
to be in normal form
-/
def cons (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head ∈ toSubgroup A B u → u = u') :
    NormalWord d :=
  { head := g,
    toList := (u, w.head) :: w.toList,
    mem_set := by
      intro u' g' h'
      simp only [List.mem_cons, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl⟩ | h'
      · exact h1
      · exact w.mem_set _ _ h'
    chain := by
      refine List.isChain_cons.2 ⟨?_, w.chain⟩
      rintro ⟨u', g'⟩ hu' hw1
      exact h2 _ (by simp_all) hw1 }

/-- A recursor to induct on a `NormalWord`, by proving the property is preserved under `cons` -/
@[elab_as_elim]
/-
**HNNExtension.NormalWord.consRecOn** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.Norm
alWord`。
形式化陈述：consRecOn {motive : NormalWord d -> Sort*} (w : NormalWord d) (ofGroup : f
orall g, motive (ofGroup g)) (cons : forall (g : G) (u : Intˣ) (w : NormalWord d
) (h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.fst w.toList.head?
, w.head in toSubgroup A B u -> u = u'), motive w -> motive (cons g u w h1 h2)) 
: motive w
参数：w : NormalWord d；ofGroup : forall g, motive (ofGroup g)；cons : forall (g : G)
 (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u) (h2 : forall u' in Optio
n.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u'), motive w -
> motive (cons g u w h1 h2)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor to induct on a `NormalWord`, by proving the property is preserved und
er `cons`
-/
def consRecOn {motive : NormalWord d → Sort*} (w : NormalWord d)
    (ofGroup : ∀ g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
        w.head ∈ toSubgroup A B u → u = u'),
      motive w → motive (cons g u w h1 h2)) : motive w := by
  rcases w with ⟨⟨g, l, chain⟩, mem_set⟩
  induction l generalizing g with
  | nil => exact ofGroup _
  | cons a l ih =>
    exact cons g a.1
      { head := a.2
        toList := l
        mem_set := fun _ _ h => mem_set _ _ (List.mem_cons_of_mem _ h),
        chain := (List.isChain_cons.1 chain).2 }
      (mem_set a.1 a.2 List.mem_cons_self)
      (by simpa using (List.isChain_cons.1 chain).1)
      (ih _ _ _)

@[simp]
/-
**HNNExtension.NormalWord.consRecOn_ofGroup** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtens
ion.NormalWord`。
形式化陈述：consRecOn_ofGroup {motive : NormalWord d -> Sort*} (g : G) (ofGroup : fora
ll g, motive (ofGroup g)) (cons : forall (g : G) (u : Intˣ) (w : NormalWord d) (
h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.fst w.toList.head?, w
.head in toSubgroup A B u -> u = u'), motive w -> motive (cons g u w h1 h2)) : c
onsRecOn (.ofGroup g) ofGroup cons = ofGroup g
参数：g : G；ofGroup : forall g, motive (ofGroup g)；cons : forall (g : G) (u : Intˣ)
 (w : NormalWord d) (h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.
fst w.toList.head?, w.head in toSubgroup A B u -> u = u'), motive w -> motive (c
ons g u w h1 h2)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem consRecOn_ofGroup {motive : NormalWord d → Sort*}
    (g : G) (ofGroup : ∀ g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head
        ∈ toSubgroup A B u → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.ofGroup g) ofGroup cons = ofGroup g := rfl

@[simp]
/-
**HNNExtension.NormalWord.consRecOn_cons** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension
.NormalWord`。
形式化陈述：consRecOn_cons {motive : NormalWord d -> Sort*} (g : G) (u : Intˣ) (w : No
rmalWord d) (h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.fst w.to
List.head?, w.head in toSubgroup A B u -> u = u') (ofGroup : forall g, motive (o
fGroup g)) (cons : forall (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in 
d.set u) (h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubg
roup A B u -> u = u'), motive w -> motive (cons g u w h1 h2)) : consRecOn (.cons
 g u w h1 h2) ofGroup cons
参数：g : G；u : Intˣ；w : NormalWord d；h1 : w.head in d.set u；h2 : forall u' in Opti
on.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u'；ofGroup : f
orall g, motive (ofGroup g)；cons : forall (g : G) (u : Intˣ) (w : NormalWord d) 
(h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.fst w.toList.head?, 
w.head in toSubgroup A B u -> u = u'), motive w -> motive (cons g u w h1 h2)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem consRecOn_cons {motive : NormalWord d → Sort*}
    (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head ∈ toSubgroup A B u → u = u')
    (ofGroup : ∀ g, motive (ofGroup g))
    (cons : ∀ (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
      (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
        w.head ∈ toSubgroup A B u → u = u'),
      motive w → motive (cons g u w h1 h2)) :
    consRecOn (.cons g u w h1 h2) ofGroup cons = cons g u w h1 h2
      (consRecOn w ofGroup cons) := rfl

@[simp]
/-
**HNNExtension.NormalWord.smul_cons** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.Norm
alWord`。
形式化陈述：smul_cons (g₁ g₂ : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set 
u) (h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubgroup A
 B u -> u = u') : g₁ • cons g₂ u w h1 h2 = cons (g₁ * g₂) u w h1 h2
参数：g₁ g₂ : G；u : Intˣ；w : NormalWord d；h1 : w.head in d.set u；h2 : forall u' in 
Option.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_cons (g₁ g₂ : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?, w.head ∈ toSubgroup A B u → u = u') :
    g₁ • cons g₂ u w h1 h2 = cons (g₁ * g₂) u w h1 h2 :=
  rfl

@[simp]
/-
**HNNExtension.NormalWord.smul_ofGroup** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.N
ormalWord`。
形式化陈述：smul_ofGroup (g₁ g₂ : G) : g₁ • (ofGroup g₂ : NormalWord d) = ofGroup (g₁ 
* g₂)
参数：g₁ g₂ : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_ofGroup (g₁ g₂ : G) :
    g₁ • (ofGroup g₂ : NormalWord d) = ofGroup (g₁ * g₂) := rfl

variable (d)
/-- The action of `t^u` on `ofGroup g`. The normal form will be
`a * t^u * g'` where `a ∈ toSubgroup A B (-u)` -/
/-
**HNNExtension.NormalWord.unitsSMulGroup** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension
.NormalWord`。
形式化陈述：unitsSMulGroup (u : Intˣ) (g : G) : (toSubgroup A B (-u)) × d.set u
参数：u : Intˣ；g : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HNNExtension.NormalWord.TransversalPair.compl`：∀ {G : Type u_1} [inst : 
Group G] {A B : Subgroup G} (self : HNNExtension.NormalWord.TransversalPair G A 
B) (u : ℤˣ),   Subgroup.IsComplemen…

--- 原说明 ---
The action of `t^u` on `ofGroup g`. The normal form will be
`a * t^u * g'` where `a ∈ toSubgroup A B (-u)`
-/
noncomputable def unitsSMulGroup (u : ℤˣ) (g : G) :
    (toSubgroup A B (-u)) × d.set u :=
  let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)
/-
**HNNExtension.NormalWord.unitsSMulGroup_snd** 是 Mathlib 中的一个定理，位于命名空间 `HNNExten
sion.NormalWord`。
形式化陈述：unitsSMulGroup_snd (u : Intˣ) (g : G) : (unitsSMulGroup φ d u g).2 = ((d.c
ompl u).equiv g).2
参数：u : Intˣ；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HNNExtension.NormalWord.TransversalPair.compl`：∀ {G : Type u_1} [inst : 
Group G] {A B : Subgroup G} (self : HNNExtension.NormalWord.TransversalPair G A 
B) (u : ℤˣ),   Subgroup.IsComplemen…
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem unitsSMulGroup_snd (u : ℤˣ) (g : G) :
    (unitsSMulGroup φ d u g).2 = ((d.compl u).equiv g).2 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

variable {d}

/-- `Cancels u w` is a predicate expressing whether `t^u` cancels with some occurrence
of `t^-u` when we multiply `t^u` by `w`. -/
/-
**HNNExtension.NormalWord.Cancels** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.Normal
Word`。
形式化陈述：Cancels (u : Intˣ) (w : NormalWord d) : Prop
参数：u : Intˣ；w : NormalWord d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cancels u w` is a predicate expressing whether `t^u` cancels with some occurren
ce
of `t^-u` when we multiply `t^u` by `w`.
-/
def Cancels (u : ℤˣ) (w : NormalWord d) : Prop :=
  (w.head ∈ (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

/-- Multiplying `t^u` by `w` in the special case where cancellation happens -/
/-
**HNNExtension.NormalWord.unitsSMulWithCancel** 是 Mathlib 中的一个定义，位于命名空间 `HNNExte
nsion.NormalWord`。
形式化陈述：unitsSMulWithCancel (u : Intˣ) (w : NormalWord d) : Cancels u w -> NormalW
ord d
参数：u : Intˣ；w : NormalWord d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying `t^u` by `w` in the special case where cancellation happens
-/
def unitsSMulWithCancel (u : ℤˣ) (w : NormalWord d) : Cancels u w → NormalWord d :=
  consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g _ w _ _ _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

/-- Multiplying `t^u` by a `NormalWord`, `w` and putting the result in normal form. -/
/-
**HNNExtension.NormalWord.unitsSMul** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.Norm
alWord`。
形式化陈述：unitsSMul (u : Intˣ) (w : NormalWord d) : NormalWord d
参数：u : Intˣ；w : NormalWord d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying `t^u` by a `NormalWord`, `w` and putting the result in normal form.
-/
noncomputable def unitsSMul (u : ℤˣ) (w : NormalWord d) : NormalWord d :=
  letI := Classical.dec
  if h : Cancels u w
  then unitsSMulWithCancel φ u w h
  else let g' := unitsSMulGroup φ d u w.head
    cons g'.1 u ((g'.2 * w.head⁻¹ : G) • w)
      (by simp)
      (by
        simp only [g', group_smul_toList, Option.mem_def, Option.map_eq_some_iff, Prod.exists,
          exists_and_right, exists_eq_right, group_smul_head, inv_mul_cancel_right,
          forall_exists_index, unitsSMulGroup]
        simp only [Cancels, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right,
          not_and, not_exists] at h
        intro u' x hx hmem
        have : w.head ∈ toSubgroup A B u := by
          have := (d.compl u).rightCosetEquivalence_equiv_snd w.head
          rw [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_left hmem] at this
          simp_all
        have := h this x
        simp_all [Int.units_ne_iff_eq_neg])

/-- A condition for not cancelling whose hypotheses are the same as those of the `cons` function. -/
/-
**HNNExtension.NormalWord.not_cancels_of_cons_hyp** 是 Mathlib 中的一个定理，位于命名空间 `HNN
Extension.NormalWord`。
形式化陈述：not_cancels_of_cons_hyp (u : Intˣ) (w : NormalWord d) (h2 : forall u' in O
ption.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u') : ¬ Can
cels u w
参数：u : Intˣ；w : NormalWord d；h2 : forall u' in Option.map Prod.fst w.toList.head
?, w.head in toSubgroup A B u -> u = u'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
A condition for not cancelling whose hypotheses are the same as those of the `co
ns` function.
-/
theorem not_cancels_of_cons_hyp (u : ℤˣ) (w : NormalWord d)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
      w.head ∈ toSubgroup A B u → u = u') :
    ¬ Cancels u w := by
  simp only [Cancels, Option.map_eq_some_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_and, not_exists]
  intro hw x hx
  rw [hx] at h2
  simpa using h2 (-u) rfl hw

set_option backward.isDefEq.respectTransparency false in
/-
**HNNExtension.NormalWord.unitsSMul_cancels_iff** 是 Mathlib 中的一个定理，位于命名空间 `HNNEx
tension.NormalWord`。
形式化陈述：unitsSMul_cancels_iff (u : Intˣ) (w : NormalWord d) : Cancels (-u) (unitsS
Mul φ u w) ↔ ¬ Cancels u w
参数：u : Intˣ；w : NormalWord d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HNNExtension.NormalWord.ofGroup_head`：∀ {G : Type u_1} [inst : Group G] 
{A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G), 
  (HNNExtension.NormalWord…
· 使用定理 `HNNExtension.NormalWord.ofGroup_toList`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G)
,   (HNNExtension.NormalWord…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HNNExtension.NormalWord.not_cancels_of_cons_hyp`：not_cancels_of_cons_hyp
 (u : Intˣ) (w : NormalWord d) (h2 : forall u' in Option.map Prod.fst w.toList.h
ead?, w.head in toSubgroup A B u -> u…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HNNExtension.NormalWord.cons_head`：∀ {G : Type u_1} [inst : Group G] {A 
B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G)   (u
 : ℤˣ) (w : HNNExtensio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HNNExtension.NormalWord.cons_toList`：∀ {G : Type u_1} [inst : Group G] {
A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G)   
(u : ℤˣ) (w : HNNExtensio…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
theorem unitsSMul_cancels_iff (u : ℤˣ) (w : NormalWord d) :
    Cancels (-u) (unitsSMul φ u w) ↔ ¬ Cancels u w := by
  by_cases h : Cancels u w
  · simp only [unitsSMul, h, dite_true, not_true_eq_false, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitsSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      apply not_cancels_of_cons_hyp _ _ h2
      simp only [Cancels, cons_head, cons_toList, List.head?_cons,
        Option.map_some, Option.some.injEq] at h
      cases h.2
      simpa [Cancels, unitsSMulWithCancel,
        Subgroup.mul_mem_cancel_left] using hc
  · simp only [unitsSMul, dif_neg h]
    simpa [Cancels] using h
/-
**HNNExtension.NormalWord.unitsSMul_neg** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.
NormalWord`。
形式化陈述：unitsSMul_neg (u : Intˣ) (w : NormalWord d) : unitsSMul φ (-u) (unitsSMul 
φ u w) = w
参数：u : Intˣ；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.NormalWord.unitsSMul.eq_1`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} (φ : ↥A ≃* ↥B) {d : HNNExtension.NormalWord.TransversalPair
 G A B}   (u : ℤˣ) (w : HNNE…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HNNExtension.NormalWord.unitsSMul_cancels_iff`：unitsSMul_cancels_iff (u 
: Intˣ) (w : NormalWord d) : Cancels (-u) (unitsSMul φ u w) ↔ ¬ Cancels u w
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `HNNExtension.NormalWord.unitsSMulWithCancel.congr_simp`：∀ {G : Type u_1}
 [inst : Group G] {A B : Subgroup G} (φ φ_1 : ↥A ≃* ↥B),   φ = φ_1 →     ∀ {d : 
HNNExtension.NormalWord.TransversalPair G A …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HNNExtension.NormalWord.TransversalPair.compl`：∀ {G : Type u_1} [inst : 
Group G] {A B : Subgroup G} (self : HNNExtension.NormalWord.TransversalPair G A 
B) (u : ℤˣ),   Subgroup.IsComplemen…
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HNNExtension.NormalWord.cons.congr_simp`：∀ {G : Type u_1} [inst : Group 
G] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g g_1
 : G),   g = g_1 →     ∀ (u u…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `HNNExtension.toSubgroupEquiv_neg_apply`：toSubgroupEquiv_neg_apply (u : I
ntˣ) (a : toSubgroup A B u) : (toSubgroupEquiv φ (-u) (toSubgroupEquiv φ u a) : 
G) = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HNNExtension.NormalWord.ofGroup_head`：∀ {G : Type u_1} [inst : Group G] 
{A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G), 
  (HNNExtension.NormalWord…
· 使用定理 `HNNExtension.NormalWord.ofGroup_toList`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G)
,   (HNNExtension.NormalWord…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
（共 55 条，此处仅展示前 30 条）
-/
theorem unitsSMul_neg (u : ℤˣ) (w : NormalWord d) :
    unitsSMul φ (-u) (unitsSMul φ u w) = w := by
  rw [unitsSMul]
  split_ifs with hcan
  · set_option backward.isDefEq.respectTransparency false in
    have hncan : ¬ Cancels u w := (unitsSMul_cancels_iff _ _ _).1 hcan
    unfold unitsSMul
    simp only [dif_neg hncan]
    simp [unitsSMulWithCancel, unitsSMulGroup, (d.compl u).equiv_snd_eq_inv_mul,
      -SetLike.coe_sort_coe]
  · have hcan2 : Cancels u w := not_not.1 (mt (unitsSMul_cancels_iff _ _ _).2 hcan)
    unfold unitsSMul at hcan ⊢
    simp only [dif_pos hcan2] at hcan ⊢
    cases w using consRecOn with
    | ofGroup => simp [Cancels] at hcan2
    | cons g u' w h1 h2 ih =>
      clear ih
      simp only [unitsSMulGroup, SetLike.coe_sort_coe, unitsSMulWithCancel, consRecOn_cons,
        group_smul_head,
        mul_inv_rev]
      cases hcan2.2
      have : ((d.compl (-u)).equiv w.head).1 = 1 :=
        (d.compl (-u)).equiv_fst_eq_one_of_mem_of_one_mem _ h1
      simpa [NormalWord.ext_iff, (d.compl (-u)).equiv_mul_left, Units.ext_iff,
        (d.compl (-u)).equiv_snd_eq_inv_mul]

/-- the equivalence given by multiplication on the left by `t` -/
@[simps]
/-
**HNNExtension.NormalWord.unitsSMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension
.NormalWord`。
形式化陈述：unitsSMulEquiv : NormalWord d ≃ NormalWord d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the equivalence given by multiplication on the left by `t`
-/
noncomputable def unitsSMulEquiv : NormalWord d ≃ NormalWord d :=
  { toFun := unitsSMul φ 1
    invFun := unitsSMul φ (-1),
    left_inv := fun _ => by rw [unitsSMul_neg]
    right_inv := fun w => by convert! unitsSMul_neg _ _ w; simp }

set_option backward.isDefEq.respectTransparency false in
/-
**HNNExtension.NormalWord.unitsSMul_one_group_smul** 是 Mathlib 中的一个定理，位于命名空间 `HN
NExtension.NormalWord`。
形式化陈述：unitsSMul_one_group_smul (g : A) (w : NormalWord d) : unitsSMul φ 1 ((g : 
G) • w) = (φ g : G) • (unitsSMul φ 1 w)
参数：g : A；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `HNNExtension.NormalWord.cons.congr_simp`：∀ {G : Type u_1} [inst : Group 
G] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g g_1
 : G),   g = g_1 →     ∀ (u u…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `HNNExtension.NormalWord.ofGroup_head`：∀ {G : Type u_1} [inst : Group G] 
{A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G), 
  (HNNExtension.NormalWord…
· 使用定理 `HNNExtension.NormalWord.ofGroup_toList`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G)
,   (HNNExtension.NormalWord…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Subgroup.coe_mul`：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `HNNExtension.NormalWord.TransversalPair.compl`：∀ {G : Type u_1} [inst : 
Group G] {A B : Subgroup G} (self : HNNExtension.NormalWord.TransversalPair G A 
B) (u : ℤˣ),   Subgroup.IsComplemen…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
（共 33 条，此处仅展示前 30 条）
-/
theorem unitsSMul_one_group_smul (g : A) (w : NormalWord d) :
    unitsSMul φ 1 ((g : G) • w) = (φ g : G) • (unitsSMul φ 1 w) := by
  unfold unitsSMul
  have : Cancels 1 ((g : G) • w) ↔ Cancels 1 w := by
    simp [Cancels, Subgroup.mul_mem_cancel_left]
  by_cases hcan : Cancels 1 w
  · simp only [unitsSMulWithCancel, toSubgroup_one, id_eq, toSubgroup_neg_one, toSubgroupEquiv_one,
      group_smul_head, mul_inv_rev, dif_pos (this.2 hcan), dif_pos hcan]
    cases w using consRecOn
    · simp [Cancels] at hcan
    · simp only [smul_cons, consRecOn_cons]
      rw [← mul_smul, ← Subgroup.coe_mul, ← map_mul φ]
      rfl
  · rw [dif_neg (mt this.1 hcan), dif_neg hcan]
    -- Before https://github.com/leanprover/lean4/pull/2644, all this was just
    -- `simp [← mul_smul, mul_assoc, unitsSMulGroup]`
    simp +instances only [toSubgroup_neg_one, unitsSMulGroup, toSubgroup_one, toSubgroupEquiv_one,
      SetLike.coe_sort_coe, group_smul_head, mul_inv_rev, ← mul_smul, mul_assoc, inv_mul_cancel,
      mul_one, smul_cons]
    -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
    congr 1
    · conv_lhs => erw [IsComplement.equiv_mul_left]
      simp_rw [toSubgroup_one]
      simp only [SetLike.coe_sort_coe, map_mul, Subgroup.coe_mul]
    conv_lhs => erw [IsComplement.equiv_mul_left]
    rfl
/-
**HNNExtension.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `HNNExtension.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MulAction (HNNExtension G A B φ) (NormalWord d) :=
  MulAction.ofEndHom <| (MulAction.toEndHom (M := Equiv.Perm (NormalWord d))).comp
    (HNNExtension.lift (MulAction.toPermHom _ _) (unitsSMulEquiv φ) <| by
      intro a
      ext : 1
      simp [unitsSMul_one_group_smul])

@[simp]
/-
**HNNExtension.NormalWord.prod_group_smul** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtensio
n.NormalWord`。
形式化陈述：prod_group_smul (g : G) (w : NormalWord d) : (g • w).prod φ = of g * (w.pr
od φ)
参数：g : G；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_group_smul (g : G) (w : NormalWord d) :
    (g • w).prod φ = of g * (w.prod φ) := by
  simp [ReducedWord.prod, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**HNNExtension.NormalWord.of_smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtensio
n.NormalWord`。
形式化陈述：of_smul_eq_smul (g : G) (w : NormalWord d) : (of g : HNNExtension G A B φ)
 • w = g • w
参数：g : G；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HNNExtension.NormalWord.mem_set`：∀ {G : Type u_1} [inst : Group G] {A B 
: Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B}   (self : HNNE
xtension.NormalWord d…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HNNExtension.lift_of`：lift_of (f : G ->* H) (x : H) (hx : forall a : A, 
x * f ↑a = f (φ a : G) * x) (g : G) : lift f x hx (of g) = f g
· 使用定理 `MulAction.toPermHom_apply`：∀ (G : Type u_1) (α : Type u_5) [inst : Group
 G] [inst_1 : MulAction G α] (a : G),   (MulAction.toPermHom G α) a = MulAction.
toPerm a
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_smul_eq_smul (g : G) (w : NormalWord d) :
    (of g : HNNExtension G A B φ) • w = g • w := by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

set_option backward.isDefEq.respectTransparency false in
/-
**HNNExtension.NormalWord.t_smul_eq_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `HNNExte
nsion.NormalWord`。
形式化陈述：t_smul_eq_unitsSMul (w : NormalWord d) : (t : HNNExtension G A B φ) • w = 
unitsSMul φ 1 w
参数：w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HNNExtension.lift_t`：lift_t (f : G ->* H) (x : H) (hx : forall a : A, x 
* f ↑a = f (φ a : G) * x) : lift f x hx t = x
· 使用定理 `HNNExtension.NormalWord.unitsSMulEquiv_apply`：∀ {G : Type u_1} [inst : G
roup G] {A B : Subgroup G} (φ : ↥A ≃* ↥B) {d : HNNExtension.NormalWord.Transvers
alPair G A B}   (w : HNNExtension.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t_smul_eq_unitsSMul (w : NormalWord d) :
    (t : HNNExtension G A B φ) • w = unitsSMul φ 1 w := by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

set_option backward.isDefEq.respectTransparency false in
/-
**HNNExtension.NormalWord.t_pow_smul_eq_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `HNN
Extension.NormalWord`。
形式化陈述：t_pow_smul_eq_unitsSMul (u : Intˣ) (w : NormalWord d) : (t ^ (u : Int) : H
NNExtension G A B φ) • w = unitsSMul φ u w
参数：u : Intˣ；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HNNExtension.lift_t`：lift_t (f : G ->* H) (x : H) (hx : forall a : A, x 
* f ↑a = f (φ a : G) * x) : lift f x hx t = x
· 使用定理 `HNNExtension.NormalWord.unitsSMulEquiv_apply`：∀ {G : Type u_1} [inst : G
roup G] {A B : Subgroup G} (φ : ↥A ≃* ↥B) {d : HNNExtension.NormalWord.Transvers
alPair G A B}   (w : HNNExtension.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `HNNExtension.NormalWord.unitsSMulEquiv_symm_apply`：∀ {G : Type u_1} [ins
t : Group G] {A B : Subgroup G} (φ : ↥A ≃* ↥B) {d : HNNExtension.NormalWord.Tran
sversalPair G A B}   (w : HNNExtension.…
-/
theorem t_pow_smul_eq_unitsSMul (u : ℤˣ) (w : NormalWord d) :
    (t ^ (u : ℤ) : HNNExtension G A B φ) • w = unitsSMul φ u w := by
  rcases Int.units_eq_one_or u with (rfl | rfl) <;>
    simp +instances [instHSMul, SMul.smul, MulAction.toEndHom, Equiv.Perm.inv_def]

@[simp]
/-
**HNNExtension.NormalWord.prod_cons** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.Norm
alWord`。
形式化陈述：prod_cons (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u) (
h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubgroup A B u
 -> u = u') : (cons g u w h1 h2).prod φ = of g * (t ^ (u : Int) * w.prod φ)
参数：g : G；u : Intˣ；w : NormalWord d；h1 : w.head in d.set u；h2 : forall u' in Opti
on.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_cons (g : G) (u : ℤˣ) (w : NormalWord d) (h1 : w.head ∈ d.set u)
    (h2 : ∀ u' ∈ Option.map Prod.fst w.toList.head?,
      w.head ∈ toSubgroup A B u → u = u') :
    (cons g u w h1 h2).prod φ = of g * (t ^ (u : ℤ) * w.prod φ) := by
  simp [ReducedWord.prod, cons, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**HNNExtension.NormalWord.prod_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension
.NormalWord`。
形式化陈述：prod_unitsSMul (u : Intˣ) (w : NormalWord d) : (unitsSMul φ u w).prod φ = 
(t ^ (u : Int) * w.prod φ : HNNExtension G A B φ)
参数：u : Intˣ；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.NormalWord.unitsSMul.eq_1`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} (φ : ↥A ≃* ↥B) {d : HNNExtension.NormalWord.TransversalPair
 G A B}   (u : ℤˣ) (w : HNNE…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HNNExtension.NormalWord.ofGroup_head`：∀ {G : Type u_1} [inst : Group G] 
{A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G), 
  (HNNExtension.NormalWord…
· 使用定理 `HNNExtension.NormalWord.ofGroup_toList`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B} (g : G)
,   (HNNExtension.NormalWord…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HNNExtension.NormalWord.prod_group_smul`：prod_group_smul (g : G) (w : No
rmalWord d) : (g • w).prod φ = of g * (w.prod φ)
· 使用定理 `HNNExtension.NormalWord.prod_cons`：prod_cons (g : G) (u : Intˣ) (w : Nor
malWord d) (h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.fst w.toL
ist.head?, w.head in to…
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HNNExtension.equiv_eq_conj`：equiv_eq_conj (a : A) : (of (φ a : G) : HNNE
xtension G A B φ) = t * of (a : G) * t⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `HNNExtension.equiv_symm_eq_conj`：equiv_symm_eq_conj (b : B) : (of (φ.sym
m b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `HNNExtension.NormalWord.TransversalPair.compl`：∀ {G : Type u_1} [inst : 
Group G] {A B : Subgroup G} (self : HNNExtension.NormalWord.TransversalPair G A 
B) (u : ℤˣ),   Subgroup.IsComplemen…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 36 条，此处仅展示前 30 条）
-/
theorem prod_unitsSMul (u : ℤˣ) (w : NormalWord d) :
    (unitsSMul φ u w).prod φ = (t ^ (u : ℤ) * w.prod φ : HNNExtension G A B φ) := by
  rw [unitsSMul]
  split_ifs with hcan
  · cases w using consRecOn
    · simp [Cancels] at hcan
    · cases hcan.2
      simp only [unitsSMulWithCancel, id_eq, consRecOn_cons, prod_group_smul, prod_cons, zpow_neg]
      rcases Int.units_eq_one_or u with (rfl | rfl)
      · simp [equiv_eq_conj, mul_assoc]
      · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
        -- simp [equiv_symm_eq_conj, mul_assoc].
        simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
          Int.reduceNeg, zpow_neg, zpow_one, inv_inv]
        erw [equiv_symm_eq_conj, mul_assoc, mul_assoc]
  · simp only [unitsSMulGroup, SetLike.coe_sort_coe, prod_cons, prod_group_smul, map_mul, map_inv]
    rcases Int.units_eq_one_or u with (rfl | rfl)
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul].
      simp only [toSubgroup_neg_one, toSubgroup_one, toSubgroupEquiv_one, equiv_eq_conj, mul_assoc,
        Units.val_one, zpow_one, inv_mul_cancel_left, mul_right_inj]
      erw [(d.compl 1).equiv_snd_eq_inv_mul]
      simp [mul_assoc]
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_symm_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]
      simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
        Int.reduceNeg, zpow_neg, zpow_one, mul_assoc]
      erw [equiv_symm_eq_conj, (d.compl (-1)).equiv_snd_eq_inv_mul]
      simp [mul_assoc]

@[simp]
/-
**HNNExtension.NormalWord.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.Nor
malWord`。
形式化陈述：prod_empty : (empty : NormalWord d).prod φ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HNNExtension.NormalWord.empty_head`：∀ {G : Type u_1} [inst : Group G] {A
 B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B},   HNNExten
sion.NormalWord.empty.he…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `HNNExtension.NormalWord.empty_toList`：∀ {G : Type u_1} [inst : Group G] 
{A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B},   HNNExt
ension.NormalWord.empty.to…
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_empty : (empty : NormalWord d).prod φ = 1 := by
  simp [ReducedWord.prod]

@[simp]
/-
**HNNExtension.NormalWord.prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension.Norm
alWord`。
形式化陈述：prod_smul (g : HNNExtension G A B φ) (w : NormalWord d) : (g • w).prod φ =
 g * w.prod φ
参数：g : HNNExtension G A B φ；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HNNExtension.induction_on`：induction_on {motive : HNNExtension G A B φ -
> Prop} (x : HNNExtension G A B φ) (of : forall g, motive (of g)) (t : motive t)
 (mul : forall …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.NormalWord.of_smul_eq_smul`：of_smul_eq_smul (g : G) (w : No
rmalWord d) : (of g : HNNExtension G A B φ) • w = g • w
· 使用定理 `HNNExtension.NormalWord.prod_group_smul`：prod_group_smul (g : G) (w : No
rmalWord d) : (g • w).prod φ = of g * (w.prod φ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HNNExtension.NormalWord.t_smul_eq_unitsSMul`：t_smul_eq_unitsSMul (w : No
rmalWord d) : (t : HNNExtension G A B φ) • w = unitsSMul φ 1 w
· 使用定理 `HNNExtension.NormalWord.prod_unitsSMul`：prod_unitsSMul (u : Intˣ) (w : N
ormalWord d) : (unitsSMul φ u w).prod φ = (t ^ (u : Int) * w.prod φ : HNNExtensi
on G A B φ)
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem prod_smul (g : HNNExtension G A B φ) (w : NormalWord d) :
    (g • w).prod φ = g * w.prod φ := by
  induction g using induction_on generalizing w with
  | of => simp [of_smul_eq_smul]
  | t => simp [t_smul_eq_unitsSMul, prod_unitsSMul]
  | mul => simp_all [mul_smul, mul_assoc]
  | inv x ih =>
    rw [← mul_right_inj x, ← ih]
    simp

@[simp]
/-
**HNNExtension.NormalWord.prod_smul_empty** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtensio
n.NormalWord`。
形式化陈述：prod_smul_empty (w : NormalWord d) : (w.prod φ) • empty = w
参数：w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HNNExtension.NormalWord.ReducedWord.chain`：∀ {G : Type u_1} [inst : Grou
p G] {A B : Subgroup G} (self : HNNExtension.NormalWord.ReducedWord G A B),   Li
st.IsChain (fun a b => a.2 ∈ HN…
· 使用定理 `HNNExtension.NormalWord.empty_toList`：∀ {G : Type u_1} [inst : Group G] 
{A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B},   HNNExt
ension.NormalWord.empty.to…
· 使用定理 `HNNExtension.NormalWord.mem_set`：∀ {G : Type u_1} [inst : Group G] {A B 
: Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B}   (self : HNNE
xtension.NormalWord d…
· 使用定理 `HNNExtension.NormalWord.ReducedWord.mk.congr_simp`：∀ {G : Type u_1} [ins
t : Group G] {A B : Subgroup G} (head head_1 : G),   head = head_1 →     ∀ (toLi
st toList_1 : List (ℤˣ × G)) (e_toList …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HNNExtension.NormalWord.empty_head`：∀ {G : Type u_1} [inst : Group G] {A
 B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B},   HNNExten
sion.NormalWord.empty.he…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `HNNExtension.NormalWord.of_smul_eq_smul`：of_smul_eq_smul (g : G) (w : No
rmalWord d) : (of g : HNNExtension G A B φ) • w = g • w
· 使用定理 `HNNExtension.NormalWord.mk.congr_simp`：∀ {G : Type u_1} [inst : Group G]
 {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B}   (toRed
ucedWord toReducedWord_1 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HNNExtension.NormalWord.prod_cons`：prod_cons (g : G) (u : Intˣ) (w : Nor
malWord d) (h1 : w.head in d.set u) (h2 : forall u' in Option.map Prod.fst w.toL
ist.head?, w.head in to…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `HNNExtension.NormalWord.t_pow_smul_eq_unitsSMul`：t_pow_smul_eq_unitsSMul
 (u : Intˣ) (w : NormalWord d) : (t ^ (u : Int) : HNNExtension G A B φ) • w = un
itsSMul φ u w
· 使用定理 `HNNExtension.NormalWord.unitsSMul.eq_1`：∀ {G : Type u_1} [inst : Group G
] {A B : Subgroup G} (φ : ↥A ≃* ↥B) {d : HNNExtension.NormalWord.TransversalPair
 G A B}   (u : ℤˣ) (w : HNNE…
· 使用定理 `HNNExtension.NormalWord.not_cancels_of_cons_hyp`：not_cancels_of_cons_hyp
 (u : Intˣ) (w : NormalWord d) (h2 : forall u' in Option.map Prod.fst w.toList.h
ead?, w.head in toSubgroup A B u -> u…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `HNNExtension.NormalWord.TransversalPair.compl`：∀ {G : Type u_1} [inst : 
Group G] {A B : Subgroup G} (self : HNNExtension.NormalWord.TransversalPair G A 
B) (u : ℤˣ),   Subgroup.IsComplemen…
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_one_of_mem_of_one_mem`：equiv_fst_eq_o
ne_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) : (hST.equiv g).fst = ⟨
1, h1⟩
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
（共 46 条，此处仅展示前 30 条）
-/
theorem prod_smul_empty (w : NormalWord d) :
    (w.prod φ) • empty = w := by
  induction w using consRecOn with
  | ofGroup => simp [ofGroup, ReducedWord.prod, of_smul_eq_smul, group_smul_def]
  | cons g u w h1 h2 ih =>
    rw [prod_cons, ← mul_assoc, mul_smul, ih, mul_smul, t_pow_smul_eq_unitsSMul,
      of_smul_eq_smul, unitsSMul]
    rw [dif_neg (not_cancels_of_cons_hyp u w h2)]
    -- Before https://github.com/leanprover/lean4/pull/2644, this was just
    -- simp [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
    --   -SetLike.coe_sort_coe]
    -- ext <;> simp [-SetLike.coe_sort_coe]
    simp only [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
      (d.compl _).equiv_snd_eq_inv_mul, inv_one, one_mul, mul_inv_cancel, one_smul, smul_cons]
    ext <;> simp

variable (d)
/-- The equivalence between elements of the HNN extension and words in normal form. -/
/-
**HNNExtension.NormalWord.equiv** 是 Mathlib 中的一个定义，位于命名空间 `HNNExtension.NormalWo
rd`。
形式化陈述：equiv : HNNExtension G A B φ ≃ NormalWord d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between elements of the HNN extension and words in normal form.
-/
noncomputable def equiv : HNNExtension G A B φ ≃ NormalWord d :=
  { toFun := fun g => g • empty,
    invFun := fun w => w.prod φ,
    left_inv := fun g => by simp [prod_smul]
    right_inv := fun w => by simp }
/-
**HNNExtension.NormalWord.prod_injective** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension
.NormalWord`。
形式化陈述：prod_injective : Injective (fun w => w.prod φ : NormalWord d -> HNNExtensi
on G A B φ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem prod_injective : Injective
    (fun w => w.prod φ : NormalWord d → HNNExtension G A B φ) :=
  (equiv φ d).symm.injective
/-
**HNNExtension.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `HNNExtension.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul (HNNExtension G A B φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg (fun w => w.prod φ) (h empty)⟩

end NormalWord

open NormalWord

/-
**HNNExtension.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `HNNExtension`。
形式化陈述：of_injective : Function.Injective (of : G -> HNNExtension G A B φ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HNNExtension.NormalWord.TransversalPair.nonempty`：∀ (G : Type u_1) [inst
 : Group G] (A B : Subgroup G), Nonempty (HNNExtension.NormalWord.TransversalPai
r G A B)
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `HNNExtension.NormalWord.instFaithfulSMul`：∀ {G : Type u_1} [inst : Group
 G] {A B : Subgroup G} {d : HNNExtension.NormalWord.TransversalPair G A B},   Fa
ithfulSMul G (HNNExtension.Nor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HNNExtension.NormalWord.of_smul_eq_smul`：of_smul_eq_smul (g : G) (w : No
rmalWord d) : (of g : HNNExtension G A B φ) • w = g • w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_injective : Function.Injective (of : G → HNNExtension G A B φ) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  refine Function.Injective.of_comp
    (f := ((· • ·) : HNNExtension G A B φ → NormalWord d → NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

namespace ReducedWord

/-
**HNNExtension.ReducedWord.exists_normalWord_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `
HNNExtension.ReducedWord`。
形式化陈述：exists_normalWord_prod_eq (d : TransversalPair G A B) (w : ReducedWord G A
 B) : exists w' : NormalWord d, w'.prod φ = w.prod φ ∧ w'.toList.map Prod.fst = 
w.toList.map Prod.fst ∧ forall u in w.toList.head?.map Prod.fst, w'.head⁻¹ * w.h
ead in toSubgroup A B (-u)
参数：d : TransversalPair G A B；w : ReducedWord G A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_nil`：isChain_nil : IsChain R []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_cons`：isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y i
n head? l, R x y) ∧ IsChain R l
· 使用定理 `HNNExtension.NormalWord.prod_smul`：prod_smul (g : HNNExtension G A B φ) 
(w : NormalWord d) : (g • w).prod φ = g * w.prod φ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Option.map_some`：∀ {α : Type u_1} {β : Type u_2} (a : α) (f : α → β), Op
tion.map f (some a) = some (f a)
（共 56 条，此处仅展示前 30 条）
-/
theorem exists_normalWord_prod_eq
    (d : TransversalPair G A B) (w : ReducedWord G A B) :
    ∃ w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      ∀ u ∈ w.toList.head?.map Prod.fst,
      w'.head⁻¹ * w.head ∈ toSubgroup A B (-u) := by
  suffices ∀ w : ReducedWord G A B,
      w.head = 1 → ∃ w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      ∀ u ∈ w.toList.head?.map Prod.fst,
      w'.head ∈ toSubgroup A B (-u) by
    by_cases hw1 : w.head = 1
    · simp only [hw1, inv_mem_iff, mul_one]
      exact this w hw1
    · rcases this ⟨1, w.toList, w.chain⟩ rfl with ⟨w', hw'⟩
      exact ⟨w.head • w', by
        simpa [ReducedWord.prod, mul_assoc] using hw'⟩
  intro w hw1
  rcases w with ⟨g, l, chain⟩
  dsimp at hw1; subst hw1
  induction l with
  | nil =>
    exact
      ⟨{ head := 1
         toList := []
         mem_set := by simp
         chain := List.isChain_nil }, by simp⟩
  | cons a l ih =>
    rcases ih (List.isChain_cons.1 chain).2 with ⟨w', hw'1, hw'2, hw'3⟩
    clear ih
    refine ⟨(t^(a.1 : ℤ) * of a.2 : HNNExtension G A B φ) • w', ?_, ?_⟩
    · rw [prod_smul, hw'1]
      simp [ReducedWord.prod]
    · have : ¬ Cancels a.1 (a.2 • w') := by
        simp only [Cancels, group_smul_head, group_smul_toList, Option.map_eq_some_iff,
          Prod.exists, exists_and_right, exists_eq_right, not_and, not_exists]
        intro hS x hx
        have hx' := congr_arg (Option.map Prod.fst) hx
        rw [← List.head?_map, hw'2, List.head?_map, Option.map_some] at hx'
        have : w'.head ∈ toSubgroup A B a.fst := by
          simpa using hw'3 _ hx'
        rw [mul_mem_cancel_right this] at hS
        have : a.fst = -a.fst := by
          have hl : l ≠ [] := by rintro rfl; simp_all
          have : a.fst = (l.head hl).fst := (List.isChain_cons.1 chain).1 (l.head hl)
            (List.head?_eq_some_head _) hS
          rwa [List.head?_eq_some_head hl, Option.map_some, ← this, Option.some_inj] at hx'
        simp at this
      simp [mul_smul, of_smul_eq_smul, t_pow_smul_eq_unitsSMul, unitsSMul, dif_neg this, ← hw'2]

/-- Two reduced words representing the same element of the `HNNExtension G A B φ` have the same
length corresponding list, with the same pattern of occurrences of `t^1` and `t^(-1)`,
and also the `head` is in the same left coset of `toSubgroup A B (-u)`, where `u : ℤˣ`
is the exponent of the first occurrence of `t` in the word. -/
/-
**HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `
HNNExtension.ReducedWord`。
形式化陈述：map_fst_eq_and_of_prod_eq {w₁ w₂ : ReducedWord G A B} (hprod : w₁.prod φ =
 w₂.prod φ) : w₁.toList.map Prod.fst = w₂.toList.map Prod.fst ∧ forall u in w₁.t
oList.head?.map Prod.fst, w₁.head⁻¹ * w₂.head in toSubgroup A B (-u)
参数：hprod : w₁.prod φ = w₂.prod φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HNNExtension.NormalWord.TransversalPair.nonempty`：∀ (G : Type u_1) [inst
 : Group G] (A B : Subgroup G), Nonempty (HNNExtension.NormalWord.TransversalPai
r G A B)
· 使用定理 `HNNExtension.ReducedWord.exists_normalWord_prod_eq`：exists_normalWord_pr
od_eq (d : TransversalPair G A B) (w : ReducedWord G A B) : exists w' : NormalWo
rd d, w'.prod φ = w.prod φ ∧ w'.toList.m…
· 使用定理 `HNNExtension.NormalWord.prod_injective`：prod_injective : Injective (fun 
w => w.prod φ : NormalWord d -> HNNExtension G A B φ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.head?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α}
, (List.map f l).head? = Option.map f l.head?

--- 原说明 ---
Two reduced words representing the same element of the `HNNExtension G A B φ` ha
ve the same
length corresponding list, with the same pattern of occurrences of `t^1` and `t^
(-1)`,
and also the `head` is in the same left coset of `toSubgroup A B (-u)`, where `u
 : ℤˣ`
is the exponent of the first occurrence of `t` in the word.
-/
theorem map_fst_eq_and_of_prod_eq {w₁ w₂ : ReducedWord G A B}
    (hprod : w₁.prod φ = w₂.prod φ) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst ∧
     ∀ u ∈ w₁.toList.head?.map Prod.fst,
      w₁.head⁻¹ * w₂.head ∈ toSubgroup A B (-u) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  rcases exists_normalWord_prod_eq φ d w₁ with ⟨w₁', hw₁'1, hw₁'2, hw₁'3⟩
  rcases exists_normalWord_prod_eq φ d w₂ with ⟨w₂', hw₂'1, hw₂'2, hw₂'3⟩
  have : w₁' = w₂' :=
    NormalWord.prod_injective φ d (by dsimp only; rw [hw₁'1, hw₂'1, hprod])
  subst this
  refine ⟨by rw [← hw₁'2, hw₂'2], ?_⟩
  simp only [← leftCoset_eq_iff] at *
  intro u hu
  rw [← hw₁'3 _ hu, ← hw₂'3 _]
  rwa [← List.head?_map, ← hw₂'2, hw₁'2, List.head?_map]

/-- **Britton's Lemma**. Any reduced word whose product is an element of `G`, has no
occurrences of `t`. -/
/-
**HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range** 是 Mathlib 中的一个定理，位于命名
空间 `HNNExtension.ReducedWord`。
形式化陈述：toList_eq_nil_of_mem_of_range (w : ReducedWord G A B) (hw : w.prod φ in (o
f.range : Subgroup (HNNExtension G A B φ))) : w.toList = []
参数：w : ReducedWord G A B；hw : w.prod φ in (of.range : Subgroup (HNNExtension G A
 B φ))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HNNExtension.NormalWord.ReducedWord.chain`：∀ {G : Type u_1} [inst : Grou
p G] {A B : Subgroup G} (self : HNNExtension.NormalWord.ReducedWord G A B),   Li
st.IsChain (fun a b => a.2 ∈ HN…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HNNExtension.NormalWord.ReducedWord.empty_toList`：∀ (G : Type u_1) [inst
 : Group G] (A B : Subgroup G), (HNNExtension.NormalWord.ReducedWord.empty G A B
).toList = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`：map_fst_eq_and_of_pr
od_eq {w₁ w₂ : ReducedWord G A B} (hprod : w₁.prod φ = w₂.prod φ) : w₁.toList.ma
p Prod.fst = w₂.toList.map Prod.fst ∧ fo…

--- 原说明 ---
**Britton's Lemma**. Any reduced word whose product is an element of `G`, has no
occurrences of `t`.
-/
theorem toList_eq_nil_of_mem_of_range (w : ReducedWord G A B)
    (hw : w.prod φ ∈ (of.range : Subgroup (HNNExtension G A B φ))) :
    w.toList = [] := by
  rcases hw with ⟨g, hg⟩
  let w' : ReducedWord G A B := { ReducedWord.empty G A B with head := g }
  have : w.prod φ = w'.prod φ := by simp [w', ReducedWord.prod, hg]
  simpa [w'] using (map_fst_eq_and_of_prod_eq φ this).1

end ReducedWord

end HNNExtension

