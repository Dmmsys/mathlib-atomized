/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Order.Disjoint

/-!
# Canonical homomorphism from a pair of monoids

This file defines the construction of the canonical homomorphism from a pair of monoids.

Given two morphisms of monoids `f : M →* P` and `g : N →* P` where elements in the images
of the two morphisms commute, we obtain a canonical morphism
`MonoidHom.noncommCoprod : M × N →* P` whose composition with `inl M N` coincides with `f`
and whose composition with `inr M N` coincides with `g`.

There is an analogue `MulHom.noncommCoprod` when `f` and `g` are only `MulHom`s.

## Main theorems:

* `noncommCoprod_comp_inr` and `noncommCoprod_comp_inl` prove that the compositions
  of `MonoidHom.noncommCoprod f g _` with `inl M N` and `inr M N` coincide with `f` and `g`.
* `comp_noncommCoprod` proves that the composition of a morphism of monoids `h`
  with `noncommCoprod f g _` coincides with `noncommCoprod (h.comp f) (h.comp g)`.

For a product of a family of morphisms of monoids, see `MonoidHom.noncommPiCoprod`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

namespace MulHom

variable {M N P : Type*} [Mul M] [Mul N] [Semigroup P]
  (f : M →ₙ* P) (g : N →ₙ* P)

/-- Coproduct of two `MulHom`s with the same codomain with `Commute` assumption:
  `f.noncommCoprod g _ (p : M × N) = f p.1 * g p.2`.
  (For the commutative case, use `MulHom.coprod`) -/
@[to_additive (attr := simps)
    /-- Coproduct of two `AddHom`s with the same codomain with `AddCommute` assumption:
    `f.noncommCoprod g _ (p : M × N) = f p.1 + g p.2`.
    (For the commutative case, use `AddHom.coprod`) -/]
/-
**MulHom.noncommCoprod** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：noncommCoprod (comm : forall m n, Commute (f m) (g n)) : M × N ->ₙ* P wher
e toFun mn
参数：comm : forall m n, Commute (f m) (g n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def noncommCoprod (comm : ∀ m n, Commute (f m) (g n)) : M × N →ₙ* P where
  toFun mn := f mn.fst * g mn.snd
  map_mul' mn mn' := by simpa using (comm _ _).mul_mul_mul_comm _ _

/-- Variant of `MulHom.noncommCoprod_apply` with the product written in the other direction. -/
@[to_additive
  /-- Variant of `AddHom.noncommCoprod_apply`, with the sum written in the other direction -/]
/-
**MulHom.noncommCoprod_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：noncommCoprod_apply' (comm) (mn : M × N) : (f.noncommCoprod g comm) mn = g
 mn.2 * f mn.1
参数：comm；mn : M × N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_
3} [inst : Mul M] [inst_1 : Mul N] [inst_2 : Semigroup P] (f : M →ₙ* P)   (g : N
 →ₙ* P) (comm : …
-/
theorem noncommCoprod_apply' (comm) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, noncommCoprod_apply]

@[to_additive]
/-
**MulHom.comp_noncommCoprod** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：comp_noncommCoprod {Q : Type*} [Semigroup Q] (h : P ->ₙ* Q) (comm : forall
 m n, Commute (f m) (g n)) : h.comp (f.noncommCoprod g comm) = (h.comp f).noncom
mCoprod (h.comp g) (fun m n => (comm m n).map h)
参数：h : P ->ₙ* Q；comm : forall m n, Commute (f m) (g n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
theorem comp_noncommCoprod {Q : Type*} [Semigroup Q] (h : P →ₙ* Q)
    (comm : ∀ m n, Commute (f m) (g n)) :
    h.comp (f.noncommCoprod g comm) =
      (h.comp f).noncommCoprod (h.comp g) (fun m n ↦ (comm m n).map h) :=
  ext fun _ => map_mul h _ _

end MulHom

namespace MonoidHom

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [Monoid P]
  (f : M →* P) (g : N →* P) (comm : ∀ m n, Commute (f m) (g n))

/-- Coproduct of two `MonoidHom`s with the same codomain,
  with a commutation assumption:
  `f.noncommCoprod g _ (p : M × N) = f p.1 * g p.2`.
  (Noncommutative case; in the commutative case, use `MonoidHom.coprod`.) -/
@[to_additive (attr := simps)
    /-- Coproduct of two `AddMonoidHom`s with the same codomain,
    with a commutation assumption:
    `f.noncommCoprod g (p : M × N) = f p.1 + g p.2`.
    (Noncommutative case; in the commutative case, use `AddHom.coprod`.) -/]
/-
**MonoidHom.noncommCoprod** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod : M × N ->* P where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def noncommCoprod : M × N →* P where
  toFun := fun mn ↦ (f mn.fst) * (g mn.snd)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, mul_one]
  __ := f.toMulHom.noncommCoprod g.toMulHom comm

/-- Variant of `MonoidHom.noncommCoprod_apply` with the product written in the other direction. -/
@[to_additive
  /-- Variant of `AddMonoidHom.noncommCoprod_apply` with the sum written in the other direction -/]
/-
**MonoidHom.noncommCoprod_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_apply' (comm) (mn : M × N) : (f.noncommCoprod g comm) mn = g
 mn.2 * f mn.1
参数：comm；mn : M × N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
-/
theorem noncommCoprod_apply' (comm) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, MonoidHom.noncommCoprod_apply]

@[to_additive (attr := simp)]
/-
**MonoidHom.noncommCoprod_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_comp_inl : (f.noncommCoprod g comm).comp (inl M N) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem noncommCoprod_comp_inl : (f.noncommCoprod g comm).comp (inl M N) = f :=
  ext fun x => by simp

@[to_additive (attr := simp)]
/-
**MonoidHom.noncommCoprod_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_comp_inr : (f.noncommCoprod g comm).comp (inr M N) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem noncommCoprod_comp_inr : (f.noncommCoprod g comm).comp (inr M N) = g :=
  ext fun x => by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidHom.noncommCoprod_unique** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_unique (f : M × N ->* P) : (f.comp (inl M N)).noncommCoprod 
(f.comp (inr M N)) (fun _ _ => (commute_inl_inr _ _).map f) = f
参数：f : M × N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidHom.commute_inl_inr`：commute_inl_inr (m : M) (n : N) : Commute (in
l M N m) (inr M N n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem noncommCoprod_unique (f : M × N →* P) :
    (f.comp (inl M N)).noncommCoprod (f.comp (inr M N)) (fun _ _ => (commute_inl_inr _ _).map f)
      = f :=
  ext fun x => by simp [inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]
/-
**MonoidHom.noncommCoprod_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_inl_inr {M N : Type*} [Monoid M] [Monoid N] : (inl M N).nonc
ommCoprod (inr M N) commute_inl_inr = id (M × N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.noncommCoprod_unique`：noncommCoprod_unique (f : M × N ->* P) :
 (f.comp (inl M N)).noncommCoprod (f.comp (inr M N)) (fun _ _ => (commute_inl_in
r _ _).map f) = f
-/
theorem noncommCoprod_inl_inr {M N : Type*} [Monoid M] [Monoid N] :
    (inl M N).noncommCoprod (inr M N) commute_inl_inr = id (M × N) :=
  noncommCoprod_unique <| .id (M × N)

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MonoidHom.comp_noncommCoprod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comp_noncommCoprod {Q : Type*} [Monoid Q] (h : P ->* Q) : h.comp (f.noncom
mCoprod g comm) = (h.comp f).noncommCoprod (h.comp g) (fun m n => (comm m n).map
 h)
参数：h : P ->* Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_noncommCoprod {Q : Type*} [Monoid Q] (h : P →* Q) :
    h.comp (f.noncommCoprod g comm) =
      (h.comp f).noncommCoprod (h.comp g) (fun m n ↦ (comm m n).map h) :=
  ext fun x => by simp

section group

open Subgroup

/-
**MonoidHom.noncommCoprod_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_injective {M N P : Type*} [Group M] [Group N] [Group P] (f :
 M ->* P) (g : N ->* P) (comm : forall (m : M) (n : N), Commute (f m) (g n)) : F
unction.Injective (noncommCoprod f g comm) ↔ (Function.Injective f ∧ Function.In
jective g ∧ _root_.Disjoint f.range g.range)
参数：f : M ->* P；g : N ->* P；comm : forall (m : M) (n : N), Commute (f m) (g n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `inv_eq_iff_mul_eq_one`：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
-/
lemma noncommCoprod_injective {M N P : Type*} [Group M] [Group N] [Group P]
    (f : M →* P) (g : N →* P) (comm : ∀ (m : M) (n : N), Commute (f m) (g n)) :
    Function.Injective (noncommCoprod f g comm) ↔
      (Function.Injective f ∧ Function.Injective g ∧ _root_.Disjoint f.range g.range) := by
  simp only [injective_iff_map_eq_one, disjoint_iff_inf_le,
    noncommCoprod_apply, Prod.forall, Prod.mk_eq_one]
  refine ⟨fun h ↦ ⟨fun x ↦ ?_, fun x ↦ ?_, ?_⟩, ?_⟩
  · simpa using h x 1
  · simpa using h 1 x
  · intro x ⟨⟨y, hy⟩, z, hz⟩
    rwa [(h y z⁻¹ (by rw [map_inv, hy, hz, mul_inv_cancel])).1, map_one, eq_comm] at hy
  · intro ⟨hf, hg, hp⟩ a b h
    have key := hp ⟨⟨a⁻¹, by rwa [map_inv, inv_eq_iff_mul_eq_one]⟩, b, rfl⟩
    exact ⟨hf a (by rwa [key, mul_one] at h), hg b key⟩
/-
**MonoidHom.noncommCoprod_range** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：noncommCoprod_range {M N P : Type*} [Group M] [Group N] [Group P] (f : M -
>* P) (g : N ->* P) (comm : forall (m : M) (n : N), Commute (f m) (g n)) : (nonc
ommCoprod f g comm).range = f.range ⊔ g.range
参数：f : M ->* P；g : N ->* P；comm : forall (m : M) (n : N), Commute (f m) (g n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.mem_sup_left`：mem_sup_left {S T : Subgroup G} : forall {x : G},
 x in S -> x in S ⊔ T
· 使用定理 `Subgroup.mem_sup_right`：mem_sup_right {S T : Subgroup G} : forall {x : G
}, x in T -> x in S ⊔ T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma noncommCoprod_range {M N P : Type*} [Group M] [Group N] [Group P]
    (f : M →* P) (g : N →* P) (comm : ∀ (m : M) (n : N), Commute (f m) (g n)) :
    (noncommCoprod f g comm).range = f.range ⊔ g.range := by
  apply le_antisymm
  · rintro - ⟨a, rfl⟩
    exact mul_mem (mem_sup_left ⟨a.1, rfl⟩) (mem_sup_right ⟨a.2, rfl⟩)
  · rw [sup_le_iff]
    constructor
    · rintro - ⟨a, rfl⟩
      exact ⟨(a, 1), by rw [noncommCoprod_apply, map_one, mul_one]⟩
    · rintro - ⟨a, rfl⟩
      exact ⟨(1, a), by rw [noncommCoprod_apply, map_one, one_mul]⟩

end group

end MonoidHom

