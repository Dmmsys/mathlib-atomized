/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Star projections

This file defines star projections, which are self-adjoint idempotents.

In star-ordered rings, star projections are non-negative.
(See `IsStarProjection.nonneg` in `Mathlib/Algebra/Order/Star/Basic.lean`.)
-/

public section

variable {R : Type*}

/-- A star projection is a self-adjoint idempotent. -/
@[mk_iff]
/-
**IsStarProjection** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Mul R] → [Star R] → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A star projection is a self-adjoint idempotent.
-/
structure IsStarProjection [Mul R] [Star R] (p : R) : Prop where
  protected isIdempotentElem : IsIdempotentElem p
  protected isSelfAdjoint : IsSelfAdjoint p

attribute [grind →, aesop safe forward]
  IsStarProjection.isIdempotentElem IsStarProjection.isSelfAdjoint

namespace IsStarProjection

variable {p q : R}

/-
**IsStarProjection._root_.isStarProjection_iff'** 是 Mathlib 中的一个引理，位于命名空间 `IsSta
rProjection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isStarProjection_iff' [Mul R] [Star R] :
    IsStarProjection p ↔ p * p = p ∧ star p = p :=
  isStarProjection_iff _
/-
**IsStarProjection.isStarNormal** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：isStarNormal [Mul R] [Star R] (hp : IsStarProjection p) : IsStarNormal p
参数：hp : IsStarProjection p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.isStarNormal`：isStarNormal {R : Type*} [Mul R] [Star R] {x
 : R} (hx : IsSelfAdjoint x) : IsStarNormal x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
-/
theorem isStarNormal [Mul R] [Star R]
    (hp : IsStarProjection p) : IsStarNormal p :=
  hp.isSelfAdjoint.isStarNormal
/-
**IsStarProjection.map** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：∀ {A : Type u_2} {B : Type u_3} [inst : Mul A] [inst_1 : Star A] [inst_2 :
 Mul B] [inst_3 : Star B] {F : Type u_4}   [inst_4 : FunLike F A B] [StarHomClas
s F A B] [MulHomClass F A B] {x : A},   IsStarProjection x → ∀ (f : F), IsStarPr
ojection (f x)
参数：f : F；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.map`：map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHo
mClass F M N] {e : M} (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e)
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `IsSelfAdjoint.map`：map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
 [StarHomClass F R S] {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f 
x)
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
-/
protected theorem map {A B : Type*} [Mul A] [Star A] [Mul B] [Star B]
    {F : Type*} [FunLike F A B] [StarHomClass F A B] [MulHomClass F A B]
    {x : A} (hx : IsStarProjection x) (f : F) : IsStarProjection (f x) where
  isIdempotentElem := hx.isIdempotentElem.map f
  isSelfAdjoint := hx.isSelfAdjoint.map f

variable (R) in
@[simp]
/-
**IsStarProjection.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：∀ (R : Type u_1) [inst : NonUnitalNonAssocSemiring R] [inst_1 : StarAddMon
oid R], IsStarProjection 0
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.zero`：zero : IsIdempotentElem (0 : M₀)
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
-/
protected theorem zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R] : IsStarProjection (0 : R) :=
  ⟨.zero, .zero _⟩

variable (R) in
@[simp]
/-
**IsStarProjection.one** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：∀ (R : Type u_1) [inst : MulOneClass R] [inst_1 : StarMul R], IsStarProjec
tion 1
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one`：one : IsIdempotentElem (1 : M)
· 使用定理 `IsSelfAdjoint.one`：∀ (R : Type u_1) [inst : MulOneClass R] [inst_1 : Sta
rMul R], IsSelfAdjoint 1
-/
protected theorem one [MulOneClass R] [StarMul R] : IsStarProjection (1 : R) :=
  ⟨.one, .one _⟩
/-
**IsStarProjection.pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：pow_eq [Monoid R] [Star R] (hp : IsStarProjection p) {n : Nat} (hn : n != 
0) : p ^ n = p
参数：hp : IsStarProjection p；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIdempotentElem.pow_eq`：pow_eq (h : IsIdempotentElem a) {n : Nat} (hn :
 n != 0) : a ^ n = a
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
-/
theorem pow_eq [Monoid R] [Star R] (hp : IsStarProjection p) {n : ℕ} (hn : n ≠ 0) : p ^ n = p :=
  hp.isIdempotentElem.pow_eq hn
/-
**IsStarProjection.pow_succ_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：pow_succ_eq [Monoid R] [Star R] (hp : IsStarProjection p) (n : Nat) : p ^ 
(n + 1) = p
参数：hp : IsStarProjection p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.pow_succ_eq`：pow_succ_eq (n : Nat) (h : IsIdempotentEle
m a) : a ^ (n + 1) = a
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
-/
theorem pow_succ_eq [Monoid R] [Star R] (hp : IsStarProjection p) (n : ℕ) : p ^ (n + 1) = p :=
  hp.isIdempotentElem.pow_succ_eq n

section NonAssocRing
variable [NonAssocRing R]

/-
**IsStarProjection.one_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：one_sub [StarRing R] (hp : IsStarProjection p) : IsStarProjection (1 - p) 
where isIdempotentElem
参数：hp : IsStarProjection p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `IsSelfAdjoint.one`：∀ (R : Type u_1) [inst : MulOneClass R] [inst_1 : Sta
rMul R], IsSelfAdjoint 1
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
-/
theorem one_sub [StarRing R] (hp : IsStarProjection p) : IsStarProjection (1 - p) where
  isIdempotentElem := hp.isIdempotentElem.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint
/-
**IsStarProjection._root_.isStarProjection_one_sub_iff** 是 Mathlib 中的一个定理，位于命名空间
 `IsStarProjection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isStarProjection_one_sub_iff [StarRing R] :
    IsStarProjection (1 - p) ↔ IsStarProjection p :=
  ⟨fun h ↦ sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff
/-
**IsStarProjection.mul_one_sub_self** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjection`
。
形式化陈述：mul_one_sub_self [Star R] (hp : IsStarProjection p) : p * (1 - p) = 0
参数：hp : IsStarProjection p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.mul_one_sub_self`：mul_one_sub_self (h : IsIdempotentEle
m a) : a * (1 - a) = 0
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
-/
lemma mul_one_sub_self [Star R] (hp : IsStarProjection p) : p * (1 - p) = 0 :=
  hp.isIdempotentElem.mul_one_sub_self
/-
**IsStarProjection.one_sub_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `IsStarProjection`
。
形式化陈述：one_sub_mul_self [Star R] (hp : IsStarProjection p) : (1 - p) * p = 0
参数：hp : IsStarProjection p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one_sub_mul_self`：one_sub_mul_self (h : IsIdempotentEle
m a) : (1 - a) * a = 0
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
-/
lemma one_sub_mul_self [Star R] (hp : IsStarProjection p) : (1 - p) * p = 0 :=
  hp.isIdempotentElem.one_sub_mul_self

end NonAssocRing

/-- The sum of star projections is a star projection if their product is `0`. -/
/-
**IsStarProjection.add** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：add [NonUnitalNonAssocSemiring R] [StarRing R] (hp : IsStarProjection p) (
hq : IsStarProjection q) (hpq : p * q = 0) : IsStarProjection (p + q) where isSe
lfAdjoint
参数：hp : IsStarProjection p；hq : IsStarProjection q；hpq : p * q = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIdempotentElem.add`：add [NonUnitalNonAssocSemiring R] {a b : R} (ha : 
IsIdempotentElem a) (hb : IsIdempotentElem b) (hab : a * b + b * a = 0) : IsIdem
potentElem…
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `IsSelfAdjoint.add`：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x + y)

--- 原说明 ---
The sum of star projections is a star projection if their product is `0`.
-/
theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    IsStarProjection (p + q) where
  isSelfAdjoint := hp.isSelfAdjoint.add hq.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem <| by
    rw [hpq, zero_add]
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq))

/-- The product of star projections is a star projection if they commute. -/
/-
**IsStarProjection.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjection`。
形式化陈述：mul [NonUnitalSemiring R] [StarRing R] (hp : IsStarProjection p) (hq : IsS
tarProjection q) (hpq : Commute p q) : IsStarProjection (p * q) where isSelfAdjo
int
参数：hp : IsStarProjection p；hq : IsStarProjection q；hpq : Commute p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.mul_of_commute`：mul_of_commute (hab : Commute a b) (ha 
: IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b)
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsSelfAdjoint.commute_iff`：commute_iff {R : Type*} [Mul R] [StarMul R] {
x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdj
oint (x * y)
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p

--- 原说明 ---
The product of star projections is a star projection if they commute.
-/
theorem mul [NonUnitalSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) where
  isSelfAdjoint := (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.isIdempotentElem.mul_of_commute hpq hq.isIdempotentElem

/-- `q - p` is a star projection when `p * q = p`. -/
/-
**IsStarProjection.sub_of_mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjectio
n`。
形式化陈述：sub_of_mul_eq_left [NonUnitalNonAssocRing R] [StarRing R] (hp : IsStarProj
ection p) (hq : IsStarProjection q) (hpq : p * q = p) : IsStarProjection (q - p)
 where isSelfAdjoint
参数：hp : IsStarProjection p；hq : IsStarProjection q；hpq : p * q = p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.sub`：sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsId
empotentElem a) (hb : IsIdempotentElem b) (hab : a * b = a) (hba : b * a = a) : 
IsIdempote…
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)

--- 原说明 ---
`q - p` is a star projection when `p * q = p`.
-/
theorem sub_of_mul_eq_left [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    IsStarProjection (q - p) where
  isSelfAdjoint := hq.isSelfAdjoint.sub hp.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.sub
    hq.isIdempotentElem hpq
    (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq)))

/-- `q - p` is a star projection when `q * p = p`. -/
/-
**IsStarProjection.sub_of_mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjecti
on`。
形式化陈述：sub_of_mul_eq_right [NonUnitalNonAssocRing R] [StarRing R] (hp : IsStarPro
jection p) (hq : IsStarProjection q) (hqp : q * p = p) : IsStarProjection (q - p
)
参数：hp : IsStarProjection p；hq : IsStarProjection q；hqp : q * p = p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStarProjection.sub_of_mul_eq_left`：sub_of_mul_eq_left [NonUnitalNonAss
ocRing R] [StarRing R] (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq 
: p * q = p) : IsStarProj…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p

--- 原说明 ---
`q - p` is a star projection when `q * p = p`.
-/
theorem sub_of_mul_eq_right [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q * p = p) :
    IsStarProjection (q - p) := hp.sub_of_mul_eq_left hq
  (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hqp)))

/-- `q - p` is a star projection iff `p * q = p`. -/
/-
**IsStarProjection.sub_iff_mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProjecti
on`。
形式化陈述：sub_iff_mul_eq_left [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R] {p
 q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) : IsStarProjection (
q - p) ↔ p * q = p
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStarProjection_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] 
(p : R), IsStarProjection p ↔ IsIdempotentElem p ∧ IsSelfAdjoint p
· 使用定理 `IsIdempotentElem.sub_iff`：sub_iff [NonUnitalRing R] [IsAddTorsionFree R]
 {p q : R} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) : IsIdempotentEle
m (q - p) ↔ p …
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_eq_iff_star_eq`：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : 
star r = s ↔ star s = r
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`q - p` is a star projection iff `p * q = p`.
-/
theorem sub_iff_mul_eq_left [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ p * q = p := by
  rw [isStarProjection_iff, hp.isIdempotentElem.sub_iff hq.isIdempotentElem]
  simp_rw [hq.isSelfAdjoint.sub hp.isSelfAdjoint, and_true]
  nth_rw 3 [← hp.isSelfAdjoint]
  nth_rw 2 [← hq.isSelfAdjoint]
  rw [← star_mul, star_eq_iff_star_eq, hp.isSelfAdjoint, eq_comm]
  simp_rw [and_self]

/-- `q - p` is a star projection iff `q * p = p`. -/
/-
**IsStarProjection.sub_iff_mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProject
ion`。
形式化陈述：sub_iff_mul_eq_right [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R] {
p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) : IsStarProjection 
(q - p) ↔ q * p = p
参数：hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_inj`：star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = 
y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStarProjection.sub_iff_mul_eq_left`：sub_iff_mul_eq_left [NonUnitalRing
 R] [StarRing R] [IsAddTorsionFree R] {p q : R} (hp : IsStarProjection p) (hq : 
IsStarProjection q) : IsSt…
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`q - p` is a star projection iff `q * p = p`.
-/
theorem sub_iff_mul_eq_right [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ q * p = p := by
  rw [← star_inj]
  simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    sub_iff_mul_eq_left hp hq]
/-
**IsStarProjection.add_sub_mul_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsStarProje
ction`。
形式化陈述：add_sub_mul_of_commute [NonUnitalRing R] [StarRing R] (hpq : Commute p q) 
(hp : IsStarProjection p) (hq : IsStarProjection q) : IsStarProjection (p + q - 
p * q) where isIdempotentElem
参数：hpq : Commute p q；hp : IsStarProjection p；hq : IsStarProjection q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.add_sub_mul_of_commute`：add_sub_mul_of_commute (h : Com
mute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem
 (a + b - a * b)
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `IsSelfAdjoint.add`：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x + y)
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsSelfAdjoint.commute_iff`：commute_iff {R : Type*} [Mul R] [StarMul R] {
x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdj
oint (x * y)
-/
theorem add_sub_mul_of_commute [NonUnitalRing R] [StarRing R]
    (hpq : Commute p q) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q - p * q) where
  isIdempotentElem := hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (hp.isSelfAdjoint.add hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

end IsStarProjection

