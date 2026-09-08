/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Ring.Defs

/-! # Lemmas about additive closures of `Subsemigroup`. -/

public section

open AddSubmonoid

namespace MulMemClass
variable {M R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
/-
**MulMemClass.mul_right_mem_add_closure** 是 Mathlib 中的一个引理，位于命名空间 `MulMemClass`。
形式化陈述：mul_right_mem_add_closure (ha : a in closure (S : Set R)) (hb : b in S) : 
a * b in closure (S : Set R)
参数：ha : a in closure (S : Set R)；hb : b in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.mem_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : 
Set M} {x : M},   x ∈ AddSubmonoid.closure s ↔ ∀ (S : AddSubmonoid M), s ⊆ ↑S → 
x ∈ S
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M

--- 原说明 ---
The product of an element of the additive closure of a multiplicative subsemigro
up `M`
and an element of `M` is contained in the additive closure of `M`.
-/
lemma mul_right_mem_add_closure (ha : a ∈ closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ closure (S : Set R) := by
  induction ha using closure_induction with
  | mem r hr => exact mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  | zero => simp only [zero_mul, zero_mem _]
  | add r s _ _ hr hs => simpa only [add_mul] using add_mem hr hs

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
/-
**MulMemClass.mul_mem_add_closure** 是 Mathlib 中的一个引理，位于命名空间 `MulMemClass`。
形式化陈述：mul_mem_add_closure (ha : a in closure (S : Set R)) (hb : b in closure (S 
: Set R)) : a * b in closure (S : Set R)
参数：ha : a in closure (S : Set R)；hb : b in closure (S : Set R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用引理 `MulMemClass.mul_right_mem_add_closure`：mul_right_mem_add_closure (ha : a
 in closure (S : Set R)) (hb : b in S) : a * b in closure (S : Set R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M

--- 原说明 ---
The product of two elements of the additive closure of a submonoid `M` is an ele
ment of the
additive closure of `M`.
-/
lemma mul_mem_add_closure (ha : a ∈ closure (S : Set R))
    (hb : b ∈ closure (S : Set R)) : a * b ∈ closure (S : Set R) := by
  induction hb using closure_induction with
  | mem r hr => exact MulMemClass.mul_right_mem_add_closure ha hr
  | zero => simp only [mul_zero, zero_mem _]
  | add r s _ _ hr hs => simpa only [mul_add] using add_mem hr hs

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
/-
**MulMemClass.mul_left_mem_add_closure** 是 Mathlib 中的一个引理，位于命名空间 `MulMemClass`。
形式化陈述：mul_left_mem_add_closure (ha : a in S) (hb : b in closure (S : Set R)) : a
 * b in closure (S : Set R)
参数：ha : a in S；hb : b in closure (S : Set R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulMemClass.mul_mem_add_closure`：mul_mem_add_closure (ha : a in closure 
(S : Set R)) (hb : b in closure (S : Set R)) : a * b in closure (S : Set R)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.mem_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : 
Set M} {x : M},   x ∈ AddSubmonoid.closure s ↔ ∀ (S : AddSubmonoid M), s ⊆ ↑S → 
x ∈ S

--- 原说明 ---
The product of an element of `S` and an element of the additive closure of a mul
tiplicative
submonoid `S` is contained in the additive closure of `S`.
-/
lemma mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ closure (S : Set R)) :
    a * b ∈ closure (S : Set R) :=
  mul_mem_add_closure (mem_closure.mpr fun _sT hT => hT ha) hb

end MulMemClass

