/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.SetLike.Basic

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type*) [Ring R] [StarRing R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star non-unital, non-associative, semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

@[expose] public section

assert_not_exists Finset Subgroup Rat.instField

open scoped Ring

universe u v w

open MulOpposite

variable {R : Type u}

/-- `StarMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
/-
**StarMemClass** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：StarMemClass (S R : Type*) [Star R] [SetLike S R] : Prop where /-- Closure
 under star. -/ star_mem : forall {s : S} {r : R}, r in s -> star r in s  export
 StarMemClass (star_mem)  attribute [aesop 90% (rule_sets
参数：S R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`StarMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under star.
-/
class StarMemClass (S R : Type*) [Star R] [SetLike S R] : Prop where
  /-- Closure under star. -/
  star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s

export StarMemClass (star_mem)

attribute [aesop 90% (rule_sets := [SetLike])] star_mem

namespace StarMemClass

variable {S : Type w} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

/-
**StarMemClass.instStar** 是 Mathlib 中的一个实例，位于命名空间 `StarMemClass`。
形式化陈述：instStar : Star s where star r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStar : Star s where
  star r := ⟨star (r : R), star_mem r.prop⟩
/-
**StarMemClass.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `StarMemClass`。
形式化陈述：∀ {R : Type u} {S : Type w} [inst : Star R] [inst_1 : SetLike S R] [hS : S
tarMemClass S R] (s : S) (x : ↥s),   ↑(star x) = star ↑x
参数：s : S；x : ↥s；star x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_star (x : s) : star x = star (x : R) := rfl

end StarMemClass

/-- Typeclass for a star operation with is involutive.
-/
/-
**InvolutiveStar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a star operation with is involutive.
-/
class InvolutiveStar (R : Type u) extends Star R where
  /-- Involutive condition. -/
  star_involutive : Function.Involutive star

export InvolutiveStar (star_involutive)

@[simp]
/-
**star_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_star [InvolutiveStar R] (r : R) : star (star r) = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
-/
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _
/-
**star_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：star_mem_iff {S : Type*} [SetLike S R] [InvolutiveStar R] [StarMemClass S 
R] {s : S} {x : R} : star x in s ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
lemma star_mem_iff {S : Type*} [SetLike S R] [InvolutiveStar R] [StarMemClass S R]
    {s : S} {x : R} : star x ∈ s ↔ x ∈ s :=
  ⟨fun h => star_star x ▸ star_mem h, fun h => star_mem h⟩
/-
**star_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_injective [InvolutiveStar R] : Function.Injective (star : R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
-/
theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) :=
  Function.Involutive.injective star_involutive

@[aesop 5% (rule_sets := [SetLike!])]
/-
**mem_of_star_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_of_star_mem {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemCla
ss S R] {s : S} {r : R} (hr : star r in s) : r in s
参数：hr : star r in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
-/
theorem mem_of_star_mem {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    {s : S} {r : R} (hr : star r ∈ s) : r ∈ s := by rw [← star_star r]; exact star_mem hr

@[simp]
/-
**star_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
-/
theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y :=
  star_injective.eq_iff

/-- `star` as an equivalence when it is involutive. -/
@[simps! apply]
/-
**Equiv.Perm.star** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：{R : Type u} → [InvolutiveStar R] → Equiv.Perm R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
`star` as an equivalence when it is involutive.
-/
protected def Equiv.Perm.star [InvolutiveStar R] : Equiv.Perm R where
  toFun := star
  invFun := star
  __ : Equiv.Perm R := star_involutive.toPerm _

@[simp]
/-
**Equiv.Perm.symm_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.symm_star [InvolutiveStar R] : (Equiv.Perm.star : R ≃ R).symm =
 Equiv.Perm.star
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.Perm.symm_star [InvolutiveStar R] :
    (Equiv.Perm.star : R ≃ R).symm = Equiv.Perm.star :=
  rfl
/-
**eq_star_of_eq_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = sta
r r
参数：h : r = star s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]
/-
**eq_star_iff_eq_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_star_of_eq_star`：eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h :
 r = star s) : s = star r
-/
theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩
/-
**star_eq_iff_star_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_star_iff_eq_star`：eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : 
r = star s ↔ s = star r
-/
theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm

/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
/-
**TrivialStar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Star R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  /-- Condition that star is trivial -/
  star_trivial : ∀ r : R, star r = r

export TrivialStar (star_trivial)

attribute [simp] star_trivial

/-- A \*-magma is a magma `R` with an involutive operation `star`
such that `star (r * s) = star s * star r`.
-/
/-
**StarMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Mul R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A \*-magma is a magma `R` with an involutive operation `star`
such that `star (r * s) = star s * star r`.
-/
class StarMul (R : Type u) [Mul R] extends InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, star (r * s) = star s * star r

export StarMul (star_mul)

attribute [simp 900] star_mul

section StarMul

variable [Mul R] [StarMul R]

/-
**star_star_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_star_mul (x y : R) : star (star x * y) = star y * x
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]
/-
**star_mul_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_mul_star (x y : R) : star (x * star y) = y * star x
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]

@[simp]
/-
**semiconjBy_star_star_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：semiconjBy_star_star_star {x y z : R} : SemiconjBy (star x) (star z) (star
 y) ↔ SemiconjBy x y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem semiconjBy_star_star_star {x y z : R} :
    SemiconjBy (star x) (star z) (star y) ↔ SemiconjBy x y z := by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star

@[simp]
/-
**commute_star_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semiconjBy_star_star_star`：semiconjBy_star_star_star {x y z : R} : Semic
onjBy (star x) (star z) (star y) ↔ SemiconjBy x y z
-/
theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y :=
  semiconjBy_star_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star
/-
**commute_star_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `commute_star_star`：commute_star_star {x y : R} : Commute (star x) (star 
y) ↔ Commute x y
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star, star_star]

alias ⟨Commute.star_right, Commute.star_left⟩ := commute_star_comm

end StarMul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
/-
**star_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) = star x * st
ar y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
In a commutative ring, make `simp` prefer leaving the order unchanged.
-/
theorem star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)

/-- `star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
/-
**starMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ`
-/
def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }

/-- `star` as a `MulAut` for commutative `R`. -/
@[simps apply]
/-
**starMulAut** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starMulAut [CommSemigroup R] [StarMul R] : MulAut R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
`star` as a `MulAut` for commutative `R`.
-/
def starMulAut [CommSemigroup R] [StarMul R] : MulAut R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }

variable (R) in
@[simp]
/-
**star_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulEquiv.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOneClass M]
 [inst_1 : MulOneClass N] (h : M ≃* N), h 1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_one`：∀ {α : Type u_1} [inst : One α], MulOpposite.op 1 = 
1
-/
theorem star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm

@[simp]
/-
**Pi.star_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.star_mulSingle {ι : Type*} {R : ι -> Type*} [DecidableEq ι] [forall i, 
MulOneClass (R i)] [forall i, StarMul (R i)] (i : ι) (r : R i) : star (mulSingle
 i r) = mulSingle i (star r)
参数：R i；R i；i : ι；r : R i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.apply_mulSingle`：apply_mulSingle (f' : forall i, M i -> N i) (hf' : f
orall i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) : f' j (mulSingle i x j) = mulSin
gle i (f…
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
-/
lemma Pi.star_mulSingle {ι : Type*} {R : ι → Type*} [DecidableEq ι] [∀ i, MulOneClass (R i)]
    [∀ i, StarMul (R i)] (i : ι) (r : R i) : star (mulSingle i r) = mulSingle i (star r) := by
  ext; exact apply_mulSingle (fun _ ↦ star) (fun _ ↦ star_one _) ..

@[simp]
/-
**star_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_pow [Monoid R] [StarMul R] (x : R) (n : Nat) : star (x ^ n) = star x 
^ n
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_pow`：∀ {α : Type u_1} [inst : Monoid α] (x : α) (n : ℕ), 
MulOpposite.op (x ^ n) = MulOpposite.op x ^ n
-/
theorem star_pow [Monoid R] [StarMul R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]
/-
**star_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_inv`：∀ {α : Type u_1} [inst : Inv α] (x : α), MulOpposite
.op x⁻¹ = (MulOpposite.op x)⁻¹
-/
theorem star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
/-
**star_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_zpow [Group R] [StarMul R] (x : R) (z : Int) : star (x ^ z) = star x 
^ z
参数：x : R；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_zpow`：∀ {α : Type u_1} [inst : DivInvMonoid α] (x : α) (z
 : ℤ), MulOpposite.op (x ^ z) = MulOpposite.op x ^ z
-/
theorem star_zpow [Group R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
/-
**star_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / sta
r y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N

--- 原说明 ---
When multiplication is commutative, `star` preserves division.
-/
theorem star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / star y :=
  map_div (starMulAut : R ≃* R) _ _

/-- Any commutative monoid admits the trivial \*-structure.

See note [reducible non-instances].
-/
/-
**starMulOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：starMulOfComm {R : Type*} [CommMonoid R] : StarMul R where star x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any commutative monoid admits the trivial \*-structure.

See note [reducible non-instances].
-/
abbrev starMulOfComm {R : Type*} [CommMonoid R] : StarMul R where
  star x := x
  star_involutive _ := rfl
  star_mul := mul_comm

section

attribute [local instance] starMulOfComm

/-- Note that since `starMulOfComm` is reducible, `simp` can already prove this. -/
/-
**star_id_of_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_id_of_comm {R : Type*} [CommMonoid R] {x : R} : star x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that since `starMulOfComm` is reducible, `simp` can already prove this.
-/
theorem star_id_of_comm {R : Type*} [CommMonoid R] {x : R} : star x = x :=
  rfl

end

/-- A \*-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition. -/
/-
**StarAddMonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [AddMonoid R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A \*-additive monoid `R` is an additive monoid with an involutive `star` operati
on which
preserves addition.
-/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s

export StarAddMonoid (star_add)

attribute [simp] star_add

/-- `star` as an `AddEquiv` -/
@[simps! apply]
/-
**starAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s

--- 原说明 ---
`star` as an `AddEquiv`
-/
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R where
  toEquiv := Equiv.Perm.star
  map_add' := star_add

@[simp]
/-
**toEquiv_starAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toEquiv_starAddEquiv [AddMonoid R] [StarAddMonoid R] : (starAddEquiv : R ≃
+ R) = (Equiv.Perm.star : R ≃ R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_starAddEquiv [AddMonoid R] [StarAddMonoid R] :
    (starAddEquiv : R ≃+ R) = (Equiv.Perm.star : R ≃ R) :=
  rfl

@[simp]
/-
**symm_starAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_starAddEquiv [AddMonoid R] [StarAddMonoid R] : (starAddEquiv : R ≃+ R
).symm = starAddEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_starAddEquiv [AddMonoid R] [StarAddMonoid R] :
    (starAddEquiv : R ≃+ R).symm = starAddEquiv :=
  rfl

variable (R) in
@[simp]
/-
**star_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZeroClass 
M] [inst_1 : AddZeroClass N] (h : M ≃+ N), h 0 = 0
-/
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero

@[simp]
/-
**Pi.star_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.star_single {ι : Type*} {R : ι -> Type*} [DecidableEq ι] [forall i, Add
Monoid (R i)] [forall i, StarAddMonoid (R i)] (i : ι) (r : R i) : star (single i
 r) = single i (star r)
参数：R i；R i；i : ι；r : R i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
lemma Pi.star_single {ι : Type*} {R : ι → Type*} [DecidableEq ι] [∀ i, AddMonoid (R i)]
    [∀ i, StarAddMonoid (R i)] (i : ι) (r : R i) : star (single i r) = single i (star r) := by
  ext; exact apply_single (fun _ ↦ star) (fun _ ↦ star_zero _) ..

@[simp]
/-
**star_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZer
oClass M] [inst_1 : AddZeroClass N] (h : M ≃+ N) {x : M}, h x = 0 ↔ x = 0
-/
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff (M := R)
/-
**star_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x != 0 ↔ x != 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 := by
  simp only [ne_eq, star_eq_zero]

@[simp]
/-
**star_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_neg`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x : G), h (-x) = -h x
-/
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _

@[simp]
/-
**star_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r 
- star s
参数：r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
-/
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _
/-
**star_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_nsmul [AddMonoid R] [StarAddMonoid R] (n : Nat) (x : R) : star (n • x
) = n • star x
参数：n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (n : ℕ) (x : R) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _
/-
**star_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_zsmul [AddGroup R] [StarAddMonoid R] (n : Int) (x : R) : star (n • x)
 = n • star x
参数：n : Int；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
-/
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (n : ℤ) (x : R) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

/-- A \*-ring `R` is a non-unital, non-associative (semi)ring with an involutive `star` operation
which is additive which makes `R` with its multiplicative structure into a \*-multiplication
(i.e. `star (r * s) = star s * star r`). -/
/-
**StarRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [NonUnitalNonAssocSemiring R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A \*-ring `R` is a non-unital, non-associative (semi)ring with an involutive `st
ar` operation
which is additive which makes `R` with its multiplicative structure into a \*-mu
ltiplication
(i.e. `star (r * s) = star s * star r`).
-/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalNonAssocSemiring R] [StarRing R] :
    StarAddMonoid R where
  star_add := StarRing.star_add

/-- `star` as a `RingEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
/-
**starRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`star` as a `RingEquiv` from `R` to `Rᵐᵒᵖ`
-/
def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

@[simp, norm_cast]
/-
**star_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_natCast [NonAssocSemiring R] [StarRing R] (n : Nat) : star (n : R) = 
n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MulOpposite.unop_natCast`：unop_natCast [NatCast R] (n : Nat) : unop (n :
 Rᵐᵒᵖ) = n
-/
theorem star_natCast [NonAssocSemiring R] [StarRing R] (n : ℕ) : star (n : R) = n :=
  (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)

@[simp]
/-
**star_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_ofNat [NonAssocSemiring R] [StarRing R] (n : Nat) [n.AtLeastTwo] : st
ar (ofNat(n) : R) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_natCast`：star_natCast [NonAssocSemiring R] [StarRing R] (n : Nat) :
 star (n : R) = n
-/
theorem star_ofNat [NonAssocSemiring R] [StarRing R] (n : ℕ) [n.AtLeastTwo] :
    star (ofNat(n) : R) = ofNat(n) :=
  star_natCast _

section

@[simp, norm_cast]
/-
**star_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_intCast [NonAssocRing R] [StarRing R] (z : Int) : star (z : R) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MulOpposite.unop_intCast`：unop_intCast [IntCast R] (n : Int) : unop (n :
 Rᵐᵒᵖ) = n
-/
theorem star_intCast [NonAssocRing R] [StarRing R] (z : ℤ) : star (z : R) = z :=
  (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)

end

section CommSemiring

variable [CommSemiring R] [StarRing R]

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
/-
**starRingAut** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starRingAut : RingAut R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`star` as a ring automorphism, for commutative `R`.
-/
def starRingAut : RingAut R :=
  { starAddEquiv, starMulAut (R := R) with toFun := star, invFun := star }

variable (R) in
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the scope `ComplexConjugate`.

Note that this is the preferred form (over `starRingAut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑starRingAut : R →* R)`. -/
@[implicit_reducible]
/-
**starRingEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starRingEnd : R ->+* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`star` as a ring endomorphism, for commutative `R`. This is used to denote compl
ex
conjugation, and is available under the notation `conj` in the scope `ComplexCon
jugate`.

Note that this is the preferred form (over `starRingAut`, available under the sa
me hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved,
 as would be the
case for `(↑starRingAut : R →* R)`.
-/
def starRingEnd : R →+* R where
  toFun := star
  __ := (@starRingAut R _ _).toRingHom

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _

/-- This is not a simp lemma, since we usually want simp to keep `starRingEnd` bundled.
For example, for complex conjugation, we don't want simp to turn `conj x`
into the bare function `star x` automatically since most lemmas are about `conj x`. -/
/-
**starRingEnd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starRingEnd_apply (x : R) : starRingEnd R x = star x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not a simp lemma, since we usually want simp to keep `starRingEnd` bundl
ed.
For example, for complex conjugation, we don't want simp to turn `conj x`
into the bare function `star x` automatically since most lemmas are about `conj 
x`.
-/
theorem starRingEnd_apply (x : R) : starRingEnd R x = star x := rfl

-- Not `@[simp]` because `simp` can already prove it.
/-
**starRingEnd_self_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x := star_star x
/-
**RingHom.involutiveStar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingHom.involutiveStar {S : Type*} [NonAssocSemiring S] : InvolutiveStar (
S ->+* R) where toStar
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance RingHom.involutiveStar {S : Type*} [NonAssocSemiring S] : InvolutiveStar (S →+* R) where
  toStar := { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]
/-
**RingHom.star_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S ->+* R) : Star.st
ar f = RingHom.comp (starRingEnd R) f
参数：f : S ->+* R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S →+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl
/-
**RingHom.star_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S ->+* R) (s : S)
 : star f s = star (f s)
参数：f : S ->+* R；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S →+* R) (s : S) :
    star f s = star (f s) := rfl

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply

alias RCLike.conj_conj := starRingEnd_self_apply

open scoped ComplexConjugate
/-
**conj_trivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing R] [TrivialStar 
R] (a : R), (starRingEnd R) a = a
参数：a : R；starRingEnd R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
-/
@[simp] lemma conj_trivial [TrivialStar R] (a : R) : conj a = a := star_trivial _

end CommSemiring

@[simp]
/-
**star_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_inv`：∀ {α : Type u_1} [inst : Inv α] (x : α), MulOpposite
.op x⁻¹ = (MulOpposite.op x)⁻¹
-/
theorem star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| (map_inv₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

@[simp]
/-
**star_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_zpow [Group R] [StarMul R] (x : R) (z : Int) : star (x ^ z) = star x 
^ z
参数：x : R；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_zpow`：∀ {α : Type u_1} [inst : DivInvMonoid α] (x : α) (z
 : ℤ), MulOpposite.op (x ^ z) = MulOpposite.op x ^ z
-/
theorem star_zpow₀ [GroupWithZero R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| (map_zpow₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
/-
**star_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / sta
r y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N

--- 原说明 ---
When multiplication is commutative, `star` preserves division.
-/
theorem star_div₀ [CommGroupWithZero R] [StarMul R] (x y : R) : star (x / y) = star x / star y := by
  apply op_injective
  rw [division_def, op_div, mul_comm, star_mul, star_inv₀, op_mul, op_inv]

/-- Any commutative semiring admits the trivial \*-structure.

See note [reducible non-instances].
-/
/-
**starRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：starRingOfComm {R : Type*} [CommSemiring R] : StarRing R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any commutative semiring admits the trivial \*-structure.

See note [reducible non-instances].
-/
abbrev starRingOfComm {R : Type*} [CommSemiring R] : StarRing R :=
  { starMulOfComm with
    star_add := fun _ _ => rfl }
/-
**Nat.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instStarRing : StarRing Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Nat.instStarRing : StarRing ℕ := starRingOfComm
/-
**Int.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instStarRing : StarRing Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Int.instStarRing : StarRing ℤ := starRingOfComm
/-
**Nat.instTrivialStar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instTrivialStar : TrivialStar Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Nat.instTrivialStar : TrivialStar ℕ := ⟨fun _ ↦ rfl⟩
/-
**Int.instTrivialStar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instTrivialStar : TrivialStar Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Int.instTrivialStar : TrivialStar ℤ := ⟨fun _ ↦ rfl⟩

/-- A star module `A` over a star ring `R` is a module which is a star additive monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[Semiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]`, and that
the statement only requires `[Star R] [Star A] [SMul R A]`.

If used as `[CommRing R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]`, this represents a
star algebra.
-/
/-
**StarModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (A : Type v) → [Star R] → [Star A] → [SMul R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A star module `A` over a star ring `R` is a module which is a star additive mono
id,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[Semiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]`, an
d that
the statement only requires `[Star R] [Star A] [SMul R A]`.

If used as `[CommRing R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]`, 
this represents a
star algebra.
-/
class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  /-- `star` commutes with scalar multiplication -/
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a

export StarModule (star_smul)

attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `Monoid.toMulAction`. -/
/-
**StarMul.toStarModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StarMul.toStarModule [CommMonoid R] [StarMul R] : StarModule R R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y

--- 原说明 ---
A commutative star monoid is a star module over itself via `Monoid.toMulAction`.
-/
instance StarMul.toStarModule [CommMonoid R] [StarMul R] : StarModule R R :=
  ⟨star_mul'⟩
/-
**StarAddMonoid.toStarModuleNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StarAddMonoid.toStarModuleNat {α} [AddMonoid α] [StarAddMonoid α] : StarMo
dule Nat α where star_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `star_nsmul`：star_nsmul [AddMonoid R] [StarAddMonoid R] (n : Nat) (x : R)
 : star (n • x) = n • star x
-/
instance StarAddMonoid.toStarModuleNat {α} [AddMonoid α] [StarAddMonoid α] : StarModule ℕ α where
  star_smul := star_nsmul
/-
**StarAddMonoid.toStarModuleInt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StarAddMonoid.toStarModuleInt {α} [AddGroup α] [StarAddMonoid α] : StarMod
ule Int α where star_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `star_zsmul`：star_zsmul [AddGroup R] [StarAddMonoid R] (n : Int) (x : R) 
: star (n • x) = n • star x
-/
instance StarAddMonoid.toStarModuleInt {α} [AddGroup α] [StarAddMonoid α] : StarModule ℤ α where
  star_smul := star_zsmul

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ). -/
/-
**RingHomInvPair.** 是 Mathlib 中的一个实例，位于命名空间 `RingHomInvPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).
-/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

section

/-- `StarHomClass F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
/-
**StarHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (R : outParam (Type u_2)) → (S : outParam (Type u_3)) → [
Star R] → [Star S] → [FunLike F R S] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`StarHomClass F R S` states that `F` is a type of `star`-preserving maps from `R
` to `S`.
-/
class StarHomClass (F : Type*) (R S : outParam Type*) [Star R] [Star S] [FunLike F R S] : Prop where
  /-- the maps preserve star -/
  map_star : ∀ (f : F) (r : R), f (star r) = star (f r)

export StarHomClass (map_star)

end

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarMul R]

/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul Rˣ where
  star u :=
    { val := star u
      inv := star ↑u⁻¹
      val_inv := (star_mul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _
      inv_val := (star_mul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]
/-
**Units.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R)
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl

@[simp]
/-
**Units.coe_star_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R)
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => star_smul (u : R) a⟩

end Units

@[aesop safe apply]
/-
**IsUnit.star** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {R : Type u} [inst : Monoid R] [inst_1 : StarMul R] {a : R}, IsUnit a → 
IsUnit (star a)
参数：star a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsUnit.star [Monoid R] [StarMul R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨Star.star u, hu ▸ rfl⟩

@[simp, grind =]
/-
**isUnit_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.star`：∀ {R : Type u} [inst : Monoid R] [inst_1 : StarMul R] {a : 
R}, IsUnit a → IsUnit (star a)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

@[grind _=_]
/-
**Ring.inverse_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_star [Semiring R] [StarRing R] (a : R) : (star a)⁻¹ʳ = star (
a⁻¹ʳ)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.coe_star`：coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R)
· 使用定理 `Units.coe_star_inv`：coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R
)
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_star`：isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a
) ↔ IsUnit a
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    (star a)⁻¹ʳ = star (a⁻¹ʳ) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt isUnit_star.mp ha), star_zero]
/-
**Invertible.star** 是 Mathlib 中的一个定义，位于命名空间 `Invertible`。
形式化陈述：{R : Type u_1} → [inst : MulOneClass R] → [inst_1 : StarMul R] → (r : R) →
 [Invertible r] → Invertible (star r)
参数：r : R；star r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance Invertible.star {R : Type*} [MulOneClass R] [StarMul R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := Star.star (⅟r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]
/-
**star_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r] [Inve
rtible (star r)] : star (⅟r) = ⅟(star r)
参数：r : R；star r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟r) = ⅟(star r) := by
  rw [← mul_one (star (⅟r)), ← mul_invOf_self (star r), ← mul_assoc, ← star_mul]
  simp

section Regular

/-
**IsLeftRegular.star** 是 Mathlib 中的一个定理，位于命名空间 `IsLeftRegular`。
形式化陈述：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {x : R}, IsLeftRegular 
x → IsRightRegular (star x)
参数：star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem IsLeftRegular.star [Mul R] [StarMul R] {x : R} (hx : IsLeftRegular x) :
    IsRightRegular (star x) :=
  fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h
/-
**IsRightRegular.star** 是 Mathlib 中的一个定理，位于命名空间 `IsRightRegular`。
形式化陈述：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {x : R}, IsRightRegular
 x → IsLeftRegular (star x)
参数：star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem IsRightRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRightRegular x) :
    IsLeftRegular (star x) :=
  fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h
/-
**IsRegular.star** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {x : R}, IsRegular x → 
IsRegular (star x)
参数：star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightRegular.star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] 
{x : R}, IsRightRegular x → IsLeftRegular (star x)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `IsLeftRegular.star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {
x : R}, IsLeftRegular x → IsRightRegular (star x)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
-/
protected theorem IsRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRegular x) :
    IsRegular (star x) :=
  ⟨hx.right.star, hx.left.star⟩

@[simp]
/-
**isRightRegular_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_star_iff [Mul R] [StarMul R] {x : R} : IsRightRegular (star
 x) ↔ IsLeftRegular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightRegular.star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] 
{x : R}, IsRightRegular x → IsLeftRegular (star x)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `IsLeftRegular.star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {
x : R}, IsLeftRegular x → IsRightRegular (star x)
-/
theorem isRightRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRightRegular (star x) ↔ IsLeftRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
/-
**isLeftRegular_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_star_iff [Mul R] [StarMul R] {x : R} : IsLeftRegular (star x
) ↔ IsRightRegular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {
x : R}, IsLeftRegular x → IsRightRegular (star x)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `IsRightRegular.star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] 
{x : R}, IsRightRegular x → IsLeftRegular (star x)
-/
theorem isLeftRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsLeftRegular (star x) ↔ IsRightRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
/-
**isRegular_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_star_iff [Mul R] [StarMul R] {x : R} : IsRegular (star x) ↔ IsRe
gular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRegular_iff`：isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ I
sRightRegular c
· 使用定理 `isRightRegular_star_iff`：isRightRegular_star_iff [Mul R] [StarMul R] {x 
: R} : IsRightRegular (star x) ↔ IsLeftRegular x
· 使用定理 `isLeftRegular_star_iff`：isLeftRegular_star_iff [Mul R] [StarMul R] {x : 
R} : IsLeftRegular (star x) ↔ IsRightRegular x
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRegular (star x) ↔ IsRegular x := by
  rw [isRegular_iff, isRegular_iff, isRightRegular_star_iff, isLeftRegular_star_iff, and_comm]

end Regular

namespace Function.Injective

variable {S : Type v} (f : R → S)

/-- Given a type endowed with `star`, that `star` is involutive if it admits an injective map that
preserves `star` to a type with whose `star` is involutive. See note [reducible non-instances]. -/
/-
**Function.Injective.involutiveStar** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injectiv
e`。
形式化陈述：{R : Type u} →   {S : Type v} →     (f : R → S) →       [inst : Star R] → 
        [inst_1 : InvolutiveStar S] → Function.Injective f → (∀ (x : R), f (star
 x) = star (f x)) → InvolutiveStar R
参数：f : R → S；∀ (x : R), f (star x) = star (f x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a type endowed with `star`, that `star` is involutive if it admits an inje
ctive map that
preserves `star` to a type with whose `star` is involutive. See note [reducible 
non-instances].
-/
protected abbrev involutiveStar [Star R] [InvolutiveStar S] (hf : Injective f)
    (star : ∀ x, f (star x) = star (f x)) : InvolutiveStar R where
  star_involutive r := hf <| by rw [star, star, star_star]

/-- A type endowed with `star` and `*` is a star magma if it admits an injective map that
preserves `star` and `*` to star magma.  See note [reducible non-instances]. -/
/-
**Function.Injective.starMul** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{R : Type u} →   {S : Type v} →     (f : R → S) →       [inst : Star R] → 
        [inst_1 : Mul R] →           [inst_2 : Mul S] →             [inst_3 : St
arMul S] →               Function.Injective f →                 (∀ (x : R), f (s
tar x) = star (f x)) → (∀ (x y : R), f (x * y) = f x * f y) → StarMul R
参数：f : R → S；∀ (x : R), f (star x) = star (f x)；∀ (x y : R), f (x * y) = f x * f
 y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type endowed with `star` and `*` is a star magma if it admits an injective map
 that
preserves `star` and `*` to star magma.  See note [reducible non-instances].
-/
protected abbrev starMul [Star R] [Mul R] [Mul S] [StarMul S] (hf : Injective f)
    (star : ∀ x, f (star x) = star (f x)) (mul : ∀ x y, f (x * y) = f x * f y) :
    StarMul R where
  toInvolutiveStar := hf.involutiveStar _ star
  star_mul x y := hf <| by rw [star, mul, star_mul, mul, star, star]

/-- A additive monoid endowed with `star` is an additive star monoid if it admits an injective map
that preserves `star` and `+` to an additive star monoid.  See note [reducible non-instances]. -/
/-
**Function.Injective.starAddMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：{R : Type u} →   {S : Type v} →     (f : R → S) →       [inst : Star R] → 
        [inst_1 : AddMonoid R] →           [inst_2 : AddMonoid S] →             
[inst_3 : StarAddMonoid S] →               Function.Injective f →               
  (∀ (x : R), f (star x) = star (f x)) → (∀ (x y : R), f (x + y) = f x + f y) → 
StarAddMonoid R
参数：f : R → S；∀ (x : R), f (star x) = star (f x)；∀ (x y : R), f (x + y) = f x + f
 y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A additive monoid endowed with `star` is an additive star monoid if it admits an
 injective map
that preserves `star` and `+` to an additive star monoid.  See note [reducible n
on-instances].
-/
protected abbrev starAddMonoid [Star R] [AddMonoid R] [AddMonoid S] [StarAddMonoid S]
    (hf : Injective f) (star : ∀ x, f (star x) = star (f x)) (add : ∀ x y, f (x + y) = f x + f y) :
    StarAddMonoid R where
  toInvolutiveStar := hf.involutiveStar f star
  star_add x y := hf <| by rw [star, add, star_add, add, star, star]

/-- A non-unital non-associative ring endowed with `star` is a star ring if it admits an injective
map that preserves `star`, `*` and `+` to a star ring. See note [reducible non-instances]. -/
/-
**Function.Injective.starRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{R : Type u} →   {S : Type v} →     (f : R → S) →       [inst : Star R] → 
        [inst_1 : NonUnitalNonAssocSemiring R] →           [inst_2 : NonUnitalNo
nAssocSemiring S] →             [inst_3 : StarRing S] →               Function.I
njective f →                 (∀ (x : R), f (star x) = star (f x)) →             
      (∀ (x y : R), f (x + y) = f x + f y) → (∀ (x y : R), f (x * y) = f x * f y
) → StarRing R
参数：f : R → S；∀ (x : R), f (star x) = star (f x)；∀ (x y : R), f (x + y) = f x + f
 y；∀ (x y : R), f (x * y) = f x * f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital non-associative ring endowed with `star` is a star ring if it admit
s an injective
map that preserves `star`, `*` and `+` to a star ring. See note [reducible non-i
nstances].
-/
protected abbrev starRing [Star R] [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    [StarRing S] (hf : Injective f) (star : ∀ x, f (star x) = star (f x))
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
    StarRing R :=
  { hf.starMul f star mul, hf.starAddMonoid f star add with }

/-- A type endowed with `star` is a star module over some other type with `star` if it admits an
injective map that preserves `star` and `•` to a star module. See note [reducible non-instances]. -/
/-
**Function.Injective.starModule** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {R : Type u} {S : Type v} (f : R → S) (𝕜 : Type u_1) [inst : Star 𝕜] [in
st_1 : SMul 𝕜 R] [inst_2 : Star R]   [inst_3 : SMul 𝕜 S] [inst_4 : Star S] [Star
Module 𝕜 S],   Function.Injective f →     (∀ (x : R), f (star x) = star (f x)) →
 (∀ (r : 𝕜) (x : R), f (r • x) = r • f x) → StarModule 𝕜 R
参数：f : R → S；𝕜 : Type u_1；∀ (x : R), f (star x) = star (f x)；∀ (r : 𝕜) (x : R), 
f (r • x) = r • f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …

--- 原说明 ---
A type endowed with `star` is a star module over some other type with `star` if 
it admits an
injective map that preserves `star` and `•` to a star module. See note [reducibl
e non-instances].
-/
protected lemma starModule (𝕜 : Type*) [Star 𝕜] [SMul 𝕜 R]
    [Star R] [SMul 𝕜 S] [Star S] [StarModule 𝕜 S] (hf : Injective f)
    (star : ∀ x, f (star x) = star (f x)) (smul : ∀ (r : 𝕜) x, f (r • x) = r • f x) :
    StarModule 𝕜 R where
  star_smul r x := hf <| by rw [star, smul, star_smul, smul, star]

end Function.Injective

namespace MulOpposite

/-- The opposite type carries the same star operation. -/
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite type carries the same star operation.
-/
instance [Star R] : Star Rᵐᵒᵖ where star r := op (star r.unop)

@[simp]
/-
**MulOpposite.unop_star** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r)
参数：r : Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl

@[simp]
/-
**MulOpposite.op_star** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_star [Star R] (r : R) : op (star r) = star (op r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ where
  star_involutive r := unop_injective (star_star r.unop)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [StarMul R] : StarMul Rᵐᵒᵖ where
  star_mul x y := unop_injective (star_mul y.unop x.unop)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring R] [StarRing R] : StarRing Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Star R] [Star M] [SMul R M] [StarModule R M] :
    StarModule R Mᵐᵒᵖ where
  star_smul r x := unop_injective (star_smul r x.unop)

end MulOpposite

/-- A commutative star monoid is a star module over its opposite via
`Monoid.toOppositeMulAction`. -/
/-
**StarSemigroup.toOpposite_starModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StarSemigroup.toOpposite_starModule [CommMonoid R] [StarMul R] : StarModul
e Rᵐᵒᵖ R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y

--- 原说明 ---
A commutative star monoid is a star module over its opposite via
`Monoid.toOppositeMulAction`.
-/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarMul R] :
    StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
