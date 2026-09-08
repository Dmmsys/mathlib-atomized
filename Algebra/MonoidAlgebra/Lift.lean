/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Lifting monoid algebras

This file defines `liftNC`. For the definition of `MonoidAlgebra.lift`, see
`Mathlib/Algebra/MonoidAlgebra/Basic.lean`.

## Main results
* `MonoidAlgebra.liftNC`, `AddMonoidAlgebra.liftNC`: lift a homomorphism `f : k →+ R` and a
  function `g : G → R` to a homomorphism `k[G] →+ R`.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

/-- A non-commutative version of `MonoidAlgebra.lift`: given an additive homomorphism `f : k →+ R`
and a homomorphism `g : G → R`, returns the additive homomorphism from
`k[G]` such that `liftNC f g (single a b) = f b * g a`. If `f` is a ring homomorphism
and the range of either `f` or `g` is in center of `R`, then the result is a ring homomorphism.  If
`R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra homomorphism called
`MonoidAlgebra.lift`. -/
/-
**MonoidAlgebra.liftNC** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNC (f : k ->+ R) (g : G -> R) : k[G] ->+ R
参数：f : k ->+ R；g : G -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-commutative version of `MonoidAlgebra.lift`: given an additive homomorphis
m `f : k →+ R`
and a homomorphism `g : G → R`, returns the additive homomorphism from
`k[G]` such that `liftNC f g (single a b) = f b * g a`. If `f` is a ring homomor
phism
and the range of either `f` or `g` is in center of `R`, then the result is a rin
g homomorphism.  If
`R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra hom
omorphism called
`MonoidAlgebra.lift`.
-/
def liftNC (f : k →+ R) (g : G → R) : k[G] →+ R :=
  (liftAddHom fun x ↦ .comp (.mulRight (g x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]
/-
**MonoidAlgebra.liftNC_single** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNC_single (f : k ->+ R) (g : G -> R) (a : G) (b : k) : liftNC f g (sin
gle a b) = f b * g a
参数：f : k ->+ R；g : G -> R；a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.liftAddHom_apply_single`：liftAddHom_apply_single [AddZeroClass M
] [AddCommMonoid N] (f : α -> M ->+ N) (a : α) (b : M) : (liftAddHom (α
-/
theorem liftNC_single (f : k →+ R) (g : G → R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g a :=
  liftAddHom_apply_single _ _ _

end

section Mul

variable [Semiring k] [Mul G] [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidAlgebra.liftNC_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R] (f 
: k ->+* R) (g : g_hom) (a b : k[G]) (h_comm : forall {x y}, y in a.coeff.suppor
t -> Commute (f (b.coeff x)) (g y)) : liftNC (f : k ->+ R) g (a * b) = liftNC (f
 : k ->+ R) g a * liftNC (f : k ->+ R) g b
参数：f : k ->+* R；g : g_hom；a b : k[G]；h_comm : forall {x y}, y in a.coeff.support
 -> Commute (f (b.coeff x)) (g y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidAlgebra.sum_coeff_single`：sum_coeff_single (f : R[M]) : f.coeff.su
m single = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.mul_def`：mul_def (x y : R[M]) : x * y = x.coeff.sum fun m₁
 r₁ => y.coeff.sum fun m₂ r₂ => single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : G -> R) (a
 : G) (b : k) : liftNC f g (single a b) = f b * g a
· 使用定理 `Finsupp.sum_mul`：Finsupp.sum_mul (b : S) (s : α ->₀ R) {f : α -> R -> S}
 : s.sum f * b = s.sum fun a c => f a c * b
· 使用定理 `Finsupp.mul_sum`：Finsupp.mul_sum (b : S) (s : α ->₀ R) {f : α -> R -> S}
 : b * s.sum f = s.sum fun a c => b * f a c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) (a b : k[G])
    (h_comm : ∀ {x y}, y ∈ a.coeff.support → Commute (f (b.coeff x)) (g y)) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

end Mul

section One

variable [NonAssocSemiring R] [Semiring k] [One G]

@[simp]
/-
**MonoidAlgebra.liftNC_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNC_one {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R] (f 
: k ->+* R) (g : g_hom) : liftNC (f : k ->+ R) g 1 = 1
参数：f : k ->+* R；g : g_hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : G -> R) (a
 : G) (b : k) : liftNC f g (single a b) = f b * g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftNC_one {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) :
    liftNC (f : k →+ R) g 1 = 1 := by simp [one_def]

end One

/-! #### Semiring structure -/
section Semiring

variable [Semiring k] [Monoid G] [Semiring R] [Semiring S] [Semiring T] [Monoid M]

/-- `liftNC` as a `RingHom`, for when `f x` and `g y` commute -/
/-
**MonoidAlgebra.liftNCRingHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNCRingHom (f : k ->+* R) (g : G ->* R) (h_comm : forall x y, Commute (
f x) (g y)) : k[G] ->+* R
参数：f : k ->+* R；g : G ->* R；h_comm : forall x y, Commute (f x) (g y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftNC` as a `RingHom`, for when `f x` and `g y` commute
-/
def liftNCRingHom (f : k →+* R) (g : G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) : k[G] →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]
/-
**MonoidAlgebra.liftNCRingHom_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNCRingHom_single (f : k ->+* R) (g : G ->* R) (h_comm) (a : G) (b : k)
 : liftNCRingHom f g h_comm (single a b) = f b * g a
参数：f : k ->+* R；g : G ->* R；h_comm；a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : G -> R) (a
 : G) (b : k) : liftNC f g (single a b) = f b * g a
-/
lemma liftNCRingHom_single (f : k →+* R) (g : G →* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end Semiring

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

/-- A non-commutative version of `AddMonoidAlgebra.lift`: given an additive homomorphism
`f : k →+ R` and a map `g : Multiplicative G → R`, returns the additive
homomorphism from `k[G]` such that `liftNC f g (single a b) = f b * g a`. If `f`
is a ring homomorphism and the range of either `f` or `g` is in center of `R`, then the result is a
ring homomorphism.  If `R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra
homomorphism called `AddMonoidAlgebra.lift`. -/
/-
**AddMonoidAlgebra.liftNC** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNC (f : k ->+ R) (g : Multiplicative G -> R) : k[G] ->+ R
参数：f : k ->+ R；g : Multiplicative G -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-commutative version of `AddMonoidAlgebra.lift`: given an additive homomorp
hism
`f : k →+ R` and a map `g : Multiplicative G → R`, returns the additive
homomorphism from `k[G]` such that `liftNC f g (single a b) = f b * g a`. If `f`
is a ring homomorphism and the range of either `f` or `g` is in center of `R`, t
hen the result is a
ring homomorphism.  If `R` is a `k`-algebra and `f = algebraMap k R`, then the r
esult is an algebra
homomorphism called `AddMonoidAlgebra.lift`.
-/
def liftNC (f : k →+ R) (g : Multiplicative G → R) : k[G] →+ R :=
  (liftAddHom fun x ↦ .comp (.mulRight (g <| .ofAdd x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]
/-
**AddMonoidAlgebra.liftNC_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNC_single (f : k ->+ R) (g : Multiplicative G -> R) (a : G) (b : k) : 
liftNC f g (single a b) = f b * g (Multiplicative.ofAdd a)
参数：f : k ->+ R；g : Multiplicative G -> R；a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.liftAddHom_apply_single`：liftAddHom_apply_single [AddZeroClass M
] [AddCommMonoid N] (f : α -> M ->+ N) (a : α) (b : M) : (liftAddHom (α
-/
theorem liftNC_single (f : k →+ R) (g : Multiplicative G → R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g (Multiplicative.ofAdd a) :=
  liftAddHom_apply_single _ _ _

end

section Mul

variable [Semiring k] [Add G] [Semiring R]

/-
**AddMonoidAlgebra.liftNC_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNC_mul {g_hom : Type*} [FunLike g_hom (Multiplicative G) R] [MulHomCla
ss g_hom (Multiplicative G) R] (f : k ->+* R) (g : g_hom) (a b : k[G]) (h_comm :
 forall {x y}, y in a.coeff.support -> Commute (f (b.coeff x)) (g <| .ofAdd y)) 
: liftNC (f : k ->+ R) g (a * b) = liftNC (f : k ->+ R) g a * liftNC (f : k ->+ 
R) g b
参数：Multiplicative G；Multiplicative G；f : k ->+* R；g : g_hom；a b : k[G]；h_comm : 
forall {x y}, y in a.coeff.support -> Commute (f (b.coeff x)) (g <| .ofAdd y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.sum_coeff_single`：∀ {R : Type u_1} {M : Type u_4} [inst
 : Semiring R] (f : AddMonoidAlgebra R M), f.coeff.sum AddMonoidAlgebra.single =
 f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.mul_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Add M] (x y : AddMonoidAlgebra R M),   x * y = x.coeff.sum fun m
₁ r₁ => y.coef…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddMonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : Multipl
icative G -> R) (a : G) (b : k) : liftNC f g (single a b) = f b * g (Multiplicat
ive.ofAdd a)
· 使用定理 `Finsupp.sum_mul`：Finsupp.sum_mul (b : S) (s : α ->₀ R) {f : α -> R -> S}
 : s.sum f * b = s.sum fun a c => f a c * b
· 使用定理 `Finsupp.mul_sum`：Finsupp.mul_sum (b : S) (s : α ->₀ R) {f : α -> R -> S}
 : b * s.sum f = s.sum fun a c => b * f a c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftNC_mul {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [MulHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) (a b : k[G])
    (h_comm : ∀ {x y}, y ∈ a.coeff.support → Commute (f (b.coeff x)) (g <| .ofAdd y)) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

end Mul

section One

variable [Semiring k] [Zero G] [NonAssocSemiring R]

@[simp]
/-
**AddMonoidAlgebra.liftNC_one** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNC_one {g_hom : Type*} [FunLike g_hom (Multiplicative G) R] [OneHomCla
ss g_hom (Multiplicative G) R] (f : k ->+* R) (g : g_hom) : liftNC (f : k ->+ R)
 g 1 = 1
参数：Multiplicative G；Multiplicative G；f : k ->+* R；g : g_hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.liftNC_one`：liftNC_one {g_hom : Type*} [FunLike g_hom G R]
 [OneHomClass g_hom G R] (f : k ->+* R) (g : g_hom) : liftNC (f : k ->+ R) g 1 =
 1
-/
theorem liftNC_one {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [OneHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) : liftNC (f : k →+ R) g 1 = 1 :=
  MonoidAlgebra.liftNC_one f g

end One

/-! #### Semiring structure -/
section Semiring

variable [Semiring k] [AddMonoid G] [Semiring R] [Semiring S] [Semiring T] [AddMonoid M]

/-- `liftNC` as a `RingHom`, for when `f` and `g` commute -/
/-
**AddMonoidAlgebra.liftNCRingHom** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNCRingHom (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm : forall
 x y, Commute (f x) (g y)) : k[G] ->+* R
参数：f : k ->+* R；g : Multiplicative G ->* R；h_comm : forall x y, Commute (f x) (g
 y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftNC` as a `RingHom`, for when `f` and `g` commute
-/
def liftNCRingHom (f : k →+* R) (g : Multiplicative G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    k[G] →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]
/-
**AddMonoidAlgebra.liftNCRingHom_single** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlge
bra`。
形式化陈述：liftNCRingHom_single (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm) 
(a : G) (b : k) : liftNCRingHom f g h_comm (single a b) = f b * g (.ofAdd a)
参数：f : k ->+* R；g : Multiplicative G ->* R；h_comm；a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : Multipl
icative G -> R) (a : G) (b : k) : liftNC f g (single a b) = f b * g (Multiplicat
ive.ofAdd a)
-/
lemma liftNCRingHom_single (f : k →+* R) (g : Multiplicative G →* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g (.ofAdd a) :=
  liftNC_single _ _ _ _

end Semiring

end AddMonoidAlgebra

