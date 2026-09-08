/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Separable

/-!

# Perfect fields and rings

In this file we define perfect fields, together with a generalisation to (commutative) rings in
prime characteristic.

## Main definitions / statements:
* `PerfectRing`: a ring of characteristic `p` (prime) is said to be perfect in the sense of Serre,
  if its absolute Frobenius map `x ↦ xᵖ` is bijective.
* `PerfectField`: a field `K` is said to be perfect if every irreducible polynomial over `K` is
  separable.
* `PerfectRing.toPerfectField`: a field that is perfect in the sense of Serre is a perfect field.
* `PerfectField.toPerfectRing`: a perfect field of characteristic `p` (prime) is perfect in the
  sense of Serre.
* `PerfectField.ofCharZero`: all fields of characteristic zero are perfect.
* `PerfectField.ofFinite`: all finite fields are perfect.
* `PerfectField.separable_iff_squarefree`: a polynomial over a perfect field is separable iff
  it is square-free.
* `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `Algebra.IsAlgebraic.perfectField`:
  if `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is separable,
  and `L` is also a perfect field.

-/

@[expose] public section

open Function Polynomial

/-- A perfect ring of characteristic `p` (prime) in the sense of Serre.

NB: This is not related to the concept with the same name introduced by Bass (related to projective
covers of modules). -/
/-
**PerfectRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → ℕ → [Pow R ℕ] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A perfect ring of characteristic `p` (prime) in the sense of Serre.

NB: This is not related to the concept with the same name introduced by Bass (re
lated to projective
covers of modules).
-/
class PerfectRing (R : Type*) (p : ℕ) [Pow R ℕ] : Prop where
  /-- A ring is perfect if the Frobenius map is bijective. -/
  bijective_frobenius : Bijective fun x : R ↦ x ^ p

section PerfectRing

section Monoid
variable (M : Type*) (p q : ℕ) [CommMonoid M] [PerfectRing M p] [PerfectRing M q]

namespace PerfectRing

/-
**PerfectRing.one** 是 Mathlib 中的一个实例，位于命名空间 `PerfectRing`。
形式化陈述：one : PerfectRing M 1
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
instance one : PerfectRing M 1 :=
  ⟨by simpa using! bijective_id⟩
/-
**PerfectRing.mul** 是 Mathlib 中的一个实例，位于命名空间 `PerfectRing`。
形式化陈述：mul : PerfectRing M (p * q)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `PerfectRing.bijective_frobenius`：∀ {R : Type u_1} {p : ℕ} {inst : Pow R 
ℕ} [self : PerfectRing R p], Function.Bijective fun x => x ^ p
-/
instance mul : PerfectRing M (p * q) :=
  ⟨by simp_rw [pow_mul]; exact PerfectRing.bijective_frobenius.comp PerfectRing.bijective_frobenius⟩
/-
**PerfectRing.pow** 是 Mathlib 中的一个实例，位于命名空间 `PerfectRing`。
形式化陈述：pow (n : Nat) : PerfectRing M (p ^ n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pow (n : ℕ) : PerfectRing M (p ^ n) :=
  n.recOn (inferInstanceAs (PerfectRing M 1)) fun n _ ↦ inferInstanceAs (PerfectRing M (p ^ n * p))

end PerfectRing

/-- The `p`-th power automorphism for a perfect monoid. -/
@[simps! apply]
/-
**powMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powMulEquiv : M ≃* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-th power automorphism for a perfect monoid.
-/
noncomputable def powMulEquiv : M ≃* M :=
  .ofBijective (powMonoidHom p) PerfectRing.bijective_frobenius

@[simp]
/-
**powMulEquiv_symm_pow_p** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powMulEquiv_symm_pow_p (x : M) : ((powMulEquiv M p).symm x) ^ p = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem powMulEquiv_symm_pow_p (x : M) : ((powMulEquiv M p).symm x) ^ p = x :=
  (powMulEquiv M p).apply_symm_apply x
/-
**powMulEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M : Type u_1) [inst : CommMonoid M], powMulEquiv M 1 = MulEquiv.refl M
参数：M : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
@[simp] theorem powMulEquiv_one : powMulEquiv M 1 = .refl M :=
  MulEquiv.ext pow_one
/-
**powMulEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powMulEquiv_mul : powMulEquiv M (p * q) = (powMulEquiv M p).trans (powMulE
quiv M q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem powMulEquiv_mul : powMulEquiv M (p * q) = (powMulEquiv M p).trans (powMulEquiv M q) :=
  MulEquiv.ext fun x ↦ pow_mul x p q
/-
**powMulEquiv_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powMulEquiv_mul' : powMulEquiv M (p * q) = (powMulEquiv M q).trans (powMul
Equiv M p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
-/
theorem powMulEquiv_mul' : powMulEquiv M (p * q) = (powMulEquiv M q).trans (powMulEquiv M p) :=
  MulEquiv.ext fun x ↦ pow_mul' x p q
/-
**powMulEquiv_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powMulEquiv_pow (n : Nat) : powMulEquiv M (p ^ n) = powMulEquiv M p ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `powMulEquiv_one`：∀ (M : Type u_1) [inst : CommMonoid M], powMulEquiv M 1
 = MulEquiv.refl M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAut.mul_def`：∀ (M : Type u_2) [inst : Mul M] (e₁ e₂ : MulAut M), e₁ *
 e₂ = MulEquiv.trans e₂ e₁
· 使用定理 `powMulEquiv_mul`：powMulEquiv_mul : powMulEquiv M (p * q) = (powMulEquiv 
M p).trans (powMulEquiv M q)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem powMulEquiv_pow (n : ℕ) : powMulEquiv M (p ^ n) = powMulEquiv M p ^ n :=
  n.recOn (powMulEquiv_one M) fun n ih ↦ by
    rw [pow_succ (powMulEquiv M p), ← ih, MulAut.mul_def, ← powMulEquiv_mul]
    congr
    rw [pow_succ']

end Monoid

section CommSemiring
variable (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]

/-- For a reduced ring, surjectivity of the Frobenius map is a sufficient condition for perfection.
-/
/-
**PerfectRing.ofSurjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PerfectRing.ofSurjective (R : Type*) (p : Nat) [CommRing R] [ExpChar R p] 
[IsReduced R] (h : Surjective <| frobenius R p) : PerfectRing R p
参数：R : Type*；p : Nat；h : Surjective <| frobenius R p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frobenius_inj`：frobenius_inj : Function.Injective (frobenius R p)

--- 原说明 ---
For a reduced ring, surjectivity of the Frobenius map is a sufficient condition 
for perfection.
-/
lemma PerfectRing.ofSurjective (R : Type*) (p : ℕ) [CommRing R] [ExpChar R p]
    [IsReduced R] (h : Surjective <| frobenius R p) : PerfectRing R p :=
  ⟨frobenius_inj R p, h⟩
/-
**PerfectRing.ofFiniteOfIsReduced** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PerfectRing.ofFiniteOfIsReduced (R : Type*) [CommRing R] [ExpChar R p] [Fi
nite R] [IsReduced R] : PerfectRing R p
参数：R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PerfectRing.ofSurjective`：PerfectRing.ofSurjective (R : Type*) (p : Nat)
 [CommRing R] [ExpChar R p] [IsReduced R] (h : Surjective <| frobenius R p) : Pe
rfectRing R p
· 使用定理 `Finite.surjective_of_injective`：surjective_of_injective {f : α -> α} (hi
nj : Injective f) : Surjective f
· 使用定理 `frobenius_inj`：frobenius_inj : Function.Injective (frobenius R p)
-/
instance PerfectRing.ofFiniteOfIsReduced (R : Type*) [CommRing R] [ExpChar R p]
    [Finite R] [IsReduced R] : PerfectRing R p :=
  ofSurjective _ _ <| Finite.surjective_of_injective (frobenius_inj R p)

variable [PerfectRing R p]

@[simp]
/-
**bijective_frobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_frobenius : Bijective (frobenius R p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.bijective_frobenius`：∀ {R : Type u_1} {p : ℕ} {inst : Pow R 
ℕ} [self : PerfectRing R p], Function.Bijective fun x => x ^ p
-/
theorem bijective_frobenius : Bijective (frobenius R p) := PerfectRing.bijective_frobenius
/-
**bijective_iterateFrobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_iterateFrobenius : Bijective (iterateFrobenius R p n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.bijective_frobenius`：∀ {R : Type u_1} {p : ℕ} {inst : Pow R 
ℕ} [self : PerfectRing R p], Function.Bijective fun x => x ^ p
-/
theorem bijective_iterateFrobenius : Bijective (iterateFrobenius R p n) :=
  PerfectRing.bijective_frobenius

@[simp]
/-
**injective_frobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_frobenius : Injective (frobenius R p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `bijective_frobenius`：bijective_frobenius : Bijective (frobenius R p)
-/
theorem injective_frobenius : Injective (frobenius R p) := (bijective_frobenius R p).1

@[simp]
/-
**surjective_frobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_frobenius : Surjective (frobenius R p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `bijective_frobenius`：bijective_frobenius : Bijective (frobenius R p)
-/
theorem surjective_frobenius : Surjective (frobenius R p) := (bijective_frobenius R p).2

/-- The Frobenius automorphism for a perfect ring. -/
@[simps! apply]
/-
**frobeniusEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：frobeniusEquiv : R ≃+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Frobenius automorphism for a perfect ring.
-/
noncomputable def frobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius
/-
**powMulEquiv_eq_toMulEquiv_frobeniusEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (p : ℕ) [inst : CommSemiring R] [inst_1 : ExpChar R p] [i
nst_2 : PerfectRing R p],   powMulEquiv R p = (frobeniusEquiv R p).toMulEquiv
参数：R : Type u_1；p : ℕ；frobeniusEquiv R p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem powMulEquiv_eq_toMulEquiv_frobeniusEquiv :
    powMulEquiv R p = (frobeniusEquiv R p).toMulEquiv := rfl

@[simp]
/-
**coe_frobeniusEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobenius R p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobenius R p := rfl
/-
**frobeniusEquiv_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobeniusEquiv_def (x : R) : frobeniusEquiv R p x = x ^ p
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem frobeniusEquiv_def (x : R) : frobeniusEquiv R p x = x ^ p := rfl

/-- The iterated Frobenius automorphism for a perfect ring. -/
@[simps! apply]
/-
**iterateFrobeniusEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv : R ≃+* R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `bijective_iterateFrobenius`：bijective_iterateFrobenius : Bijective (iter
ateFrobenius R p n)

--- 原说明 ---
The iterated Frobenius automorphism for a perfect ring.
-/
noncomputable def iterateFrobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)

@[simp]
/-
**coe_iterateFrobeniusEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_iterateFrobeniusEquiv : ⇑(iterateFrobeniusEquiv R p n) = iterateFroben
ius R p n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_iterateFrobeniusEquiv : ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n := rfl
/-
**iterateFrobeniusEquiv_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_def (x : R) : iterateFrobeniusEquiv R p n x = x ^ p 
^ n
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterateFrobeniusEquiv_def (x : R) : iterateFrobeniusEquiv R p n x = x ^ p ^ n := rfl
/-
**iterateFrobeniusEquiv_add_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_add_apply (x : R) : iterateFrobeniusEquiv R p (m + n
) x = iterateFrobeniusEquiv R p m (iterateFrobeniusEquiv R p n x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iterateFrobenius_add_apply`：iterateFrobenius_add_apply : iterateFrobeniu
s R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x)
-/
theorem iterateFrobeniusEquiv_add_apply (x : R) : iterateFrobeniusEquiv R p (m + n) x =
    iterateFrobeniusEquiv R p m (iterateFrobeniusEquiv R p n x) :=
  iterateFrobenius_add_apply R p m n x
/-
**iterateFrobeniusEquiv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_add : iterateFrobeniusEquiv R p (m + n) = (iterateFr
obeniusEquiv R p n).trans (iterateFrobeniusEquiv R p m)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `iterateFrobeniusEquiv_add_apply`：iterateFrobeniusEquiv_add_apply (x : R)
 : iterateFrobeniusEquiv R p (m + n) x = iterateFrobeniusEquiv R p m (iterateFro
beniusEquiv R p n x)
-/
theorem iterateFrobeniusEquiv_add : iterateFrobeniusEquiv R p (m + n) =
    (iterateFrobeniusEquiv R p n).trans (iterateFrobeniusEquiv R p m) :=
  RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)
/-
**iterateFrobeniusEquiv_symm_add_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_symm_add_apply (x : R) : (iterateFrobeniusEquiv R p 
(m + n)).symm x = (iterateFrobeniusEquiv R p m).symm ((iterateFrobeniusEquiv R p
 n).symm x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iterateFrobeniusEquiv_add_apply`：iterateFrobeniusEquiv_add_apply (x : R)
 : iterateFrobeniusEquiv R p (m + n) x = iterateFrobeniusEquiv R p m (iterateFro
beniusEquiv R p n x)
-/
theorem iterateFrobeniusEquiv_symm_add_apply (x : R) : (iterateFrobeniusEquiv R p (m + n)).symm x =
    (iterateFrobeniusEquiv R p m).symm ((iterateFrobeniusEquiv R p n).symm x) :=
  (iterateFrobeniusEquiv R p (m + n)).injective <| by rw [RingEquiv.apply_symm_apply, add_comm,
    iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
/-
**iterateFrobeniusEquiv_symm_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_symm_add : (iterateFrobeniusEquiv R p (m + n)).symm 
= (iterateFrobeniusEquiv R p n).symm.trans (iterateFrobeniusEquiv R p m).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `iterateFrobeniusEquiv_symm_add_apply`：iterateFrobeniusEquiv_symm_add_app
ly (x : R) : (iterateFrobeniusEquiv R p (m + n)).symm x = (iterateFrobeniusEquiv
 R p m).symm ((iterateFrob…
-/
theorem iterateFrobeniusEquiv_symm_add : (iterateFrobeniusEquiv R p (m + n)).symm =
    (iterateFrobeniusEquiv R p n).symm.trans (iterateFrobeniusEquiv R p m).symm :=
  RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)
/-
**iterateFrobeniusEquiv_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_zero_apply (x : R) : iterateFrobeniusEquiv R p 0 x =
 x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iterateFrobeniusEquiv_def`：iterateFrobeniusEquiv_def (x : R) : iterateFr
obeniusEquiv R p n x = x ^ p ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem iterateFrobeniusEquiv_zero_apply (x : R) : iterateFrobeniusEquiv R p 0 x = x := by
  rw [iterateFrobeniusEquiv_def, pow_zero, pow_one]
/-
**iterateFrobeniusEquiv_one_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_one_apply (x : R) : iterateFrobeniusEquiv R p 1 x = 
x ^ p
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iterateFrobeniusEquiv_def`：iterateFrobeniusEquiv_def (x : R) : iterateFr
obeniusEquiv R p n x = x ^ p ^ n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem iterateFrobeniusEquiv_one_apply (x : R) : iterateFrobeniusEquiv R p 1 x = x ^ p := by
  rw [iterateFrobeniusEquiv_def, pow_one]

@[simp]
/-
**iterateFrobeniusEquiv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_zero : iterateFrobeniusEquiv R p 0 = RingEquiv.refl 
R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `iterateFrobeniusEquiv_zero_apply`：iterateFrobeniusEquiv_zero_apply (x : 
R) : iterateFrobeniusEquiv R p 0 x = x
-/
theorem iterateFrobeniusEquiv_zero : iterateFrobeniusEquiv R p 0 = RingEquiv.refl R :=
  RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)

@[simp]
/-
**iterateFrobeniusEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_one : iterateFrobeniusEquiv R p 1 = frobeniusEquiv R
 p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `iterateFrobeniusEquiv_one_apply`：iterateFrobeniusEquiv_one_apply (x : R)
 : iterateFrobeniusEquiv R p 1 x = x ^ p
-/
theorem iterateFrobeniusEquiv_one : iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p :=
  RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)
/-
**iterateFrobeniusEquiv_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_eq_pow : iterateFrobeniusEquiv R p n = frobeniusEqui
v R p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Equiv.Perm.coe_pow`：∀ {α : Type u_4} (f : Equiv.Perm α) (n : ℕ), ⇑(f ^ n
) = (⇑f)^[n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_iterate`：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^
 k)^[n] = fun x => x ^ k ^ n
-/
theorem iterateFrobeniusEquiv_eq_pow : iterateFrobeniusEquiv R p n = frobeniusEquiv R p ^ n :=
  DFunLike.ext' <| show _ = ⇑(RingAut.toPerm _ _) by
    rw [map_pow, Equiv.Perm.coe_pow]; exact (pow_iterate p n).symm
/-
**iterateFrobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobeniusEquiv_symm : (iterateFrobeniusEquiv R p n).symm = (frobeni
usEquiv R p).symm ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iterateFrobeniusEquiv_eq_pow`：iterateFrobeniusEquiv_eq_pow : iterateFrob
eniusEquiv R p n = frobeniusEquiv R p ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
-/
theorem iterateFrobeniusEquiv_symm :
    (iterateFrobeniusEquiv R p n).symm = (frobeniusEquiv R p).symm ^ n := by
  rw [iterateFrobeniusEquiv_eq_pow]; exact (inv_pow _ _).symm

@[simp]
/-
**frobeniusEquiv_symm_apply_frobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobeniusEquiv_symm_apply_frobenius (x : R) : (frobeniusEquiv R p).symm (f
robenius R p x) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem frobeniusEquiv_symm_apply_frobenius (x : R) :
    (frobeniusEquiv R p).symm (frobenius R p x) = x :=
  (frobeniusEquiv R p).symm_apply_apply x

@[simp]
/-
**frobenius_apply_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobenius_apply_frobeniusEquiv_symm (x : R) : frobenius R p ((frobeniusEqu
iv R p).symm x) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
theorem frobenius_apply_frobeniusEquiv_symm (x : R) :
    frobenius R p ((frobeniusEquiv R p).symm x) = x :=
  (frobeniusEquiv R p).apply_symm_apply x

@[simp]
/-
**frobenius_comp_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobenius_comp_frobeniusEquiv_symm : (frobenius R p).comp (frobeniusEquiv 
R p).symm = RingHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobenius_apply_frobeniusEquiv_symm`：frobenius_apply_frobeniusEquiv_symm
 (x : R) : frobenius R p ((frobeniusEquiv R p).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_comp_frobeniusEquiv_symm :
    (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R := by
  ext; simp

@[simp]
/-
**frobeniusEquiv_symm_comp_frobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobeniusEquiv_symm_comp_frobenius : ((frobeniusEquiv R p).symm : R ->+* R
).comp (frobenius R p) = RingHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobeniusEquiv_symm_apply_frobenius`：frobeniusEquiv_symm_apply_frobenius
 (x : R) : (frobeniusEquiv R p).symm (frobenius R p x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobeniusEquiv_symm_comp_frobenius :
    ((frobeniusEquiv R p).symm : R →+* R).comp (frobenius R p) = RingHom.id R := by
  ext; simp

@[simp]
/-
**coe_frobenius_comp_coe_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_frobenius_comp_coe_frobeniusEquiv_symm : ⇑(frobenius R p) ∘ ⇑(frobeniu
sEquiv R p).symm = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobenius_apply_frobeniusEquiv_symm`：frobenius_apply_frobeniusEquiv_symm
 (x : R) : frobenius R p ((frobeniusEquiv R p).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_frobenius_comp_coe_frobeniusEquiv_symm :
    ⇑(frobenius R p) ∘ ⇑(frobeniusEquiv R p).symm = id := by
  ext
  simp

@[simp]
/-
**coe_frobeniusEquiv_symm_comp_coe_frobenius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_frobeniusEquiv_symm_comp_coe_frobenius : ⇑(frobeniusEquiv R p).symm ∘ 
⇑(frobenius R p) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobeniusEquiv_symm_apply_frobenius`：frobeniusEquiv_symm_apply_frobenius
 (x : R) : (frobeniusEquiv R p).symm (frobenius R p x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_frobeniusEquiv_symm_comp_coe_frobenius :
    ⇑(frobeniusEquiv R p).symm ∘ ⇑(frobenius R p) = id := by
  ext
  simp

@[simp]
/-
**frobeniusEquiv_symm_pow_p** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobeniusEquiv_symm_pow_p (x : R) : ((frobeniusEquiv R p).symm x) ^ p = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frobenius_apply_frobeniusEquiv_symm`：frobenius_apply_frobeniusEquiv_symm
 (x : R) : frobenius R p ((frobeniusEquiv R p).symm x) = x
-/
theorem frobeniusEquiv_symm_pow_p (x : R) : ((frobeniusEquiv R p).symm x) ^ p = x :=
  frobenius_apply_frobeniusEquiv_symm R p x

/-- Variant with `· ^ p` inside of `frobeniusEquiv`. -/
/-
**frobeniusEquiv_symm_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：frobeniusEquiv_symm_pow (x : R) : (frobeniusEquiv R p).symm (x ^ p) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x

--- 原说明 ---
Variant with `· ^ p` inside of `frobeniusEquiv`.
-/
lemma frobeniusEquiv_symm_pow (x : R) : (frobeniusEquiv R p).symm (x ^ p) = x :=
  (frobeniusEquiv R p).symm_apply_apply x

@[simp]
/-
**iterate_frobeniusEquiv_symm_pow_p_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterate_frobeniusEquiv_symm_pow_p_pow (x : R) (n : Nat) : ((frobeniusEquiv
 R p).symm^[n]) x ^ (p ^ n) = x
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `frobeniusEquiv_symm_pow_p`：frobeniusEquiv_symm_pow_p (x : R) : ((frobeni
usEquiv R p).symm x) ^ p = x
-/
theorem iterate_frobeniusEquiv_symm_pow_p_pow (x : R) (n : ℕ) :
    ((frobeniusEquiv R p).symm^[n]) x ^ (p ^ n) = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih]

section commute

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)
    [ExpChar R p] [PerfectRing R p] [ExpChar S p] [PerfectRing S p]

/--
The `(frobeniusEquiv R p).symm` version of `MonoidHom.map_frobenius`.
`(frobeniusEquiv R p).symm` commute with any monoid homomorphisms.
-/
/-
**MonoidHom.map_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_frobeniusEquiv_symm (f : R ->* S) (x : R) : f ((frobeniusEqu
iv R p).symm x) = (frobeniusEquiv S p).symm (f x)
参数：f : R ->* S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobeniusEquiv_apply`：∀ (R : Type u_1) (p : ℕ) [inst : CommSemiring R] [
inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (frobeniusEquiv R p)
 a = (frob…
· 使用定理 `frobenius_apply_frobeniusEquiv_symm`：frobenius_apply_frobeniusEquiv_symm
 (x : R) : frobenius R p ((frobeniusEquiv R p).symm x) = x
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `(frobeniusEquiv R p).symm` version of `MonoidHom.map_frobenius`.
`(frobeniusEquiv R p).symm` commute with any monoid homomorphisms.
-/
theorem MonoidHom.map_frobeniusEquiv_symm (f : R →* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply_fun (frobeniusEquiv S p)
  simp [← MonoidHom.map_frobenius]
/-
**RingHom.map_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.map_frobeniusEquiv_symm (f : R ->+* S) (x : R) : f ((frobeniusEqui
v R p).symm x) = (frobeniusEquiv S p).symm (f x)
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobeniusEquiv_apply`：∀ (R : Type u_1) (p : ℕ) [inst : CommSemiring R] [
inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (frobeniusEquiv R p)
 a = (frob…
· 使用定理 `frobenius_apply_frobeniusEquiv_symm`：frobenius_apply_frobeniusEquiv_symm
 (x : R) : frobenius R p ((frobeniusEquiv R p).symm x) = x
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem RingHom.map_frobeniusEquiv_symm (f : R →+* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply_fun (frobeniusEquiv S p)
  simp [← RingHom.map_frobenius]
/-
**MonoidHom.map_iterate_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_iterate_frobeniusEquiv_symm (f : R ->* S) (n : Nat) (x : R) 
: f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x)
参数：f : R ->* S；n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.Commute.comp_iterate`：comp_iterate (h : Commute f g) (n : Nat) 
: (f ∘ g)^[n] = f^[n] ∘ g^[n]
· 使用定理 `coe_frobeniusEquiv`：coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobeni
us R p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `frobeniusEquiv_apply`：∀ (R : Type u_1) (p : ℕ) [inst : CommSemiring R] [
inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (frobeniusEquiv R p)
 a = (frob…
· 使用定理 `frobeniusEquiv_symm_apply_frobenius`：frobeniusEquiv_symm_apply_frobenius
 (x : R) : (frobeniusEquiv R p).symm (frobenius R p x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `coe_frobenius_comp_coe_frobeniusEquiv_symm`：coe_frobenius_comp_coe_frobe
niusEquiv_symm : ⇑(frobenius R p) ∘ ⇑(frobeniusEquiv R p).symm = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id
-/
theorem MonoidHom.map_iterate_frobeniusEquiv_symm (f : R →* S) (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x) := by
  apply_fun (frobeniusEquiv S p)^[n]
  · simp only [coe_frobeniusEquiv, ← map_iterate_frobenius]
    · rw [← Function.comp_apply (f := (⇑(frobenius R p))^[n]),
          ← Function.comp_apply (f := (⇑(frobenius S p))^[n]),
          ← Function.Commute.comp_iterate, ← Function.Commute.comp_iterate]
      · simp
      all_goals rw [← coe_frobeniusEquiv]; simp [Function.Commute, Function.Semiconj]
  apply Function.Injective.iterate
  simp
/-
**RingHom.map_iterate_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.map_iterate_frobeniusEquiv_symm (f : R ->+* S) (n : Nat) (x : R) :
 f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x)
参数：f : R ->+* S；n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_iterate_frobeniusEquiv_symm`：MonoidHom.map_iterate_frobeni
usEquiv_symm (f : R ->* S) (n : Nat) (x : R) : f (((frobeniusEquiv R p).symm^[n]
) x) = ((frobeniusEquiv S p).sy…
-/
theorem RingHom.map_iterate_frobeniusEquiv_symm (f : R →+* S) (n : ℕ) (x : R) :
    f (((frobeniusEquiv R p).symm^[n]) x) = ((frobeniusEquiv S p).symm^[n]) (f x) :=
  MonoidHom.map_iterate_frobeniusEquiv_symm p (f.toMonoidHom) n x

end commute

/-
**injective_pow_p** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y
参数：h : x ^ p = y ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
-/
theorem injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y := (frobeniusEquiv R p).injective h
/-
**polynomial_expand_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：polynomial_expand_eq (f : R[X]) : expand R p f = (f.map (frobeniusEquiv R 
p).symm) ^ p
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_frobenius_expand`：map_frobenius_expand (f : R[X]) : map (
frobenius R p) (expand R p f) = f ^ p
· 使用定理 `Polynomial.map_expand`：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : 
map f (expand R p q) = expand S p (map f q)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `frobenius_comp_frobeniusEquiv_symm`：frobenius_comp_frobeniusEquiv_symm :
 (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
-/
lemma polynomial_expand_eq (f : R[X]) :
    expand R p f = (f.map (frobeniusEquiv R p).symm) ^ p := by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).map_frobenius_expand p, map_expand, map_map,
    frobenius_comp_frobeniusEquiv_symm, map_id]

@[simp]
/-
**not_irreducible_expand** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_irreducible_expand (R p) [CommSemiring R] [Fact p.Prime] [CharP R p] [
PerfectRing R p] (f : R[X]) : ¬ Irreducible (expand R p f)
参数：R p；f : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `polynomial_expand_eq`：polynomial_expand_eq (f : R[X]) : expand R p f = (
f.map (frobeniusEquiv R p).symm) ^ p
· 使用引理 `not_irreducible_pow`：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬
 Irreducible (x ^ n) | 0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem not_irreducible_expand (R p) [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (f : R[X]) : ¬ Irreducible (expand R p f) := by
  rw [polynomial_expand_eq]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one
/-
**instPerfectRingProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instPerfectRingProd (S : Type*) [CommSemiring S] [ExpChar S p] [PerfectRin
g S p] : PerfectRing (R × S) p where bijective_frobenius
参数：S : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Bijective f → Function.Bij
ective g → Funct…
· 使用定理 `bijective_frobenius`：bijective_frobenius : Bijective (frobenius R p)
-/
instance instPerfectRingProd (S : Type*) [CommSemiring S] [ExpChar S p] [PerfectRing S p] :
    PerfectRing (R × S) p where
  bijective_frobenius := (bijective_frobenius R p).prodMap (bijective_frobenius S p)

end CommSemiring

end PerfectRing

/-- A perfect field.

See also `PerfectRing` for a generalisation in positive characteristic. -/
/-
**PerfectField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → [Field K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A perfect field.

See also `PerfectRing` for a generalisation in positive characteristic.
-/
class PerfectField (K : Type*) [Field K] : Prop where
  /-- A field is perfect if every irreducible polynomial is separable. -/
  separable_of_irreducible : ∀ {f : K[X]}, Irreducible f → f.Separable
/-
**PerfectRing.toPerfectField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PerfectRing.toPerfectField (K : Type*) (p : Nat) [Field K] [ExpChar K p] [
PerfectRing K p] : PerfectField K
参数：K : Type*；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.separable`：∀ {F : Type u} [inst : Field F] [CharZero F] {f :
 Polynomial F}, Irreducible f → f.Separable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.separable_or`：separable_or {f : F[X]} (hf : Irreducible f) : 
f.Separable ∨ ¬f.Separable ∧ exists g : F[X], Irreducible g ∧ expand F p g = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma PerfectRing.toPerfectField (K : Type*) (p : ℕ)
    [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K := by
  obtain hp | ⟨hp⟩ := ‹ExpChar K p›
  · exact ⟨Irreducible.separable⟩
  refine PerfectField.mk fun hf ↦ ?_
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; have := Fact.mk hp; simp

namespace PerfectField

variable {K : Type*} [Field K]

/-
**PerfectField.ofCharZero** 是 Mathlib 中的一个实例，位于命名空间 `PerfectField`。
形式化陈述：ofCharZero [CharZero K] : PerfectField K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.separable`：∀ {F : Type u} [inst : Field F] [CharZero F] {f :
 Polynomial F}, Irreducible f → f.Separable
-/
instance ofCharZero [CharZero K] : PerfectField K := ⟨Irreducible.separable⟩
/-
**PerfectField.ofFinite** 是 Mathlib 中的一个实例，位于命名空间 `PerfectField`。
形式化陈述：ofFinite [Finite K] : PerfectField K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `CharP.char_is_prime`：char_is_prime (p : Nat) [CharP R p] : p.Prime
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `PerfectRing.toPerfectField`：PerfectRing.toPerfectField (K : Type*) (p : 
Nat) [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
-/
instance ofFinite [Finite K] : PerfectField K := by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p

variable [PerfectField K]

set_option backward.isDefEq.respectTransparency.types false in
/-- A perfect field of characteristic `p` (prime) is a perfect ring. -/
/-
**PerfectField.toPerfectRing** 是 Mathlib 中的一个实例，位于命名空间 `PerfectField`。
形式化陈述：toPerfectRing (p : Nat) [hp : ExpChar K p] : PerfectRing K p
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PerfectRing.ofSurjective`：PerfectRing.ofSurjective (R : Type*) (p : Nat)
 [CommRing R] [ExpChar R p] [IsReduced R] (h : Surjective <| frobenius R p) : Pe
rfectRing R p
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `X_pow_sub_C_irreducible_of_prime`：X_pow_sub_C_irreducible_of_prime {p : 
Nat} (hp : p.Prime) {a : K} (ha : forall b : K, b ^ p != a) : Irreducible (X ^ p
 - C a)
· 使用定理 `PerfectField.separable_of_irreducible`：∀ {K : Type u_1} {inst : Field K}
 [self : PerfectField K] {f : Polynomial K}, Irreducible f → f.Separable
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.derivative_X_pow`：derivative_X_pow (n : Nat) : derivative (X 
^ n : R[X]) = C (n : R) * X ^ (n - 1)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A perfect field of characteristic `p` (prime) is a perfect ring.
-/
instance toPerfectRing (p : ℕ) [hp : ExpChar K p] : PerfectRing K p := by
  refine PerfectRing.ofSurjective _ _ fun y ↦ ?_
  rcases hp with _ | hp
  · simp [frobenius]
  rw [← not_forall_not]
  apply mt (X_pow_sub_C_irreducible_of_prime hp)
  apply mt separable_of_irreducible
  simp [separable_def, isCoprime_zero_right, isUnit_iff_degree_eq_zero,
    derivative_X_pow, degree_X_pow_sub_C hp.pos, hp.ne_zero]
/-
**PerfectField.separable_iff_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `PerfectField`
。
形式化陈述：separable_iff_squarefree {g : K[X]} : g.Separable ↔ Squarefree g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.squarefree`：∀ {R : Type u} [inst : CommSemiring R] 
{p : Polynomial R}, p.Separable → Squarefree p
· 使用定理 `isCoprime_of_irreducible_dvd`：isCoprime_of_irreducible_dvd {x y : R} (no
nzero : ¬(x = 0 ∧ y = 0)) (H : forall z : R, Irreducible z -> z ∣ x -> ¬z ∣ y) :
 IsCoprime x y
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsCoprime.dvd_of_dvd_mul_left`：IsCoprime.dvd_of_dvd_mul_left (H1 : IsCop
rime x y) (H2 : x ∣ y * z) : x ∣ z
· 使用定理 `PerfectField.separable_of_irreducible`：∀ {K : Type u_1} {inst : Field K}
 [self : PerfectField K] {f : Polynomial K}, Irreducible f → f.Separable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_add_left`：dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem separable_iff_squarefree {g : K[X]} : g.Separable ↔ Squarefree g := by
  refine ⟨Separable.squarefree, fun sqf ↦ isCoprime_of_irreducible_dvd (sqf.ne_zero ·.1) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  replace dvd : p ∣ q := by
    rw [derivative_mul, dvd_add_left (dvd_mul_right p _)] at dvd
    exact (separable_of_irreducible h).dvd_of_dvd_mul_left dvd
  exact (h.1 : ¬ IsUnit p) (sqf _ <| mul_dvd_mul_left _ dvd)

end PerfectField

/-- If `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is separable. -/
/-
**Algebra.IsAlgebraic.isSeparable_of_perfectField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.isSeparable_of_perfectField {K L : Type*} [Field K] [F
ield L] [Algebra K L] [Algebra.IsAlgebraic K L] [PerfectField K] : Algebra.IsSep
arable K L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectField.separable_of_irreducible`：∀ {K : Type u_1} {inst : Field K}
 [self : PerfectField K] {f : Polynomial K}, Irreducible f → f.Separable
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A

--- 原说明 ---
If `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is se
parable.
-/
instance Algebra.IsAlgebraic.isSeparable_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [PerfectField K] : Algebra.IsSeparable K L :=
  ⟨fun x ↦ PerfectField.separable_of_irreducible <|
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)⟩

/-- If `L / K` is an algebraic extension, `K` is a perfect field, then so is `L`. -/
/-
**Algebra.IsAlgebraic.perfectField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.perfectField (K : Type*) {L : Type*} [Field K] [Field 
L] [Algebra K L] [Algebra.IsAlgebraic K L] [PerfectField K] : PerfectField L
参数：K : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.exists_dvd_monic_irreducible_of_isIntegral`：Irreducible.exis
ts_dvd_monic_irreducible_of_isIntegral {K L : Type*} [CommRing K] [IsDomain K] [
Field L] [Algebra K L] [Algebra.IsIntegral K…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `PerfectField.separable_of_irreducible`：∀ {K : Type u_1} {inst : Field K}
 [self : PerfectField K] {f : Polynomial K}, Irreducible f → f.Separable

--- 原说明 ---
If `L / K` is an algebraic extension, `K` is a perfect field, then so is `L`.
-/
theorem Algebra.IsAlgebraic.perfectField (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [PerfectField K] : PerfectField L := ⟨fun {f} hf ↦ by
  obtain ⟨_, _, hi, h⟩ := hf.exists_dvd_monic_irreducible_of_isIntegral (K := K)
  exact (PerfectField.separable_of_irreducible hi).map |>.of_dvd h⟩
/-
**PerfectField.of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PerfectField.of_ringEquiv {K L : Type*} [Field K] [Field L] (h : K ≃+* L) 
[PerfectField K] : PerfectField L
参数：h : K ≃+* L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.perfectField`：Algebra.IsAlgebraic.perfectField (K : 
Type*) {L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [
PerfectField K] : Perf…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHom.Finite.instFinite`：∀ {A : Type u_1} {B : Type u_2} [inst : CommR
ing A] [inst_1 : CommRing B] (h : A ≃+* B), Module.Finite A B
-/
theorem PerfectField.of_ringEquiv {K L : Type*} [Field K] [Field L] (h : K ≃+* L) [PerfectField K] :
    PerfectField L :=
  let := h.toRingHom.toAlgebra
  Algebra.IsAlgebraic.perfectField K

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] (p n : ℕ) [ExpChar R p] (f : R[X])

open Multiset

/-
**Polynomial.roots_expand_pow_map_iterateFrobenius_le** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：roots_expand_pow_map_iterateFrobenius_le : (expand R (p ^ n) f).roots.map 
(iterateFrobenius R p n) <= p ^ n • f.roots
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.count_map`：count_map {α β : Type*} (f : α -> β) (s : Multiset α
) [DecidableEq β] (b : β) : count b (map f s) = card (s.filter fun a => b = f a)
· 使用定理 `Multiset.count_eq_card_filter_eq`：count_eq_card_filter_eq [DecidableEq α
] (s : Multiset α) (a : α) : s.count a = card (s.filter (a = ·))
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Multiset.monotone_filter_right`：monotone_filter_right (s : Multiset α) ⦃
p q : α -> Prop⦄ [DecidablePred p] [DecidablePred q] (h : forall b, p b -> q b) 
: s.filter p <= s.fi…
· 使用定理 `iterateFrobenius_inj`：iterateFrobenius_inj : Function.Injective (iterate
Frobenius R p n)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `Multiset.count_filter_of_neg`：count_filter_of_neg {p} [DecidablePred p] 
{a} {s : Multiset α} (h : ¬p a) : count a (filter p s) = 0
· 使用定理 `Multiset.count_zero`：count_zero (a : α) : count a 0 = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem roots_expand_pow_map_iterateFrobenius_le :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) ≤ p ^ n • f.roots := by
  classical
  refine le_iff_count.2 fun r ↦ ?_
  by_cases h : ∃ s, r = s ^ p ^ n
  · obtain ⟨s, rfl⟩ := h
    simp_rw [count_nsmul, count_roots, ← rootMultiplicity_expand_pow, ← count_roots, count_map,
      count_eq_card_filter_eq]
    exact card_le_card (monotone_filter_right _ fun _ h ↦ iterateFrobenius_inj R p n h)
  convert! Nat.zero_le _
  simp_rw [count_map, card_eq_zero]
  exact ext' fun t ↦ count_zero t ▸ count_filter_of_neg fun h' ↦ h ⟨t, h'⟩
/-
**Polynomial.roots_expand_map_frobenius_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：roots_expand_map_frobenius_le : (expand R p f).roots.map (frobenius R p) <
= p • f.roots
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iterateFrobenius_one`：iterateFrobenius_one : iterateFrobenius R p 1 = fr
obenius R p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.roots_expand_pow_map_iterateFrobenius_le`：roots_expand_pow_ma
p_iterateFrobenius_le : (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) 
<= p ^ n • f.roots
-/
theorem roots_expand_map_frobenius_le :
    (expand R p f).roots.map (frobenius R p) ≤ p • f.roots := by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_map_iterateFrobenius_le p 1 f <;> apply pow_one
/-
**Polynomial.roots_expand_pow_image_iterateFrobenius_subset** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial`。
形式化陈述：roots_expand_pow_image_iterateFrobenius_subset [DecidableEq R] : (expand R
 (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) subseteq f.roots.toFin
set
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_toFinset`：image_toFinset [DecidableEq α] {s : Multiset α} :
 s.toFinset.image f = (s.map f).toFinset
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
· 使用定理 `Multiset.toFinset_subset`：toFinset_subset : s.toFinset subseteq t.toFins
et ↔ s subseteq t
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Polynomial.roots_expand_pow_map_iterateFrobenius_le`：roots_expand_pow_ma
p_iterateFrobenius_le : (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) 
<= p ^ n • f.roots
-/
theorem roots_expand_pow_image_iterateFrobenius_subset [DecidableEq R] :
    (expand R (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) ⊆ f.roots.toFinset := by
  rw [Finset.image_toFinset, ← (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne',
    toFinset_subset]
  exact subset_of_le (roots_expand_pow_map_iterateFrobenius_le p n f)
/-
**Polynomial.roots_expand_image_frobenius_subset** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：roots_expand_image_frobenius_subset [DecidableEq R] : (expand R p f).roots
.toFinset.image (frobenius R p) subseteq f.roots.toFinset
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iterateFrobenius_one`：iterateFrobenius_one : iterateFrobenius R p 1 = fr
obenius R p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.roots_expand_pow_image_iterateFrobenius_subset`：roots_expand_
pow_image_iterateFrobenius_subset [DecidableEq R] : (expand R (p ^ n) f).roots.t
oFinset.image (iterateFrobenius R p n) subseteq…
-/
theorem roots_expand_image_frobenius_subset [DecidableEq R] :
    (expand R p f).roots.toFinset.image (frobenius R p) ⊆ f.roots.toFinset := by
  rw [← iterateFrobenius_one]
  convert! ← roots_expand_pow_image_iterateFrobenius_subset p 1 f
  apply pow_one

section PerfectRing
variable {p n f}
variable [PerfectRing R p]

/-
**Polynomial.roots_expand_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_expand_pow : (expand R (p ^ n) f).roots = p ^ n • f.roots.map (itera
teFrobeniusEquiv R p n).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.rootMultiplicity_expand_pow`：rootMultiplicity_expand_pow : (e
xpand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `Multiset.count_map`：count_map {α β : Type*} (f : α -> β) (s : Multiset α
) [DecidableEq β] (b : β) : count b (map f s) = card (s.filter fun a => b = f a)
· 使用定理 `Multiset.count_eq_card_filter_eq`：count_eq_card_filter_eq [DecidableEq α
] (s : Multiset α) (a : α) : s.count a = card (s.filter (a = ·))
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RingEquiv.eq_symm_apply`：eq_symm_apply (e : R ≃+* S) {x : S} {y : R} : y
 = e.symm x ↔ e y = x
-/
theorem roots_expand_pow :
    (expand R (p ^ n) f).roots = p ^ n • f.roots.map (iterateFrobeniusEquiv R p n).symm := by
  classical
  refine ext' fun r ↦ ?_
  rw [count_roots, rootMultiplicity_expand_pow, ← count_roots, count_nsmul, count_map,
    count_eq_card_filter_eq]; congr; ext
  exact (iterateFrobeniusEquiv R p n).eq_symm_apply.symm
/-
**Polynomial.roots_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_expand : (expand R p f).roots = p • f.roots.map (frobeniusEquiv R p)
.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.roots_expand_pow`：roots_expand_pow : (expand R (p ^ n) f).roo
ts = p ^ n • f.roots.map (iterateFrobeniusEquiv R p n).symm
· 使用定理 `iterateFrobeniusEquiv_eq_pow`：iterateFrobeniusEquiv_eq_pow : iterateFrob
eniusEquiv R p n = frobeniusEquiv R p ^ n
-/
theorem roots_expand : (expand R p f).roots = p • f.roots.map (frobeniusEquiv R p).symm := by
  conv_lhs => rw [← pow_one p, roots_expand_pow, iterateFrobeniusEquiv_eq_pow, pow_one]
  rfl
/-
**Polynomial.roots_X_pow_char_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X_pow_char_pow_sub_C {y : R} : (X ^ p ^ n - C y).roots = p ^ n • {(i
terateFrobeniusEquiv R p n).symm y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_expand_pow`：roots_expand_pow : (expand R (p ^ n) f).roo
ts = p ^ n • f.roots.map (iterateFrobeniusEquiv R p n).symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
-/
theorem roots_X_pow_char_pow_sub_C {y : R} :
    (X ^ p ^ n - C y).roots = p ^ n • {(iterateFrobeniusEquiv R p n).symm y} := by
  have H := roots_expand_pow (p := p) (n := n) (f := X - C y)
  rwa [roots_X_sub_C, Multiset.map_singleton, map_sub, expand_X, expand_C] at H
/-
**Polynomial.roots_X_pow_char_pow_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：roots_X_pow_char_pow_sub_C_pow {y : R} {m : Nat} : ((X ^ p ^ n - C y) ^ m)
.roots = (m * p ^ n) • {(iterateFrobeniusEquiv R p n).symm y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots_pow`：roots_pow (p : R[X]) (n : Nat) : (p ^ n).roots = n
 • p.roots
· 使用定理 `Polynomial.roots_X_pow_char_pow_sub_C`：roots_X_pow_char_pow_sub_C {y : R
} : (X ^ p ^ n - C y).roots = p ^ n • {(iterateFrobeniusEquiv R p n).symm y}
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem roots_X_pow_char_pow_sub_C_pow {y : R} {m : ℕ} :
    ((X ^ p ^ n - C y) ^ m).roots = (m * p ^ n) • {(iterateFrobeniusEquiv R p n).symm y} := by
  rw [roots_pow, roots_X_pow_char_pow_sub_C, mul_smul]
/-
**Polynomial.roots_X_pow_char_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X_pow_char_sub_C {y : R} : (X ^ p - C y).roots = p • {(frobeniusEqui
v R p).symm y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_X_pow_char_pow_sub_C`：roots_X_pow_char_pow_sub_C {y : R
} : (X ^ p ^ n - C y).roots = p ^ n • {(iterateFrobeniusEquiv R p n).symm y}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iterateFrobeniusEquiv_one`：iterateFrobeniusEquiv_one : iterateFrobeniusE
quiv R p 1 = frobeniusEquiv R p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem roots_X_pow_char_sub_C {y : R} :
    (X ^ p - C y).roots = p • {(frobeniusEquiv R p).symm y} := by
  have H := roots_X_pow_char_pow_sub_C (p := p) (n := 1) (y := y)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H
/-
**Polynomial.roots_X_pow_char_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_X_pow_char_sub_C_pow {y : R} {m : Nat} : ((X ^ p - C y) ^ m).roots =
 (m * p) • {(frobeniusEquiv R p).symm y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_X_pow_char_pow_sub_C_pow`：roots_X_pow_char_pow_sub_C_po
w {y : R} {m : Nat} : ((X ^ p ^ n - C y) ^ m).roots = (m * p ^ n) • {(iterateFro
beniusEquiv R p n).symm y}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iterateFrobeniusEquiv_one`：iterateFrobeniusEquiv_one : iterateFrobeniusE
quiv R p 1 = frobeniusEquiv R p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem roots_X_pow_char_sub_C_pow {y : R} {m : ℕ} :
    ((X ^ p - C y) ^ m).roots = (m * p) • {(frobeniusEquiv R p).symm y} := by
  have H := roots_X_pow_char_pow_sub_C_pow (p := p) (n := 1) (y := y) (m := m)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H
/-
**Polynomial.roots_expand_pow_map_iterateFrobenius** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：roots_expand_pow_map_iterateFrobenius : (expand R (p ^ n) f).roots.map (it
erateFrobenius R p n) = p ^ n • f.roots
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots_expand_pow`：roots_expand_pow : (expand R (p ^ n) f).roo
ts = p ^ n • f.roots.map (iterateFrobeniusEquiv R p n).symm
· 使用引理 `Multiset.map_nsmul`：map_nsmul (f : α -> β) (n : Nat) (s) : map f (n • s)
 = n • map f s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_expand_pow_map_iterateFrobenius :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) = p ^ n • f.roots := by
  simp_rw [← coe_iterateFrobeniusEquiv, roots_expand_pow, Multiset.map_nsmul,
    Multiset.map_map, comp_apply, RingEquiv.apply_symm_apply, map_id']
/-
**Polynomial.roots_expand_map_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_expand_map_frobenius : (expand R p f).roots.map (frobenius R p) = p 
• f.roots
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots_expand`：roots_expand : (expand R p f).roots = p • f.roo
ts.map (frobeniusEquiv R p).symm
· 使用引理 `Multiset.map_nsmul`：map_nsmul (f : α -> β) (n : Nat) (s) : map f (n • s)
 = n • map f s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `frobenius_apply_frobeniusEquiv_symm`：frobenius_apply_frobeniusEquiv_symm
 (x : R) : frobenius R p ((frobeniusEquiv R p).symm x) = x
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_expand_map_frobenius : (expand R p f).roots.map (frobenius R p) = p • f.roots := by
  simp [roots_expand, Multiset.map_nsmul]
/-
**Polynomial.roots_expand_image_iterateFrobenius** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：roots_expand_image_iterateFrobenius [DecidableEq R] : (expand R (p ^ n) f)
.roots.toFinset.image (iterateFrobenius R p n) = f.roots.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_toFinset`：image_toFinset [DecidableEq α] {s : Multiset α} :
 s.toFinset.image f = (s.map f).toFinset
· 使用定理 `Polynomial.roots_expand_pow_map_iterateFrobenius`：roots_expand_pow_map_i
terateFrobenius : (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) = p ^ 
n • f.roots
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
-/
theorem roots_expand_image_iterateFrobenius [DecidableEq R] :
    (expand R (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) = f.roots.toFinset := by
  rw [Finset.image_toFinset, roots_expand_pow_map_iterateFrobenius,
    (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']
/-
**Polynomial.roots_expand_image_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：roots_expand_image_frobenius [DecidableEq R] : (expand R p f).roots.toFins
et.image (frobenius R p) = f.roots.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_toFinset`：image_toFinset [DecidableEq α] {s : Multiset α} :
 s.toFinset.image f = (s.map f).toFinset
· 使用定理 `Polynomial.roots_expand_map_frobenius`：roots_expand_map_frobenius : (exp
and R p f).roots.map (frobenius R p) = p • f.roots
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `expChar_pos`：expChar_pos (q : Nat) [ExpChar R q] : 0 < q
-/
theorem roots_expand_image_frobenius [DecidableEq R] :
    (expand R p f).roots.toFinset.image (frobenius R p) = f.roots.toFinset := by
  rw [Finset.image_toFinset, roots_expand_map_frobenius,
      (roots f).toFinset_nsmul _ (expChar_pos R p).ne']

end PerfectRing

variable [DecidableEq R]

/-- If `f` is a polynomial over an integral domain `R` of characteristic `p`, then there is
a map from the set of roots of `Polynomial.expand R p f` to the set of roots of `f`.
It's given by `x ↦ x ^ p`, see `rootsExpandToRoots_apply`. -/
/-
**Polynomial.rootsExpandToRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandToRoots : (expand R p f).roots.toFinset ↪ f.roots.toFinset wher
e toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a polynomial over an integral domain `R` of characteristic `p`, then t
here is
a map from the set of roots of `Polynomial.expand R p f` to the set of roots of 
`f`.
It's given by `x ↦ x ^ p`, see `rootsExpandToRoots_apply`.
-/
noncomputable def rootsExpandToRoots : (expand R p f).roots.toFinset ↪ f.roots.toFinset where
  toFun x := ⟨x ^ p, roots_expand_image_frobenius_subset p f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (frobenius_inj R p <| Subtype.ext_iff.1 h)

@[simp]
/-
**Polynomial.rootsExpandToRoots_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandToRoots_apply (x) : (rootsExpandToRoots p f x : R) = x ^ p
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsExpandToRoots_apply (x) : (rootsExpandToRoots p f x : R) = x ^ p := rfl

/-- If `f` is a polynomial over an integral domain `R` of characteristic `p`, then there is
a map from the set of roots of `Polynomial.expand R (p ^ n) f` to the set of roots of `f`.
It's given by `x ↦ x ^ (p ^ n)`, see `rootsExpandPowToRoots_apply`. -/
/-
**Polynomial.rootsExpandPowToRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandPowToRoots : (expand R (p ^ n) f).roots.toFinset ↪ f.roots.toFi
nset where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a polynomial over an integral domain `R` of characteristic `p`, then t
here is
a map from the set of roots of `Polynomial.expand R (p ^ n) f` to the set of roo
ts of `f`.
It's given by `x ↦ x ^ (p ^ n)`, see `rootsExpandPowToRoots_apply`.
-/
noncomputable def rootsExpandPowToRoots :
    (expand R (p ^ n) f).roots.toFinset ↪ f.roots.toFinset where
  toFun x := ⟨x ^ p ^ n,
    roots_expand_pow_image_iterateFrobenius_subset p n f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (iterateFrobenius_inj R p n <| Subtype.ext_iff.1 h)

@[simp]
/-
**Polynomial.rootsExpandPowToRoots_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandPowToRoots_apply (x) : (rootsExpandPowToRoots p n f x : R) = x 
^ p ^ n
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsExpandPowToRoots_apply (x) : (rootsExpandPowToRoots p n f x : R) = x ^ p ^ n := rfl

variable [PerfectRing R p]

/-- If `f` is a polynomial over a perfect integral domain `R` of characteristic `p`, then there is
a bijection from the set of roots of `Polynomial.expand R p f` to the set of roots of `f`.
It's given by `x ↦ x ^ p`, see `rootsExpandEquivRoots_apply`. -/
/-
**Polynomial.rootsExpandEquivRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandEquivRoots : (expand R p f).roots.toFinset ≃ f.roots.toFinset
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `f` is a polynomial over a perfect integral domain `R` of characteristic `p`,
 then there is
a bijection from the set of roots of `Polynomial.expand R p f` to the set of roo
ts of `f`.
It's given by `x ↦ x ^ p`, see `rootsExpandEquivRoots_apply`.
-/
noncomputable def rootsExpandEquivRoots : (expand R p f).roots.toFinset ≃ f.roots.toFinset :=
  ((frobeniusEquiv R p).image _).trans <| .setCongr <| by
    rw [← roots_expand_image_frobenius (p := p) (f := f)]
    simp

@[simp]
/-
**Polynomial.rootsExpandEquivRoots_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandEquivRoots_apply (x) : (rootsExpandEquivRoots p f x : R) = x ^ 
p
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsExpandEquivRoots_apply (x) : (rootsExpandEquivRoots p f x : R) = x ^ p := rfl

/-- If `f` is a polynomial over a perfect integral domain `R` of characteristic `p`, then there is
a bijection from the set of roots of `Polynomial.expand R (p ^ n) f` to the set of roots of `f`.
It's given by `x ↦ x ^ (p ^ n)`, see `rootsExpandPowEquivRoots_apply`. -/
/-
**Polynomial.rootsExpandPowEquivRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootsExpandPowEquivRoots (n : Nat) : (expand R (p ^ n) f).roots.toFinset ≃
 f.roots.toFinset
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `f` is a polynomial over a perfect integral domain `R` of characteristic `p`,
 then there is
a bijection from the set of roots of `Polynomial.expand R (p ^ n) f` to the set 
of roots of `f`.
It's given by `x ↦ x ^ (p ^ n)`, see `rootsExpandPowEquivRoots_apply`.
-/
noncomputable def rootsExpandPowEquivRoots (n : ℕ) :
    (expand R (p ^ n) f).roots.toFinset ≃ f.roots.toFinset :=
  ((iterateFrobeniusEquiv R p n).image _).trans <| .setCongr <| by
    rw [← roots_expand_image_iterateFrobenius (p := p) (f := f) (n := n)]
    simp

@[simp]
/-
**Polynomial.rootsExpandPowEquivRoots_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：rootsExpandPowEquivRoots_apply (n : Nat) (x) : (rootsExpandPowEquivRoots p
 f n x : R) = x ^ p ^ n
参数：n : Nat；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsExpandPowEquivRoots_apply (n : ℕ) (x) :
    (rootsExpandPowEquivRoots p f n x : R) = x ^ p ^ n := rfl

end Polynomial

