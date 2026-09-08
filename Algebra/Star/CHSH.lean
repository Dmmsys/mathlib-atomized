/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Real.Star

/-!
# The Clauser-Horne-Shimony-Holt inequality and Tsirelson's inequality.

We establish a version of the Clauser-Horne-Shimony-Holt (CHSH) inequality
(which is a generalization of Bell's inequality).
This is a foundational result which implies that
quantum mechanics is not a local hidden variable theory.

As usually stated the CHSH inequality requires substantial language from physics and probability,
but it is possible to give a statement that is purely about ordered \*-algebras.
We do that here, to avoid as many practical and logical dependencies as possible.
Since the algebra of observables of any quantum system is an ordered \*-algebra
(in particular a von Neumann algebra) this is a strict generalization of the usual statement.

Let `R` be a \*-ring.

A CHSH tuple in `R` consists of
* four elements `A₀ A₁ B₀ B₁ : R`, such that
* each `Aᵢ` and `Bⱼ` is a self-adjoint involution, and
* the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that the four elements are observables (hence self-adjoint)
that take values ±1 (hence involutions), and that the `Aᵢ` are spacelike separated from the `Bⱼ`
(and hence commute).

The CHSH inequality says that when `R` is an ordered \*-ring
(that is, a \*-ring which is ordered, and for every `r : R`, `0 ≤ star r * r`),
which is moreover *commutative*, we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`

On the other hand, Tsirelson's inequality says that for any ordered \*-ring we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2√2`

(A caveat: in the commutative case we need 2⁻¹ in the ring,
and in the noncommutative case we need √2 and √2⁻¹.
To keep things simple we just assume our rings are ℝ-algebras.)

The proofs I've seen in the literature either
assume a significant framework for quantum mechanics,
or assume the ring is a C⋆-algebra.
In the C⋆-algebra case,
the order structure is completely determined by the \*-algebra structure:
`0 ≤ A` iff there exists some `B` so `A = star B * B`.
There's a nice proof of both bounds in this setting at
https://en.wikipedia.org/wiki/Tsirelson%27s_bound
The proof given here is purely algebraic.

## Future work

One can show that Tsirelson's inequality is tight.
In the \*-ring of n-by-n complex matrices, if `A ≤ λ I` for some `λ : ℝ`,
then every eigenvalue has absolute value at most `λ`.
There is a CHSH tuple in 4-by-4 matrices such that
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has `2√2` as an eigenvalue.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]
* [Bell, *On the Einstein Podolsky Rosen Paradox*][MR3790629]
* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]

-/

public section


universe u

/-- A CHSH tuple in a \*-monoid consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁` such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of Boolean observables which
are spacelike separated from another pair `B₀` and `B₁` of Boolean observables.
-/
/-
**IsCHSHTuple** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [inst : Monoid R] → [StarMul R] → R → R → R → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CHSH tuple in a \*-monoid consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁`
 such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of Boolean observab
les which
are spacelike separated from another pair `B₀` and `B₁` of Boolean observables.
-/
structure IsCHSHTuple {R} [Monoid R] [StarMul R] (A₀ A₁ B₀ B₁ : R) : Prop where
  A₀_inv : A₀ ^ 2 = 1
  A₁_inv : A₁ ^ 2 = 1
  B₀_inv : B₀ ^ 2 = 1
  B₁_inv : B₁ ^ 2 = 1
  A₀_sa : star A₀ = A₀
  A₁_sa : star A₁ = A₁
  B₀_sa : star B₀ = B₀
  B₁_sa : star B₁ = B₁
  A₀B₀_commutes : A₀ * B₀ = B₀ * A₀
  A₀B₁_commutes : A₀ * B₁ = B₁ * A₀
  A₁B₀_commutes : A₁ * B₀ = B₀ * A₁
  A₁B₁_commutes : A₁ * B₁ = B₁ * A₁

variable {R : Type u}
/-
**CHSH_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ 
^ 2 = 1) (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) : (2 - A₀ * B₀ - A₀ * B₁ - 
A₁ * B₀ + A₁ * B₁) * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) = 4 * (2 - A₀ *
 B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁)
参数：A₀_inv : A₀ ^ 2 = 1；A₁_inv : A₁ ^ 2 = 1；B₀_inv : B₀ ^ 2 = 1；B₁_inv : B₁ ^ 2 =
 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ ^ 2 = 1)
    (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) :
    (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) =
      4 * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) := by
  grind

/-- Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered \*-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
/-
**CHSH_inequality_of_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CHSH_inequality_of_comm [CommRing R] [PartialOrder R] [StarRing R] [StarOr
deredRing R] [Algebra Real R] [IsOrderedModule Real R] (A₀ A₁ B₀ B₁ : R) (T : Is
CHSHTuple A₀ A₁ B₀ B₁) : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ <= 2
参数：A₀ A₁ B₀ B₁ : R；T : IsCHSHTuple A₀ A₁ B₀ B₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CHSH_id`：CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A
₁_inv : A₁ ^ 2 = 1) (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) : (2 - A₀ * B…
· 使用定理 `IsCHSHTuple.A₀_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₀ ^ 2 = 1
· 使用定理 `IsCHSHTuple.A₁_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₁ ^ 2 = 1
· 使用定理 `IsCHSHTuple.B₀_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → B₀ ^ 2 = 1
· 使用定理 `IsCHSHTuple.B₁_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → B₁ ^ 2 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `star_ofNat`：star_ofNat [NonAssocSemiring R] [StarRing R] (n : Nat) [n.At
LeastTwo] : star (ofNat(n) : R) = ofNat(n)
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsCHSHTuple.B₀_sa`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul 
R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → star B₀ = B₀
· 使用定理 `IsCHSHTuple.A₀_sa`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul 
R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → star A₀ = A₀
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsCHSHTuple.B₁_sa`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul 
R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → star B₁ = B₁
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered \*-algebra over ℝ
,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
theorem CHSH_inequality_of_comm [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 := by
  let P := 2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁
  have i₁ : 0 ≤ P := by
    have idem : P * P = 4 * P := CHSH_id T.A₀_inv T.A₁_inv T.B₀_inv T.B₁_inv
    have idem' : P = (1 / 4 : ℝ) • (P * P) := by
      have h : 4 * P = (4 : ℝ) • P := by simp [map_ofNat, Algebra.smul_def]
      rw [idem, h, ← mul_smul]
      simp
    have sa : star P = P := by
      dsimp [P]
      simp only [star_add, star_sub, star_mul, star_ofNat, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa, mul_comm B₀, mul_comm B₁]
    simpa only [← idem', sa]
      using smul_nonneg (by simp : (0 : ℝ) ≤ 1 / 4) (star_mul_self_nonneg P)
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add] using i₁

/-!
We now prove some rather specialized lemmas in preparation for the Tsirelson inequality,
which we hide in a namespace as they are unlikely to be useful elsewhere.
-/


namespace TsirelsonInequality

/-!
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/

/-
**TsirelsonInequality.sqrt_two_inv_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Tsirelson
Inequality`。
形式化陈述：sqrt_two_inv_mul_self : (√2)⁻¹ * (√2)⁻¹ = (2⁻¹ : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/
theorem sqrt_two_inv_mul_self : (√2)⁻¹ * (√2)⁻¹ = (2⁻¹ : ℝ) := by
  rw [← mul_inv]
  simp

end TsirelsonInequality

open TsirelsonInequality

/-- In a noncommutative ordered \*-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
/-
**tsirelson_inequality** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsirelson_inequality [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRi
ng R] [Algebra Real R] [IsOrderedModule Real R] [StarModule Real R] (A₀ A₁ B₀ B₁
 : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ <= √
2 ^ 3 • (1 : R)
参数：A₀ A₁ B₀ B₁ : R；T : IsCHSHTuple A₀ A₁ B₀ B₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `TsirelsonInequality.sqrt_two_inv_mul_self`：sqrt_two_inv_mul_self : (√2)⁻
¹ * (√2)⁻¹ = (2⁻¹ : Real)
· 使用定理 `IsCHSHTuple.A₁_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₁ ^ 2 = 1
· 使用定理 `IsCHSHTuple.A₀_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₀ ^ 2 = 1
· 使用定理 `IsCHSHTuple.B₀_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → B₀ ^ 2 = 1
· 使用定理 `IsCHSHTuple.B₁_inv`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul
 R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → B₁ ^ 2 = 1
· 使用定理 `IsCHSHTuple.A₁B₀_commutes`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₁ * B₀ = B₀ * A₁
· 使用定理 `IsCHSHTuple.A₀B₀_commutes`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₀ * B₀ = B₀ * A₀
· 使用定理 `IsCHSHTuple.A₁B₁_commutes`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₁ * B₁ = B₁ * A₁
· 使用定理 `IsCHSHTuple.A₀B₁_commutes`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] {A₀ A₁ B₀ B₁ : R}, IsCHSHTuple A₀ A₁ B₀ B₁ → A₀ * B₁ = B₁ * A₀
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
In a noncommutative ordered \*-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
theorem tsirelson_inequality [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • (1 : R) := by
  -- abel will create `ℤ` multiplication. We will `simp` them away to `ℝ` multiplication.
  have M : ∀ (m : ℤ) (a : ℝ) (x : R), m • a • x = ((m : ℝ) * a) • x := fun m a x => by
    rw [← Int.cast_smul_eq_zsmul ℝ, ← mul_smul]
  let P := (√2)⁻¹ • (A₁ + A₀) - B₀
  let Q := (√2)⁻¹ • (A₁ - A₀) + B₁
  have w : √2 ^ 3 • (1 : R) - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = (√2)⁻¹ • (P ^ 2 + Q ^ 2) := by
    dsimp [P, Q]
    -- distribute out all the powers and products appearing on the RHS
    simp only [sq, sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub]
    -- pull all coefficients out to the front, and combine `√2`s where possible
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, sqrt_two_inv_mul_self]
    -- replace Aᵢ * Aᵢ = 1 and Bᵢ * Bᵢ = 1
    simp only [← sq, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv]
    -- move Aᵢ to the left of Bᵢ
    simp only [← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
    -- collect terms, simplify coefficients, and collect terms again:
    abel_nf
    -- all terms coincide, but the last one. Simplify all other terms
    simp only [M]
    simp only [neg_mul, mul_inv_cancel_of_invertible, add_assoc, add_comm,
      add_left_comm, one_smul, Int.cast_neg, neg_smul, Int.cast_ofNat, ← add_smul]
    grind
  have pos : 0 ≤ (√2)⁻¹ • (P ^ 2 + Q ^ 2) := by
    have P_sa : star P = P := by
      simp only [P, star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa]
    have Q_sa : star Q = Q := by
      simp only [Q, star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₁_sa]
    have P2_nonneg : 0 ≤ P ^ 2 := by simpa only [P_sa, sq] using star_mul_self_nonneg P
    have Q2_nonneg : 0 ≤ Q ^ 2 := by simpa only [Q_sa, sq] using star_mul_self_nonneg Q
    positivity
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add, w, Nat.cast_zero] using pos
