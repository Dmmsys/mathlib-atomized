/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Jordan rings

Let `A` be a non-unital, non-associative ring. Then `A` is said to be a (commutative, linear) Jordan
ring if the multiplication is commutative and satisfies a weak associativity law known as the
Jordan Identity: for all `a` and `b` in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute.

A more general concept of a (non-commutative) Jordan ring can also be defined, as a
(non-commutative, non-associative) ring `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute.

Every associative algebra can be equipped with a symmetrized multiplication (characterized by
`SymAlg.sym_mul_sym`) making it into a commutative Jordan algebra (`IsCommJordan`).
Jordan algebras arising this way are said to be special.

A real Jordan algebra `A` can be introduced by
```lean
variable {A : Type*} [NonUnitalNonAssocCommRing A] [Module ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [IsCommJordan A]
```

## Main results

- `two_nsmul_lie_lmul_lmul_add_add_eq_zero` : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## Motivation

Every Jordan algebra `A` has a triple product defined, for `a` `b` and `c` in `A` by
$$
{a\,b\,c} = (a * b) * c - (a * c) * b + a * (b * c).
$$
Via this triple product Jordan algebras are related to a number of other mathematical structures:
Jordan triples, partial Jordan triples, Jordan pairs and quadratic Jordan algebras. In addition to
their considerable algebraic interest ([mccrimmon2004]) these structures have been shown to have
deep connections to mathematical physics, functional analysis and differential geometry. For more
information about these connections the interested reader is referred to [alfsenshultz2003],
[chu2012], [friedmanscarr2005], [iordanescu2003] and [upmeier1987].

There are also exceptional Jordan algebras which can be shown not to be the symmetrization of any
associative algebra. The 3x3 matrices of octonions is the canonical example.

Non-commutative Jordan algebras have connections to the Vidav-Palmer theorem
[cabreragarciarodriguezpalacios2014].

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

-/

public section


variable (A : Type*)

/-- A (non-commutative) Jordan multiplication. -/
/-
**IsJordan** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → [Mul A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (non-commutative) Jordan multiplication.
-/
class IsJordan [Mul A] : Prop where
  lmul_comm_rmul : ∀ a b : A, a * b * a = a * (b * a)
  lmul_lmul_comm_lmul : ∀ a b : A, a * a * (a * b) = a * (a * a * b)
  lmul_lmul_comm_rmul : ∀ a b : A, a * a * (b * a) = a * a * b * a
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))
  rmul_comm_rmul_rmul : ∀ a b : A, b * a * (a * a) = b * (a * a) * a

/-- A commutative Jordan multiplication -/
/-
**IsCommJordan** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → [CommMagma A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative Jordan multiplication
-/
class IsCommJordan [CommMagma A] : Prop where
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))

-- see Note [lower instance priority]
/-- A (commutative) Jordan multiplication is also a Jordan multiplication -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (commutative) Jordan multiplication is also a Jordan multiplication
-/
instance (priority := 100) IsCommJordan.toIsJordan [CommMagma A] [IsCommJordan A] : IsJordan A where
  lmul_comm_rmul a b := by rw [mul_comm, mul_comm a b]
  lmul_lmul_comm_lmul a b := by
    rw [mul_comm (a * a) (a * b), IsCommJordan.lmul_comm_rmul_rmul,
      mul_comm b (a * a)]
  lmul_comm_rmul_rmul := IsCommJordan.lmul_comm_rmul_rmul
  lmul_lmul_comm_rmul a b := by
    rw [mul_comm (a * a) (b * a), mul_comm b a,
      IsCommJordan.lmul_comm_rmul_rmul, mul_comm, mul_comm b (a * a)]
  rmul_comm_rmul_rmul a b := by
    rw [mul_comm b a, IsCommJordan.lmul_comm_rmul_rmul, mul_comm]

-- see Note [lower instance priority]
/-- Semigroup multiplication satisfies the (non-commutative) Jordan axioms -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Semigroup multiplication satisfies the (non-commutative) Jordan axioms
-/
instance (priority := 100) Semigroup.isJordan [Semigroup A] : IsJordan A where
  lmul_comm_rmul a b := by rw [mul_assoc]
  lmul_lmul_comm_lmul a b := by rw [mul_assoc, mul_assoc]
  lmul_comm_rmul_rmul a b := by rw [mul_assoc]
  lmul_lmul_comm_rmul a b := by rw [← mul_assoc]
  rmul_comm_rmul_rmul a b := by rw [← mul_assoc, ← mul_assoc]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommSemigroup.isCommJordan [CommSemigroup A] : IsCommJordan A where
  lmul_comm_rmul_rmul _ _ := mul_assoc _ _ _

local notation "L" => AddMonoid.End.mulLeft

local notation "R" => AddMonoid.End.mulRight

/-!
The Jordan axioms can be expressed in terms of commuting multiplication operators.
-/


section Commute

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

@[simp]
/-
**commute_lmul_rmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_lmul_rmul (a : A) : Commute (L a) (R a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsJordan.lmul_comm_rmul`：∀ {A : Type u_1} {inst : Mul A} [self : IsJorda
n A] (a b : A), a * b * a = a * (b * a)
-/
theorem commute_lmul_rmul (a : A) : Commute (L a) (R a) :=
  AddMonoidHom.ext fun _ => (IsJordan.lmul_comm_rmul _ _).symm

@[simp]
/-
**commute_lmul_lmul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a * a))
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsJordan.lmul_lmul_comm_lmul`：∀ {A : Type u_1} {inst : Mul A} [self : Is
Jordan A] (a b : A), a * a * (a * b) = a * (a * a * b)
-/
theorem commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a * a)) :=
  AddMonoidHom.ext fun _ => (IsJordan.lmul_lmul_comm_lmul _ _).symm

@[simp]
/-
**commute_lmul_rmul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_lmul_rmul_sq (a : A) : Commute (L a) (R (a * a))
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsJordan.lmul_comm_rmul_rmul`：∀ {A : Type u_1} {inst : Mul A} [self : Is
Jordan A] (a b : A), a * b * (a * a) = a * (b * (a * a))
-/
theorem commute_lmul_rmul_sq (a : A) : Commute (L a) (R (a * a)) :=
  AddMonoidHom.ext fun _ => (IsJordan.lmul_comm_rmul_rmul _ _).symm

@[simp]
/-
**commute_lmul_sq_rmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_lmul_sq_rmul (a : A) : Commute (L (a * a)) (R a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `IsJordan.lmul_lmul_comm_rmul`：∀ {A : Type u_1} {inst : Mul A} [self : Is
Jordan A] (a b : A), a * a * (b * a) = a * a * b * a
-/
theorem commute_lmul_sq_rmul (a : A) : Commute (L (a * a)) (R a) :=
  AddMonoidHom.ext fun _ => IsJordan.lmul_lmul_comm_rmul _ _

@[simp]
/-
**commute_rmul_rmul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_rmul_rmul_sq (a : A) : Commute (R a) (R (a * a))
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsJordan.rmul_comm_rmul_rmul`：∀ {A : Type u_1} {inst : Mul A} [self : Is
Jordan A] (a b : A), b * a * (a * a) = b * (a * a) * a
-/
theorem commute_rmul_rmul_sq (a : A) : Commute (R a) (R (a * a)) :=
  AddMonoidHom.ext fun _ => (IsJordan.rmul_comm_rmul_rmul _ _).symm

end Commute

variable {A} [NonUnitalNonAssocCommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-!
The endomorphisms on an additive monoid `AddMonoid.End` form a `Ring`, and this may be equipped
with a Lie Bracket via `Ring.bracket`.
-/

set_option backward.isDefEq.respectTransparency false in
/-
**two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add [IsCommJordan A] (a b : A
) : 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (b * a)⁆) = ⁅L (a * a), L b⁆ + ⁅L (b * b), L
 a⁆
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `Commute.lie_eq`：Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0
· 使用定理 `commute_lmul_lmul_sq`：commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a
 * a))
· 使用定理 `IsCommJordan.toIsJordan`：∀ (A : Type u_1) [inst : CommMagma A] [IsCommJo
rdan A], IsJordan A
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `_private.Mathlib.Algebra.Jordan.Basic.0.two_nsmul_lie_lmul_lmul_add_eq_l
ie_lmul_lmul_add._abel_1_1`：∀ {A : Type u_1} [inst : NonUnitalNonAssocCommRing A
] (a b : A),   ⁅AddMonoid.End.mulLeft a, AddMonoid.End.mulLeft (a * b)⁆ + ⁅AddMo
noid.End…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b

--- 原说明 ---
The endomorphisms on an additive monoid `AddMonoid.End` form a `Ring`, and this 
may be equipped
with a Lie Bracket via `Ring.bracket`.
-/
theorem two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add [IsCommJordan A] (a b : A) :
    2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (b * a)⁆) = ⁅L (a * a), L b⁆ + ⁅L (b * b), L a⁆ := by
  suffices 2 • ⁅L a, L (a * b)⁆ + 2 • ⁅L b, L (b * a)⁆ + ⁅L b, L (a * a)⁆ + ⁅L a, L (b * b)⁆ = 0 by
    rwa [← sub_eq_zero, ← sub_sub, sub_eq_add_neg, sub_eq_add_neg, lie_skew, lie_skew, nsmul_add]
  convert (commute_lmul_lmul_sq (a + b)).lie_eq
  simp only [add_mul, mul_add, map_add, lie_add, add_lie, mul_comm b a,
    (commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq, zero_add, add_zero, two_smul]
  abel

set_option backward.isDefEq.respectTransparency false in
-- Porting note: the monolithic `calc`-based proof of `two_nsmul_lie_lmul_lmul_add_add_eq_zero`
-- has had four auxiliary parts `aux{0,1,2,3}` split off from it.
/-
**aux0** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux0 {a b c : A} : ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ =
    ⁅L a + L b + L c, L (a * a) + L (b * b) + L (c * c) +
    2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆ := by
  rw [add_mul, add_mul]
  iterate 6 rw [mul_add]
  iterate 10 rw [map_add]
  rw [mul_comm b a, mul_comm c a, mul_comm c b]
  iterate 3 rw [two_smul]
  simp only [add_lie]
  abel_nf

set_option backward.isDefEq.respectTransparency false in
/-
**aux1** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux1 {a b c : A} :
    ⁅L a + L b + L c, L (a * a) + L (b * b) + L (c * c) +
    2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆
    =
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
    ⁅L a, 2 • L (a * b)⁆ + ⁅L a, 2 • L (c * a)⁆ + ⁅L a, 2 • L (b * c)⁆ +
    (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
    ⁅L b, 2 • L (a * b)⁆ + ⁅L b, 2 • L (c * a)⁆ + ⁅L b, 2 • L (b * c)⁆) +
    (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
    ⁅L c, 2 • L (a * b)⁆ + ⁅L c, 2 • L (c * a)⁆ + ⁅L c, 2 • L (b * c)⁆) := by
  rw [add_lie, add_lie]
  iterate 15 rw [lie_add]

variable [IsCommJordan A]

set_option backward.isDefEq.respectTransparency false in
/-
**aux2** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux2 {a b c : A} :
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
    ⁅L a, 2 • L (a * b)⁆ + ⁅L a, 2 • L (c * a)⁆ + ⁅L a, 2 • L (b * c)⁆ +
    (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
    ⁅L b, 2 • L (a * b)⁆ + ⁅L b, 2 • L (c * a)⁆ + ⁅L b, 2 • L (b * c)⁆) +
    (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
    ⁅L c, 2 • L (a * b)⁆ + ⁅L c, 2 • L (c * a)⁆ + ⁅L c, 2 • L (b * c)⁆)
    =
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ + 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
    (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ + 2 • (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
    (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ + 2 • (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
    (2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆) := by
  rw [(commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq,
    (commute_lmul_lmul_sq c).lie_eq, zero_add, add_zero, add_zero]
  simp only [lie_nsmul]
  abel
/-
**aux3** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux3 {a b c : A} :
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ + 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
    (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ + 2 • (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
    (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ + 2 • (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
    (2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆)
    =
    2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆ := by
  rw [add_eq_right]
  nth_rw 2 [mul_comm a b]
  nth_rw 1 [mul_comm c a]
  nth_rw 2 [mul_comm b c]
  iterate 3 rw [two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add]
  iterate 2 rw [← lie_skew (L (a * a)), ← lie_skew (L (b * b)), ← lie_skew (L (c * c))]
  abel

set_option backward.isDefEq.respectTransparency false in
/-
**two_nsmul_lie_lmul_lmul_add_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_nsmul_lie_lmul_lmul_add_add_eq_zero (a b c : A) : 2 • (⁅L a, L (b * c)
⁆ + ⁅L b, L (c * a)⁆ + ⁅L c, L (a * b)⁆) = 0
参数：a b c : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.lie_eq`：Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0
· 使用定理 `commute_lmul_lmul_sq`：commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a
 * a))
· 使用定理 `IsCommJordan.toIsJordan`：∀ (A : Type u_1) [inst : CommMagma A] [IsCommJo
rdan A], IsJordan A
· 使用定理 `_private.Mathlib.Algebra.Jordan.Basic.0.aux0`：∀ {A : Type u_1} [inst : N
onUnitalNonAssocCommRing A] {a b c : A},   ⁅AddMonoid.End.mulLeft (a + b + c), A
ddMonoid.End.mulLeft ((a + b + c) …
· 使用定理 `_private.Mathlib.Algebra.Jordan.Basic.0.aux1`：∀ {A : Type u_1} [inst : N
onUnitalNonAssocCommRing A] {a b c : A},   ⁅AddMonoid.End.mulLeft a + AddMonoid.
End.mulLeft b + AddMonoid.End.mulL…
· 使用定理 `_private.Mathlib.Algebra.Jordan.Basic.0.aux2`：∀ {A : Type u_1} [inst : N
onUnitalNonAssocCommRing A] [IsCommJordan A] {a b c : A},   ⁅AddMonoid.End.mulLe
ft a, AddMonoid.End.mulLeft (a * a…
· 使用定理 `_private.Mathlib.Algebra.Jordan.Basic.0.aux3`：∀ {A : Type u_1} [inst : N
onUnitalNonAssocCommRing A] [IsCommJordan A] {a b c : A},   ⁅AddMonoid.End.mulLe
ft a, AddMonoid.End.mulLeft (b * b…
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
-/
theorem two_nsmul_lie_lmul_lmul_add_add_eq_zero (a b c : A) :
    2 • (⁅L a, L (b * c)⁆ + ⁅L b, L (c * a)⁆ + ⁅L c, L (a * b)⁆) = 0 := by
  symm
  calc
    0 = ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ := by
      rw [(commute_lmul_lmul_sq (a + b + c)).lie_eq]
    _ = _ := by rw [aux0, aux1, aux2, aux3, nsmul_add, nsmul_add]
