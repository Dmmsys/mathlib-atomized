/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Ring.Defs

/-!
# Modules over a ring

In this file we define

* `Module R M` : an additive commutative monoid `M` is a `Module` over a
  `Semiring R` if for `r : R` and `x : M` their "scalar multiplication" `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

## Implementation notes

In typical mathematical usage, our definition of `Module` corresponds to "semimodule", and the
word "module" is reserved for `Module R M` where `R` is a `Ring` and `M` an `AddCommGroup`.
If `R` is a `Field` and `M` an `AddCommGroup`, `M` would be called an `R`-vector space.
Since those assumptions can be made by changing the typeclasses applied to `R` and `M`,
without changing the axioms in `Module`, mathlib calls everything a `Module`.

In older versions of mathlib3, we had separate abbreviations for semimodules and vector spaces.
This caused inference issues in some cases, while not providing any real advantages, so we decided
to use a canonical `Module` typeclass throughout.

## Tags

semimodule, module, vector space
-/

public section

assert_not_exists Field Invertible Pi.single_smul₀ RingHom Set.indicator Multiset Units

open Function Set

universe u v

variable {R S M M₂ : Type*}

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext]
/-
**Module** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (M : Type v) → [Semiring R] → [AddCommMonoid M] → Type (max
 u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring.
-/
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

-- see Note [lower instance priority]
/-- A module over a semiring automatically inherits a `MulActionWithZero` structure. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module over a semiring automatically inherits a `MulActionWithZero` structure.
-/
instance (priority := 100) Module.toMulActionWithZero
    {R M} {_ : Semiring R} {_ : AddCommMonoid M} [Module R M] : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with
    smul_zero := smul_zero
    zero_smul := Module.zero_smul }
/-
**add_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_smul : (r + s) • x = r • x + s • x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.add_smul`：∀ {R : Type u} {M : Type v} {inst : Semiring R} {inst_1
 : AddCommMonoid M} [self : _root_.Module R M] (r s : R) (x : M),   (r + s) • x 
= r •…
-/
theorem add_smul : (r + s) • x = r • x + s • x :=
  Module.add_smul r s x
/-
**Convex.combo_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) : a • x + b • x = x
参数：h : a + b = 1；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem Convex.combo_self {a b : R} (h : a + b = 1) (x : M) : a • x + b • x = x := by
  rw [← add_smul, h, one_smul]

variable (R)
/-
**two_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_smul : (2 : R) • x = x + x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem two_smul : (2 : R) • x = x + x := by rw [← one_add_one_eq_two, add_smul, one_smul]

/-- Pullback a `Module` structure along an injective additive monoid homomorphism.
See note [reducible non-instances]. -/
/-
**Function.Injective.module** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：(R : Type u_1) →   {M : Type u_3} →     {M₂ : Type u_4} →       [inst : Se
miring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modu
le R M] →             [inst_3 : AddCommMonoid M₂] →               [inst_4 : SMul
 R M₂] →                 (f : M₂ →+ M) → Function.Injective ⇑f → (∀ (c : R) (x :
 M₂), f (c • x) = c • f x) → _root_.Module R M₂
参数：c : R；x : M₂；c • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `Module` structure along an injective additive monoid homomorphism.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.module [AddCommMonoid M₂] [SMul R M₂] (f : M₂ →+ M)
    (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.distribMulAction f smul with
    add_smul := fun c₁ c₂ x => hf <| by simp only [smul, f.map_add, add_smul]
    zero_smul := fun x => hf <| by simp only [smul, zero_smul, f.map_zero] }

/-- Pushforward a `Module` structure along a surjective additive monoid homomorphism.
See note [reducible non-instances]. -/
/-
**Function.Surjective.module** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：(R : Type u_1) →   {M : Type u_3} →     {M₂ : Type u_4} →       [inst : Se
miring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modu
le R M] →             [inst_3 : AddCommMonoid M₂] →               [inst_4 : SMul
 R M₂] →                 (f : M →+ M₂) → Function.Surjective ⇑f → (∀ (c : R) (x 
: M), f (c • x) = c • f x) → _root_.Module R M₂
参数：c : R；x : M；c • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward a `Module` structure along a surjective additive monoid homomorphism
.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.module [AddCommMonoid M₂] [SMul R M₂] (f : M →+ M₂)
    (hf : Surjective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero, ← smul, zero_smul] }

variable {R}
/-
**Module.eq_zero_of_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0
参数：zero_eq_one : (0 : R) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem Module.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 := by
  rw [← one_smul R x, ← zero_eq_one, zero_smul]

@[simp]
/-
**smul_add_one_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_add_one_sub_smul {R : Type*} [Ring R] [Module R M] {r : R} {m : M} : 
r • m + (1 - r) • m = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smul_add_one_sub_smul {R : Type*} [Ring R] [Module R M] {r : R} {m : M} :
    r • m + (1 - r) • m = m := by rw [← add_smul, add_sub_cancel, one_smul]

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M]

/-
**Convex.combo_eq_smul_sub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_eq_smul_sub_add [Module R M] {x y : M} {a b : R} (h : a + b =
 1) : a • x + b • y = b • (y - x) + x
参数：h : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_add_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a - c + (b + c) = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem Convex.combo_eq_smul_sub_add [Module R M] {x y : M} {a b : R} (h : a + b = 1) :
    a • x + b • y = b • (y - x) + x :=
  calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by rw [sub_add_add_cancel, add_comm]
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]

end AddCommGroup

-- We'll later use this to show `Module ℕ M` and `Module ℤ M` are subsingletons.
/-- A variant of `Module.ext` that's convenient for term-mode. -/
/-
**Module.ext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] (P Q : 
Module R M) (w : forall (r : R) (m : M), (haveI
参数：P Q : Module R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.ext`：∀ {R : Type u} {M : Type v} {inst : Semiring R} {inst_1 : Ad
dCommMonoid M} {x y : _root_.Module R M},   SMul.smul = SMul.smul → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A variant of `Module.ext` that's convenient for term-mode.
-/
theorem Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] (P Q : Module R M)
    (w : ∀ (r : R) (m : M), (haveI := P; r • m) = (haveI := Q; r • m)) :
    P = Q := by
  ext
  exact w _ _

section Module

variable [Ring R] [AddCommGroup M] [Module R M] (r : R) (x : M)

@[simp]
/-
**neg_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_smul : -r • x = -(r • x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem neg_smul : -r • x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← add_smul, neg_add_cancel, zero_smul]
/-
**neg_smul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_smul_neg : -r • -x = r • x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_smul_neg : -r • -x = r • x := by rw [neg_smul, smul_neg, neg_neg]

variable (R)
/-
**neg_one_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_one_smul (x : M) : (-1 : R) • x = -x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp

variable {R}
/-
**sub_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
参数：r s : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
  simp [add_smul, sub_eq_add_neg]

end Module

/-- A module over a `Subsingleton` semiring is a `Subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
/-
**Module.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZero R] [Subsingleton R]
 [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleton M
参数：R : Type u_5；M : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionWithZero.subsingleton`：∀ (M₀ : Type u_2) (A : Type u_7) [inst :
 MonoidWithZero M₀] [inst_1 : Zero A] [MulActionWithZero M₀ A]   [Subsingleton M
₀], Subsingleton A

--- 原说明 ---
A module over a `Subsingleton` semiring is a `Subsingleton`. We cannot register 
this
as an instance because Lean has no way to guess `R`.
-/
protected theorem Module.subsingleton (R M : Type*) [MonoidWithZero R] [Subsingleton R] [Zero M]
    [MulActionWithZero R M] : Subsingleton M :=
  MulActionWithZero.subsingleton R M

/-- A semiring is `Nontrivial` provided that there exists a nontrivial module over this semiring. -/
/-
**Module.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZero R] [Nontrivial M] [
inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
参数：R : Type u_5；M : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionWithZero.nontrivial`：∀ (M₀ : Type u_2) (A : Type u_7) [inst : M
onoidWithZero M₀] [inst_1 : Zero A] [MulActionWithZero M₀ A] [Nontrivial A],   N
ontrivial M₀

--- 原说明 ---
A semiring is `Nontrivial` provided that there exists a nontrivial module over t
his semiring.
-/
protected theorem Module.nontrivial (R M : Type*) [MonoidWithZero R] [Nontrivial M] [Zero M]
    [MulActionWithZero R M] : Nontrivial R :=
  MulActionWithZero.nontrivial R M

-- see Note [higher instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 1100) Semiring.toModule [Semiring R] : Module R R where
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
  smul_zero := mul_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] : DistribSMul R R where
  smul_add := left_distrib
