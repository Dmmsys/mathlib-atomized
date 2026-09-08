/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Modules over `ℕ` and `ℤ`

This file concerns modules where the scalars are the natural numbers or the integers.

## Main definitions

* `AddCommMonoid.toNatModule`: any `AddCommMonoid` is (uniquely) a module over the naturals.
* `AddCommGroup.toIntModule`: any `AddCommGroup` is a module over the integers.

## Main results

* `AddCommMonoid.uniqueNatModule`: there is a unique `AddCommMonoid ℕ M` structure for any `M`

## Tags

semimodule, module, vector space
-/

@[expose] public section

assert_not_exists RelIso Field Invertible Multiset Pi.single_smul₀ Set.indicator

open Function Set

universe u v

variable {R S M M₂ : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid M] : MulAction ℕ M where
  one_smul := one_nsmul
  mul_smul _ _ _ := mul_nsmul' ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid M] : SMulWithZero ℕ M where
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SubtractionMonoid M] : MulAction ℤ M where
  one_smul := one_zsmul
  mul_smul _ _ _ := mul_zsmul ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SubtractionMonoid M] : SMulWithZero ℤ M where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul

section AddCommMonoid

variable [AddCommMonoid M]

/-
**AddCommMonoid.toNatModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommMonoid.toNatModule : Module Nat M where smul_add n a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
-/
instance AddCommMonoid.toNatModule : Module ℕ M where
  smul_add n a b := nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s
/-
**DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom : toAddMonoidHom M = nsmul
AddMonoidHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom :
    toAddMonoidHom M = nsmulAddMonoidHom := rfl

end AddCommMonoid

section AddCommGroup

variable (M) [AddCommGroup M]

/-
**AddCommGroup.toIntModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommGroup.toIntModule : Module Int M where one_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddCommGroup.toIntModule : Module ℤ M where
  one_smul := one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s
/-
**DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom : toAddMonoidHom M = zsmulA
ddGroupHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom :
    toAddMonoidHom M = zsmulAddGroupHom := rfl

end AddCommGroup

variable (R) in
/-- An `AddCommMonoid` that is a `Module` over a `Ring` carries a natural `AddCommGroup`
structure.
See note [reducible non-instances]. -/
/-
**Module.addCommMonoidToAddCommGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Module.addCommMonoidToAddCommGroup [Ring R] [AddCommMonoid M] [Module R M]
 : AddCommGroup M where neg
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a

--- 原说明 ---
An `AddCommMonoid` that is a `Module` over a `Ring` carries a natural `AddCommGr
oup`
structure.
See note [reducible non-instances].
-/
abbrev Module.addCommMonoidToAddCommGroup
    [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M where
  neg := fun a => (-1 : R) • a
  neg_add_cancel := fun a =>
    show (-1 : R) • a + a = 0 by
      nth_rw 2 [← one_smul R a]
      rw [← add_smul, neg_add_cancel, zero_smul]
  zsmul z a := (z : R) • a
  zsmul_zero' a := by simp_rw [HSMul.hSMul, SMul.smul, Int.cast_zero]; exact zero_smul R a
  zsmul_succ' z a := by simp_rw [HSMul.hSMul, SMul.smul]; simp [add_comm, add_smul]
  zsmul_neg' z a := by
    change (Int.negSucc z : R) • a = -1 • ((z.succ : ℤ) : R) • a
    simp [← smul_assoc]

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
@[norm_cast]
/-
**Nat.cast_smul_eq_nsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : R) • b = n • b
参数：n : Nat；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
`nsmul` is equal to any other module structure via a cast.
-/
lemma Nat.cast_smul_eq_nsmul (n : ℕ) (b : M) : (n : R) • b = n • b := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul]
  | succ n ih => rw [Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]

/-- `nsmul` is equal to any other module structure via a cast. -/
/-
**ofNat_smul_eq_nsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofNat_smul_eq_nsmul (n : Nat) [n.AtLeastTwo] (b : M) : (ofNat(n) : R) • b 
= ofNat(n) • b
参数：n : Nat；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b

--- 原说明 ---
`nsmul` is equal to any other module structure via a cast.
-/
lemma ofNat_smul_eq_nsmul (n : ℕ) [n.AtLeastTwo] (b : M) :
    (ofNat(n) : R) • b = ofNat(n) • b := Nat.cast_smul_eq_nsmul ..

end

/-- Convert back any exotic `ℕ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommMonoid`s should normally have exactly one `ℕ`-module structure by design.
-/
/-
**nat_smul_eq_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nat_smul_eq_nsmul (h : Module Nat M) (n : Nat) (x : M) : h.smul n x = n • 
x
参数：h : Module Nat M；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b

--- 原说明 ---
Convert back any exotic `ℕ`-smul to the canonical instance. This should not be n
eeded since in
mathlib all `AddCommMonoid`s should normally have exactly one `ℕ`-module structu
re by design.
-/
theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) : h.smul n x = n • x :=
  Nat.cast_smul_eq_nsmul ..

/-- All `ℕ`-module structures are equal. Not an instance since in mathlib all `AddCommMonoid`
should normally have exactly one `ℕ`-module structure by design. -/
@[instance_reducible]
/-
**AddCommMonoid.uniqueNatModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCommMonoid.uniqueNatModule : Unique (Module Nat M) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All `ℕ`-module structures are equal. Not an instance since in mathlib all `AddCo
mmMonoid`
should normally have exactly one `ℕ`-module structure by design.
-/
def AddCommMonoid.uniqueNatModule : Unique (Module ℕ M) where
  default := inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! nat_smul_eq_nsmul P n

/-- All `ℕ`-module structures are equal. See also `AddCommMonoid.uniqueNatModule`. -/
/-
**AddCommMonoid.subsingletonNatModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommMonoid.subsingletonNatModule : Subsingleton (Module Nat M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
All `ℕ`-module structures are equal. See also `AddCommMonoid.uniqueNatModule`.
-/
instance AddCommMonoid.subsingletonNatModule : Subsingleton (Module ℕ M) :=
  AddCommMonoid.uniqueNatModule.instSubsingleton
/-
**AddCommMonoid.nat_isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommMonoid.nat_isScalarTower : IsScalarTower Nat R M where smul_assoc n
 x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
instance AddCommMonoid.nat_isScalarTower : IsScalarTower ℕ R M where
  smul_assoc n x y := by
    induction n with
    | zero => simp only [zero_smul]
    | succ n ih => simp only [add_smul, one_smul, ih]

end AddCommMonoid

/-
**map_natCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike
 F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Semiring R] [Semiring
 S] [Module R M] [Module S M₂] (x : Nat) (a : M) : f ((x : R) • a) = (x : S) • f
 a
参数：f : F；R S : Type*；x : Nat；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Semiring R] [Semiring S] [Module R M]
    [Module S M₂] (x : ℕ) (a : M) : f ((x : R) • a) = (x : S) • f a := by
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]
/-
**Nat.smul_one_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring R] (m : Nat) : m • (1 :
 R) = ↑m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring R] (m : ℕ) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul, mul_one]
/-
**Int.smul_one_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.smul_one_eq_cast {R : Type*} [NonAssocRing R] (m : Int) : m • (1 : R) 
= ↑m
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Int.smul_one_eq_cast {R : Type*} [NonAssocRing R] (m : ℤ) : m • (1 : R) = ↑m := by
  rw [zsmul_eq_mul, mul_one]

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M]

section

variable (R)

/-- `zsmul` is equal to any other module structure via a cast. -/
@[norm_cast]
/-
**Int.cast_smul_eq_zsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : R) • b = n • b
参数：n : Int；b : M。
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
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)

--- 原说明 ---
`zsmul` is equal to any other module structure via a cast.
-/
lemma Int.cast_smul_eq_zsmul (n : ℤ) (b : M) : (n : R) • b = n • b := by
  cases n with
  | ofNat => simp [Nat.cast_smul_eq_nsmul]
  | negSucc => simp [add_smul, Nat.cast_smul_eq_nsmul]

end

/-- Convert back any exotic `ℤ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommGroup`s should normally have exactly one `ℤ`-module structure by design. -/
/-
**int_smul_eq_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：int_smul_eq_zsmul (h : Module Int M) (n : Int) (x : M) : h.smul n x = n • 
x
参数：h : Module Int M；n : Int；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b

--- 原说明 ---
Convert back any exotic `ℤ`-smul to the canonical instance. This should not be n
eeded since in
mathlib all `AddCommGroup`s should normally have exactly one `ℤ`-module structur
e by design.
-/
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) : h.smul n x = n • x :=
  Int.cast_smul_eq_zsmul ..

/-- All `ℤ`-module structures are equal. Not an instance since in mathlib all `AddCommGroup`
should normally have exactly one `ℤ`-module structure by design. -/
@[instance_reducible]
/-
**AddCommGroup.uniqueIntModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCommGroup.uniqueIntModule : Unique (Module Int M) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All `ℤ`-module structures are equal. Not an instance since in mathlib all `AddCo
mmGroup`
should normally have exactly one `ℤ`-module structure by design.
-/
def AddCommGroup.uniqueIntModule : Unique (Module ℤ M) where
  default := inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! int_smul_eq_zsmul P n

end AddCommGroup

/-- All `ℤ`-module structures are equal. See also `AddCommGroup.uniqueIntModule`. -/
/-
**AddCommMonoid.subsingletonIntModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommMonoid.subsingletonIntModule [AddCommMonoid M] : Subsingleton (Modu
le Int M) where allEq a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
All `ℤ`-module structures are equal. See also `AddCommGroup.uniqueIntModule`.
-/
instance AddCommMonoid.subsingletonIntModule [AddCommMonoid M] : Subsingleton (Module ℤ M) where
  allEq a b :=
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℤ
    AddCommGroup.uniqueIntModule.instSubsingleton.allEq a b
/-
**map_intCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F
 M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Modul
e R M] [Module S M₂] (x : Int) (a : M) : f ((x : R) • a) = (x : S) • f a
参数：f : F；R S : Type*；x : Int；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M] [Module S M₂]
    (x : ℤ) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by simp only [Int.cast_smul_eq_zsmul, map_zsmul]
/-
**AddCommGroup.intIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommG
roup M] [Module R M] : IsScalarTower Int R M where smul_assoc n x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
-/
instance AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] : IsScalarTower ℤ R M where
  smul_assoc n x y := by
    cases n with
    | ofNat => simp [mul_smul, Nat.cast_smul_eq_nsmul]
    | negSucc => simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]

variable (M) in
/-- If `M` is an `R`-module with one and `M` has characteristic zero, then `R` has characteristic
zero as well. Usually `M` is an `R`-algebra. -/
/-
**CharZero.of_module** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CharZero.of_module [Semiring R] [AddCommMonoidWithOne M] [CharZero M] [Mod
ule R M] : CharZero R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b

--- 原说明 ---
If `M` is an `R`-module with one and `M` has characteristic zero, then `R` has c
haracteristic
zero as well. Usually `M` is an `R`-algebra.
-/
lemma CharZero.of_module [Semiring R] [AddCommMonoidWithOne M] [CharZero M] [Module R M] :
    CharZero R := by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one, ← nsmul_one, ← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, h]
