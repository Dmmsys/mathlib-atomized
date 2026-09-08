/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Ring.Associator

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The five typeclasses are:

* `DirectSum.GNonUnitalNonAssocSemiring A`
* `DirectSum.GSemiring A`
* `DirectSum.GRing A`
* `DirectSum.GCommSemiring A`
* `DirectSum.GCommRing A`

Respectively, these five typeclasses imbue the external direct sum `⨁ i, A i` with:

* `DirectSum.nonUnitalNonAssocSemiring`, `DirectSum.nonUnitalNonAssocRing`
* `DirectSum.semiring`
* `DirectSum.ring`
* `DirectSum.commSemiring`
* `DirectSum.commRing`

the base ring `A 0` with instances of these types:

* `NonUnitalNonAssocSemiring (A 0)`, `NonUnitalNonAssocRing (A 0)`
* `Semiring (A 0)`
* `Ring (A 0)`
* `CommSemiring (A 0)`
* `CommRing (A 0)`

and the `i`th grade `A i` with `A 0`-actions (`•`) of these types:

* `SMulWithZero (A 0) (A i)`
* `Module (A 0) (A i)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`DirectSum.ofZeroRingHom : A 0 →+* ⨁ i, A i` provides `DirectSum.of A 0` as a ring
homomorphism.

`DirectSum.toSemiring` extends `DirectSum.toAddMonoid` to produce a `RingHom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `GSemiring` and `GCommSemiring`
instances for:

* `A : ι → Submonoid S`:
  `DirectSum.GSemiring.ofAddSubmonoids`, `DirectSum.GCommSemiring.ofAddSubmonoids`.
* `A : ι → Subgroup S`:
  `DirectSum.GSemiring.ofAddSubgroups`, `DirectSum.GCommSemiring.ofAddSubgroups`.
* `A : ι → Submodule S`:
  `DirectSum.GSemiring.ofSubmodules`, `DirectSum.GCommSemiring.ofSubmodules`.

If `sSupIndep A`, these provide a gradation of `⨆ i, A i`, and the mapping `⨁ i, A i →+ ⨆ i, A i`
can be obtained as `DirectSum.toMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

## Implementation details

The instances on `A 0` are scoped to the `DirectSum` namespace, because they have
very general discriminantion tree keys.

## Tags

graded ring, filtered ring, direct sum, additive submonoid
-/

@[expose] public section


variable {ι : Type*} [DecidableEq ι]

namespace DirectSum

open DirectSum

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type*)

/-- A graded version of `NonUnitalNonAssocSemiring`. -/
/-
**DirectSum.GNonUnitalNonAssocSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [Add ι] → [(i : ι) → AddCommMonoid (
A i)] → Type (max u_1 u_2)
参数：A : ι → Type u_2；i : ι；A i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `NonUnitalNonAssocSemiring`.
-/
class GNonUnitalNonAssocSemiring [Add ι] [∀ i, AddCommMonoid (A i)] extends
  GradedMonoid.GMul A where
  /-- Multiplication from the right with any graded component's zero vanishes. -/
  mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0
  /-- Multiplication from the left with any graded component's zero vanishes. -/
  zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0
  /-- Multiplication from the right between graded components distributes with respect to
  addition. -/
  mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
  /-- Multiplication from the left between graded components distributes with respect to
  addition. -/
  add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c

end Defs

section Defs

variable (A : ι → Type*)

/-- A graded version of `Semiring`. -/
/-
**DirectSum.GSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [AddMonoid ι] → [(i : ι) → AddCommMo
noid (A i)] → Type (max u_1 u_2)
参数：A : ι → Type u_2；i : ι；A i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Semiring`.
-/
class GSemiring [AddMonoid ι] [∀ i, AddCommMonoid (A i)] extends GNonUnitalNonAssocSemiring A,
  GradedMonoid.GMonoid A where
  /-- The canonical map from ℕ to the zeroth component of a graded semiring. -/
  natCast : ℕ → A 0
  /-- The canonical map from ℕ to a graded semiring respects zero. -/
  natCast_zero : natCast 0 = 0
  /-- The canonical map from ℕ to a graded semiring respects successors. -/
  natCast_succ : ∀ n : ℕ, natCast (n + 1) = natCast n + GradedMonoid.GOne.one

/-- A graded version of `CommSemiring`. -/
/-
**DirectSum.GCommSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [AddCommMonoid ι] → [(i : ι) → AddCo
mmMonoid (A i)] → Type (max u_1 u_2)
参数：A : ι → Type u_2；i : ι；A i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `CommSemiring`.
-/
class GCommSemiring [AddCommMonoid ι] [∀ i, AddCommMonoid (A i)] extends GSemiring A,
  GradedMonoid.GCommMonoid A

/-- A graded version of `Ring`. -/
/-
**DirectSum.GRing** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [AddMonoid ι] → [(i : ι) → AddCommGr
oup (A i)] → Type (max u_1 u_2)
参数：A : ι → Type u_2；i : ι；A i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Ring`.
-/
class GRing [AddMonoid ι] [∀ i, AddCommGroup (A i)] extends GSemiring A where
  /-- The canonical map from ℤ to the zeroth component of a graded ring. -/
  intCast : ℤ → A 0
  /-- The canonical map from ℤ to a graded ring extends the canonical map from ℕ to the underlying
  graded semiring. -/
  intCast_ofNat : ∀ n : ℕ, intCast n = natCast n
  /-- On negative integers, the canonical map from ℤ to a graded ring is the negative extension of
  the canonical map from ℕ to the underlying graded semiring. -/
  -- Porting note: -(n + 1) -> Int.negSucc
  intCast_negSucc_ofNat : ∀ n : ℕ, intCast (Int.negSucc n) = -natCast (n + 1 : ℕ)

/-- A graded version of `CommRing`. -/
/-
**DirectSum.GCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [AddCommMonoid ι] → [(i : ι) → AddCo
mmGroup (A i)] → Type (max u_1 u_2)
参数：A : ι → Type u_2；i : ι；A i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `CommRing`.
-/
class GCommRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends GRing A, GCommSemiring A

end Defs

/-
**DirectSum.of_eq_of_gradedMonoid_eq** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_eq_of_gradedMonoid_eq {A : ι -> Type*} [forall i : ι, AddCommMonoid (A 
i)] {i j : ι} {a : A i} {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b
) : DirectSum.of A i a = DirectSum.of A j b
参数：A i；h : GradedMonoid.mk i a = GradedMonoid.mk j b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_eq_of_sigma_eq`：single_eq_of_sigma_eq {i j} {xi : β i} {
xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) : DFinsupp.single i xi = DFinsupp.
single j xj
-/
theorem of_eq_of_gradedMonoid_eq {A : ι → Type*} [∀ i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
    {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b) :
    DirectSum.of A i a = DirectSum.of A j b :=
  DFinsupp.single_eq_of_sigma_eq h

variable (A : ι → Type*)

/-! ### Instances for `⨁ i, A i` -/


section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (⨁ i, A i) where one := DirectSum.of A 0 GradedMonoid.GOne.one
/-
**DirectSum.one_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：one_def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one := rfl

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp compHom)

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
/-
**DirectSum.gMulHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：gMulHom {i j} : A i ->+ A j ->+ A (i + j) where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.GNonUnitalNonAssocSemiring.mul_zero`：∀ {ι : Type u_1} {A : ι →
 Type u_2} {inst : Add ι} {inst_1 : (i : ι) → AddCommMonoid (A i)}   [self : Dir
ectSum.GNonUnitalNonAssocSemiring A…
· 使用定理 `DirectSum.GNonUnitalNonAssocSemiring.mul_add`：∀ {ι : Type u_1} {A : ι → 
Type u_2} {inst : Add ι} {inst_1 : (i : ι) → AddCommMonoid (A i)}   [self : Dire
ctSum.GNonUnitalNonAssocSemiring A…

--- 原说明 ---
The piecewise multiplication from the `Mul` instance, as a bundled homomorphism.
-/
def gMulHom {i j} : A i →+ A j →+ A (i + j) where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GNonUnitalNonAssocSemiring.mul_zero _
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GNonUnitalNonAssocSemiring.zero_mul a
  map_add' _ _ := AddMonoidHom.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

/-- The multiplication from the `Mul` instance, as a bundled homomorphism. -/
-- See note [non-reducible instance]
@[reducible]
/-
**DirectSum.mulHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：mulHom : (⨁ i, A i) ->+ (⨁ i, A i) ->+ ⨁ i, A i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulHom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun _ =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gMulHom A
/-
**DirectSum.instMul** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：instMul : Mul (⨁ i, A i) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (⨁ i, A i) where
  mul := fun a b => mulHom A a b
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalNonAssocSemiring (⨁ i, A i) where
  zero_mul := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero, AddMonoidHom.zero_apply]
  mul_zero := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero]
  left_distrib := fun _ _ _ => by simp only [Mul.mul, HMul.hMul, map_add]
  right_distrib := fun _ _ _ => by
    simp only [Mul.mul, HMul.hMul, map_add, AddMonoidHom.add_apply]

variable {A}
/-
**DirectSum.mulHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mulHom_apply (a b : ⨁ i, A i) : mulHom A a b = a * b
参数：a b : ⨁ i, A i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulHom_apply (a b : ⨁ i, A i) : mulHom A a b = a * b := rfl
/-
**DirectSum.mulHom_of_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mulHom_of_of {i j} (a : A i) (b : A j) : mulHom A (of A i a) (of A j b) = 
of A (i + j) (GradedMonoid.GMul.mul a b)
参数：a : A i；b : A j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
· 使用定理 `AddMonoidHom.compHom_apply_apply`：∀ {M : Type uM} {N : Type uN} {P : Typ
e uP} [inst : AddZeroClass M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMono
id P] (g : N →+ P) (hm…
· 使用定理 `DirectSum.gMulHom_apply_apply`：∀ {ι : Type u_1} (A : ι → Type u_2) [inst
 : Add ι] [inst_1 : (i : ι) → AddCommMonoid (A i)]   [inst_2 : DirectSum.GNonUni
talNonAssocSemiring…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulHom_of_of {i j} (a : A i) (b : A j) :
    mulHom A (of A i a) (of A j b) = of A (i + j) (GradedMonoid.GMul.mul a b) := by
  simp
/-
**DirectSum.of_mul_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of A j b = of _ (i + j) (
GradedMonoid.GMul.mul a b)
参数：a : A i；b : A j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.mulHom_of_of`：mulHom_of_of {i j} (a : A i) (b : A j) : mulHom 
A (of A i a) (of A j b) = of A (i + j) (GradedMonoid.GMul.mul a b)
-/
theorem of_mul_of {i j} (a : A i) (b : A j) :
    of A i a * of A j b = of _ (i + j) (GradedMonoid.GMul.mul a b) :=
  mulHom_of_of a b

end Mul

section Semiring

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

open AddMonoidHom (flipHom coe_comp compHom flip_apply)

private nonrec theorem one_mul (x : ⨁ i, A i) : 1 * x = x := by
  suffices mulHom A One.one = AddMonoidHom.id (⨁ i, A i) from DFunLike.congr_fun this x
  apply addHom_ext; intro i xi
  simp only [One.one]
  rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (one_mul <| GradedMonoid.mk i xi)

private nonrec theorem mul_one (x : ⨁ i, A i) : x * 1 = x := by
  suffices (mulHom A).flip One.one = AddMonoidHom.id (⨁ i, A i) from DFunLike.congr_fun this x
  apply addHom_ext; intro i xi
  simp only [One.one]
  rw [flip_apply, mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (mul_one <| GradedMonoid.mk i xi)

set_option backward.defeqAttrib.useBackward true in
/-
**DirectSum.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, AddMonoidHom.mulLeft₃_apply,
    AddMonoidHom.mulRight₃_apply]
  simp_rw [of_mul_of]
  exact of_eq_of_gradedMonoid_eq (_root_.mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)
/-
**DirectSum.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：instNatCast : NatCast (⨁ i, A i) where natCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast (⨁ i, A i) where
  natCast := fun n => of _ _ (GSemiring.natCast n)

/-- The `Semiring` structure derived from `GSemiring A`. -/
/-
**DirectSum.semiring** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：semiring : Semiring (⨁ i, A i) where one_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Semiring` structure derived from `GSemiring A`.
-/
instance semiring : Semiring (⨁ i, A i) where
  one_mul := private one_mul A
  mul_one := private mul_one A
  mul_assoc := private mul_assoc A
  toNatCast := instNatCast _
  natCast_zero := by simp only [NatCast.natCast, GSemiring.natCast_zero, map_zero]
  natCast_succ := fun n => by
    simp_rw [NatCast.natCast, GSemiring.natCast_succ]
    rw [map_add]
    rfl
/-
**DirectSum.ofPow** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：ofPow {i} (a : A i) (n : Nat) : of _ i a ^ n = of _ (n • i) (GradedMonoid.
GMonoid.gnpow _ a)
参数：a : A i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.of_eq_of_gradedMonoid_eq`：of_eq_of_gradedMonoid_eq {A : ι -> T
ype*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i} {b : A j} (h : Gra
dedMonoid.mk i a = Grade…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
-/
theorem ofPow {i} (a : A i) (n : ℕ) :
    of _ i a ^ n = of _ (n • i) (GradedMonoid.GMonoid.gnpow _ a) := by
  induction n with
  | zero => exact of_eq_of_gradedMonoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  | succ n n_ih =>
    rw [pow_succ, n_ih, of_mul_of]
    exact of_eq_of_gradedMonoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm
/-
**DirectSum.ofList_dProd** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：ofList_dProd {α} (l : List α) (fι : α -> ι) (fA : forall a, A (fι a)) : of
 A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA a)).prod
参数：l : List α；fι : α -> ι；fA : forall a, A (fι a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
-/
theorem ofList_dProd {α} (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA a)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.dProd_nil]; rfl
  | cons head tail =>
    rename_i ih
    simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← ih]
    rw [DirectSum.of_mul_of (fA head)]
    rfl
/-
**DirectSum.list_prod_ofFn_of_eq_dProd** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：list_prod_ofFn_of_eq_dProd (n : Nat) (fι : Fin n -> ι) (fA : forall a, A (
fι a)) : (List.ofFn fun a => of A (fι a) (fA a)).prod = of A _ ((List.finRange n
).dProd fι fA)
参数：n : Nat；fι : Fin n -> ι；fA : forall a, A (fι a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `DirectSum.ofList_dProd`：ofList_dProd {α} (l : List α) (fι : α -> ι) (fA 
: forall a, A (fι a)) : of A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA
 a)).prod
-/
theorem list_prod_ofFn_of_eq_dProd (n : ℕ) (fι : Fin n → ι) (fA : ∀ a, A (fι a)) :
    (List.ofFn fun a => of A (fι a) (fA a)).prod = of A _ ((List.finRange n).dProd fι fA) := by
  rw [List.ofFn_eq_map, ofList_dProd]

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.mul_eq_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mul_eq_dfinsuppSum [forall (i : ι) (x : A i), Decidable (x != 0)] (a a' : 
⨁ i, A i) : a * a' = a.sum fun _ ai => a'.sum fun _ aj => DirectSum.of _ _ Grade
dMonoid.GMul.mul ai aj
参数：i : ι；x : A i；x != 0；a a' : ⨁ i, A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.mulHom.eq_1`：∀ {ι : Type u_1} [inst : DecidableEq ι] (A : ι → 
Type u_2) [inst_1 : Add ι] [inst_2 : (i : ι) → AddCommMonoid (A i)]   [inst_3 : 
DirectSum.G…
· 使用定理 `DirectSum.toAddMonoid.eq_1`：∀ {ι : Type v} {β : ι → Type w} [inst : (i :
 ι) → AddCommMonoid (β i)] [inst_1 : DecidableEq ι] {γ : Type u₁}   [inst_2 : Ad
dCommMonoid γ] (…
· 使用定理 `DFinsupp.liftAddHom_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : AddCo
mmMonoid γ] (φ …
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `AddMonoidHom.dfinsuppSum_apply`：∀ {ι : Type u} {β : ι → Type v} [inst : 
DecidableEq ι] {R : Type u_1} {S : Type u_2} [inst_1 : (i : ι) → Zero (β i)]   [
inst_2 : (i : ι) → (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `AddMonoidHom.compHom_apply_apply`：∀ {M : Type uM} {N : Type uN} {P : Typ
e uP} [inst : AddZeroClass M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMono
id P] (g : N →+ P) (hm…
· 使用定理 `DirectSum.gMulHom_apply_apply`：∀ {ι : Type u_1} (A : ι → Type u_2) [inst
 : Add ι] [inst_1 : (i : ι) → AddCommMonoid (A i)]   [inst_2 : DirectSum.GNonUni
talNonAssocSemiring…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_eq_dfinsuppSum [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a'
      = a.sum fun _ ai => a'.sum fun _ aj => DirectSum.of _ _ <| GradedMonoid.GMul.mul ai aj := by
  change mulHom _ a a' = _
  -- Porting note: I have no idea how the proof from ml3 worked it used to be
  -- simpa only [mul_hom, to_add_monoid, dfinsupp.lift_add_hom_apply, dfinsupp.sum_add_hom_apply,
  -- add_monoid_hom.dfinsupp_sum_apply, flip_apply, add_monoid_hom.dfinsupp_sum_add_hom_apply],
  rw [mulHom, toAddMonoid, DFinsupp.liftAddHom_apply]
  dsimp only [DirectSum]
  rw [DFinsupp.sumAddHom_apply, AddMonoidHom.dfinsuppSum_apply]
  apply congrArg _
  funext x
  simp [AddMonoidHom.dfinsuppSum_apply, DFinsupp.sumAddHom_apply, DirectSum.toAddMonoid]

set_option backward.isDefEq.respectTransparency false in
/-- A heavily unfolded version of the definition of multiplication -/
/-
**DirectSum.mul_eq_sum_support_ghas_mul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mul_eq_sum_support_ghas_mul [forall (i : ι) (x : A i), Decidable (x != 0)]
 (a a' : ⨁ i, A i) : a * a' = ∑ ij in DFinsupp.support a ×ˢ DFinsupp.support a',
 DirectSum.of _ _ (GradedMonoid.GMul.mul (a ij.fst) (a' ij.snd))
参数：i : ι；x : A i；x != 0；a a' : ⨁ i, A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.mul_eq_dfinsuppSum`：mul_eq_dfinsuppSum [forall (i : ι) (x : A 
i), Decidable (x != 0)] (a a' : ⨁ i, A i) : a * a' = a.sum fun _ ai => a'.sum fu
n _ aj => DirectSu…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A heavily unfolded version of the definition of multiplication
-/
theorem mul_eq_sum_support_ghas_mul [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a' =
      ∑ ij ∈ DFinsupp.support a ×ˢ DFinsupp.support a',
        DirectSum.of _ _ (GradedMonoid.GMul.mul (a ij.fst) (a' ij.snd)) := by
  simp only [mul_eq_dfinsuppSum, DFinsupp.sum, Finset.sum_product]

end Semiring

section CommSemiring

variable [∀ i, AddCommMonoid (A i)] [AddCommMonoid ι] [GCommSemiring A]

/-
**DirectSum.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
  suffices mulHom A = (mulHom A).flip by
    rw [← mulHom_apply, this, AddMonoidHom.flip_apply, mulHom_apply]
  apply addHom_ext; intro ai ax; apply addHom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply, mulHom_of_of, mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (GCommSemiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)

/-- The `CommSemiring` structure derived from `GCommSemiring A`. -/
/-
**DirectSum.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：commSemiring : CommSemiring (⨁ i, A i) where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommSemiring` structure derived from `GCommSemiring A`.
-/
instance commSemiring : CommSemiring (⨁ i, A i) where
  mul_comm := private mul_comm A

end CommSemiring

section NonUnitalNonAssocRing

variable [∀ i, AddCommGroup (A i)] [Add ι] [GNonUnitalNonAssocSemiring A]

/-- The `Ring` derived from `GSemiring A`. -/
/-
**DirectSum.nonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} →   [DecidableEq ι] →     (A : ι → Type u_2) →       [inst 
: (i : ι) → AddCommGroup (A i)] →         [inst_1 : Add ι] → [DirectSum.GNonUnit
alNonAssocSemiring A] → NonUnitalNonAssocRing (DirectSum ι fun i => A i)
参数：A : ι → Type u_2；i : ι；A i；DirectSum ι fun i => A i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Ring` derived from `GSemiring A`.
-/
instance nonAssocRing : NonUnitalNonAssocRing (⨁ i, A i) where

end NonUnitalNonAssocRing

section Ring

variable [∀ i, AddCommGroup (A i)] [AddMonoid ι] [GRing A]

-- Porting note: overspecified fields in ml4
/-- The `Ring` derived from `GSemiring A`. -/
/-
**DirectSum.ring** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：ring : Ring (⨁ i, A i) where toIntCast.intCast z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Ring` derived from `GSemiring A`.
-/
instance ring : Ring (⨁ i, A i) where
  toIntCast.intCast z := of A 0 <| (GRing.intCast z)
  intCast_ofNat _ := congrArg (of A 0) <| GRing.intCast_ofNat _
  intCast_negSucc _ :=
    (congrArg (of A 0) <| GRing.intCast_negSucc_ofNat _).trans <| map_neg _ _

end Ring

section CommRing

variable [∀ i, AddCommGroup (A i)] [AddCommMonoid ι] [GCommRing A]

/-- The `CommRing` derived from `GCommSemiring A`. -/
/-
**DirectSum.commRing** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} →   [DecidableEq ι] →     (A : ι → Type u_2) →       [inst 
: (i : ι) → AddCommGroup (A i)] →         [inst_1 : AddCommMonoid ι] → [DirectSu
m.GCommRing A] → CommRing (DirectSum ι fun i => A i)
参数：A : ι → Type u_2；i : ι；A i；DirectSum ι fun i => A i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommRing` derived from `GCommSemiring A`.
-/
instance commRing : CommRing (⨁ i, A i) where

end CommRing

/-! ### Instances for `A 0`

The various `G*` instances are enough to promote the `AddCommMonoid (A 0)` structure to various
types of multiplicative structure.

Implementation detail: Note that these instances on `A 0` have very general discrimination
tree keys (e.g. `DirectSum.instRingOfNat` has discrimination tree key `Ring _` and often
sends typeclass inference on a wild goose chase with any goal of the form `Ring (F X)`),
so we scope these instances to the `DirectSum` namespace.

-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

@[simp]
/-
**DirectSum.of_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_zero_one : of _ 0 (1 : A 0) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl

end One

section Mul

variable [AddZeroClass ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

@[simp]
/-
**DirectSum.of_zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ 
b
参数：a : A 0；b : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.of_eq_of_gradedMonoid_eq`：of_eq_of_gradedMonoid_eq {A : ι -> T
ype*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i} {b : A j} (h : Gra
dedMonoid.mk i a = Grade…
· 使用定理 `GradedMonoid.mk_zero_smul`：mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (
a • b) = mk _ a * mk _ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
-/
theorem of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
  (of_eq_of_gradedMonoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]
/-
**DirectSum.of_zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b
参数：a b : A 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.of_zero_smul`：of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a
 • b) = of _ _ a * of _ _ b
-/
theorem of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b :=
  of_zero_smul A a b

/-- The `NonUnitalNonAssocSemiring` structure on the grade zero part
of a `GNonUnitalNonAssocSemiring`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NonUnitalNonAssocSemiring` structure on the grade zero part
of a `GNonUnitalNonAssocSemiring`.
-/
scoped instance (priority := 900) :
    NonUnitalNonAssocSemiring (A 0) :=
  Function.Injective.nonUnitalNonAssocSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (map_nsmul _)

/-- The `SMulWithZero` structure on the grade zero part
of a `GNonUnitalNonAssocSemiring`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SMulWithZero` structure on the grade zero part
of a `GNonUnitalNonAssocSemiring`.
-/
scoped instance (i : ι) : SMulWithZero (A 0) (A i) := by
  letI := SMulWithZero.compHom (⨁ i, A i) (of A 0).toZeroHom
  exact Function.Injective.smulWithZero (of A i).toZeroHom DFinsupp.single_injective
    (of_zero_smul A)

end Mul

section Semiring

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

@[simp]
/-
**DirectSum.of_zero_pow** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_zero_pow (a : A 0) : forall n : Nat, of A 0 (a ^ n) = of A 0 a ^ n | 0 
=> by rw [pow_zero, pow_zero, DirectSum.of_zero_one] -- Porting note: Lean doesn
't think this terminates if we only use `of_zero_pow` alone | n + 1 => by rw [po
w_succ, pow_succ, of_zero_mul, of_zero_pow _ n]  /-- The `NatCast` instance on `
A 0`, given `GSemiring A`. -/ scoped instance (priority
参数：a : A 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_zero_pow (a : A 0) : ∀ n : ℕ, of A 0 (a ^ n) = of A 0 a ^ n
  | 0 => by rw [pow_zero, pow_zero, DirectSum.of_zero_one]
  -- Porting note: Lean doesn't think this terminates if we only use `of_zero_pow` alone
  | n + 1 => by rw [pow_succ, pow_succ, of_zero_mul, of_zero_pow _ n]

/-- The `NatCast` instance on `A 0`, given `GSemiring A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NatCast` instance on `A 0`, given `GSemiring A`.
-/
scoped instance (priority := 900) : NatCast (A 0) :=
  ⟨GSemiring.natCast⟩


-- TODO: These could be replaced by the general lemmas for `AddMonoidHomClass` (`map_natCast'` and
-- `map_ofNat'`) if those were marked `@[simp low]`.
@[simp]
/-
**DirectSum.of_natCast** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_natCast (n : Nat) : of A 0 n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_natCast (n : ℕ) : of A 0 n = n :=
  rfl

@[simp]
/-
**DirectSum.of_zero_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_zero_ofNat (n : Nat) [n.AtLeastTwo] : of A 0 ofNat(n) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.of_natCast`：of_natCast (n : Nat) : of A 0 n = n
-/
theorem of_zero_ofNat (n : ℕ) [n.AtLeastTwo] : of A 0 ofNat(n) = ofNat(n) :=
  of_natCast A n

/-- The `Semiring` structure derived from `GSemiring A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Semiring` structure derived from `GSemiring A`.
-/
scoped instance (priority := 900) : Semiring (A 0) :=
  Function.Injective.semiring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (fun _ _ ↦ (of A 0).map_nsmul _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)

/-- `of A 0` is a `RingHom`, using the `DirectSum.GradeZero.semiring` structure. -/
/-
**DirectSum.ofZeroRingHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：ofZeroRingHom : A 0 ->+* ⨁ i, A i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`of A 0` is a `RingHom`, using the `DirectSum.GradeZero.semiring` structure.
-/
def ofZeroRingHom : A 0 →+* ⨁ i, A i :=
  { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }

/-- Each grade `A i` derives an `A 0`-module structure from `GSemiring A`. Note that this results
in an overall `Module (A 0) (⨁ i, A i)` structure via `DirectSum.module`.
-/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each grade `A i` derives an `A 0`-module structure from `GSemiring A`. Note that
 this results
in an overall `Module (A 0) (⨁ i, A i)` structure via `DirectSum.module`.
-/
scoped instance {i} : Module (A 0) (A i) :=
  letI := Module.compHom (⨁ i, A i) (ofZeroRingHom A)
  DFinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a

end Semiring

section CommSemiring

variable [∀ i, AddCommMonoid (A i)] [AddCommMonoid ι] [GCommSemiring A]

/-- The `CommSemiring` structure derived from `GCommSemiring A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommSemiring` structure derived from `GCommSemiring A`.
-/
scoped instance (priority := 900) : CommSemiring (A 0) :=
  Function.Injective.commSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of_zero_one A) (of A 0).map_add (of_zero_mul A) (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)

end CommSemiring

section Ring

variable [∀ i, AddCommGroup (A i)] [AddZeroClass ι] [GNonUnitalNonAssocSemiring A]

/-- The `NonUnitalNonAssocRing` derived from `GNonUnitalNonAssocSemiring A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NonUnitalNonAssocRing` derived from `GNonUnitalNonAssocSemiring A`.
-/
scoped instance (priority := 900) : NonUnitalNonAssocRing (A 0) :=
  Function.Injective.nonUnitalNonAssocRing (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ ↦ map_zsmul _ _ _)

end Ring

section Ring

variable [∀ i, AddCommGroup (A i)] [AddMonoid ι] [GRing A]

/-- The `IntCast` instance on `A 0`, given `GRing A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `IntCast` instance on `A 0`, given `GRing A`.
-/
scoped instance (priority := 900) : IntCast (A 0) :=
  ⟨GRing.intCast⟩

@[simp]
/-
**DirectSum.of_intCast** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_intCast (n : Int) : of A 0 n = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_intCast (n : ℤ) : of A 0 n = n := by
  rfl

/-- The `Ring` derived from `GSemiring A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Ring` derived from `GSemiring A`.
-/
scoped instance (priority := 900) : Ring (A 0) :=
  Function.Injective.ring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ ↦ map_zsmul _ _ _) (fun _ _ => of_zero_pow _ _ _) (of_natCast A) (of_intCast A)

end Ring

section CommRing

variable [∀ i, AddCommGroup (A i)] [AddCommMonoid ι] [GCommRing A]

/-- The `CommRing` derived from `GCommSemiring A`. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommRing` derived from `GCommSemiring A`.
-/
scoped instance (priority := 900) : CommRing (A 0) :=
  Function.Injective.commRing (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ ↦ map_nsmul _ _ _)
    (fun _ _ ↦ map_zsmul _ _ _) (fun _ _ => of_zero_pow _ _ _) (of_natCast A) (of_intCast A)

end CommRing

end GradeZero

section ToSemiring

variable {R : Type*} [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A] [Semiring R]
variable {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
/-
**DirectSum.ringHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：ringHom_ext' ⦃F G : (⨁ i, A i) ->+* R⦄ (h : forall i, (↑F : _ ->+ R).comp 
(of A i) = (↑G : _ ->+ R).comp (of A i)) : F = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.coe_addMonoidHom_injective`：coe_addMonoidHom_injective : Injecti
ve (fun f : α ->+* β => (f : α ->+ β))
· 使用定理 `DirectSum.addHom_ext'`：addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (
⨁ i, β i) ->+ γ⦄ (H : forall i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g

--- 原说明 ---
If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas].
-/
theorem ringHom_ext' ⦃F G : (⨁ i, A i) →+* R⦄
    (h : ∀ i, (↑F : _ →+ R).comp (of A i) = (↑G : _ →+ R).comp (of A i)) : F = G :=
  RingHom.coe_addMonoidHom_injective <| DirectSum.addHom_ext' h

/-- Two `RingHom`s out of a direct sum are equal if they agree on the generators. -/
/-
**DirectSum.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：ringHom_ext ⦃f g : (⨁ i, A i) ->+* R⦄ (h : forall i x, f (of A i x) = g (o
f A i x)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.ringHom_ext'`：ringHom_ext' ⦃F G : (⨁ i, A i) ->+* R⦄ (h : fora
ll i, (↑F : _ ->+ R).comp (of A i) = (↑G : _ ->+ R).comp (of A i)) : F = G
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
Two `RingHom`s out of a direct sum are equal if they agree on the generators.
-/
theorem ringHom_ext ⦃f g : (⨁ i, A i) →+* R⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  ringHom_ext' fun i => AddMonoidHom.ext <| h i

/-- A family of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mul`
describes a `RingHom`s on `⨁ i, A i`. This is a stronger version of `DirectSum.toMonoid`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the family of
coercions such as `AddSubmonoid.subtype (A i)`, and the `[GSemiring A]` structure originates from
`DirectSum.gsemiring.ofAddSubmonoids`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
/-
**DirectSum.toSemiring** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：toSemiring (f : forall i, A i ->+ R) (hone : f _ GradedMonoid.GOne.one = 1
) (hmul : forall {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) 
= f _ ai * f _ aj) : (⨁ i, A i) ->+* R
参数：f : forall i, A i ->+ R；hone : f _ GradedMonoid.GOne.one = 1；hmul : forall {i
 j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mu
l`
describes a `RingHom`s on `⨁ i, A i`. This is a stronger version of `DirectSum.t
oMonoid`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the
 family of
coercions such as `AddSubmonoid.subtype (A i)`, and the `[GSemiring A]` structur
e originates from
`DirectSum.gsemiring.ofAddSubmonoids`, in which case the proofs about `GOne` and
 `GMul`
can be discharged by `rfl`.
-/
def toSemiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) →+* R :=
  { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
      refine DirectSum.addHom_ext' (fun yi ↦ AddMonoidHom.ext (fun yv ↦ ?_))
      change
        toAddMonoid f (of A xi xv * of A yi yv) =
          toAddMonoid f (of A xi xv) * toAddMonoid f (of A yi yv)
      simp_rw [of_mul_of, toAddMonoid_of]
      exact hmul _ _ }
/-
**DirectSum.toSemiring_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toSemiring_of (f : forall i, A i ->+ R) (hone hmul) (i : ι) (x : A i) : to
Semiring f hone hmul (of _ i x) = f _ x
参数：f : forall i, A i ->+ R；hone hmul；i : ι；x : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
-/
theorem toSemiring_of (f : ∀ i, A i →+ R) (hone hmul) (i : ι) (x : A i) :
    toSemiring f hone hmul (of _ i x) = f _ x :=
  toAddMonoid_of f i x

@[simp]
/-
**DirectSum.toSemiring_coe_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toSemiring_coe_addMonoidHom (f : forall i, A i ->+ R) (hone hmul) : (toSem
iring f hone hmul : (⨁ i, A i) ->+ R) = toAddMonoid f
参数：f : forall i, A i ->+ R；hone hmul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem toSemiring_coe_addMonoidHom (f : ∀ i, A i →+ R) (hone hmul) :
    (toSemiring f hone hmul : (⨁ i, A i) →+ R) = toAddMonoid f :=
  rfl

/-- Families of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mul`
are isomorphic to `RingHom`s on `⨁ i, A i`. This is a stronger version of `DFinsupp.liftAddHom`.
-/
@[simps]
/-
**DirectSum.liftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：liftRingHom : { f : forall {i}, A i ->+ R // f GradedMonoid.GOne.one = 1 ∧
 forall {i j} (ai : A i) (aj : A j), f (GradedMonoid.GMul.mul ai aj) = f ai * f 
aj } ≃ ((⨁ i, A i) ->+* R) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Families of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mu
l`
are isomorphic to `RingHom`s on `⨁ i, A i`. This is a stronger version of `DFins
upp.liftAddHom`.
-/
def liftRingHom :
    { f : ∀ {i}, A i →+ R //
        f GradedMonoid.GOne.one = 1 ∧
          ∀ {i j} (ai : A i) (aj : A j), f (GradedMonoid.GMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) →+* R) where
  toFun f := toSemiring (fun _ => f.1) f.2.1 f.2.2
  invFun F :=
    ⟨by intro i; exact (F : (⨁ i, A i) →+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply]
      rw [← F.map_one]
      rfl,
      by
      intro i j ai aj
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe]
      rw [← F.map_mul (of A i ai), of_mul_of ai]⟩
  left_inv f := by
    ext xi xv
    exact toAddMonoid_of (fun _ => f.1) xi xv
  right_inv F := by
    apply RingHom.coe_addMonoidHom_injective
    refine DirectSum.addHom_ext' (fun xi ↦ AddMonoidHom.ext (fun xv ↦ ?_))
    simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, toSemiring_coe_addMonoidHom]

end ToSemiring

end DirectSum

/-! ### Concrete instances -/


section Uniform

variable (ι)

/-- A direct sum of copies of a `NonUnitalNonAssocSemiring` inherits the multiplication structure.
-/
/-
**NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring** 是 Mathlib 中的一个
实例，位于命名空间 ``。
形式化陈述：NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring {R : Type*} 
[AddMonoid ι] [NonUnitalNonAssocSemiring R] : DirectSum.GNonUnitalNonAssocSemiri
ng fun _ : ι => R where mul_zero
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocSemiring.mul_zero`：∀ {α : Type u} [self : NonUnitalNonA
ssocSemiring α] (a : α), a * 0 = 0
· 使用定理 `NonUnitalNonAssocSemiring.zero_mul`：∀ {α : Type u} [self : NonUnitalNonA
ssocSemiring α] (a : α), 0 * a = 0

--- 原说明 ---
A direct sum of copies of a `NonUnitalNonAssocSemiring` inherits the multiplicat
ion structure.
-/
instance NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring {R : Type*} [AddMonoid ι]
    [NonUnitalNonAssocSemiring R] : DirectSum.GNonUnitalNonAssocSemiring fun _ : ι => R where
  mul_zero := mul_zero
  zero_mul := zero_mul
  mul_add := mul_add
  add_mul := add_mul

/-- A direct sum of copies of a `Semiring` inherits the multiplication structure. -/
/-
**Semiring.directSumGSemiring** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semiring.directSumGSemiring {R : Type*} [AddMonoid ι] [Semiring R] : Direc
tSum.GSemiring fun _ : ι => R where natCast n
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direct sum of copies of a `Semiring` inherits the multiplication structure.
-/
instance Semiring.directSumGSemiring {R : Type*} [AddMonoid ι] [Semiring R] :
    DirectSum.GSemiring fun _ : ι => R where
  natCast n := n
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

/-- A direct sum of copies of a `Ring` inherits the multiplication structure. -/
/-
**Ring.directSumGRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ring.directSumGRing {R : Type*} [AddMonoid ι] [Ring R] : DirectSum.GRing f
un _ : ι => R where intCast z
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direct sum of copies of a `Ring` inherits the multiplication structure.
-/
instance Ring.directSumGRing {R : Type*} [AddMonoid ι] [Ring R] :
    DirectSum.GRing fun _ : ι => R where
  intCast z := z
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc

open DirectSum

-- To check `Mul.gmul_mul` matches
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {R : Type*} [AddMonoid ι] [Semiring R] (i j : ι) (a b : R) :
    (DirectSum.of _ i a * DirectSum.of _ j b : ⨁ _, R) = DirectSum.of _ (i + j) (a * b) := by
  rw [DirectSum.of_mul_of, Mul.gMul_mul]

/-- A direct sum of copies of a `CommSemiring` inherits the commutative multiplication structure. -/
/-
**CommSemiring.directSumGCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `CommSemiring`。
形式化陈述：(ι : Type u_1) →   {R : Type u_2} → [inst : AddCommMonoid ι] → [inst_1 : C
ommSemiring R] → DirectSum.GCommSemiring fun x => R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direct sum of copies of a `CommSemiring` inherits the commutative multiplicati
on structure.
-/
instance CommSemiring.directSumGCommSemiring {R : Type*} [AddCommMonoid ι] [CommSemiring R] :
    DirectSum.GCommSemiring fun _ : ι => R where

/-- A direct sum of copies of a `CommRing` inherits the commutative multiplication structure. -/
/-
**CommRing.directSumGCommRing** 是 Mathlib 中的一个定义，位于命名空间 `CommRing`。
形式化陈述：(ι : Type u_1) → {R : Type u_2} → [inst : AddCommMonoid ι] → [inst_1 : Com
mRing R] → DirectSum.GCommRing fun x => R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direct sum of copies of a `CommRing` inherits the commutative multiplication s
tructure.
-/
instance CommRing.directSumGCommRing {R : Type*} [AddCommMonoid ι] [CommRing R] :
    DirectSum.GCommRing fun _ : ι => R where

end Uniform

