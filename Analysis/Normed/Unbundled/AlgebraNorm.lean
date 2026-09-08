/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Seminorm

/-!
# Algebra norms

We define algebra norms and multiplicative algebra norms.

## Main Definitions
* `AlgebraNorm` : an algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with
  the action of `R`.
* `MulAlgebraNorm` : a multiplicative algebra norm on an `R`-algebra `S` is a multiplicative
  ring norm on `S` compatible with the action of `R`.

## Tags

norm, algebra norm
-/

@[expose] public section

/-- An algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with the
action of `R`. -/
/-
**AlgebraNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [inst : SeminormedCommRing R] → (S : Type u_2) → [inst_1 
: Ring S] → [Algebra R S] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with the
action of `R`.
-/
structure AlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S] extends
  RingNorm S, Seminorm R S

attribute [nolint docBlame] AlgebraNorm.toSeminorm AlgebraNorm.toRingNorm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Type*) [NormedField K] : Inhabited (AlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      mul_le'   := norm_mul_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `AlgebraNormClass F R S` states that `F` is a type of `R`-algebra norms on the ring `S`.
You should extend this class when you extend `AlgebraNorm`. -/
/-
**AlgebraNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     [inst : SeminormedCommR
ing R] →       (S : outParam (Type u_3)) → [inst_1 : Ring S] → [Algebra R S] → [
FunLike F S ℝ] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgebraNormClass F R S` states that `F` is a type of `R`-algebra norms on the r
ing `S`.
You should extend this class when you extend `AlgebraNorm`.
-/
class AlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S ℝ] : Prop
    extends RingNormClass F S ℝ, SeminormClass F R S

namespace AlgebraNorm

variable {R : Type*} [SeminormedCommRing R] {S : Type*} [Ring S] [Algebra R S] {f : AlgebraNorm R S}

/-- The ring seminorm underlying an algebra norm. -/
/-
**AlgebraNorm.toRingSeminorm'** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraNorm`。
形式化陈述：toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S
参数：f : AlgebraNorm R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring seminorm underlying an algebra norm.
-/
def toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S :=
  f.toRingNorm.toRingSeminorm
/-
**AlgebraNorm.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (AlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, RingSeminorm.toFun_eq_coe] at h
    cases f; cases f'; congr
    simp only at h
    ext s
    erw [h]
    rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**AlgebraNorm.algebraNormClass** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraNorm`。
形式化陈述：algebraNormClass : AlgebraNormClass (AlgebraNorm R S) R S where map_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `RingSeminorm.mul_le'`：∀ {R : Type u_2} [inst : NonUnitalNonAssocRing R] 
(self : RingSeminorm R) (x y : R),   self.toFun (x * y) ≤ self.toFun x * self.to
Fun y
· 使用定理 `RingNorm.eq_zero_of_map_eq_zero'`：∀ {R : Type u_2} [inst : NonUnitalNonA
ssocRing R] (self : RingNorm R) (x : R), self.toFun x = 0 → x = 0
· 使用定理 `AlgebraNorm.smul'`：∀ {R : Type u_1} [inst : SeminormedCommRing R] {S : T
ype u_2} [inst_1 : Ring S] [inst_2 : Algebra R S]   (self : AlgebraNorm R S) (a 
: R) (x…
-/
instance algebraNormClass : AlgebraNormClass (AlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_mul_le_mul f  := f.mul_le'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'
/-
**AlgebraNorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraNorm`。
形式化陈述：toFun_eq_coe (p : AlgebraNorm R S) : p.toFun = p
参数：p : AlgebraNorm R S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (p : AlgebraNorm R S) : p.toFun = p := rfl

@[ext]
/-
**AlgebraNorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraNorm`。
形式化陈述：ext {p q : AlgebraNorm R S} : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : AlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
/-
**AlgebraNorm.extends_norm'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraNorm`。
形式化陈述：extends_norm' (hf1 : f 1 = 1) (a : R) : f (a • (1 : S)) = ‖a‖
参数：hf1 : f 1 = 1；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AlgebraNorm.smul'`：∀ {R : Type u_1} [inst : SeminormedCommRing R] {S : T
ype u_2} [inst_1 : Ring S] [inst_2 : Algebra R S]   (self : AlgebraNorm R S) (a 
: R) (x…

--- 原说明 ---
An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`.
-/
theorem extends_norm' (hf1 : f 1 = 1) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← hf1]; exact f.smul' _ _

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
/-
**AlgebraNorm.extends_norm** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraNorm`。
形式化陈述：extends_norm (hf1 : f 1 = 1) (a : R) : f (algebraMap R S a) = ‖a‖
参数：hf1 : f 1 = 1；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `AlgebraNorm.extends_norm'`：extends_norm' (hf1 : f 1 = 1) (a : R) : f (a 
• (1 : S)) = ‖a‖

--- 原说明 ---
An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`.
-/
theorem extends_norm (hf1 : f 1 = 1) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' hf1 _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The restriction of an algebra norm to a subalgebra. -/
/-
**AlgebraNorm.restriction** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraNorm`。
形式化陈述：restriction (A : Subalgebra R S) (f : AlgebraNorm R S) : AlgebraNorm R A w
here toFun x
参数：A : Subalgebra R S；f : AlgebraNorm R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an algebra norm to a subalgebra.
-/
def restriction (A : Subalgebra R S) (f : AlgebraNorm R S) : AlgebraNorm R A where
  toFun x     := f x.val
  map_zero'   := map_zero f
  add_le' x y := map_add_le_add _ _ _
  neg' x      := map_neg_eq_map _ _
  mul_le' x y := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' x hx := by
    rw [← ZeroMemClass.coe_eq_zero]; exact eq_zero_of_map_eq_zero f hx
  smul' r x := map_smul_eq_mul _ _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The restriction of an algebra norm in a scalar tower. -/
/-
**AlgebraNorm.isScalarTower_restriction** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraNorm`。
形式化陈述：isScalarTower_restriction {A : Type*} [CommRing A] [Algebra R A] [Algebra 
A S] [IsScalarTower R A S] (hinj : Function.Injective (algebraMap A S)) (f : Alg
ebraNorm R S) : AlgebraNorm R A where toFun x
参数：hinj : Function.Injective (algebraMap A S)；f : AlgebraNorm R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an algebra norm in a scalar tower.
-/
def isScalarTower_restriction {A : Type*} [CommRing A] [Algebra R A] [Algebra A S]
    [IsScalarTower R A S] (hinj : Function.Injective (algebraMap A S)) (f : AlgebraNorm R S) :
    AlgebraNorm R A where
  toFun x     := f (algebraMap A S x)
  map_zero'   := by simp only [map_zero]
  add_le' x y := by simp only [map_add, map_add_le_add]
  neg' x      := by simp only [map_neg, map_neg_eq_map]
  mul_le' x y := by simp only [map_mul, map_mul_le_mul]
  eq_zero_of_map_eq_zero' x hx := by
    rw [← map_eq_zero_iff (algebraMap A S) hinj]
    exact eq_zero_of_map_eq_zero f hx
  smul' r x := by
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    simp only [← smul_eq_mul, algebraMap_smul, map_smul_eq_mul]

end AlgebraNorm

/-- A multiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative ring norm on `S`
  compatible with the action of `R`. -/
/-
**MulAlgebraNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [inst : SeminormedCommRing R] → (S : Type u_2) → [inst_1 
: Ring S] → [Algebra R S] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative rin
g norm on `S`
  compatible with the action of `R`.
-/
structure MulAlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S]
  extends MulRingNorm S, Seminorm R S

attribute [nolint docBlame] MulAlgebraNorm.toSeminorm MulAlgebraNorm.toMulRingNorm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Type*) [NormedField K] : Inhabited (MulAlgebraNorm K K) :=
  ⟨{  toFun     := norm
      map_zero' := norm_zero
      add_le'   := norm_add_le
      neg'      := norm_neg
      smul'     := norm_mul
      map_one'  := norm_one
      map_mul'  := norm_mul
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero.mp }⟩

/-- `MulAlgebraNormClass F R S` states that `F` is a type of multiplicative `R`-algebra norms on
the ring `S`. You should extend this class when you extend `MulAlgebraNorm`. -/
/-
**MulAlgebraNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     [inst : SeminormedCommR
ing R] →       (S : outParam (Type u_3)) → [inst_1 : Ring S] → [Algebra R S] → [
FunLike F S ℝ] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulAlgebraNormClass F R S` states that `F` is a type of multiplicative `R`-alge
bra norms on
the ring `S`. You should extend this class when you extend `MulAlgebraNorm`.
-/
class MulAlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S ℝ] : Prop
    extends MulRingNormClass F S ℝ, SeminormClass F R S

namespace MulAlgebraNorm

variable {R S : outParam <| Type*} [SeminormedCommRing R] [Ring S] [Algebra R S]
  {f : AlgebraNorm R S}

/-
**MulAlgebraNorm.** 是 Mathlib 中的一个实例，位于命名空间 `MulAlgebraNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (MulAlgebraNorm R S) S ℝ where
  coe f := f.toFun
  coe_injective f f' h := by
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, DFunLike.coe_fn_eq] at h
    obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := f'; congr

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**MulAlgebraNorm.mulAlgebraNormClass** 是 Mathlib 中的一个实例，位于命名空间 `MulAlgebraNorm`。
形式化陈述：mulAlgebraNormClass : MulAlgebraNormClass (MulAlgebraNorm R S) R S where m
ap_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `MulRingSeminorm.map_mul'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R) (x y : R),   self.toFun (x * y) = self.toFun x * self.toFu
n y
· 使用定理 `MulRingSeminorm.map_one'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R), self.toFun 1 = 1
· 使用定理 `MulRingNorm.eq_zero_of_map_eq_zero'`：∀ {R : Type u_2} [inst : NonAssocRi
ng R] (self : MulRingNorm R) (x : R), self.toFun x = 0 → x = 0
· 使用定理 `MulAlgebraNorm.smul'`：∀ {R : Type u_1} [inst : SeminormedCommRing R] {S 
: Type u_2} [inst_1 : Ring S] [inst_2 : Algebra R S]   (self : MulAlgebraNorm R 
S) (a : R)…
-/
instance mulAlgebraNormClass : MulAlgebraNormClass (MulAlgebraNorm R S) R S where
  map_zero f        := f.map_zero'
  map_add_le_add f  := f.add_le'
  map_one f         := f.map_one'
  map_mul f         := f.map_mul'
  map_neg_eq_map f  := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
  map_smul_eq_mul f := f.smul'
/-
**MulAlgebraNorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulAlgebraNorm`。
形式化陈述：toFun_eq_coe (p : MulAlgebraNorm R S) : p.toFun = p
参数：p : MulAlgebraNorm R S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (p : MulAlgebraNorm R S) : p.toFun = p := rfl

@[ext]
/-
**MulAlgebraNorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulAlgebraNorm`。
形式化陈述：ext {p q : MulAlgebraNorm R S} : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : MulAlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
/-
**MulAlgebraNorm.extends_norm'** 是 Mathlib 中的一个定理，位于命名空间 `MulAlgebraNorm`。
形式化陈述：extends_norm' (f : MulAlgebraNorm R S) (a : R) : f (a • (1 : S)) = ‖a‖
参数：f : MulAlgebraNorm R S；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulRingSeminorm.map_one'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R), self.toFun 1 = 1
· 使用定理 `MulAlgebraNorm.smul'`：∀ {R : Type u_1} [inst : SeminormedCommRing R] {S 
: Type u_2} [inst_1 : Ring S] [inst_2 : Algebra R S]   (self : MulAlgebraNorm R 
S) (a : R)…
· 使用定理 `MulAlgebraNorm.toFun_eq_coe`：toFun_eq_coe (p : MulAlgebraNorm R S) : p.t
oFun = p

--- 原说明 ---
A multiplicative `R`-algebra norm extends the norm on `R`.
-/
theorem extends_norm' (f : MulAlgebraNorm R S) (a : R) : f (a • (1 : S)) = ‖a‖ := by
  rw [← mul_one ‖a‖, ← f.map_one', ← f.smul', toFun_eq_coe]

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
/-
**MulAlgebraNorm.extends_norm** 是 Mathlib 中的一个定理，位于命名空间 `MulAlgebraNorm`。
形式化陈述：extends_norm (f : MulAlgebraNorm R S) (a : R) : f (algebraMap R S a) = ‖a‖
参数：f : MulAlgebraNorm R S；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `MulAlgebraNorm.extends_norm'`：extends_norm' (f : MulAlgebraNorm R S) (a 
: R) : f (a • (1 : S)) = ‖a‖

--- 原说明 ---
A multiplicative `R`-algebra norm extends the norm on `R`.
-/
theorem extends_norm (f : MulAlgebraNorm R S) (a : R) : f (algebraMap R S a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one]; exact extends_norm' _ _

/-- The algebra norm underlying an multiplicative algebra norm. -/
/-
**MulAlgebraNorm.toAlgebraNorm** 是 Mathlib 中的一个定义，位于命名空间 `MulAlgebraNorm`。
形式化陈述：toAlgebraNorm (f : MulAlgebraNorm R S) : AlgebraNorm R S where __
参数：f : MulAlgebraNorm R S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAlgebraNorm.smul'`：∀ {R : Type u_1} [inst : SeminormedCommRing R] {S 
: Type u_2} [inst_1 : Ring S] [inst_2 : Algebra R S]   (self : MulAlgebraNorm R 
S) (a : R)…

--- 原说明 ---
The algebra norm underlying an multiplicative algebra norm.
-/
def toAlgebraNorm (f : MulAlgebraNorm R S) : AlgebraNorm R S where
  __ := f
  mul_le' _ _ := (f.map_mul' _ _).le
/-
**MulAlgebraNorm.instCoeAlgebraNorm** 是 Mathlib 中的一个实例，位于命名空间 `MulAlgebraNorm`。
形式化陈述：instCoeAlgebraNorm : Coe (MulAlgebraNorm R S) (AlgebraNorm R S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeAlgebraNorm : Coe (MulAlgebraNorm R S) (AlgebraNorm R S) := ⟨toAlgebraNorm⟩

@[simp]
/-
**MulAlgebraNorm.coe_AlgebraNorm** 是 Mathlib 中的一个引理，位于命名空间 `MulAlgebraNorm`。
形式化陈述：coe_AlgebraNorm (f : MulAlgebraNorm R S) : ⇑(f : AlgebraNorm R S) = ⇑f
参数：f : MulAlgebraNorm R S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_AlgebraNorm (f : MulAlgebraNorm R S) : ⇑(f : AlgebraNorm R S) = ⇑f := rfl

end MulAlgebraNorm

namespace NormedAlgebra

variable (K L : Type*) [NormedField K] [NormedField L] [NormedAlgebra K L]

/-- Given a normed field extension `L / K`, the norm on `L` is a multiplicative `K`-algebra norm. -/
/-
**NormedAlgebra.toMulAlgebraNorm** 是 Mathlib 中的一个定义，位于命名空间 `NormedAlgebra`。
形式化陈述：toMulAlgebraNorm : MulAlgebraNorm K L where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normed field extension `L / K`, the norm on `L` is a multiplicative `K`-
algebra norm.
-/
def toMulAlgebraNorm : MulAlgebraNorm K L where
  __ := NormedField.toMulRingNorm L
  smul' r x := by
    simp only [Algebra.smul_def, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
      map_mul, mul_eq_mul_right_iff, map_eq_zero]
    exact Or.inl <| norm_algebraMap' L r

@[simp]
/-
**NormedAlgebra.toMulAlgebraNorm_apply** 是 Mathlib 中的一个引理，位于命名空间 `NormedAlgebra`
。
形式化陈述：toMulAlgebraNorm_apply (x : L) : toMulAlgebraNorm K L x = ‖x‖
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toMulAlgebraNorm_apply (x : L) : toMulAlgebraNorm K L x = ‖x‖ := rfl

end NormedAlgebra

namespace MulRingNorm

variable {R : Type*} [NonAssocRing R]

/-- The ring norm underlying a multiplicative ring norm. -/
/-
**MulRingNorm.toRingNorm** 是 Mathlib 中的一个定义，位于命名空间 `MulRingNorm`。
形式化陈述：toRingNorm (f : MulRingNorm R) : RingNorm R where toFun
参数：f : MulRingNorm R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulRingNorm.eq_zero_of_map_eq_zero'`：∀ {R : Type u_2} [inst : NonAssocRi
ng R] (self : MulRingNorm R) (x : R), self.toFun x = 0 → x = 0

--- 原说明 ---
The ring norm underlying a multiplicative ring norm.
-/
def toRingNorm (f : MulRingNorm R) : RingNorm R where
  toFun := f
  __ := f
  mul_le' x y := le_of_eq (f.map_mul' x y)

/-- A multiplicative ring norm is power-multiplicative. -/
/-
**MulRingNorm.isPowMul** 是 Mathlib 中的一个定理，位于命名空间 `MulRingNorm`。
形式化陈述：isPowMul {A : Type*} [Ring A] (f : MulRingNorm A) : IsPowMul f
参数：f : MulRingNorm A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MulRingSeminormClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} [inst : NonAssocRing α] [inst_1 : Se
miring β]   [inst_2 : PartialOrder …
· 使用定理 `MulRingNormClass.toMulRingSeminormClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : NonAssocRing α} {inst_1 : Semiring
 β}   {inst_2 : PartialOrder …

--- 原说明 ---
A multiplicative ring norm is power-multiplicative.
-/
theorem isPowMul {A : Type*} [Ring A] (f : MulRingNorm A) : IsPowMul f := fun x n hn => by
  cases n
  · lia
  · rw [map_pow]

end MulRingNorm

