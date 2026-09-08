/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Mitchell Lee, Johan Commelin
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteSpan
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Tactic.Module

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
1. the kernel of `f` is fixed,
2. the point `x` maps to `-x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries an inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

* `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
  the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
  discharging this proof obligation.
* `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
  that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
  linear map.
* `Module.reflection_mul_reflection_pow_apply`: a formula for $(r_1 r_2)^m z$, where $r_1$ and
  $r_2$ are reflections and $z \in M$. It involves the Chebyshev polynomials and holds over any
  commutative ring. This is used to define reflection representations of Coxeter groups.
* `Module.Dual.eq_of_preReflection_mapsTo`: a uniqueness result about reflections that preserve
  finite spanning sets. It is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exist elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflection` defined here.

-/

@[expose] public section

open Function Set
open Module
open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (f : Dual R M) (y : M)

namespace Module

/-- Given an element `x` in a module `M` and a linear form `f` on `M`, we define the endomorphism
of `M` for which `y ↦ y - (f y) • x`.

One is typically interested in this endomorphism when `f x = 2`; this definition exists to allow the
user defer discharging this proof obligation. See also `Module.reflection`. -/
/-
**Module.preReflection** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：preReflection : End R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `x` in a module `M` and a linear form `f` on `M`, we define the
 endomorphism
of `M` for which `y ↦ y - (f y) • x`.

One is typically interested in this endomorphism when `f x = 2`; this definition
 exists to allow the
user defer discharging this proof obligation. See also `Module.reflection`.
-/
def preReflection : End R M :=
  LinearMap.id - f.smulRight x
/-
**Module.preReflection_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：preReflection_apply : preReflection x f y = y - (f y) • x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}
/-
**Module.preReflection_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：preReflection_apply_self (h : f x = 2) : preReflection x f x = -x
参数：h : f x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.preReflection_apply`：preReflection_apply : preReflection x f y = 
y - (f y) • x
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `_private.Mathlib.LinearAlgebra.Reflection.0.Module.preReflection_apply_s
elf._abel_1_1`：∀ {M : Type u_1} [inst : AddCommGroup M] {x : M}, x - (x + x) = -
x
-/
lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = -x := by
  rw [preReflection_apply, h, two_smul]; abel
/-
**Module.involutive_preReflection** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：involutive_preReflection (h : f x = 2) : Involutive (preReflection x f)
参数：h : f x = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.preReflection_apply`：preReflection_apply : preReflection x f y = 
y - (f y) • x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y ↦ by simp [map_sub, h, two_smul, preReflection_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.preReflection_preReflection** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：preReflection_preReflection (g : Dual R M) (h : f x = 2) : preReflection (
preReflection x f y) (preReflection f (Dual.eval R M x) g) = (preReflection x f)
 ∘ₗ (preReflection y g) ∘ₗ (preReflection x f)
参数：g : Dual R M；h : f x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Module.preReflection_apply`：preReflection_apply : preReflection x f y = 
y - (f y) • x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.LinearAlgebra.Reflection.0.Module.preReflection_preRefl
ection._abel_1_1`：∀ {R : Type u_2} {M : Type u_1} [inst : CommRing R] [inst_1 : 
AddCommGroup M] [inst_2 : _root_.Module R M] {x : M}   {f : Module.Dual R M} (…
-/
lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

/-- Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define
the endomorphism of `M` for which `y ↦ y - (f y) • x`.

It is an involutive endomorphism of `M` fixing the kernel of `f` for which `x ↦ -x`. -/
/-
**Module.reflection** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：reflection (h : f x = 2) : M ≃ₗ[R] M
参数：h : f x = 2。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Module.involutive_preReflection`：involutive_preReflection (h : f x = 2) 
: Involutive (preReflection x f)
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x
 = 2`, we define
the endomorphism of `M` for which `y ↦ y - (f y) • x`.

It is an involutive endomorphism of `M` fixing the kernel of `f` for which `x ↦ 
-x`.
-/
def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  { preReflection x f, (involutive_preReflection h).toPerm with }
/-
**Module.reflection_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_apply (h : f x = 2) : reflection h y = y - (f y) • x
参数：h : f x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Module.preReflection_apply`：preReflection_apply : preReflection x f y = 
y - (f y) • x
-/
lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x f y

@[simp]
/-
**Module.reflection_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_apply_self (h : f x = 2) : reflection h x = -x
参数：h : f x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Module.preReflection_apply_self`：preReflection_apply_self (h : f x = 2) 
: preReflection x f x = -x
-/
lemma reflection_apply_self (h : f x = 2) :
    reflection h x = -x :=
  preReflection_apply_self h
/-
**Module.involutive_reflection** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：involutive_reflection (h : f x = 2) : Involutive (reflection h)
参数：h : f x = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Module.involutive_preReflection`：involutive_preReflection (h : f x = 2) 
: Involutive (preReflection x f)
-/
lemma involutive_reflection (h : f x = 2) :
    Involutive (reflection h) :=
  involutive_preReflection h

@[simp]
/-
**Module.reflection_inv** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_inv (h : f x = 2) : (reflection h)⁻¹ = reflection h
参数：h : f x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma reflection_inv (h : f x = 2) : (reflection h)⁻¹ = reflection h := rfl

@[simp]
/-
**Module.reflection_symm** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_symm (h : f x = 2) : (reflection h).symm = reflection h
参数：h : f x = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma reflection_symm (h : f x = 2) :
    (reflection h).symm = reflection h :=
  rfl
/-
**Module.invOn_reflection_of_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：invOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) : InvOn (reflection h
) (reflection h) Φ Φ
参数：h : f x = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Module.involutive_reflection`：involutive_reflection (h : f x = 2) : Invo
lutive (reflection h)
-/
lemma invOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) :
    InvOn (reflection h) (reflection h) Φ Φ :=
  ⟨fun x _ ↦ involutive_reflection h x, fun x _ ↦ involutive_reflection h x⟩
/-
**Module.bijOn_reflection_of_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：bijOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflect
ion h) Φ Φ) : BijOn (reflection h) Φ Φ
参数：h : f x = 2；h' : MapsTo (reflection h) Φ Φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用引理 `Module.invOn_reflection_of_mapsTo`：invOn_reflection_of_mapsTo {Φ : Set M
} (h : f x = 2) : InvOn (reflection h) (reflection h) Φ Φ
-/
lemma bijOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) :
    BijOn (reflection h) Φ Φ :=
  (invOn_reflection_of_mapsTo h).bijOn h' h'
/-
**Module._root_.Submodule.mem_invtSubmodule_reflection_of_mem** 是 Mathlib 中的一个引理
，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submodule.mem_invtSubmodule_reflection_of_mem (h : f x = 2)
    (p : Submodule R M) (hx : x ∈ p) :
    p ∈ End.invtSubmodule (reflection h) := by
  suffices ∀ y ∈ p, reflection h y ∈ p from
    (End.mem_invtSubmodule _).mpr fun y hy ↦ by simpa using this y hy
  intro y hy
  simpa only [reflection_apply, p.sub_mem_iff_right hy] using p.smul_mem (f y) hx
/-
**Module._root_.Submodule.mem_invtSubmodule_reflection_iff** 是 Mathlib 中的一个引理，位于
命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submodule.mem_invtSubmodule_reflection_iff [IsDomain R] [NeZero (2 : R)]
    [IsTorsionFree R M] (h : f x = 2) {p : Submodule R M} (hp : Disjoint p (R ∙ x)) :
    p ∈ End.invtSubmodule (reflection h) ↔ p ≤ LinearMap.ker f := by
  refine ⟨fun h' y hy ↦ ?_, fun h' y hy ↦ ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; exact two_ne_zero (α := R) <| by simp [← h]
    suffices f y • x ∈ p by
      have aux : f y • x ∈ p ⊓ R ∙ x := ⟨this, Submodule.mem_span_singleton.mpr ⟨f y, rfl⟩⟩
      rw [hp.eq_bot, Submodule.mem_bot, smul_eq_zero] at aux
      exact aux.resolve_right hx
    specialize h' hy
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply] at h'
    simpa using p.sub_mem h' hy
  · have hy' : f y = 0 := by simpa using h' hy
    simpa [reflection_apply, hy']

/-! ### Powers of the product of two reflections

Let $M$ be a module over a commutative ring $R$. Let $x, y \in M$ and $f, g \in M^*$ with
$f(x) = g(y) = 2$. The corresponding reflections $r_1, r_2 \colon M \to M$ (`Module.reflection`) are
given by $r_1z = z - f(z) x$ and $r_2 z = z - g(z) y$. These are linear automorphisms of $M$.

To define reflection representations of a Coxeter group, it is important to be able to compute the
order of the composition $r_1 r_2$.

Note that if $M$ is a real inner product space and $r_1$ and $r_2$ are both orthogonal
reflections (i.e. $f(z) = 2 \langle x, z \rangle / \langle x, x \rangle$ and
$g(z) = 2 \langle y, z\rangle / \langle y, y\rangle$ for all $z \in M$),
then $r_1 r_2$ is a rotation by the angle
$$\cos^{-1}\left(\frac{f(y) g(x) - 2}{2}\right)$$
and one may determine the order of $r_1 r_2$ accordingly.

However, if $M$ does not have an inner product, and even if $R$ is not $\mathbb{R}$, then we may
instead use the formulas in this section. These formulas all involve evaluating Chebyshev
$S$-polynomials (`Polynomial.Chebyshev.S`) at $t = f(y) g(x) - 2$, and they hold over any
commutative ring. -/
section

open Int Polynomial.Chebyshev

variable {x y : M} {f g : Dual R M} (hf : f x = 2) (hg : g y = 2)

set_option backward.isDefEq.respectTransparency false in
/-- A formula for $(r_1 r_2)^m z$, where $m$ is a natural number and $z \in M$. -/
/-
**Module.reflection_mul_reflection_pow_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_mul_reflection_pow_apply (m : Nat) (z : M) (t : R
参数：m : Nat；z : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Int.neg_ediv_self`：∀ (a : ℤ), a ≠ 0 → -a / a = -1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Chebyshev.S_neg_one`：S_neg_one : S R (-1) = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `Polynomial.Chebyshev.S_neg_two`：S_neg_two : S R (-2) = -1
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `EuclideanDomain.zero_div`：zero_div {a : R} : 0 / a = 0
· 使用定理 `Polynomial.Chebyshev.S_zero`：S_zero : S R 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Chebyshev.S_sub_two`：S_sub_two (n : Int) : S R (n - 2) = X * 
S R (n - 1) - S R n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
（共 130 条，此处仅展示前 30 条）

--- 原说明 ---
A formula for $(r_1 r_2)^m z$, where $m$ is a natural number and $z \in M$.
-/
lemma reflection_mul_reflection_pow_apply (m : ℕ) (z : M)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x * f z - g z) • y - f z • x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    /- Now, let us collect two facts about the evaluations of `S r k`. These easily follow from the
    properties of the `S` polynomials. -/
    have S_eval_t_sub_two (k : ℤ) :
        (S R (k - 2)).eval t = t * (S R (k - 1)).eval t - (S R k).eval t := by
      simp [S_sub_two]
    have S_eval_t_sq_add_S_eval_t_sq (k : ℤ) :
        (S R k).eval t ^ 2 + (S R (k + 1)).eval t ^ 2 - t * (S R k).eval t * (S R (k + 1)).eval t
        = 1 := by
      simpa using congr_arg (Polynomial.eval t) (S_sq_add_S_sq R k)
    -- Apply the inductive hypothesis.
    rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.mul_apply]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- `m` can be written in the form `2 * k + e`, where `e` is `0` or `1`.
    push_cast
    rw [← Int.mul_ediv_add_emod m 2]
    set k : ℤ := m / 2
    set e : ℤ := m % 2
    simp_rw [add_assoc (2 * k), add_sub_assoc (2 * k), add_comm (2 * k),
      add_mul_ediv_left _ k (by simp : (2 : ℤ) ≠ 0)]
    have he : e = 0 ∨ e = 1 := by lia
    clear_value e
    /- Now, equate the coefficients on both sides. These linear combinations were
    found using `polyrith`. -/
    match_scalars
    · rfl
    · linear_combination (norm := skip) (-g z * f y * (S R (e - 1 + k)).eval t +
          f z * (S R (e - 1 + k)).eval t) * S_eval_t_sub_two (e + k) +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf
    · linear_combination (norm := skip)
          g z * (S R (e - 1 + k)).eval t * S_eval_t_sub_two (e + k) +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf

/-- A formula for $(r_1 r_2)^m$, where $m$ is a natural number. -/
/-
**Module.reflection_mul_reflection_pow** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_mul_reflection_pow (m : Nat) (t : R
参数：m : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.reflection_mul_reflection_pow_apply`：reflection_mul_reflection_po
w_apply (m : Nat) (z : M) (t : R

--- 原说明 ---
A formula for $(r_1 r_2)^m$, where $m$ is a natural number.
-/
lemma reflection_mul_reflection_pow (m : ℕ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m).toLinearMap =
      LinearMap.id (R := R) (M := M) +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x • f - g).smulRight y - f.smulRight x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y • g - f).smulRight x - g.smulRight y) := by
  ext z
  simpa using reflection_mul_reflection_pow_apply hf hg m z t ht

/-- A formula for $(r_1 r_2)^m z$, where $m$ is an integer and $z \in M$. -/
/-
**Module.reflection_mul_reflection_zpow_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module`
。
形式化陈述：reflection_mul_reflection_zpow_apply (m : Int) (z : M) (t : R
参数：m : Int；z : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Module.reflection_mul_reflection_pow_apply`：reflection_mul_reflection_po
w_apply (m : Nat) (z : M) (t : R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `Module.reflection_inv`：reflection_inv (h : f x = 2) : (reflection h)⁻¹ =
 reflection h
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Polynomial.Chebyshev.S_neg_sub_two`：S_neg_sub_two (n : Int) : S R (-n - 
2) = -S R n
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
A formula for $(r_1 r_2)^m z$, where $m$ is an integer and $z \in M$.
-/
lemma reflection_mul_reflection_zpow_apply (m : ℤ) (z : M)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x * f z - g z) • y - f z • x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m using Int.negInduction with
  | nat m => exact_mod_cast reflection_mul_reflection_pow_apply hf hg m z t ht
  | neg _ m =>
    have ht' : t = g x * f y - 2 := by rwa [mul_comm (g x)]
    rw [zpow_neg, ← inv_zpow, mul_inv_rev, reflection_inv, reflection_inv, zpow_natCast,
      reflection_mul_reflection_pow_apply hg hf m z t ht', add_right_comm z]
    have aux (a b : ℤ) (hab : a + b = -3 := by lia) : a / 2 = -(b / 2) - 2 := by lia
    rw [aux (-m - 3) m, aux (-m - 2) (m - 1), aux (-m - 1) (m - 2), aux (-m) (m - 3)]
    simp only [S_neg_sub_two, Polynomial.eval_neg]
    ring_nf

/-- A formula for $(r_1 r_2)^m$, where $m$ is an integer. -/
/-
**Module.reflection_mul_reflection_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_mul_reflection_zpow (m : Int) (t : R
参数：m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.reflection_mul_reflection_zpow_apply`：reflection_mul_reflection_z
pow_apply (m : Int) (z : M) (t : R

--- 原说明 ---
A formula for $(r_1 r_2)^m$, where $m$ is an integer.
-/
lemma reflection_mul_reflection_zpow (m : ℤ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m).toLinearMap =
      LinearMap.id (R := R) (M := M) +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x • f - g).smulRight y - f.smulRight x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y • g - f).smulRight x - g.smulRight y) := by
  ext z
  simpa using reflection_mul_reflection_zpow_apply hf hg m z t ht

set_option backward.isDefEq.respectTransparency false in
/-- A formula for $(r_1 r_2)^m x$, where $m$ is an integer. This is the special case of
`Module.reflection_mul_reflection_zpow_apply` with $z = x$. -/
/-
**Module.reflection_mul_reflection_zpow_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dule`。
形式化陈述：reflection_mul_reflection_zpow_apply_self (m : Int) (t : R
参数：m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.S_sub_two`：S_sub_two (n : Int) : S R (n - 2) = X * 
S R (n - 1) - S R n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.Chebyshev.S_zero`：S_zero : S R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Polynomial.Chebyshev.S_neg_one`：S_neg_one : S R (-1) = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `zpow_one_add`：zpow_one_add (a : G) (n : Int) : a ^ (1 + n) = a * a ^ n
· 使用定理 `LinearEquiv.mul_apply`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f g : M ≃ₗ[R] M) (
x : M), (f …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 115 条，此处仅展示前 30 条）

--- 原说明 ---
A formula for $(r_1 r_2)^m x$, where $m$ is an integer. This is the special case
 of
`Module.reflection_mul_reflection_zpow_apply` with $z = x$.
-/
lemma reflection_mul_reflection_zpow_apply_self (m : ℤ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R (m - 1)).eval t * -g x) • y := by
  /- Even though this is a special case of `Module.reflection_mul_reflection_zpow_apply`, it is
  easier to prove it from scratch. -/
  have S_eval_t_sub_two (k : ℤ) :
      (S R (k - 2)).eval t = (f y * g x - 2) * (S R (k - 1)).eval t - (S R k).eval t := by
    simp [S_sub_two, ht]
  induction m with
  | zero => simp
  | succ m ih =>
    -- Apply the inductive hypothesis.
    rw [add_comm (m : ℤ) 1, zpow_one_add, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (m + 1)
    · ring_nf
  | pred m ih =>
    -- Apply the inductive hypothesis.
    rw [sub_eq_add_neg (-m : ℤ) 1, add_comm (-m : ℤ) (-1), zpow_add, zpow_neg_one, mul_inv_rev,
      reflection_inv, reflection_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (-m)
    · linear_combination (norm := ring_nf) g x * S_eval_t_sub_two (-m)

/-- A formula for $(r_1 r_2)^m x$, where $m$ is a natural number. This is the special case of
`Module.reflection_mul_reflection_pow_apply` with $z = x$. -/
/-
**Module.reflection_mul_reflection_pow_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ule`。
形式化陈述：reflection_mul_reflection_pow_apply_self (m : Nat) (t : R
参数：m : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Module.reflection_mul_reflection_zpow_apply_self`：reflection_mul_reflect
ion_zpow_apply_self (m : Int) (t : R

--- 原说明 ---
A formula for $(r_1 r_2)^m x$, where $m$ is a natural number. This is the specia
l case of
`Module.reflection_mul_reflection_pow_apply` with $z = x$.
-/
lemma reflection_mul_reflection_pow_apply_self (m : ℕ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R (m - 1)).eval t * -g x) • y :=
  mod_cast reflection_mul_reflection_zpow_apply_self hf hg m t ht

set_option backward.isDefEq.respectTransparency false in
/-- A formula for $r_2 (r_1 r_2)^m x$, where $m$ is an integer. -/
/-
**Module.reflection_mul_reflection_mul_reflection_zpow_apply_self** 是 Mathlib 中的
一个引理，位于命名空间 `Module`。
形式化陈述：reflection_mul_reflection_mul_reflection_zpow_apply_self (m : Int) (t : R
参数：m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.mul_apply`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f g : M ≃ₗ[R] M) (
x : M), (f …
· 使用引理 `Module.reflection_mul_reflection_zpow_apply_self`：reflection_mul_reflect
ion_zpow_apply_self (m : Int) (t : R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `Module.reflection_apply`：reflection_apply (h : f x = 2) : reflection h y
 = y - (f y) • x
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
A formula for $r_2 (r_1 r_2)^m x$, where $m$ is an integer.
-/
lemma reflection_mul_reflection_mul_reflection_zpow_apply_self (m : ℤ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R m).eval t * -g x) • y := by
  rw [LinearEquiv.mul_apply, reflection_mul_reflection_zpow_apply_self hf hg m t ht]
  -- Expand out all the reflections and use `hf`, `hg`.
  simp only [reflection_apply, map_add, map_smul, hg]
  -- Equate coefficients of `x` and `y`.
  module

/-- A formula for $r_2 (r_1 r_2)^m x$, where $m$ is a natural number. -/
/-
**Module.reflection_mul_reflection_mul_reflection_pow_apply_self** 是 Mathlib 中的一
个引理，位于命名空间 `Module`。
形式化陈述：reflection_mul_reflection_mul_reflection_pow_apply_self (m : Nat) (t : R
参数：m : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Module.reflection_mul_reflection_mul_reflection_zpow_apply_self`：reflect
ion_mul_reflection_mul_reflection_zpow_apply_self (m : Int) (t : R

--- 原说明 ---
A formula for $r_2 (r_1 r_2)^m x$, where $m$ is a natural number.
-/
lemma reflection_mul_reflection_mul_reflection_pow_apply_self (m : ℕ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R m).eval t * -g x) • y :=
  mod_cast reflection_mul_reflection_mul_reflection_zpow_apply_self hf hg m t ht

end

/-! ### Lemmas used to prove uniqueness results for root data -/

set_option backward.isDefEq.respectTransparency false in
/-- See also `Module.Dual.eq_of_preReflection_mapsTo'` for a variant of this lemma which
applies when `Φ` does not span.

This rather technical-looking lemma exists because it is exactly what is needed to establish various
uniqueness results for root data / systems. One might regard this lemma as lying at the boundary of
linear algebra and combinatorics since the finiteness assumption is the key. -/
/-
**Module.Dual.eq_of_preReflection_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`
。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] [CharZero R]   [IsDomain R] [Module.IsTorsionFr
ee R M] {x : M} {Φ : Set M},   Φ.Finite →     Submodule.span R Φ = ⊤ →       ∀ {
f g : Module.Dual R M},         f x = 2 →           Set.MapsTo (⇑(Module.preRefl
ection x f)) Φ Φ → g x = 2 → Set.MapsTo (⇑(Module.preReflection x g)) Φ Φ → f = 
g
参数：⇑(Module.preReflection x f)；⇑(Module.preReflection x g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Module.reflection_apply`：reflection_apply (h : f x = 2) : reflection h y
 = y - (f y) • x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `_private.Mathlib.LinearAlgebra.Reflection.0.Module.Dual.eq_of_preReflect
ion_mapsTo._abel_1_2`：∀ {R : Type u_2} {M : Type u_1} [inst : CommRing R] [inst_
1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x : M}   {f g : Module.Dual R 
M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
See also `Module.Dual.eq_of_preReflection_mapsTo'` for a variant of this lemma w
hich
applies when `Φ` does not span.

This rather technical-looking lemma exists because it is exactly what is needed 
to establish various
uniqueness results for root data / systems. One might regard this lemma as lying
 at the boundary of
linear algebra and combinatorics since the finiteness assumption is the key.
-/
lemma Dual.eq_of_preReflection_mapsTo [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {x : M} {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    f = g := by
  have hx : x ≠ 0 := by rintro rfl; simp at hf₁
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, Module.End.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : ∀ (n : ℕ),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, ih, hu, add_mul, mul_add, mul_add]
      simp_rw [Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M →ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  exact u.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo hΦ₁ hΦ₂ (hg₂.comp hf₂)

/-- This rather technical-looking lemma exists because it is exactly what is needed to establish a
uniqueness result for root data. See the doc string of `Module.Dual.eq_of_preReflection_mapsTo` for
further remarks. -/
/-
**Module.Dual.eq_of_preReflection_mapsTo'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual
`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] [CharZero R]   [IsDomain R] [Module.IsTorsionFr
ee R M] {x : M} {Φ : Set M},   Φ.Finite →     x ∈ Submodule.span R Φ →       ∀ {
f g : Module.Dual R M},         f x = 2 →           Set.MapsTo (⇑(Module.preRefl
ection x f)) Φ Φ →             g x = 2 →               Set.MapsTo (⇑(Module.preR
eflection x g)) Φ Φ →                 (Submodule.span R Φ).subtype.dualMap f = (
Submodule.span R Φ).subtype.dualMap g
参数：⇑(Module.preReflection x f)；⇑(Module.preReflection x g)；Submodule.span R Φ；Su
bmodule.span R Φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.span_setOfPred_mem_eq_top`：span_setOfPred_mem_eq_top : span R 
{x : span R s | (x : M) in s} = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Dual.eq_of_preReflection_mapsTo`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [Char
Zero R]   [IsDomain R] [Modu…
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…

--- 原说明 ---
This rather technical-looking lemma exists because it is exactly what is needed 
to establish a
uniqueness result for root data. See the doc string of `Module.Dual.eq_of_preRef
lection_mapsTo` for
further remarks.
-/
lemma Dual.eq_of_preReflection_mapsTo' [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {x : M} {Φ : Set M} (hΦ₁ : Φ.Finite) (hx : x ∈ span R Φ) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by
    simp only [Φ']
    rw [range_inclusion]
    simp
  let x' : span R Φ := ⟨x, hx⟩
  have : ∀ {F : Dual R M}, MapsTo (preReflection x F) Φ Φ →
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ'] at hy' ⊢
    rw [range_inclusion] at hy'
    simp only [SetLike.coe_sort_coe, mem_ofPred_eq] at hy' ⊢
    rw [range_inclusion]
    exact hF hy'
  exact eq_of_preReflection_mapsTo hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

variable {y}
variable {g : Dual R M}

set_option backward.isDefEq.respectTransparency false in
/-- Composite of reflections in "parallel" hyperplanes is a shear (special case). -/
/-
**Module.reflection_reflection_iterate** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：reflection_reflection_iterate (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y
 * g x = 4) (n : Nat) : ((reflection hgy).trans (reflection hfx))^[n] y = y + n 
• (f y • x - (2 : R) • y)
参数：hfx : f x = 2；hgy : g y = 2；hgxfy : f y * g x = 4；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用引理 `Module.reflection_apply_self`：reflection_apply_self (h : f x = 2) : refl
ection h x = -x
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Module.reflection_apply`：reflection_apply (h : f x = 2) : reflection h y
 = y - (f y) • x
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Composite of reflections in "parallel" hyperplanes is a shear (special case).
-/
lemma reflection_reflection_iterate
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) (n : ℕ) :
    ((reflection hgy).trans (reflection hfx))^[n] y = y + n • (f y • x - (2 : R) • y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : ∀ z : M, f y • g x • z = 2 • 2 • z := by
      intro z
      rw [smul_smul, hgxfy, smul_smul, ← Nat.cast_smul_eq_nsmul R (2 * 2), show 2 * 2 = 4 from rfl,
        Nat.cast_ofNat]
    simp only [iterate_succ', comp_apply, ih, two_smul, smul_sub, smul_add, map_add,
      LinearEquiv.trans_apply, reflection_apply_self, map_neg, reflection_apply, neg_sub, map_sub,
      map_nsmul, map_smul, smul_neg, hz, add_smul]
    abel
/-
**Module.infinite_range_reflection_reflection_iterate_iff** 是 Mathlib 中的一个引理，位于命
名空间 `Module`。
形式化陈述：infinite_range_reflection_reflection_iterate_iff [IsAddTorsionFree M] (hfx
 : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) : (range <| fun n => ((refle
ction hgy).trans (reflection hfx))^[n] y).Infinite ↔ f y • x != (2 : R) • y
参数：hfx : f x = 2；hgy : g y = 2；hgxfy : f y * g x = 4。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Module.reflection_reflection_iterate`：reflection_reflection_iterate (hfx
 : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) (n : Nat) : ((reflection hgy
).trans (reflection hfx))^…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma infinite_range_reflection_reflection_iterate_iff [IsAddTorsionFree M]
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) :
    (range <| fun n ↦ ((reflection hgy).trans (reflection hfx))^[n] y).Infinite ↔
    f y • x ≠ (2 : R) • y := by
  simp only [reflection_reflection_iterate hfx hgy hgxfy, infinite_range_add_nsmul_iff, sub_ne_zero]
/-
**Module.eq_of_mapsTo_reflection_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：eq_of_mapsTo_reflection_of_mem [IsAddTorsionFree M] {Φ : Set M} (hΦ : Φ.Fi
nite) (hfx : f x = 2) (hgy : g y = 2) (hgx : g x = 2) (hfy : f y = 2) (hxfΦ : Ma
psTo (preReflection x f) Φ Φ) (hygΦ : MapsTo (preReflection y g) Φ Φ) (hyΦ : y i
n Φ) : x = y
参数：hΦ : Φ.Finite；hfx : f x = 2；hgy : g y = 2；hgx : g x = 2；hfy : f y = 2；hxfΦ : 
MapsTo (preReflection x f) Φ Φ；hygΦ : MapsTo (preReflection y g) Φ Φ；hyΦ : y in 
Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.infinite_range_reflection_reflection_iterate_iff`：infinite_range_
reflection_reflection_iterate_iff [IsAddTorsionFree M] (hfx : f x = 2) (hgy : g 
y = 2) (hgxfy : f y * g x = 4) : (range <| fu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.IsFixedPt.image_iterate`：image_iterate {s : Set α} (h : IsFixed
Pt (Set.image f) s) (n : Nat) : IsFixedPt (Set.image f^[n]) s
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.BijOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.BijOn g t p → Set.BijO
n f …
· 使用引理 `Module.bijOn_reflection_of_mapsTo`：bijOn_reflection_of_mapsTo {Φ : Set M
} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) : BijOn (reflection h) Φ Φ
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
-/
lemma eq_of_mapsTo_reflection_of_mem [IsAddTorsionFree M] {Φ : Set M} (hΦ : Φ.Finite)
    (hfx : f x = 2) (hgy : g y = 2) (hgx : g x = 2) (hfy : f y = 2)
    (hxfΦ : MapsTo (preReflection x f) Φ Φ)
    (hygΦ : MapsTo (preReflection y g) Φ Φ)
    (hyΦ : y ∈ Φ) :
    x = y := by
  suffices h : f y • x = (2 : R) • y by
    rw [hfy, two_smul R x, two_smul R y, ← two_zsmul, ← two_zsmul] at h
    exact smul_right_injective _ two_ne_zero h
  contrapose! hΦ
  apply ((infinite_range_reflection_reflection_iterate_iff hfx hgy
    (by rw [hfy, hgx]; norm_cast)).mpr hΦ).mono
  rw [range_subset_iff]
  intro n
  rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo hfx hxfΦ).comp
    (bijOn_reflection_of_mapsTo hgy hygΦ)).image_eq n]
  exact mem_image_of_mem _ hyΦ
/-
**Module.injOn_dualMap_subtype_span_range_range** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e`。
形式化陈述：injOn_dualMap_subtype_span_range_range {ι : Type*} [IsAddTorsionFree M] {r
 : ι ↪ M} {c : ι -> Dual R M} (hfin : (range r).Finite) (h_two : forall i, c i (
r i) = 2) (h_mapsTo : forall i, MapsTo (preReflection (r i) (c i)) (range r) (ra
nge r)) : InjOn (span R (range r)).subtype.dualMap (range c)
参数：hfin : (range r).Finite；h_two : forall i, c i (r i) = 2；h_mapsTo : forall i, 
MapsTo (preReflection (r i) (c i)) (range r) (range r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用引理 `Module.eq_of_mapsTo_reflection_of_mem`：eq_of_mapsTo_reflection_of_mem [I
sAddTorsionFree M] {Φ : Set M} (hΦ : Φ.Finite) (hfx : f x = 2) (hgy : g y = 2) (
hgx : g x = 2) (hfy : f y =…
-/
lemma injOn_dualMap_subtype_span_range_range {ι : Type*} [IsAddTorsionFree M]
    {r : ι ↪ M} {c : ι → Dual R M} (hfin : (range r).Finite)
    (h_two : ∀ i, c i (r i) = 2)
    (h_mapsTo : ∀ i, MapsTo (preReflection (r i) (c i)) (range r) (range r)) :
    InjOn (span R (range r)).subtype.dualMap (range c) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices ∀ k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

end Module

