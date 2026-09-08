/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary

/-!
# The ⋆-algebra automorphism given by a unitary element

This file defines the ⋆-algebra automorphism on `R` given by a unitary `u`,
which is `Unitary.conjStarAlgAut S R u`, defined to be `x ↦ u * x * star u`.
-/

@[expose] public section

namespace Unitary
variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (S R) in
/-- Each unitary element `u` defines a ⋆-algebra automorphism such that
`x ↦ u * x * star u`.

This is the ⋆-algebra automorphism version of a specialized version of
`MulSemiringAction.toAlgAut`. -/
/-
**Unitary.conjStarAlgAut** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：conjStarAlgAut : unitary R ->* (R ≃⋆ₐ[S] R) where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each unitary element `u` defines a ⋆-algebra automorphism such that
`x ↦ u * x * star u`.

This is the ⋆-algebra automorphism version of a specialized version of
`MulSemiringAction.toAlgAut`.
-/
def conjStarAlgAut : unitary R →* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
    map_smul' _ _ := smul_comm _ _ _ |>.symm
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp
/-
**Unitary.conjStarAlgAut_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : StarMul R] [
inst_2 : SMul S R]   [inst_3 : IsScalarTower S R R] [inst_4 : SMulCommClass S R 
R] (u : ↥(unitary R)) (x : R),   ((Unitary.conjStarAlgAut S R) u) x = ↑u * x * s
tar ↑u
参数：u : ↥(unitary R)；x : R；(Unitary.conjStarAlgAut S R) u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem conjStarAlgAut_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R u x = u * x * (star u : R) := rfl
/-
**Unitary.conjStarAlgAut_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：conjStarAlgAut_symm_apply (u : unitary R) (x : R) : (conjStarAlgAut S R u)
.symm x = (star u : R) * x * u
参数：u : unitary R；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjStarAlgAut_symm_apply (u : unitary R) (x : R) :
    (conjStarAlgAut S R u).symm x = (star u : R) * x * u := rfl
/-
**Unitary.conjStarAlgAut_star_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：conjStarAlgAut_star_apply (u : unitary R) (x : R) : conjStarAlgAut S R (st
ar u) x = (star u : R) * x * u
参数：u : unitary R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjStarAlgAut_star_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R (star u) x = (star u : R) * x * u := by simp
/-
**Unitary.conjStarAlgAut_symm** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : StarMul R] [
inst_2 : SMul S R]   [inst_3 : IsScalarTower S R R] [inst_4 : SMulCommClass S R 
R] (u : ↥(unitary R)),   ((Unitary.conjStarAlgAut S R) u).symm = (Unitary.conjSt
arAlgAut S R) (star u)
参数：u : ↥(unitary R)；(Unitary.conjStarAlgAut S R) u；Unitary.conjStarAlgAut S R；st
ar u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.ext`：ext {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a) : f =
 g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem conjStarAlgAut_symm (u : unitary R) :
    (conjStarAlgAut S R u).symm = conjStarAlgAut S R (star u) := by
  ext; simp [conjStarAlgAut_symm_apply]
/-
**Unitary.conjStarAlgAut_trans_conjStarAlgAut** 是 Mathlib 中的一个定理，位于命名空间 `Unitary
`。
形式化陈述：conjStarAlgAut_trans_conjStarAlgAut (u₁ u₂ : unitary R) : (conjStarAlgAut 
S R u₁).trans (conjStarAlgAut S R u₂) = conjStarAlgAut S R (u₂ * u₁)
参数：u₁ u₂ : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem conjStarAlgAut_trans_conjStarAlgAut (u₁ u₂ : unitary R) :
    (conjStarAlgAut S R u₁).trans (conjStarAlgAut S R u₂) = conjStarAlgAut S R (u₂ * u₁) :=
  map_mul _ _ _ |>.symm
/-
**Unitary.conjStarAlgAut_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：conjStarAlgAut_mul_apply (u₁ u₂ : unitary R) (x : R) : conjStarAlgAut S R 
(u₁ * u₂) x = conjStarAlgAut S R u₁ (conjStarAlgAut S R u₂ x)
参数：u₁ u₂ : unitary R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjStarAlgAut_mul_apply (u₁ u₂ : unitary R) (x : R) :
    conjStarAlgAut S R (u₁ * u₂) x = conjStarAlgAut S R u₁ (conjStarAlgAut S R u₂ x) := by simp
/-
**Unitary.toRingEquiv_conjStarAlgAut** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：toRingEquiv_conjStarAlgAut (u : unitary R) : (conjStarAlgAut S R u).toRing
Equiv = MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
参数：u : unitary R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_conjStarAlgAut (u : unitary R) :
    (conjStarAlgAut S R u).toRingEquiv =
      MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl
/-
**Unitary.toAlgEquiv_conjStarAlgAut** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：toAlgEquiv_conjStarAlgAut {S : Type*} [CommSemiring S] [Algebra S R] (u : 
unitary R) : (conjStarAlgAut S R u).toAlgEquiv = MulSemiringAction.toAlgEquiv _ 
R (ConjAct.toConjAct <| toUnits u)
参数：u : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toAlgEquiv_conjStarAlgAut {S : Type*} [CommSemiring S] [Algebra S R] (u : unitary R) :
    (conjStarAlgAut S R u).toAlgEquiv =
      MulSemiringAction.toAlgEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl
/-
**Unitary.conjStarAlgAut_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：conjStarAlgAut_ext_iff {S : Type*} [CommSemiring S] [Algebra S R] [Algebra
.IsCentral S R] (u v : unitary R) : conjStarAlgAut S R u = conjStarAlgAut S R v 
↔ exists α : S, (u : R) = α • v
参数：u v : unitary R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.mem_center_iff`：mem_center_iff {a : A} : a in center R A ↔ fo
rall b : A, b * a = a * b
· 使用引理 `Algebra.IsCentral.center_eq_bot`：center_eq_bot : Subalgebra.center K D =
 ⊥
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem conjStarAlgAut_ext_iff {S : Type*} [CommSemiring S] [Algebra S R] [Algebra.IsCentral S R]
    (u v : unitary R) : conjStarAlgAut S R u = conjStarAlgAut S R v ↔ ∃ α : S, (u : R) = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm,
    mul_one, eq_comm]
/-
**Unitary.conjStarAlgAut_ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：conjStarAlgAut_ext_iff' {R S : Type*} [Ring R] [StarMul R] [CommRing S] [S
tarMul S] [Algebra S R] [StarModule S R] [Algebra.IsCentral S R] [IsCancelMulZer
o S] [Module.IsTorsionFree S R] (u v : unitary R) : conjStarAlgAut S R u = conjS
tarAlgAut S R v ↔ exists α : unitary S, u = α • v
参数：u v : unitary R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.mem_center_iff`：mem_center_iff {a : A} : a in center R A ↔ fo
rall b : A, b * a = a * b
· 使用引理 `Algebra.IsCentral.center_eq_bot`：center_eq_bot : Subalgebra.center K D =
 ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Unitary.val_inv_toUnits_apply`：∀ {R : Type u_1} [inst : Monoid R] [inst_
1 : StarMul R] (x : ↥(unitary R)), ↑(Unitary.toUnits x)⁻¹ = ↑x⁻¹
· 使用定理 `Unitary.val_toUnits_apply`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] (x : ↥(unitary R)), ↑(Unitary.toUnits x) = ↑x
· 使用定理 `Unitary.mul_star_self_of_mem`：mul_star_self_of_mem {U : R} (hU : U in un
itary R) : U * star U = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 36 条，此处仅展示前 30 条）
-/
theorem conjStarAlgAut_ext_iff' {R S : Type*} [Ring R] [StarMul R] [CommRing S] [StarMul S]
    [Algebra S R] [StarModule S R] [Algebra.IsCentral S R] [IsCancelMulZero S]
    [Module.IsTorsionFree S R] (u v : unitary R) :
    conjStarAlgAut S R u = conjStarAlgAut S R v ↔ ∃ α : unitary S, u = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, val_inv_toUnits_apply, val_toUnits_apply,
    ← star_eq_inv, coe_star]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : S), by
    simp only [h, coe_smul, mul_smul_comm, SetLike.coe_mem, star_mul_self_of_mem]; rfl⟩⟩
  have huv : (u : R) = y • (v : R) := by simpa [← mul_assoc] using congr(v * $h).symm
  have hvu : (v : R) = star y • (u : R) := by simpa [← mul_assoc] using congr(u * (star $h)).symm
  have hvy : (v : R) = (star y * y) • (v : R) := by simp [← smul_smul, ← huv, ← hvu]
  nth_rw 1 [← one_smul S (v : R)] at hvy
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, eq_comm] at hvy
  obtain (this | this) := hvy
  · exact ⟨⟨y, by simp [mem_iff, this, mul_comm y]⟩, by ext; exact huv⟩
  · exact ⟨1, by ext; simp [this, huv] at huv ⊢⟩

end Unitary

