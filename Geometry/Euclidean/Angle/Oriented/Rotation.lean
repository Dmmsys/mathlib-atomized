/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `Orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

-/

@[expose] public section


noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}
variable [NormedAddCommGroup V] [NormedAddCommGroup V']
variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']
variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "J" => o.rightAngleRotation

/-- Auxiliary construction to build a rotation by the oriented angle `θ`. -/
/-
**Orientation.rotationAux** 是 Mathlib 中的一个定义，位于命名空间 `Orientation`。
形式化陈述：rotationAux (θ : Real.Angle) : V ->ₗᵢ[Real] V
参数：θ : Real.Angle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction to build a rotation by the oriented angle `θ`.
-/
def rotationAux (θ : Real.Angle) : V →ₗᵢ[ℝ] V :=
  LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left,
        Orientation.inner_rightAngleRotation_right, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right]
      linear_combination ⟪x, y⟫ * θ.cos_sq_add_sin_sq)

@[simp]
/-
**Orientation.rotationAux_apply** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotationAux_apply (θ : Real.Angle) (x : V) : o.rotationAux θ x = Real.Angl
e.cos θ • x + Real.Angle.sin θ • J x
参数：θ : Real.Angle；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotationAux_apply (θ : Real.Angle) (x : V) :
    o.rotationAux θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

/-- A rotation by the oriented angle `θ`. -/
/-
**Orientation.rotation** 是 Mathlib 中的一个定义，位于命名空间 `Orientation`。
形式化陈述：rotation (θ : Real.Angle) : V ≃ₗᵢ[Real] V
参数：θ : Real.Angle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rotation by the oriented angle `θ`.
-/
def rotation (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      convert! congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_smul, map_sub, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)
    (by
      ext x
      convert! congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_add, map_smul, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)
/-
**Orientation.rotation_apply** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_apply (θ : Real.Angle) (x : V) : o.rotation θ x = Real.Angle.cos 
θ • x + Real.Angle.sin θ • J x
参数：θ : Real.Angle；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotation_apply (θ : Real.Angle) (x : V) :
    o.rotation θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl
/-
**Orientation.rotation_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_symm_apply (θ : Real.Angle) (x : V) : (o.rotation θ).symm x = Rea
l.Angle.cos θ • x - Real.Angle.sin θ • J x
参数：θ : Real.Angle；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotation_symm_apply (θ : Real.Angle) (x : V) :
    (o.rotation θ).symm x = Real.Angle.cos θ • x - Real.Angle.sin θ • J x :=
  rfl
/-
**Orientation.rotation_eq_matrix_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_eq_matrix_toLin (θ : Real.Angle) {x : V} (hx : x != 0) : (o.rotat
ion θ).toLinearMap = Matrix.toLin (o.basisRightAngleRotation x hx) (o.basisRight
AngleRotation x hx) !![θ.cos, -θ.sin; θ.sin, θ.cos]
参数：θ : Real.Angle；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Orientation.coe_basisRightAngleRotation`：coe_basisRightAngleRotation (x 
: E) (hx : x != 0) : ⇑(o.basisRightAngleRotation x hx) = ![x, J x]
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Orientation.rightAngleRotation_rightAngleRotation`：rightAngleRotation_ri
ghtAngleRotation (x : E) : J (J x) = -x
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
（共 32 条，此处仅展示前 30 条）
-/
theorem rotation_eq_matrix_toLin (θ : Real.Angle) {x : V} (hx : x ≠ 0) :
    (o.rotation θ).toLinearMap =
      Matrix.toLin (o.basisRightAngleRotation x hx) (o.basisRightAngleRotation x hx)
        !![θ.cos, -θ.sin; θ.sin, θ.cos] := by
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  fin_cases i
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ]
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ, add_comm]

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
/-
**Orientation.det_rotation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：det_rotation (θ : Real.Angle) : LinearMap.det (o.rotation θ).toLinearMap =
 1
参数：θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_eq_succ`：Module.nontrivial_of_finrank_eq_su
cc {n : Nat} (hn : finrank R M = n.succ) : Nontrivial M
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.rotation_eq_matrix_toLin`：rotation_eq_matrix_toLin (θ : Real
.Angle) {x : V} (hx : x != 0) : (o.rotation θ).toLinearMap = Matrix.toLin (o.bas
isRightAngleRotation x hx)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.det_toLin`：det_toLin (b : Basis ι R M) (f : Matrix ι ι R) : Li
nearMap.det (Matrix.toLin b b f) = f.det
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.Angle.cos_sq_add_sin_sq`：cos_sq_add_sin_sq (θ : Real.Angle) : cos θ
 ^ 2 + sin θ ^ 2 = 1

--- 原说明 ---
The determinant of `rotation` (as a linear map) is equal to `1`.
-/
theorem det_rotation (θ : Real.Angle) : LinearMap.det (o.rotation θ).toLinearMap = 1 := by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  rw [o.rotation_eq_matrix_toLin θ hx]
  simpa [sq] using θ.cos_sq_add_sin_sq

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
/-
**Orientation.linearEquiv_det_rotation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：linearEquiv_det_rotation (θ : Real.Angle) : LinearEquiv.det (o.rotation θ)
.toLinearEquiv = 1
参数：θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Orientation.det_rotation`：det_rotation (θ : Real.Angle) : LinearMap.det 
(o.rotation θ).toLinearMap = 1

--- 原说明 ---
The determinant of `rotation` (as a linear equiv) is equal to `1`.
-/
theorem linearEquiv_det_rotation (θ : Real.Angle) :
    LinearEquiv.det (o.rotation θ).toLinearEquiv = 1 :=
  Units.ext <| by
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp]
/-
**Orientation.rotation_symm** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ)
参数：θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.cos_neg`：cos_neg (θ : Angle) : cos (-θ) = cos θ
· 使用定理 `Real.Angle.sin_neg`：sin_neg (θ : Angle) : sin (-θ) = -sin θ
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inverse of `rotation` is rotation by the negation of the angle.
-/
theorem rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ) := by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

/-- Rotation by 0 is the identity. -/
@[simp]
/-
**Orientation.rotation_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl Real V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.Angle.cos_zero`：cos_zero : cos (0 : Angle) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Real.Angle.sin_zero`：sin_zero : sin (0 : Angle) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LinearIsometryEquiv.ofLinearIsometry.congr_simp`：∀ {R : Type u_1} {R₂ : 
Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring 
R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rotation by 0 is the identity.
-/
theorem rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl ℝ V := by ext; simp [rotation]

/-- Rotation by π is negation. -/
@[simp]
/-
**Orientation.rotation_pi** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_pi : o.rotation π = LinearIsometryEquiv.neg Real
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.cos_pi`：cos_pi : cos π = -1
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Real.sin_pi`：sin_pi : sin π = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LinearIsometryEquiv.ofLinearIsometry.congr_simp`：∀ {R : Type u_1} {R₂ : 
Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring 
R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rotation by π is negation.
-/
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg ℝ := by
  ext x
  simp [rotation]

/-- Rotation by π is negation. -/
/-
**Orientation.rotation_pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_pi_apply (x : V) : o.rotation π x = -x
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.rotation_pi`：rotation_pi : o.rotation π = LinearIsometryEqui
v.neg Real
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rotation by π is negation.
-/
theorem rotation_pi_apply (x : V) : o.rotation π x = -x := by simp

/-- Rotation by π / 2 is the "right-angle-rotation" map `J`. -/
/-
**Orientation.rotation_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_pi_div_two : o.rotation (π / 2 : Real) = J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.cos_pi_div_two`：cos_pi_div_two : cos (π / 2) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `LinearIsometryEquiv.ofLinearIsometry.congr_simp`：∀ {R : Type u_1} {R₂ : 
Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring 
R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rotation by π / 2 is the "right-angle-rotation" map `J`.
-/
theorem rotation_pi_div_two : o.rotation (π / 2 : ℝ) = J := by
  ext x
  simp [rotation]

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
/-
**Orientation.rotation_rotation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_rotation (θ₁ θ₂ : Real.Angle) (x : V) : o.rotation θ₁ (o.rotation
 θ₂ x) = o.rotation (θ₁ + θ₂) x
参数：θ₁ θ₂ : Real.Angle；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Orientation.rightAngleRotation_rightAngleRotation`：rightAngleRotation_ri
ghtAngleRotation (x : E) : J (J x) = -x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.cos_add`：cos_add (θ₁ θ₂ : Real.Angle) : cos (θ₁ + θ₂) = cos θ
₁ * cos θ₂ - sin θ₁ * sin θ₂
· 使用定理 `Real.Angle.sin_add`：sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ
₁ * cos θ₂ + cos θ₁ * sin θ₂
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Rotating twice is equivalent to rotating by the sum of the angles.
-/
theorem rotation_rotation (θ₁ θ₂ : Real.Angle) (x : V) :
    o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x := by
  simp only [o.rotation_apply, Real.Angle.cos_add, Real.Angle.sin_add, map_add,
    map_smul, rightAngleRotation_rightAngleRotation]
  module

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
/-
**Orientation.rotation_trans** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_trans (θ₁ θ₂ : Real.Angle) : (o.rotation θ₁).trans (o.rotation θ₂
) = o.rotation (θ₂ + θ₁)
参数：θ₁ θ₂ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.rotation_rotation`：rotation_rotation (θ₁ θ₂ : Real.Angle) (x
 : V) : o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x
· 使用定理 `LinearIsometryEquiv.trans_apply`：trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ :
 E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) : (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c)

--- 原说明 ---
Rotating twice is equivalent to rotating by the sum of the angles.
-/
theorem rotation_trans (θ₁ θ₂ : Real.Angle) :
    (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
  LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]

/-- Rotating the first of two vectors by `θ` scales their Kähler form by `cos θ - sin θ * I`. -/
@[simp]
/-
**Orientation.kahler_rotation_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：kahler_rotation_left (x y : V) (θ : Real.Angle) : o.kahler (o.rotation θ x
) y = conj (θ.toCircle : Complex) * o.kahler x y
参数：x y : V；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Orientation.kahler_rightAngleRotation_left`：kahler_rightAngleRotation_le
ft (x y : E) : o.kahler (J x) y = -Complex.I * o.kahler x y
· 使用引理 `Real.Angle.coe_toCircle`：coe_toCircle (θ : Angle) : (θ.toCircle : Comple
x) = θ.cos + θ.sin * I
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Rotating the first of two vectors by `θ` scales their Kähler form by `cos θ - si
n θ * I`.
-/
theorem kahler_rotation_left (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = conj (θ.toCircle : ℂ) * o.kahler x y := by
  simp only [o.rotation_apply, map_add, map_mul, map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_toCircle, Complex.conj_ofReal, conj_I]
  ring

/-- Negating a rotation is equivalent to rotation by π plus the angle. -/
/-
**Orientation.neg_rotation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：neg_rotation (θ : Real.Angle) (x : V) : -o.rotation θ x = o.rotation (π + 
θ) x
参数：θ : Real.Angle；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.rotation_pi_apply`：rotation_pi_apply (x : V) : o.rotation π 
x = -x
· 使用定理 `Orientation.rotation_rotation`：rotation_rotation (θ₁ θ₂ : Real.Angle) (x
 : V) : o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x

--- 原说明 ---
Negating a rotation is equivalent to rotation by π plus the angle.
-/
theorem neg_rotation (θ : Real.Angle) (x : V) : -o.rotation θ x = o.rotation (π + θ) x := by
  rw [← o.rotation_pi_apply, rotation_rotation]

/-- Negating a rotation by -π / 2 is equivalent to rotation by π / 2. -/
@[simp]
/-
**Orientation.neg_rotation_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Orientation
`。
形式化陈述：neg_rotation_neg_pi_div_two (x : V) : -o.rotation (-π / 2 : Real) x = o.ro
tation (π / 2 : Real) x
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.neg_rotation`：neg_rotation (θ : Real.Angle) (x : V) : -o.rot
ation θ x = o.rotation (π + θ) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `sub_half`：sub_half (a : K) : a - a / 2 = a / 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
Negating a rotation by -π / 2 is equivalent to rotation by π / 2.
-/
theorem neg_rotation_neg_pi_div_two (x : V) :
    -o.rotation (-π / 2 : ℝ) x = o.rotation (π / 2 : ℝ) x := by
  rw [neg_rotation, ← Real.Angle.coe_add, neg_div, ← sub_eq_add_neg, sub_half]

/-- Negating a rotation by π / 2 is equivalent to rotation by -π / 2. -/
/-
**Orientation.neg_rotation_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : Real) x = o.rotatio
n (-π / 2 : Real) x
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Orientation.neg_rotation_neg_pi_div_two`：neg_rotation_neg_pi_div_two (x 
: V) : -o.rotation (-π / 2 : Real) x = o.rotation (π / 2 : Real) x

--- 原说明 ---
Negating a rotation by π / 2 is equivalent to rotation by -π / 2.
-/
theorem neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : ℝ) x = o.rotation (-π / 2 : ℝ) x :=
  (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm

/-- Rotating the first of two vectors by `θ` scales their Kähler form by `cos (-θ) + sin (-θ) * I`.
-/
/-
**Orientation.kahler_rotation_left'** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：kahler_rotation_left' (x y : V) (θ : Real.Angle) : o.kahler (o.rotation θ 
x) y = (-θ).toCircle * o.kahler x y
参数：x y : V；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.kahler_rotation_left`：kahler_rotation_left (x y : V) (θ : Re
al.Angle) : o.kahler (o.rotation θ x) y = conj (θ.toCircle : Complex) * o.kahler
 x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.toCircle_neg`：∀ (θ : Real.Angle), (-θ).toCircle = θ.toCircle⁻
¹
· 使用引理 `Circle.coe_inv_eq_conj`：coe_inv_eq_conj (z : Circle) : ↑z⁻¹ = conj (z : 
Complex)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rotating the first of two vectors by `θ` scales their Kähler form by `cos (-θ) +
 sin (-θ) * I`.
-/
theorem kahler_rotation_left' (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = (-θ).toCircle * o.kahler x y := by
  simp only [Real.Angle.toCircle_neg, Circle.coe_inv_eq_conj, kahler_rotation_left]

/-- Rotating the second of two vectors by `θ` scales their Kähler form by `cos θ + sin θ * I`. -/
@[simp]
/-
**Orientation.kahler_rotation_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：kahler_rotation_right (x y : V) (θ : Real.Angle) : o.kahler x (o.rotation 
θ y) = θ.toCircle * o.kahler x y
参数：x y : V；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Orientation.kahler_rightAngleRotation_right`：kahler_rightAngleRotation_r
ight (x y : E) : o.kahler x (J y) = Complex.I * o.kahler x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Real.Angle.coe_toCircle`：coe_toCircle (θ : Angle) : (θ.toCircle : Comple
x) = θ.cos + θ.sin * I
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b

--- 原说明 ---
Rotating the second of two vectors by `θ` scales their Kähler form by `cos θ + s
in θ * I`.
-/
theorem kahler_rotation_right (x y : V) (θ : Real.Angle) :
    o.kahler x (o.rotation θ y) = θ.toCircle * o.kahler x y := by
  simp only [o.rotation_apply, map_add, map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_toCircle]
  ring

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp]
/-
**Orientation.oangle_rotation_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_rotation_left {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real.Angle
) : o.oangle (o.rotation θ x) y = o.oangle x y - θ
参数：hx : x != 0；hy : y != 0；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.kahler_rotation_left'`：kahler_rotation_left' (x y : V) (θ : 
Real.Angle) : o.kahler (o.rotation θ x) y = (-θ).toCircle * o.kahler x y
· 使用定理 `Complex.arg_mul_coe_angle`：arg_mul_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x * y) : Real.Angle) = arg x + arg y
· 使用定理 `Circle.coe_ne_zero`：∀ (z : Circle), ↑z ≠ 0
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0
· 使用定理 `Real.Angle.arg_toCircle`：∀ (θ : Real.Angle), ↑(↑θ.toCircle).arg = θ
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation.0.Orientatio
n.oangle_rotation_left._abel_1_2`：∀ {V : Type u_1} [inst : NormedAddCommGroup V]
 [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)]   (o 
: Orientation …

--- 原说明 ---
Rotating the first vector by `θ` subtracts `θ` from the angle between two vector
s.
-/
theorem oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) y = o.oangle x y - θ := by
  simp only [oangle, o.kahler_rotation_left']
  rw [Complex.arg_mul_coe_angle, Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp]
/-
**Orientation.oangle_rotation_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_rotation_right {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real.Angl
e) : o.oangle x (o.rotation θ y) = o.oangle x y + θ
参数：hx : x != 0；hy : y != 0；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.kahler_rotation_right`：kahler_rotation_right (x y : V) (θ : 
Real.Angle) : o.kahler x (o.rotation θ y) = θ.toCircle * o.kahler x y
· 使用定理 `Complex.arg_mul_coe_angle`：arg_mul_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x * y) : Real.Angle) = arg x + arg y
· 使用定理 `Circle.coe_ne_zero`：∀ (z : Circle), ↑z ≠ 0
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0
· 使用定理 `Real.Angle.arg_toCircle`：∀ (θ : Real.Angle), ↑(↑θ.toCircle).arg = θ
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation.0.Orientatio
n.oangle_rotation_right._abel_1_2`：∀ {V : Type u_1} [inst : NormedAddCommGroup V
] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)]   (o
 : Orientation …

--- 原说明 ---
Rotating the second vector by `θ` adds `θ` to the angle between two vectors.
-/
theorem oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ y) = o.oangle x y + θ := by
  simp only [oangle, o.kahler_rotation_right]
  rw [Complex.arg_mul_coe_angle, Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
/-
**Orientation.oangle_rotation_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_rotation_self_left {x : V} (hx : x != 0) (θ : Real.Angle) : o.oangl
e (o.rotation θ x) x = -θ
参数：hx : x != 0；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rotation_left`：oangle_rotation_left {x y : V} (hx : x
 != 0) (hy : y != 0) (θ : Real.Angle) : o.oangle (o.rotation θ x) y = o.oangle x
 y - θ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rotation of a vector by `θ` has an angle of `-θ` from that vector.
-/
theorem oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) x = -θ := by simp [hx]

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
/-
**Orientation.oangle_rotation_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：oangle_rotation_self_right {x : V} (hx : x != 0) (θ : Real.Angle) : o.oang
le x (o.rotation θ x) = θ
参数：hx : x != 0；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rotation_right`：oangle_rotation_right {x y : V} (hx :
 x != 0) (hy : y != 0) (θ : Real.Angle) : o.oangle x (o.rotation θ y) = o.oangle
 x y + θ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A vector has an angle of `θ` from the rotation of that vector by `θ`.
-/
theorem oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ x) = θ := by simp [hx]

/-- Rotating the first vector by the angle between the two vectors results in an angle of 0. -/
@[simp]
/-
**Orientation.oangle_rotation_oangle_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation
`。
形式化陈述：oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y
) x) y = 0
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Orientation.rotation.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommG
roup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)
]   (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Orientation.rotation_zero`：rotation_zero : o.rotation 0 = LinearIsometry
Equiv.refl Real V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Orientation.oangle_rotation_left`：oangle_rotation_left {x y : V} (hx : x
 != 0) (hy : y != 0) (θ : Real.Angle) : o.oangle (o.rotation θ x) y = o.oangle x
 y - θ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Rotating the first vector by the angle between the two vectors results in an ang
le of 0.
-/
theorem oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [hx, hy]

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results in an angle of 0. -/
@[simp]
/-
**Orientation.oangle_rotation_oangle_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle 
x y) x) = 0
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle_rotation_oangle_left`：oangle_rotation_oangle_left (x 
y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rotating the first vector by the angle between the two vectors and swapping the 
vectors
results in an angle of 0.
-/
theorem oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle x y) x) = 0 := by
  rw [oangle_rev]
  simp

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp]
/-
**Orientation.oangle_rotation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_rotation (x y : V) (θ : Real.Angle) : o.oangle (o.rotation θ x) (o.
rotation θ y) = o.oangle x y
参数：x y : V；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle_rotation_right`：oangle_rotation_right {x y : V} (hx :
 x != 0) (hy : y != 0) (θ : Real.Angle) : o.oangle x (o.rotation θ y) = o.oangle
 x y + θ
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.oangle_rotation_left`：oangle_rotation_left {x y : V} (hx : x
 != 0) (hy : y != 0) (θ : Real.Angle) : o.oangle (o.rotation θ x) y = o.oangle x
 y - θ
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
Rotating both vectors by the same angle does not change the angle between those 
vectors.
-/
theorem oangle_rotation (x y : V) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp]
/-
**Orientation.rotation_eq_self_iff_angle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orie
ntation`。
形式化陈述：rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x != 0) (θ : Real.Angle) 
: o.rotation θ x = x ↔ θ = 0
参数：hx : x != 0；θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Orientation.oangle_rotation_right`：oangle_rotation_right {x y : V} (hx :
 x != 0) (hy : y != 0) (θ : Real.Angle) : o.oangle x (o.rotation θ y) = o.oangle
 x y + θ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Orientation.rotation.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommG
roup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)
]   (o o_1 : Orientat…
· 使用定理 `Orientation.rotation_zero`：rotation_zero : o.rotation 0 = LinearIsometry
Equiv.refl Real V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A rotation of a nonzero vector equals that vector if and only if the angle is ze
ro.
-/
theorem rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.rotation θ x = x ↔ θ = 0 := by
  constructor
  · intro h
    rw [eq_comm]
    simpa [hx, h] using o.oangle_rotation_right hx hx θ
  · intro h
    simp [h]

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp]
/-
**Orientation.eq_rotation_self_iff_angle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orie
ntation`。
形式化陈述：eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x != 0) (θ : Real.Angle) 
: x = o.rotation θ x ↔ θ = 0
参数：hx : x != 0；θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.rotation_eq_self_iff_angle_eq_zero`：rotation_eq_self_iff_ang
le_eq_zero {x : V} (hx : x != 0) (θ : Real.Angle) : o.rotation θ x = x ↔ θ = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A nonzero vector equals a rotation of that vector if and only if the angle is ze
ro.
-/
theorem eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    x = o.rotation θ x ↔ θ = 0 := by rw [← o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
/-
**Orientation.rotation_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0
 ∨ θ = 0
参数：x : V；θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
A rotation of a vector equals that vector if and only if the vector or the angle
 is zero.
-/
theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0 := by
  by_cases h : x = 0 <;> simp [h]

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
/-
**Orientation.eq_rotation_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0
 ∨ θ = 0
参数：x : V；θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.rotation_eq_self_iff`：rotation_eq_self_iff (x : V) (θ : Real
.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A vector equals a rotation of that vector if and only if the vector or the angle
 is zero.
-/
theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0 ∨ θ = 0 := by
  rw [← rotation_eq_self_iff, eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp]
/-
**Orientation.rotation_oangle_eq_iff_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y
 ↔ ‖x‖ = ‖y‖
参数：x y : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `Orientation.eq_iff_oangle_eq_zero_of_norm_eq`：eq_iff_oangle_eq_zero_of_n
orm_eq {x y : V} (h : ‖x‖ = ‖y‖) : x = y ↔ o.oangle x y = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_rotation_oangle_left`：oangle_rotation_oangle_left (x 
y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0

--- 原说明 ---
Rotating a vector by the angle to another vector gives the second vector if and 
only if the
norms are equal.
-/
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖ := by
  constructor
  · intro h
    rw [← h, LinearIsometryEquiv.norm_map]
  · intro h
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
/-
**Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero** 是 Mathli
b 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x 
!= 0) (hy : y != 0) (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖ / ‖x‖) • o.ro
tation θ x
参数：hx : x != 0；hy : y != 0；θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Orientation.rotation_oangle_eq_iff_norm_eq`：rotation_oangle_eq_iff_norm_
eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `Orientation.oangle_rotation_self_right`：oangle_rotation_self_right {x : 
V} (hx : x != 0) (θ : Real.Angle) : o.oangle x (o.rotation θ x) = θ

--- 原说明 ---
The angle between two nonzero vectors is `θ` if and only if the second vector is
 the first
rotated by `θ` and scaled by the ratio of the norms.
-/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖ / ‖x‖) • o.rotation θ x := by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  constructor
  · rintro rfl
    rw [← map_smul, ← o.oangle_smul_left_of_pos x y hp, eq_comm,
      rotation_oangle_eq_iff_norm_eq, norm_smul, Real.norm_of_nonneg hp.le,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  · intro hye
    rw [hye, o.oangle_smul_right_of_pos _ _ hp, o.oangle_rotation_self_right hx]

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
/-
**Orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero** 是 Mathlib 中的一个定理，位
于命名空间 `Orientation`。
形式化陈述：oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x != 0) (hy 
: y != 0) (θ : Real.Angle) : o.oangle x y = θ ↔ exists r : Real, 0 < r ∧ y = r •
 o.rotation θ x
参数：hx : x != 0；hy : y != 0；θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero`：oan
gle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x != 0) (hy
 : y != 0) (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖…
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `Orientation.oangle_rotation_self_right`：oangle_rotation_self_right {x : 
V} (hx : x != 0) (θ : Real.Angle) : o.oangle x (o.rotation θ x) = θ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The angle between two nonzero vectors is `θ` if and only if the second vector is
 the first
rotated by `θ` and scaled by a positive real.
-/
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x := by
  constructor
  · intro h
    rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
  · rintro ⟨r, hr, rfl⟩
    rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx]

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
/-
**Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero** 是 Mathli
b 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Rea
l.Angle) : o.oangle x y = θ ↔ x != 0 ∧ y != 0 ∧ y = (‖y‖ / ‖x‖) • o.rotation θ x
 ∨ θ = 0 ∧ (x = 0 ∨ y = 0)
参数：θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero`：oan
gle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x != 0) (hy
 : y != 0) (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The angle between two vectors is `θ` if and only if they are nonzero and the sec
ond vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at 
least one of the
vectors are zero.
-/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • o.rotation θ x ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
/-
**Orientation.oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `Orientation`。
形式化陈述：oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
 o.oangle x y = θ ↔ (x != 0 ∧ y != 0 ∧ exists r : Real, 0 < r ∧ y = r • o.rotati
on θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0)
参数：θ : Real.Angle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero`：oangle_eq_iff
_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real
.Angle) : o.oangle x y = θ ↔ exists r : Real, 0…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The angle between two vectors is `θ` if and only if they are nonzero and the sec
ond vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least o
ne of the
vectors are zero.
-/
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
/-
**Orientation.exists_linearIsometryEquiv_eq_of_det_pos** 是 Mathlib 中的一个定理，位于命名空间
 `Orientation`。
形式化陈述：exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[Real] V} (hd : 0 < Lin
earMap.det (f.toLinearEquiv : V ->ₗ[Real] V)) : exists θ : Real.Angle, f = o.rot
ation θ
参数：hd : 0 < LinearMap.det (f.toLinearEquiv : V ->ₗ[Real] V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_eq_succ`：Module.nontrivial_of_finrank_eq_su
cc {n : Nat} (hn : finrank R M = n.succ) : Nontrivial M
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `LinearIsometryEquiv.toLinearEquiv_injective`：∀ {R : Type u_1} {R₂ : Type
 u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂] 
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Orientation.coe_basisRightAngleRotation`：coe_basisRightAngleRotation (x 
: E) (hx : x != 0) : ⇑(o.basisRightAngleRotation x hx) = ![x, J x]
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.linearIsometryEquiv_comp_rightAngleRotation`：linearIsometryE
quiv_comp_rightAngleRotation (φ : E ≃ₗᵢ[Real] E) (hφ : 0 < LinearMap.det (φ.toLi
nearEquiv : E ->ₗ[Real] E)) (x : E) : φ (J x)…
· 使用定理 `Orientation.kahler_comp_rightAngleRotation`：kahler_comp_rightAngleRotati
on (x y : E) : o.kahler (J x) (J y) = o.kahler x y
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Any linear isometric equivalence in `V` with positive determinant is `rotation`.
-/
theorem exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < LinearMap.det (f.toLinearEquiv : V →ₗ[ℝ] V)) :
    ∃ θ : Real.Angle, f = o.rotation θ := by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  use o.oangle x (f x)
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  symm
  fin_cases i
  · simp
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x) := by
    simp only [oangle, o.linearIsometryEquiv_comp_rightAngleRotation f hd,
      o.kahler_comp_rightAngleRotation]
  simp [← this]
/-
**Orientation.rotation_map** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[Real] V') (x : V') : (Orientation
.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.rotation θ (f.symm x))
参数：θ : Real.Angle；f : V ≃ₗᵢ[Real] V'；x : V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.rightAngleRotation_map`：rightAngleRotation_map {F : Type*} [
NormedAddCommGroup F] [InnerProductSpace Real F] [hF : Fact (finrank Real F = 2)
] (φ : E ≃ₗᵢ[Real] F) (x…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] V') (x : V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.rotation θ (f.symm x)) := by
  simp [rotation_apply, o.rightAngleRotation_map]

@[simp]
/-
**Orientation._root_.Complex.rotation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Complex.rotation (θ : Real.Angle) (z : ℂ) :
    Complex.orientation.rotation θ z = θ.toCircle * z := by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_toCircle, real_smul]
  ring

/-- Rotation in an oriented real inner product space of dimension 2 can be evaluated in terms of a
complex-number representation of the space. -/
/-
**Orientation.rotation_map_complex** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：rotation_map_complex (θ : Real.Angle) (f : V ≃ₗᵢ[Real] Complex) (hf : Orie
ntation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) : f (o.rota
tion θ x) = θ.toCircle * f x
参数：θ : Real.Angle；f : V ≃ₗᵢ[Real] Complex；hf : Orientation.map (Fin 2) f.toLinea
rEquiv o = Complex.orientation；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.finrank_real_complex_fact`：finrank_real_complex_fact : Fact (fin
rank Real Complex = 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.rotation`：∀ (θ : Real.Angle) (z : ℂ), (Complex.orientation.rotat
ion θ) z = ↑θ.toCircle * z
· 使用定理 `Orientation.rotation_map`：rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[Real]
 V') (x : V') : (Orientation.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.
rotation θ (f.…
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x

--- 原说明 ---
Rotation in an oriented real inner product space of dimension 2 can be evaluated
 in terms of a
complex-number representation of the space.
-/
theorem rotation_map_complex (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) :
    f (o.rotation θ x) = θ.toCircle * f x := by
  rw [← Complex.rotation, ← hf, o.rotation_map, LinearIsometryEquiv.symm_apply_apply]

/-- Negating the orientation negates the angle in `rotation`. -/
/-
**Orientation.rotation_neg_orientation_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rot
ation (-θ)
参数：θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.rightAngleRotation_trans_neg_orientation`：rightAngleRotation
_trans_neg_orientation : (-o).rightAngleRotation = o.rightAngleRotation.trans (L
inearIsometryEquiv.neg Real)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Real.Angle.cos_neg`：cos_neg (θ : Angle) : cos (-θ) = cos θ
· 使用定理 `Real.Angle.sin_neg`：sin_neg (θ : Angle) : sin (-θ) = -sin θ
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Negating the orientation negates the angle in `rotation`.
-/
theorem rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ) :=
  LinearIsometryEquiv.ext <| by simp [rotation_apply]

/-- The inner product between a `π / 2` rotation of a vector and that vector is zero. -/
@[simp]
/-
**Orientation.inner_rotation_pi_div_two_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : Real) x, x⟫ 
= 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.rotation_pi_div_two`：rotation_pi_div_two : o.rotation (π / 2
 : Real) = J
· 使用定理 `Orientation.inner_rightAngleRotation_self`：inner_rightAngleRotation_self
 (x : E) : ⟪J x, x⟫ = 0

--- 原说明 ---
The inner product between a `π / 2` rotation of a vector and that vector is zero
.
-/
theorem inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [rotation_pi_div_two, inner_rightAngleRotation_self]

/-- The inner product between a vector and a `π / 2` rotation of that vector is zero. -/
@[simp]
/-
**Orientation.inner_rotation_pi_div_two_right** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : Real) x⟫
 = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Orientation.inner_rotation_pi_div_two_left`：inner_rotation_pi_div_two_le
ft (x : V) : ⟪o.rotation (π / 2 : Real) x, x⟫ = 0

--- 原说明 ---
The inner product between a vector and a `π / 2` rotation of that vector is zero
.
-/
theorem inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and that vector is
zero. -/
@[simp]
/-
**Orientation.inner_smul_rotation_pi_div_two_left** 是 Mathlib 中的一个定理，位于命名空间 `Ori
entation`。
形式化陈述：inner_smul_rotation_pi_div_two_left (x : V) (r : Real) : ⟪r • o.rotation (
π / 2 : Real) x, x⟫ = 0
参数：x : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `Orientation.inner_rotation_pi_div_two_left`：inner_rotation_pi_div_two_le
ft (x : V) : ⟪o.rotation (π / 2 : Real) x, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
The inner product between a multiple of a `π / 2` rotation of a vector and that 
vector is
zero.
-/
theorem inner_smul_rotation_pi_div_two_left (x : V) (r : ℝ) :
    ⟪r • o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [inner_smul_left, inner_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a vector and a multiple of a `π / 2` rotation of that vector is
zero. -/
@[simp]
/-
**Orientation.inner_smul_rotation_pi_div_two_right** 是 Mathlib 中的一个定理，位于命名空间 `Or
ientation`。
形式化陈述：inner_smul_rotation_pi_div_two_right (x : V) (r : Real) : ⟪x, r • o.rotati
on (π / 2 : Real) x⟫ = 0
参数：x : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Orientation.inner_smul_rotation_pi_div_two_left`：inner_smul_rotation_pi_
div_two_left (x : V) (r : Real) : ⟪r • o.rotation (π / 2 : Real) x, x⟫ = 0

--- 原说明 ---
The inner product between a vector and a multiple of a `π / 2` rotation of that 
vector is
zero.
-/
theorem inner_smul_rotation_pi_div_two_right (x : V) (r : ℝ) :
    ⟪x, r • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_left]

/-- The inner product between a `π / 2` rotation of a vector and a multiple of that vector is
zero. -/
@[simp]
/-
**Orientation.inner_rotation_pi_div_two_left_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ori
entation`。
形式化陈述：inner_rotation_pi_div_two_left_smul (x : V) (r : Real) : ⟪o.rotation (π / 
2 : Real) x, r • x⟫ = 0
参数：x : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Orientation.inner_rotation_pi_div_two_left`：inner_rotation_pi_div_two_le
ft (x : V) : ⟪o.rotation (π / 2 : Real) x, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
The inner product between a `π / 2` rotation of a vector and a multiple of that 
vector is
zero.
-/
theorem inner_rotation_pi_div_two_left_smul (x : V) (r : ℝ) :
    ⟪o.rotation (π / 2 : ℝ) x, r • x⟫ = 0 := by
  rw [inner_smul_right, inner_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a multiple of a vector and a `π / 2` rotation of that vector is
zero. -/
@[simp]
/-
**Orientation.inner_rotation_pi_div_two_right_smul** 是 Mathlib 中的一个定理，位于命名空间 `Or
ientation`。
形式化陈述：inner_rotation_pi_div_two_right_smul (x : V) (r : Real) : ⟪r • x, o.rotati
on (π / 2 : Real) x⟫ = 0
参数：x : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Orientation.inner_rotation_pi_div_two_left_smul`：inner_rotation_pi_div_t
wo_left_smul (x : V) (r : Real) : ⟪o.rotation (π / 2 : Real) x, r • x⟫ = 0

--- 原说明 ---
The inner product between a multiple of a vector and a `π / 2` rotation of that 
vector is
zero.
-/
theorem inner_rotation_pi_div_two_right_smul (x : V) (r : ℝ) :
    ⟪r • x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left_smul]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and a multiple of
that vector is zero. -/
@[simp]
/-
**Orientation.inner_smul_rotation_pi_div_two_smul_left** 是 Mathlib 中的一个定理，位于命名空间
 `Orientation`。
形式化陈述：inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : Real) : ⟪r₁ • o.
rotation (π / 2 : Real) x, r₂ • x⟫ = 0
参数：x : V；r₁ r₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Orientation.inner_smul_rotation_pi_div_two_left`：inner_smul_rotation_pi_
div_two_left (x : V) (r : Real) : ⟪r • o.rotation (π / 2 : Real) x, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
The inner product between a multiple of a `π / 2` rotation of a vector and a mul
tiple of
that vector is zero.
-/
theorem inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : ℝ) :
    ⟪r₁ • o.rotation (π / 2 : ℝ) x, r₂ • x⟫ = 0 := by
  rw [inner_smul_right, inner_smul_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a multiple of a vector and a multiple of a `π / 2` rotation of
that vector is zero. -/
@[simp]
/-
**Orientation.inner_smul_rotation_pi_div_two_smul_right** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : Real) : ⟪r₂ • x
, r₁ • o.rotation (π / 2 : Real) x⟫ = 0
参数：x : V；r₁ r₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Orientation.inner_smul_rotation_pi_div_two_smul_left`：inner_smul_rotatio
n_pi_div_two_smul_left (x : V) (r₁ r₂ : Real) : ⟪r₁ • o.rotation (π / 2 : Real) 
x, r₂ • x⟫ = 0

--- 原说明 ---
The inner product between a multiple of a vector and a multiple of a `π / 2` rot
ation of
that vector is zero.
-/
theorem inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : ℝ) :
    ⟪r₂ • x, r₁ • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_smul_left]

/-- The inner product between two vectors is zero if and only if the first vector is zero or
the second is a multiple of a `π / 2` rotation of that vector. -/
/-
**Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two** 是 Mathl
ib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} : ⟪x, y
⟫ = 0 ↔ x = 0 ∨ exists r : Real, r • o.rotation (π / 2 : Real) x = y
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero`：eq_zero_or_oangle_eq
_iff_inner_eq_zero {x y : V} : x = 0 ∨ y = 0 ∨ o.oangle x y = (π / 2 : Real) ∨ o
.oangle x y = (-π / 2 : Real) ↔ ⟪x, y⟫ =…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The inner product between two vectors is zero if and only if the first vector is
 zero or
the second is a multiple of a `π / 2` rotation of that vector.
-/
theorem inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} :
    ⟪x, y⟫ = 0 ↔ x = 0 ∨ ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) x = y := by
  by_cases! +distrib H : x = 0 ∨ y = 0
  · rcases H with (rfl | rfl) <;> simp
  simp only [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero, H, ← neg_smul, false_or,
    o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero H.1 H.2, ← o.neg_rotation_pi_div_two, smul_neg]
  constructor
  · grind
  · rintro ⟨r, rfl⟩
    rcases lt_trichotomy 0 r with (hr0 | rfl | hr0)
    · grind
    · simp_all
    · right
      use -r
      simp_all

end Orientation

