/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Isometry

/-!
# Isometric equivalences with respect to quadratic forms

## Main definitions

* `QuadraticForm.IsometryEquiv`: `LinearEquiv`s which map between two different quadratic forms
* `QuadraticForm.Equivalent`: propositional version of the above

## Main results

* `equivalent_weighted_sum_squares`: in finite dimensions, any quadratic form is equivalent to a
  parametrization of `QuadraticForm.weightedSumSquares`.
-/

@[expose] public section

open Module QuadraticMap

variable {ι R K M M₁ M₂ M₃ V N : Type*}

namespace QuadraticMap

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
         [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]

/-- An isometric equivalence between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
/-
**QuadraticMap.IsometryEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type u_2} →   {M₁ : Type u_5} →     {M₂ : Type u_6} →       {N : Type
 u_9} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid M₁] 
→             [inst_2 : AddCommMonoid M₂] →               [inst_3 : AddCommMonoi
d N] →                 [inst_4 : _root_.Module R M₁] →                   [inst_5
 : _root_.Module R M₂] →                     [inst_6 : _root_.Module R N] → Quad
raticMap R M₁ N → QuadraticMap R M₂ N → Type (max u_5 u_6)
参数：max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric equivalence between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over
 a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic f
orms.
-/
structure IsometryEquiv (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    extends M₁ ≃ₗ[R] M₂ where
  map_app' : ∀ m, Q₂ (toFun m) = Q₁ m

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometric equivalence between them:
a linear equivalence that transforms one quadratic form into the other. -/
/-
**QuadraticMap.Equivalent** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：Equivalent (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) : Prop
参数：Q₁ : QuadraticMap R M₁ N；Q₂ : QuadraticMap R M₂ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two quadratic forms over a ring `R` are equivalent
if there exists an isometric equivalence between them:
a linear equivalence that transforms one quadratic form into the other.
-/
def Equivalent (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) : Prop :=
  Nonempty (Q₁.IsometryEquiv Q₂)

namespace IsometryEquiv

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

/-
**QuadraticMap.IsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap.IsometryEq
uiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (Q₁.IsometryEquiv Q₂) M₁ M₂ where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual
/-
**QuadraticMap.IsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap.IsometryEq
uiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearEquivClass (Q₁.IsometryEquiv Q₂) R M₁ M₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv
/-
**QuadraticMap.IsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap.IsometryEq
uiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (Q₁.IsometryEquiv Q₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]
/-
**QuadraticMap.IsometryEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quadra
ticMap.IsometryEquiv`。
形式化陈述：coe_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f
参数：f : Q₁.IsometryEquiv Q₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f :=
  rfl

@[simp]
/-
**QuadraticMap.IsometryEquiv.map_app** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Iso
metryEquiv`。
形式化陈述：map_app (f : Q₁.IsometryEquiv Q₂) (m : M₁) : Q₂ (f m) = Q₁ m
参数：f : Q₁.IsometryEquiv Q₂；m : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.IsometryEquiv.map_app'`：∀ {R : Type u_2} {M₁ : Type u_5} {M
₂ : Type u_6} {N : Type u_9} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁]
   [inst_2 : AddCommMonoi…
-/
theorem map_app (f : Q₁.IsometryEquiv Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

/-- The identity isometric equivalence between a quadratic form and itself. -/
@[refl]
/-
**QuadraticMap.IsometryEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isomet
ryEquiv`。
形式化陈述：refl (Q : QuadraticMap R M N) : Q.IsometryEquiv Q
参数：Q : QuadraticMap R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isometric equivalence between a quadratic form and itself.
-/
def refl (Q : QuadraticMap R M N) : Q.IsometryEquiv Q :=
  { LinearEquiv.refl R M with map_app' := fun _ => rfl }

/-- The inverse isometric equivalence of an isometric equivalence between two quadratic forms. -/
@[symm]
/-
**QuadraticMap.IsometryEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isomet
ryEquiv`。
形式化陈述：symm (f : Q₁.IsometryEquiv Q₂) : Q₂.IsometryEquiv Q₁
参数：f : Q₁.IsometryEquiv Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse isometric equivalence of an isometric equivalence between two quadra
tic forms.
-/
def symm (f : Q₁.IsometryEquiv Q₂) : Q₂.IsometryEquiv Q₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by intro m; rw [← f.map_app]; congr; exact f.toLinearEquiv.apply_symm_apply m }

/-- The composition of two isometric equivalences between quadratic forms. -/
@[trans]
/-
**QuadraticMap.IsometryEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isome
tryEquiv`。
形式化陈述：trans (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) : Q₁.IsometryEqu
iv Q₃
参数：f : Q₁.IsometryEquiv Q₂；g : Q₂.IsometryEquiv Q₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two isometric equivalences between quadratic forms.
-/
def trans (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) : Q₁.IsometryEquiv Q₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro m; rw [← f.map_app, ← g.map_app]; rfl }

/-- Isometric equivalences are isometric maps -/
@[simps]
/-
**QuadraticMap.IsometryEquiv.toIsometry** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.
IsometryEquiv`。
形式化陈述：toIsometry (g : Q₁.IsometryEquiv Q₂) : Q₁ ->qᵢ Q₂ where toFun x
参数：g : Q₁.IsometryEquiv Q₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.IsometryEquiv.map_app'`：∀ {R : Type u_2} {M₁ : Type u_5} {M
₂ : Type u_6} {N : Type u_9} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁]
   [inst_2 : AddCommMonoi…

--- 原说明 ---
Isometric equivalences are isometric maps
-/
def toIsometry (g : Q₁.IsometryEquiv Q₂) : Q₁ →qᵢ Q₂ where
  toFun x := g x
  __ := g
/-
**QuadraticMap.IsometryEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Quadrat
icMap.IsometryEquiv`。
形式化陈述：∀ {R : Type u_2} {M₁ : Type u_5} {M₂ : Type u_6} {N : Type u_9} [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 
: AddCommMonoid N] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]  
 [inst_6 : _root_.Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂
 N} (f : Q₁.IsometryEquiv Q₂) (x : M₂),   f (f.symm x) = x
参数：f : Q₁.IsometryEquiv Q₂；x : M₂；f.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
@[simp] lemma apply_symm_apply (f : Q₁.IsometryEquiv Q₂) (x : M₂) : f (f.symm x) = x :=
  f.toEquiv.apply_symm_apply x
/-
**QuadraticMap.IsometryEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Quadrat
icMap.IsometryEquiv`。
形式化陈述：∀ {R : Type u_2} {M₁ : Type u_5} {M₂ : Type u_6} {N : Type u_9} [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 
: AddCommMonoid N] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]  
 [inst_6 : _root_.Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂
 N} (f : Q₁.IsometryEquiv Q₂) (x : M₁),   f.symm (f x) = x
参数：f : Q₁.IsometryEquiv Q₂；x : M₁；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
@[simp] lemma symm_apply_apply (f : Q₁.IsometryEquiv Q₂) (x : M₁) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x
/-
**QuadraticMap.IsometryEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticM
ap.IsometryEquiv`。
形式化陈述：symm_apply_eq (f : Q₁.IsometryEquiv Q₂) {x y} : f.symm x = y ↔ x = f y
参数：f : Q₁.IsometryEquiv Q₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (f : Q₁.IsometryEquiv Q₂) {x y} :
    f.symm x = y ↔ x = f y :=
  f.toEquiv.symm_apply_eq
/-
**QuadraticMap.IsometryEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticM
ap.IsometryEquiv`。
形式化陈述：eq_symm_apply (f : Q₁.IsometryEquiv Q₂) {x y} : y = f.symm x ↔ f y = x
参数：f : Q₁.IsometryEquiv Q₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (f : Q₁.IsometryEquiv Q₂) {x y} :
    y = f.symm x ↔ f y = x :=
  f.toEquiv.eq_symm_apply
/-
**QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Q
uadraticMap.IsometryEquiv`。
形式化陈述：∀ {R : Type u_2} {M₁ : Type u_5} {M₂ : Type u_6} {N : Type u_9} [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 
: AddCommMonoid N] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]  
 [inst_6 : _root_.Module R N] {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂
 N} (f : Q₁.IsometryEquiv Q₂),   f.symm = f.symm.toLinearEquiv
参数：f : Q₁.IsometryEquiv Q₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_symm_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) : f.toLinearEquiv.symm = f.symm :=
  rfl

end IsometryEquiv

namespace Equivalent

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

@[refl]
/-
**QuadraticMap.Equivalent.refl** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Equivalen
t`。
形式化陈述：refl (Q : QuadraticMap R M N) : Q.Equivalent Q
参数：Q : QuadraticMap R M N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (Q : QuadraticMap R M N) : Q.Equivalent Q :=
  ⟨IsometryEquiv.refl Q⟩

@[symm]
/-
**QuadraticMap.Equivalent.symm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Equivalen
t`。
形式化陈述：symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalent Q₁
参数：h : Q₁.Equivalent Q₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalent Q₁ :=
  h.elim fun f => ⟨f.symm⟩

@[trans]
/-
**QuadraticMap.Equivalent.trans** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Equivale
nt`。
形式化陈述：trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃
参数：h : Q₁.Equivalent Q₂；h' : Q₂.Equivalent Q₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃ :=
  h'.elim <| h.elim fun f g => ⟨f.trans g⟩

end Equivalent

/-- A quadratic form composed with a `LinearEquiv` is isometric to itself. -/
/-
**QuadraticMap.isometryEquivOfCompLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Quadrat
icMap`。
形式化陈述：isometryEquivOfCompLinearEquiv (Q : QuadraticMap R M N) (f : M₁ ≃ₗ[R] M) :
 Q.IsometryEquiv (Q.comp (f : M₁ ->ₗ[R] M))
参数：Q : QuadraticMap R M N；f : M₁ ≃ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quadratic form composed with a `LinearEquiv` is isometric to itself.
-/
def isometryEquivOfCompLinearEquiv (Q : QuadraticMap R M N) (f : M₁ ≃ₗ[R] M) :
    Q.IsometryEquiv (Q.comp (f : M₁ →ₗ[R] M)) :=
  { f.symm with
    map_app' := by
      intro
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

variable [Finite ι]

/-- A quadratic form is isometrically equivalent to its bases representations. -/
/-
**QuadraticMap.isometryEquivBasisRepr** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：isometryEquivBasisRepr (Q : QuadraticMap R M N) (v : Basis ι R M) : Isomet
ryEquiv Q (Q.basisRepr v)
参数：Q : QuadraticMap R M N；v : Basis ι R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quadratic form is isometrically equivalent to its bases representations.
-/
noncomputable def isometryEquivBasisRepr (Q : QuadraticMap R M N) (v : Basis ι R M) :
    IsometryEquiv Q (Q.basisRepr v) :=
  isometryEquivOfCompLinearEquiv Q v.equivFun.symm

end QuadraticMap

namespace QuadraticForm
variable [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]

/-- Given an orthogonal basis, a quadratic form is isometrically equivalent with a weighted sum of
squares. -/
/-
**QuadraticForm.isometryEquivWeightedSumSquares** 是 Mathlib 中的一个定义，位于命名空间 `Quadr
aticForm`。
形式化陈述：isometryEquivWeightedSumSquares (Q : QuadraticForm K V) (v : Basis (Fin (M
odule.finrank K V)) K V) (hv₁ : (associated (R
参数：Q : QuadraticForm K V；v : Basis (Fin (Module.finrank K V)) K V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an orthogonal basis, a quadratic form is isometrically equivalent with a w
eighted sum of
squares.
-/
noncomputable def isometryEquivWeightedSumSquares (Q : QuadraticForm K V)
    (v : Basis (Fin (Module.finrank K V)) K V)
    (hv₁ : (associated (R := K) Q).IsOrthoᵢ v) :
    Q.IsometryEquiv (weightedSumSquares K fun i => Q (v i)) := by
  let iso := Q.isometryEquivBasisRepr v
  refine ⟨iso, fun m => ?_⟩
  convert! iso.map_app m
  rw [basisRepr_eq_of_iIsOrtho _ _ hv₁]

variable [FiniteDimensional K V]

open LinearMap.BilinForm
/-
**QuadraticForm.equivalent_weightedSumSquares** 是 Mathlib 中的一个定理，位于命名空间 `Quadrat
icForm`。
形式化陈述：equivalent_weightedSumSquares (Q : QuadraticForm K V) : exists w : Fin (Mo
dule.finrank K V) -> K, Equivalent Q (weightedSumSquares K w)
参数：Q : QuadraticForm K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.BilinForm.exists_orthogonal_basis`：exists_orthogonal_basis [hK
 : Invertible (2 : K)] {B : LinearMap.BilinForm K V} (hB₂ : B.IsSymm) : exists v
 : Basis (Fin (finrank K V)) K V,…
· 使用定理 `QuadraticForm.associated_isSymm`：∀ (S : Type u_1) {R : Type u_3} {M : Ty
pe u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module 
R M] [inst_3 : CommSe…
-/
theorem equivalent_weightedSumSquares (Q : QuadraticForm K V) :
    ∃ w : Fin (Module.finrank K V) → K, Equivalent Q (weightedSumSquares K w) :=
  let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm _ Q)
  ⟨_, ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩
/-
**QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'** 是 Mathli
b 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：equivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K
 V) (hQ : (associated (R
参数：Q : QuadraticForm K V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.BilinForm.exists_orthogonal_basis`：exists_orthogonal_basis [hK
 : Invertible (2 : K)] {B : LinearMap.BilinForm K V} (hB₂ : B.IsSymm) : exists v
 : Basis (Fin (finrank K V)) K V,…
· 使用定理 `QuadraticForm.associated_isSymm`：∀ (S : Type u_1) {R : Type u_3} {M : Ty
pe u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module 
R M] [inst_3 : CommSe…
· 使用定理 `LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft`：∀ {n : Type
 u_19} {R : Type u_20} {M : Type u_21} {M₁ : Type u_22} [inst : CommSemiring R] 
[inst_1 : AddCommMonoid M]   [inst_2 : AddCommMon…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x
-/
theorem equivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K V)
    (hQ : (associated (R := K) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank K V) → Kˣ, Equivalent Q (weightedSumSquares K w) := by
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm K Q)
  have hv₂ := hv₁.not_isOrtho_basis_self_of_separatingLeft hQ
  simp_rw [associated_eq_self_apply] at hv₂
  exact ⟨fun i => Units.mk0 _ (hv₂ i), ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

variable {ι S R : Type*}
variable [Fintype ι] [CommSemiring R] [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
variable [IsScalarTower S R R]
variable {w : ι → S} {w' : ι → S}

/-- The isometry between two weighted sum of squares of equal weights. -/
/-
**QuadraticForm.weightedSumSquaresCongr** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm
`。
形式化陈述：weightedSumSquaresCongr (h : w = w') : IsometryEquiv (weightedSumSquares R
 w) (weightedSumSquares R w') where __
参数：h : w = w'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isometry between two weighted sum of squares of equal weights.
-/
def weightedSumSquaresCongr (h : w = w') :
    IsometryEquiv (weightedSumSquares R w) (weightedSumSquares R w') where
  __ := LinearEquiv.refl R (ι → R)
  map_app' := by simp [h]

/-- The isometry between two weighted sum of squares, give that each weight is scaled by the square
of a unit. -/
/-
**QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares** 是 Mathlib 中的
一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：isometryEquivWeightedSumSquaresWeightedSumSquares (u : ι -> Sˣ) (h : foral
l i, w' i * u i ^ 2 = w i) : IsometryEquiv (weightedSumSquares R w) (weightedSum
Squares R w') where toFun x
参数：u : ι -> Sˣ；h : forall i, w' i * u i ^ 2 = w i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isometry between two weighted sum of squares, give that each weight is scale
d by the square
of a unit.
-/
def isometryEquivWeightedSumSquaresWeightedSumSquares (u : ι → Sˣ) (h : ∀ i, w' i * u i ^ 2 = w i) :
    IsometryEquiv (weightedSumSquares R w) (weightedSumSquares R w') where
  toFun x := u • x
  invFun x := u⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' v x := by
    ext i
    simp only [Pi.smul_apply', Pi.smul_apply, RingHom.id_apply, smul_comm]
  map_app' x := by
    simp only [weightedSumSquares_apply, Pi.smul_apply']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_mul_smul, Units.smul_def, smul_smul, ← pow_two, ← h]
    simp

end QuadraticForm

