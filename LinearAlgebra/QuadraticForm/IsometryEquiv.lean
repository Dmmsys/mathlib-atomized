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

/--
Definition of `IsometryEquiv` / `IsometryEquiv` 的定义

English:
structure IsometryEquiv
  parameters: (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
  extends: M₁ ≃ₗ[R] M₂
  axioms and operations (1):
    - map_app' : forall m, Q₂ (toFun m) = Q₁ m

中文:
结构 等距等价
  参数: (Q₁ : 二次映射 R M₁ N) (Q₂ : 二次映射 R M₂ N)
  继承: M₁ ≃ₗ[R] M₂
  公理与运算 (1 个):
    - map_app' : 对任意 m, Q₂ (toFun m) = Q₁ m
-/
structure IsometryEquiv (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
    extends M₁ ≃ₗ[R] M₂ where
  map_app' : forall m, Q₂ (toFun m) = Q₁ m

/--
Definition of `Equivalent` / `Equivalent` 的定义

English:
definition Equivalent
  signature: (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
  body: Nonempty (Q₁.IsometryEquiv Q₂)

中文:
定义 Equivalent
  签名: (Q₁ : 二次映射 R M₁ N) (Q₂ : 二次映射 R M₂ N)
  定义体: Nonempty (Q₁.IsometryEquiv Q₂)

Depends on / 依赖: IsometryEquiv, Nonempty
-/
def Equivalent (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) : Prop :=
  Nonempty (Q₁.IsometryEquiv Q₂)

namespace IsometryEquiv

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (Q₁.IsometryEquiv Q₂) M₁ M₂
  body: f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

中文:
实例 :
  签名: 等价状 (Q₁.等距等价 Q₂) M₁ M₂
  定义体: f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

Depends on / 依赖: f.toLinearEquiv, toLinearEquiv
-/
instance : EquivLike (Q₁.IsometryEquiv Q₂) M₁ M₂ where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearEquivClass (Q₁.IsometryEquiv Q₂) R M₁ M₂
  body: map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

中文:
实例 :
  签名: LinearEquivClass (Q₁.等距等价 Q₂) R M₁ M₂
  定义体: map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

Depends on / 依赖: f.toLinearEquiv, map_add, toLinearEquiv
-/
instance : LinearEquivClass (Q₁.IsometryEquiv Q₂) R M₁ M₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (Q₁.IsometryEquiv Q₂) (M₁ ≃ₗ[R] M₂)
  body: ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]

中文:
实例 :
  签名: CoeOut (Q₁.等距等价 Q₂) (M₁ ≃ₗ[R] M₂)
  定义体: ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.toLinearEquiv, toLinearEquiv
-/
instance : CoeOut (Q₁.IsometryEquiv Q₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (f : Q₁.IsometryEquiv Q₂)
  statement: ⇑(f : M₁ ≃ₗ[R] M₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_toLinearEquiv
  条件: (f : Q₁.等距等价 Q₂)
  结论: ⇑(f : M₁ ≃ₗ[R] M₂) = f
  证明: rfl

@[simp]
-/
theorem coe_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f :=
  rfl

@[simp]
/--
theorem `map_app` / 定理 `map_app`

English:
theorem map_app
  given: (f : Q₁.IsometryEquiv Q₂) (m : M₁)
  statement: Q₂ (f m) = Q₁ m
  proof: f.map_app' m

中文:
定理 map_app
  条件: (f : Q₁.等距等价 Q₂) (m : M₁)
  结论: Q₂ (f m) = Q₁ m
  证明: f.map_app' m

Depends on / 依赖: f.map_app, map_app
-/
theorem map_app (f : Q₁.IsometryEquiv Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

/-- The identity isometric equivalence between a quadratic form and itself. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (Q : QuadraticMap R M N)
  body: { LinearEquiv.refl R M with map_app' := fun _ => rfl }

中文:
定义 refl
  签名: (Q : 二次映射 R M N)
  定义体: { LinearEquiv.refl R M with map_app' := fun _ => rfl }

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, map_app
-/
def refl (Q : QuadraticMap R M N) : Q.IsometryEquiv Q :=
  { LinearEquiv.refl R M with map_app' := fun _ => rfl }

/-- The inverse isometric equivalence of an isometric equivalence between two quadratic forms. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : Q₁.IsometryEquiv Q₂)
  body: { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by intro m; rw [← f.map_app]; congr; exact f.toLinearEquiv.apply_symm_apply m }

中文:
定义 symm
  签名: (f : Q₁.等距等价 Q₂)
  定义体: { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by intro m; rw [← f.map_app]; congr; exact f.toLinearEquiv.apply_symm_apply m }

Depends on / 依赖: apply_symm_apply, f.map_app, f.toLinearEquiv.apply_symm_apply, map_app, toLinearEquiv
-/
def symm (f : Q₁.IsometryEquiv Q₂) : Q₂.IsometryEquiv Q₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by intro m; rw [← f.map_app]; congr; exact f.toLinearEquiv.apply_symm_apply m }

/-- The composition of two isometric equivalences between quadratic forms. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃)
  body: { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro m; rw [← f.map_app, ← g.map_app]; rfl }

中文:
定义 trans
  签名: (f : Q₁.等距等价 Q₂) (g : Q₂.等距等价 Q₃)
  定义体: { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro m; rw [← f.map_app, ← g.map_app]; rfl }

Depends on / 依赖: f.map_app, g.map_app, map_app
-/
def trans (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) : Q₁.IsometryEquiv Q₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro m; rw [← f.map_app, ← g.map_app]; rfl }

/-- Isometric equivalences are isometric maps -/
@[simps]
/--
Definition of `toIsometry` / `toIsometry` 的定义

English:
definition toIsometry
  signature: (g : Q₁.IsometryEquiv Q₂)
  body: g x
  __ := g

中文:
定义 toIsometry
  签名: (g : Q₁.等距等价 Q₂)
  定义体: g x
  __ := g
-/
def toIsometry (g : Q₁.IsometryEquiv Q₂) : Q₁ ->qᵢ Q₂ where
  toFun x := g x
  __ := g

/--
lemma `apply_symm_apply` / 引理 `apply_symm_apply`

English:
lemma apply_symm_apply
  given: (f : Q₁.IsometryEquiv Q₂) (x : M₂)
  statement: f (f.symm x) = x
  proof: f.toEquiv.apply_symm_apply x

中文:
引理 apply_symm_apply
  条件: (f : Q₁.等距等价 Q₂) (x : M₂)
  结论: f (f.symm x) = x
  证明: f.toEquiv.apply_symm_apply x
-/
@[simp] lemma apply_symm_apply (f : Q₁.IsometryEquiv Q₂) (x : M₂) : f (f.symm x) = x :=
  f.toEquiv.apply_symm_apply x

/--
lemma `symm_apply_apply` / 引理 `symm_apply_apply`

English:
lemma symm_apply_apply
  given: (f : Q₁.IsometryEquiv Q₂) (x : M₁)
  statement: f.symm (f x) = x
  proof: f.toEquiv.symm_apply_apply x

中文:
引理 symm_apply_apply
  条件: (f : Q₁.等距等价 Q₂) (x : M₁)
  结论: f.symm (f x) = x
  证明: f.toEquiv.symm_apply_apply x
-/
@[simp] lemma symm_apply_apply (f : Q₁.IsometryEquiv Q₂) (x : M₁) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (f : Q₁.IsometryEquiv Q₂) {x y}
  proof: f.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (f : Q₁.等距等价 Q₂) {x y}
  证明: f.toEquiv.symm_apply_eq

Depends on / 依赖: f.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (f : Q₁.IsometryEquiv Q₂) {x y} :
    f.symm x = y ↔ x = f y :=
  f.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (f : Q₁.IsometryEquiv Q₂) {x y}
  proof: f.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: (f : Q₁.等距等价 Q₂) {x y}
  证明: f.toEquiv.eq_symm_apply

Depends on / 依赖: eq_symm_apply, f.toEquiv.eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (f : Q₁.IsometryEquiv Q₂) {x y} :
    y = f.symm x ↔ f y = x :=
  f.toEquiv.eq_symm_apply

/--
lemma `coe_symm_toLinearEquiv` / 引理 `coe_symm_toLinearEquiv`

English:
lemma coe_symm_toLinearEquiv
  given: (f : Q₁.IsometryEquiv Q₂)
  statement: f.toLinearEquiv.symm = f.symm
  proof: rfl

中文:
引理 coe_symm_toLinearEquiv
  条件: (f : Q₁.等距等价 Q₂)
  结论: f.toLinearEquiv.symm = f.symm
  证明: rfl
-/
@[simp] lemma coe_symm_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) : f.toLinearEquiv.symm = f.symm :=
  rfl

end IsometryEquiv

namespace Equivalent

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {Q₃ : QuadraticMap R M₃ N}

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (Q : QuadraticMap R M N)
  statement: Q.Equivalent Q
  proof: ⟨IsometryEquiv.refl Q⟩

@[symm]

中文:
定理 refl
  条件: (Q : 二次映射 R M N)
  结论: Q.Equivalent Q
  证明: ⟨IsometryEquiv.refl Q⟩

@[symm]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.refl
-/
theorem refl (Q : QuadraticMap R M N) : Q.Equivalent Q :=
  ⟨IsometryEquiv.refl Q⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : Q₁.Equivalent Q₂)
  statement: Q₂.Equivalent Q₁
  proof: h.elim fun f => ⟨f.symm⟩

@[trans]

中文:
定理 symm
  条件: (h : Q₁.Equivalent Q₂)
  结论: Q₂.Equivalent Q₁
  证明: h.elim fun f => ⟨f.symm⟩

@[trans]

Depends on / 依赖: f.symm, h.elim
-/
theorem symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalent Q₁ :=
  h.elim fun f => ⟨f.symm⟩

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃)
  statement: Q₁.Equivalent Q₃
  proof: h'.elim h.elim fun f g => ⟨f.trans g⟩

中文:
定理 trans
  条件: (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃)
  结论: Q₁.Equivalent Q₃
  证明: h'.elim h.elim fun f g => ⟨f.trans g⟩

Depends on / 依赖: f.trans, h.elim
-/
theorem trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃ :=
h'.elim h.elim fun f g => ⟨f.trans g⟩

end Equivalent

/--
Definition of `isometryEquivOfCompLinearEquiv` / `isometryEquivOfCompLinearEquiv` 的定义

English:
definition isometryEquivOfCompLinearEquiv
  signature: (Q : QuadraticMap R M N) (f : M₁ ≃ₗ[R] M)
  body: { f.symm with
    map_app' := by
      intro
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

中文:
定义 isometryEquivOfCompLinearEquiv
  签名: (Q : 二次映射 R M N) (f : M₁ ≃ₗ[R] M)
  定义体: { f.symm with
    map_app' := by
      intro
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe, apply_symm_apply, coe_coe, comp_apply, f.apply_symm_apply, f.symm, map_app, toFun_eq_coe
-/
def isometryEquivOfCompLinearEquiv (Q : QuadraticMap R M N) (f : M₁ ≃ₗ[R] M) :
    Q.IsometryEquiv (Q.comp (f : M₁ ->ₗ[R] M)) :=
  { f.symm with
    map_app' := by
      intro
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

variable [Finite ι]

/--
Definition of `isometryEquivBasisRepr` / `isometryEquivBasisRepr` 的定义

English:
definition isometryEquivBasisRepr
  signature: (Q : QuadraticMap R M N) (v : Basis ι R M)
  body: isometryEquivOfCompLinearEquiv Q v.equivFun.symm

中文:
定义 isometryEquivBasisRepr
  签名: (Q : 二次映射 R M N) (v : 基 ι R M)
  定义体: isometryEquivOfCompLinearEquiv Q v.equivFun.symm

Depends on / 依赖: equivFun, isometryEquivOfCompLinearEquiv, v.equivFun.symm
-/
noncomputable def isometryEquivBasisRepr (Q : QuadraticMap R M N) (v : Basis ι R M) :
    IsometryEquiv Q (Q.basisRepr v) :=
  isometryEquivOfCompLinearEquiv Q v.equivFun.symm

end QuadraticMap

namespace QuadraticForm
variable [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]

/--
Definition of `isometryEquivWeightedSumSquares` / `isometryEquivWeightedSumSquares` 的定义

English:
definition isometryEquivWeightedSumSquares
  signature: (Q : QuadraticForm K V)
  body: by
  let iso := Q.isometryEquivBasisRepr v
  refine ⟨iso, fun m => ?_⟩
  convert! iso.map_app m
  rw [basisRepr_eq_of_iIsOrtho _ _ hv₁]

中文:
定义 isometryEquivWeightedSumSquares
  签名: (Q : QuadraticForm K V)
  定义体: by
  let iso := Q.isometryEquivBasisRepr v
  refine ⟨iso, fun m => ?_⟩
  convert! iso.map_app m
  rw [basisRepr_eq_of_iIsOrtho _ _ hv₁]
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

/--
theorem `equivalent_weightedSumSquares` / 定理 `equivalent_weightedSumSquares`

English:
theorem equivalent_weightedSumSquares
  given: (Q : QuadraticForm K V)
  proof: let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm _ Q)
  ⟨_, ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

中文:
定理 equivalent_weightedSumSquares
  条件: (Q : QuadraticForm K V)
  证明: let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm _ Q)
  ⟨_, ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

Depends on / 依赖: Q.isometryEquivWeightedSumSquares, associated_isSymm, exists_orthogonal_basis, isometryEquivWeightedSumSquares
-/
theorem equivalent_weightedSumSquares (Q : QuadraticForm K V) :
    exists w : Fin (Module.finrank K V) -> K, Equivalent Q (weightedSumSquares K w) :=
  let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm _ Q)
  ⟨_, ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

/--
theorem `equivalent_weightedSumSquares_units_of_nondegenerate'` / 定理 `equivalent_weightedSumSquares_units_of_nondegenerate'`

English:
theorem equivalent_weightedSumSquares_units_of_nondegenerate'
  statement: (Q : QuadraticForm K V)
  proof: by
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm K Q)
  have hv₂ := hv₁.not_isOrtho_basis_self_of_separatingLeft hQ
  simp_rw [associated_eq_self_apply] at hv₂
  exact ⟨fun i => Units.mk0 _ (hv₂ i), ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

中文:
定理 equivalent_weightedSumSquares_units_of_nondegenerate'
  结论: (Q : QuadraticForm K V)
  证明: by
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm K Q)
  have hv₂ := hv₁.not_isOrtho_basis_self_of_separatingLeft hQ
  simp_rw [associated_eq_self_apply] at hv₂
  exact ⟨fun i => Units.mk0 _ (hv₂ i), ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

Depends on / 依赖: SeparatingLeft
-/
theorem equivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K V)
    (hQ : (associated (R := K) Q).SeparatingLeft) :
    exists w : Fin (Module.finrank K V) -> Kˣ, Equivalent Q (weightedSumSquares K w) := by
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_isSymm K Q)
  have hv₂ := hv₁.not_isOrtho_basis_self_of_separatingLeft hQ
  simp_rw [associated_eq_self_apply] at hv₂
  exact ⟨fun i => Units.mk0 _ (hv₂ i), ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩

variable {ι S R : Type*}
variable [Fintype ι] [CommSemiring R] [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
variable [IsScalarTower S R R]
variable {w : ι -> S} {w' : ι -> S}

/--
Definition of `weightedSumSquaresCongr` / `weightedSumSquaresCongr` 的定义

English:
definition weightedSumSquaresCongr
  signature: (h : w = w')
  body: LinearEquiv.refl R (ι -> R)
  map_app' := by simp [h]

中文:
定义 weightedSumSquaresCongr
  签名: (h : w = w')
  定义体: LinearEquiv.refl R (ι -> R)
  map_app' := by simp [h]

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def weightedSumSquaresCongr (h : w = w') :
    IsometryEquiv (weightedSumSquares R w) (weightedSumSquares R w') where
  __ := LinearEquiv.refl R (ι -> R)
  map_app' := by simp [h]

/--
Definition of `isometryEquivWeightedSumSquaresWeightedSumSquares` / `isometryEquivWeightedSumSquaresWeightedSumSquares` 的定义

English:
definition isometryEquivWeightedSumSquaresWeightedSumSquares
  signature: (u : ι -> Sˣ) (h : forall i, w' i * u i ^ 2 = w i)
  body: u • x
  invFun x := u⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' v x := by
    ext i
    simp only [Pi.smul_apply', Pi.smul_apply, RingHom.id_apply, smul_comm]
  map_app' x := by
    simp only [weightedSumSquares_apply, Pi.smul_apply']
    refine Fin

中文:
定义 isometryEquivWeightedSumSquaresWeightedSumSquares
  签名: (u : ι -> Sˣ) (h : 对任意 i, w' i * u i ^ 2 = w i)
  定义体: u • x
  invFun x := u⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' v x := by
    ext i
    simp only [Pi.smul_apply', Pi.smul_apply, RingHom.id_apply, smul_comm]
  map_app' x := by
    simp only [weightedSumSquares_apply, Pi.smul_apply']
    refine Fin
-/
def isometryEquivWeightedSumSquaresWeightedSumSquares (u : ι -> Sˣ) (h : forall i, w' i * u i ^ 2 = w i) :
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
    rw [smul_mul_smul]; rw [Units.smul_def]; rw [smul_smul]; rw [← pow_two]; rw [← h]
    simp

end QuadraticForm
