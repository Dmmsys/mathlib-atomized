/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The characteristic predicate of tensor product

## Main definitions

- `IsTensorProduct`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `IsBaseChange`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being an
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `Algebra.IsPushout`: A predicate on the following diagram of scalar towers
  ```
    R → S
    ↓ ↓
    R' → S'
  ```
  asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

## Main results
- `TensorProduct.isBaseChange`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/

@[expose] public section

universe u v₁ v₂ v₃ v₄

open TensorProduct

section IsTensorProduct

variable {R : Type*} [CommSemiring R]
variable {M₁ M₂ M M' : Type*}
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']
variable (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M)
variable {N₁ N₂ N : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N]
variable [Module R N₁] [Module R N₂] [Module R N]
variable {g : N₁ ->ₗ[R] N₂ ->ₗ[R] N}

/--
Definition of `IsTensorProduct` / `IsTensorProduct` 的定义

English:
definition IsTensorProduct
  signature: : Prop
  body: Function.Bijective (TensorProduct.lift f)

中文:
定义 IsTensorProduct
  签名: : 命题
  定义体: Function.Bijective (TensorProduct.lift f)

Depends on / 依赖: Bijective, Function, Function.Bijective, TensorProduct, TensorProduct.lift
-/
def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)

variable (R M N) {f}

/--
theorem `TensorProduct.isTensorProduct` / 定理 `TensorProduct.isTensorProduct`

English:
theorem TensorProduct.isTensorProduct
  statement: IsTensorProduct (TensorProduct.mk R M N)
  proof: by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M otimes[R] N ->ₗ[R] M otimes[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id

中文:
定理 张量积.isTensorProduct
  结论: IsTensorProduct (张量积.mk R M N)
  证明: by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M otimes[R] N ->ₗ[R] M otimes[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id

Depends on / 依赖: Bijective, Function, Function.Bijective, Function.bijective_id, IsTensorProduct, LinearMap, LinearMap.id, TensorProduct, TensorProduct.ext, bijective_id, convert_to, otimes
-/
theorem TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N) := by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M otimes[R] N ->ₗ[R] M otimes[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id

namespace IsTensorProduct

variable {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps! apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (h : IsTensorProduct f)
  body: LinearEquiv.ofBijective _ h

@[simp]

中文:
定义 equiv
  签名: (h : IsTensorProduct f)
  定义体: LinearEquiv.ofBijective _ h

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, ofBijective
-/
noncomputable def equiv (h : IsTensorProduct f) : M₁ otimes[R] M₂ ≃ₗ[R] M :=
  LinearEquiv.ofBijective _ h

@[simp]
/--
theorem `equiv_toLinearMap` / 定理 `equiv_toLinearMap`

English:
theorem equiv_toLinearMap
  given: (h : IsTensorProduct f)
  proof: rfl

@[simp]

中文:
定理 equiv_toLinearMap
  条件: (h : IsTensorProduct f)
  证明: rfl

@[simp]
-/
theorem equiv_toLinearMap (h : IsTensorProduct f) :
    h.equiv.toLinearMap = TensorProduct.lift f :=
  rfl

@[simp]
/--
theorem `equiv_symm_apply` / 定理 `equiv_symm_apply`

English:
theorem equiv_symm_apply
  given: (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂)
  proof: by
  apply h.equiv.injective
  refine (h.equiv.apply_symm_apply _).trans ?_
  simp

中文:
定理 equiv_symm_apply
  条件: (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂)
  证明: by
  apply h.equiv.injective
  refine (h.equiv.apply_symm_apply _).trans ?_
  simp

Depends on / 依赖: apply_symm_apply, h.equiv.apply_symm_apply, h.equiv.injective, injective
-/
theorem equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) :
    h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂ := by
  apply h.equiv.injective
  refine (h.equiv.apply_symm_apply _).trans ?_
  simp

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M')
  body: (TensorProduct.lift f').comp h.equiv.symm.toLinearMap

中文:
定义 lift
  签名: (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M')
  定义体: (TensorProduct.lift f').comp h.equiv.symm.toLinearMap

Depends on / 依赖: TensorProduct, TensorProduct.lift, h.equiv.symm.toLinearMap, toLinearMap
-/
noncomputable def lift (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M') :
    M ->ₗ[R] M' :=
  (TensorProduct.lift f').comp h.equiv.symm.toLinearMap

/--
theorem `lift_eq` / 定理 `lift_eq`

English:
theorem lift_eq
  statement: (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M') (x₁ : M₁)
  proof: by
  simp [lift]

中文:
定理 lift_eq
  结论: (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M') (x₁ : M₁)
  证明: by
  simp [lift]
-/
theorem lift_eq (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M') (x₁ : M₁)
    (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ := by
  simp [lift]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (hf : IsTensorProduct f) (hg : IsTensorProduct g)
  body: hg.equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.equiv.symm.toLinearMap)

@[simp]

中文:
定义 map
  签名: (hf : IsTensorProduct f) (hg : IsTensorProduct g)
  定义体: hg.equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.equiv.symm.toLinearMap)

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.map, hf.equiv.symm.toLinearMap, hg.equiv.toLinearMap.comp, toLinearMap
-/
noncomputable def map (hf : IsTensorProduct f) (hg : IsTensorProduct g)
    (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) : M ->ₗ[R] N :=
  hg.equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.equiv.symm.toLinearMap)

@[simp]
/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  statement: (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ ->ₗ[R] N₁)
  proof: by
  simp [map]

@[elab_as_elim]

中文:
定理 map_eq
  结论: (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ ->ₗ[R] N₁)
  证明: by
  simp [map]

@[elab_as_elim]
-/
theorem map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ ->ₗ[R] N₁)
    (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) := by
  simp [map]

@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  statement: (h : IsTensorProduct f) {motive : M -> Prop} (m : M)
  proof: by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.invFun m = y
  change motive (TensorProduct.lift f y)
  induction y with
  | zero => rwa [map_zero]
  | tmul _ _ =>
    rw [TensorProduct.lift.tmul]
    apply tmul
  | add _ _ _ _ =>
    rw [map_add]
    apply add <;> assumption

中文:
定理 inductionOn
  结论: (h : IsTensorProduct f) {motive : M -> 命题} (m : M)
  证明: by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.invFun m = y
  change motive (TensorProduct.lift f y)
  induction y with
  | zero => rwa [map_zero]
  | tmul _ _ =>
    rw [TensorProduct.lift.tmul]
    apply tmul
  | add _ _ _ _ =>
    rw [map_add]
    apply add <;> assumption

Depends on / 依赖: TensorProduct, TensorProduct.lift, TensorProduct.lift.tmul, generalize, h.equiv.invFun, h.equiv.right_inv, invFun, map_add, map_zero, motive, right_inv
-/
theorem inductionOn (h : IsTensorProduct f) {motive : M -> Prop} (m : M)
    (zero : motive 0) (tmul : forall x y, motive (f x y))
    (add : forall x y, motive x -> motive y -> motive (x + y)) : motive m := by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.invFun m = y
  change motive (TensorProduct.lift f y)
  induction y with
  | zero => rwa [map_zero]
  | tmul _ _ =>
    rw [TensorProduct.lift.tmul]
    apply tmul
  | add _ _ _ _ =>
    rw [map_add]
    apply add <;> assumption

/--
lemma `of_equiv` / 引理 `of_equiv`

English:
lemma of_equiv
  given: (e : M₁ otimes[R] M₂ ≃ₗ[R] M) (he : forall x y, e (x otimesₜ y) = f x y)
  proof: by
  have : TensorProduct.lift f = e := by
    ext x y
    simp [he]
  simpa [IsTensorProduct, this] using e.bijective

中文:
引理 of_equiv
  条件: (e : M₁ otimes[R] M₂ ≃ₗ[R] M) (he : 对任意 x y, e (x otimesₜ y) = f x y)
  证明: by
  have : TensorProduct.lift f = e := by
    ext x y
    simp [he]
  simpa [IsTensorProduct, this] using e.bijective

Depends on / 依赖: IsTensorProduct, TensorProduct, TensorProduct.lift, bijective, e.bijective
-/
lemma of_equiv (e : M₁ otimes[R] M₂ ≃ₗ[R] M) (he : forall x y, e (x otimesₜ y) = f x y) :
    IsTensorProduct f := by
  have : TensorProduct.lift f = e := by
    ext x y
    simp [he]
  simpa [IsTensorProduct, this] using e.bijective

section map

variable {P₁ P₂ P : Type*} [AddCommMonoid P₁] [AddCommMonoid P₂]
  [AddCommMonoid P] [Module R P₁] [Module R P₂] [Module R P] {p : P₁ ->ₗ[R] P₂ ->ₗ[R] P}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (hp : IsTensorProduct p)
  (i₁ : N₁ ->ₗ[R] P₁) (j₁ : M₁ ->ₗ[R] N₁) (i₂ : N₂ ->ₗ[R] P₂) (j₂ : M₂ ->ₗ[R] N₂)

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = hg.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂
  proof: LinearMap.ext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

中文:
定理 map_comp
  结论: hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = hg.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂
  证明: LinearMap.ext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

Depends on / 依赖: LinearMap, LinearMap.ext, hf.inductionOn, inductionOn
-/
theorem map_comp : hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = hg.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂ :=
LinearMap.ext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (x : M)
  proof: DFunLike.congr_fun (hf.map_comp hg hp i₁ j₁ i₂ j₂).symm x

@[simp]

中文:
定理 map_map
  条件: (x : M)
  证明: DFunLike.congr_fun (hf.map_comp hg hp i₁ j₁ i₂ j₂).symm x

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, hf.map_comp, map_comp
-/
theorem map_map (x : M) :
    hg.map hp i₁ i₂ ((hf.map hg j₁ j₂) x) = hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) x :=
  DFunLike.congr_fun (hf.map_comp hg hp i₁ j₁ i₂ j₂).symm x

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  proof: LinearMap.ext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

@[simp]

中文:
定理 map_id
  证明: LinearMap.ext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, hf.inductionOn, inductionOn
-/
theorem map_id :
    hf.map hf (LinearMap.id : M₁ ->ₗ[R] M₁) (LinearMap.id : M₂ ->ₗ[R] M₂) = LinearMap.id :=
LinearMap.ext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: hf.map hf (1 : M₁ ->ₗ[R] M₁) (1 : M₂ ->ₗ[R] M₂) = 1
  proof: hf.map_id

中文:
定理 map_one
  结论: hf.map hf (1 : M₁ ->ₗ[R] M₁) (1 : M₂ ->ₗ[R] M₂) = 1
  证明: hf.map_id
-/
protected theorem map_one : hf.map hf (1 : M₁ ->ₗ[R] M₁) (1 : M₂ ->ₗ[R] M₂) = 1 :=
  hf.map_id

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (i₁ i₂ : M₁ ->ₗ[R] M₁) (j₁ j₂ : M₂ ->ₗ[R] M₂)
  proof: hf.map_comp hf hf i₁ i₂ j₁ j₂

中文:
定理 map_mul
  条件: (i₁ i₂ : M₁ ->ₗ[R] M₁) (j₁ j₂ : M₂ ->ₗ[R] M₂)
  证明: hf.map_comp hf hf i₁ i₂ j₁ j₂
-/
protected theorem map_mul (i₁ i₂ : M₁ ->ₗ[R] M₁) (j₁ j₂ : M₂ ->ₗ[R] M₂) :
    hf.map hf (i₁ * i₂) (j₁ * j₂) = hf.map hf i₁ j₁ * hf.map hf i₂ j₂ :=
  hf.map_comp hf hf i₁ i₂ j₁ j₂

/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (i : M₁ ->ₗ[R] M₁) (j : M₂ ->ₗ[R] M₂) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, ih, hf.map_mul]

中文:
定理 map_pow
  条件: (i : M₁ ->ₗ[R] M₁) (j : M₂ ->ₗ[R] M₂) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, ih, hf.map_mul]
-/
protected theorem map_pow (i : M₁ ->ₗ[R] M₁) (j : M₂ ->ₗ[R] M₂) (n : Nat) :
    hf.map hf i j ^ n = hf.map hf (i ^ n) (j ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, ih, hf.map_mul]

end map


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {M₁ M₂ M₃ M₁₂ M₂₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid M₁₂] [AddCommMonoid M₂₃]
  [Module R M₁]
  [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]
  [Module R M₃] [Module S M₃] [IsScalarTower R S M₃]
  [Module R M₁₂] [Module S M₁₂] [IsScalarTower R S M₁₂]
  [Module R M₂₃] [Module S M₂₃] [IsScalarTower R S M₂₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def assocAux
  body: letI : Module S (M₁ otimes[R] M₂) :=
    AddEquiv.module S hf.equiv.toAddEquiv
  haveI heq (s : S) (y : M₁) (x : M₂) : s • y otimesₜ[R] x = y otimesₜ[R] (s • x) := by
    change hf.equiv.symm (s • _) = _
    dsimp
    rw [← map_smul]
    apply hf.equiv_symm_apply
  haveI : IsScalarTower R S (M₁ otimes[R] M₂) := hf.equiv.isScalarTower S
  letI e₀ : M₂ otimes[R] M₁ ≃ₗ[S] M₁ otimes[R] M₂ :=
    { __ := TensorProduct.comm R M₂ M₁
      map_smul' s x := by induction x <;> simp_all [TensorProduct.smul_tmul'] }
LinearEquiv.symm
    TensorProduct.congr (.refl _ _) (hg.equiv.symm.restrictScalars R) ≪≫ₗ
    TensorProduct.comm _ _ _ ≪≫ₗ
    (AlgebraTensorModule.congr (TensorProduct.comm _ _ _) (.refl _ _)).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.assoc R S S M₃ M₂ M₁).restrictScalars R ≪≫ₗ
    (TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (TensorProduct.congr e₀ (.refl _ _)).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (hf.equiv.linearEquiv S) (.refl _ _)).restrictScalars R

中文:
定义 noncomputable
  签名: def assocAux
  定义体: letI : Module S (M₁ otimes[R] M₂) :=
    AddEquiv.module S hf.equiv.toAddEquiv
  haveI heq (s : S) (y : M₁) (x : M₂) : s • y otimesₜ[R] x = y otimesₜ[R] (s • x) := by
    change hf.equiv.symm (s • _) = _
    dsimp
    rw [← map_smul]
    apply hf.equiv_symm_apply
  haveI : IsScalarTower R S (M₁ otimes[R] M₂) := hf.equiv.isScalarTower S
  letI e₀ : M₂ otimes[R] M₁ ≃ₗ[S] M₁ otimes[R] M₂ :=
    { __ := TensorProduct.comm R M₂ M₁
      map_smul' s x := by induction x <;> simp_all [TensorProduct.smul_tmul'] }
LinearEquiv.symm
    TensorProduct.congr (.refl _ _) (hg.equiv.symm.restrictScalars R) ≪≫ₗ
    TensorProduct.comm _ _ _ ≪≫ₗ
    (AlgebraTensorModule.congr (TensorProduct.comm _ _ _) (.refl _ _)).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.assoc R S S M₃ M₂ M₁).restrictScalars R ≪≫ₗ
    (TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (TensorProduct.congr e₀ (.refl _ _)).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (hf.equiv.linearEquiv S) (.refl _ _)).restrictScalars R
-/
private noncomputable def assocAux
    (f : M₁ ->ₗ[R] M₂ ->ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ otimes[S] M₃ ≃ₗ[R] M₁ otimes[R] M₂₃ :=
  letI : Module S (M₁ otimes[R] M₂) :=
    AddEquiv.module S hf.equiv.toAddEquiv
  haveI heq (s : S) (y : M₁) (x : M₂) : s • y otimesₜ[R] x = y otimesₜ[R] (s • x) := by
    change hf.equiv.symm (s • _) = _
    dsimp
    rw [← map_smul]
    apply hf.equiv_symm_apply
  haveI : IsScalarTower R S (M₁ otimes[R] M₂) := hf.equiv.isScalarTower S
  letI e₀ : M₂ otimes[R] M₁ ≃ₗ[S] M₁ otimes[R] M₂ :=
    { __ := TensorProduct.comm R M₂ M₁
      map_smul' s x := by induction x <;> simp_all [TensorProduct.smul_tmul'] }
LinearEquiv.symm
    TensorProduct.congr (.refl _ _) (hg.equiv.symm.restrictScalars R) ≪≫ₗ
    TensorProduct.comm _ _ _ ≪≫ₗ
    (AlgebraTensorModule.congr (TensorProduct.comm _ _ _) (.refl _ _)).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.assoc R S S M₃ M₂ M₁).restrictScalars R ≪≫ₗ
    (TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (TensorProduct.congr e₀ (.refl _ _)).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (hf.equiv.linearEquiv S) (.refl _ _)).restrictScalars R

variable (f : M₁ ->ₗ[R] M₂ ->ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
/--
lemma `assocAux_symm_tmul` / 引理 `assocAux_symm_tmul`

English:
lemma assocAux_symm_tmul
  given: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  proof: by
  simp [IsTensorProduct.assocAux]

中文:
引理 assocAux_symm_tmul
  条件: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  证明: by
  simp [IsTensorProduct.assocAux]
-/
private lemma assocAux_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (IsTensorProduct.assocAux f hf g hg).symm (x₁ otimesₜ g x₂ x₃) = f x₁ x₂ otimesₜ x₃ := by
  simp [IsTensorProduct.assocAux]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `assocAux_tmul` / 引理 `assocAux_tmul`

English:
lemma assocAux_tmul
  given: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  proof: by
  have : hf.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂ := hf.equiv_symm_apply _ _
  simp [IsTensorProduct.assocAux, this]

中文:
引理 assocAux_tmul
  条件: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  证明: by
  have : hf.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂ := hf.equiv_symm_apply _ _
  simp [IsTensorProduct.assocAux, this]
-/
private lemma assocAux_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    IsTensorProduct.assocAux f hf g hg (f x₁ x₂ otimesₜ x₃) = x₁ otimesₜ g x₂ x₃ := by
  have : hf.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂ := hf.equiv_symm_apply _ _
  simp [IsTensorProduct.assocAux, this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
This is the canonical isomorphism `(M₁ ⊗[R] M₂) ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] (M₂ ⊗[S] M₃)`.
We state this for a general `M₁₂ = M₁ ⊗[R] M₂` and `M₂₃ = M₂ ⊗[R] M₃`.
For the version where `R` and `S` are flipped, see `TensorProduct.AlgebraTensorModule.assoc`.
-/
@[no_expose]
/--
Definition of `assoc` / `assoc` 的定义

English:
definition assoc
  signature: {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁]
  body: IsTensorProduct.assocAux (f.restrictScalars₁₂ R S) hf g hg
  map_smul' t x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y =>
    obtain ⟨x, rfl⟩ := hf.equiv.surjective x
    induction x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x z =>
      have : t • (f x) z = f (t • x) z := by simp
      dsimp
      rw [smul_tmul']; rw [this]; rw [← f.restrictScalars₁₂_apply_apply R S]; rw [← f.restrictScalars₁₂_apply_apply R S]; rw [IsTensorProduct.assocAux_tmul]; rw [IsTensorProduct.assocAux_tmul]; rw [TensorProduct.smul_tmul']

中文:
定义 assoc
  签名: {T : 类型} [交换半环 T] [代数 R T] [模 T M₁]
  定义体: IsTensorProduct.assocAux (f.restrictScalars₁₂ R S) hf g hg
  map_smul' t x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y =>
    obtain ⟨x, rfl⟩ := hf.equiv.surjective x
    induction x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x z =>
      have : t • (f x) z = f (t • x) z := by simp
      dsimp
      rw [smul_tmul']; rw [this]; rw [← f.restrictScalars₁₂_apply_apply R S]; rw [← f.restrictScalars₁₂_apply_apply R S]; rw [IsTensorProduct.assocAux_tmul]; rw [IsTensorProduct.assocAux_tmul]; rw [TensorProduct.smul_tmul']

Depends on / 依赖: IsTensorProduct, IsTensorProduct.assocAux, assocAux, f.restrictScalars
-/
noncomputable def assoc {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁]
    [IsScalarTower R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂]
    (f : M₁ ->ₗ[T] M₂ ->ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ otimes[S] M₃ ≃ₗ[T] M₁ otimes[R] M₂₃ where
  toAddEquiv := IsTensorProduct.assocAux (f.restrictScalars₁₂ R S) hf g hg
  map_smul' t x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y =>
    obtain ⟨x, rfl⟩ := hf.equiv.surjective x
    induction x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x z =>
      have : t • (f x) z = f (t • x) z := by simp
      dsimp
      rw [smul_tmul']; rw [this]; rw [← f.restrictScalars₁₂_apply_apply R S]; rw [← f.restrictScalars₁₂_apply_apply R S]; rw [IsTensorProduct.assocAux_tmul]; rw [IsTensorProduct.assocAux_tmul]; rw [TensorProduct.smul_tmul']

variable {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁] [IsScalarTower R T M₁]
  [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂]
  (f : M₁ ->ₗ[T] M₂ ->ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
/--
lemma `assoc_tmul` / 引理 `assoc_tmul`

English:
lemma assoc_tmul
  given: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  proof: assocAux_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

@[simp]

中文:
引理 assoc_tmul
  条件: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  证明: assocAux_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

@[simp]

Depends on / 依赖: assocAux_tmul, f.restrictScalars
-/
lemma assoc_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    assoc f hf g hg (f x₁ x₂ otimesₜ x₃) = x₁ otimesₜ g x₂ x₃ :=
  assocAux_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

@[simp]
/--
lemma `assoc_symm_tmul` / 引理 `assoc_symm_tmul`

English:
lemma assoc_symm_tmul
  given: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  proof: assocAux_symm_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

中文:
引理 assoc_symm_tmul
  条件: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  证明: assocAux_symm_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

Depends on / 依赖: assocAux_symm_tmul, f.restrictScalars
-/
lemma assoc_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (assoc f hf g hg).symm (x₁ otimesₜ g x₂ x₃) = f x₁ x₂ otimesₜ x₃ :=
  assocAux_symm_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

/--
Definition of `assocOfMapSMul` / `assocOfMapSMul` 的定义

English:
definition assocOfMapSMul
  signature: (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M₁₂) (hf : IsTensorProduct f)
  body: IsTensorProduct.assoc (.mk₂' _ _ (f ·) (by simp) (by simp [h₁]) (by simp) (by simp [h₂])) hf g hg

中文:
定义 assocOfMapSMul
  签名: (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M₁₂) (hf : IsTensorProduct f)
  定义体: IsTensorProduct.assoc (.mk₂' _ _ (f ·) (by simp) (by simp [h₁]) (by simp) (by simp [h₂])) hf g hg

Depends on / 依赖: IsTensorProduct, IsTensorProduct.assoc
-/
noncomputable def assocOfMapSMul (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M₁₂) (hf : IsTensorProduct f)
    (g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g)
    (h₁ : forall (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
    (h₂ : forall (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y) :
    M₁₂ otimes[S] M₃ ≃ₗ[T] M₁ otimes[R] M₂₃ :=
  IsTensorProduct.assoc (.mk₂' _ _ (f ·) (by simp) (by simp [h₁]) (by simp) (by simp [h₂])) hf g hg

variable (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M₁₂) (hf : IsTensorProduct f)
  (g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g)
  (h₁ : forall (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
  (h₂ : forall (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y)

@[simp]
/--
lemma `assocOfMapSMul_tmul` / 引理 `assocOfMapSMul_tmul`

English:
lemma assocOfMapSMul_tmul
  given: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  proof: IsTensorProduct.assoc_tmul ..

@[simp]

中文:
引理 assocOfMapSMul_tmul
  条件: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  证明: IsTensorProduct.assoc_tmul ..

@[simp]

Depends on / 依赖: IsTensorProduct, IsTensorProduct.assoc_tmul, assoc_tmul
-/
lemma assocOfMapSMul_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    assocOfMapSMul f hf g hg h₁ h₂ (f x₁ x₂ otimesₜ x₃) = x₁ otimesₜ g x₂ x₃ :=
  IsTensorProduct.assoc_tmul ..

@[simp]
/--
lemma `assocOfMapSMul_symm_tmul` / 引理 `assocOfMapSMul_symm_tmul`

English:
lemma assocOfMapSMul_symm_tmul
  given: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  proof: IsTensorProduct.assoc_symm_tmul ..

中文:
引理 assocOfMapSMul_symm_tmul
  条件: (x₁ : M₁) (x₂ : M₂) (x₃ : M₃)
  证明: IsTensorProduct.assoc_symm_tmul ..

Depends on / 依赖: IsTensorProduct, IsTensorProduct.assoc_symm_tmul, assoc_symm_tmul
-/
lemma assocOfMapSMul_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (assocOfMapSMul f hf g hg h₁ h₂).symm (x₁ otimesₜ g x₂ x₃) = f x₁ x₂ otimesₜ x₃ :=
  IsTensorProduct.assoc_symm_tmul ..

end

section

/--
lemma `compr₂_linearEquiv` / 引理 `compr₂_linearEquiv`

English:
lemma compr₂_linearEquiv
  given: (ist : IsTensorProduct f) (e : M ≃ₗ[R] M')
  proof: by
  simp only [IsTensorProduct] at ist ⊢
  rw [TensorProduct.lift_compr₂]
  exact e.bijective.comp ist

中文:
引理 compr₂_linearEquiv
  条件: (ist : IsTensorProduct f) (e : M ≃ₗ[R] M')
  证明: by
  simp only [IsTensorProduct] at ist ⊢
  rw [TensorProduct.lift_compr₂]
  exact e.bijective.comp ist

Depends on / 依赖: IsTensorProduct, TensorProduct, TensorProduct.lift_compr, bijective, e.bijective.comp
-/
lemma compr₂_linearEquiv (ist : IsTensorProduct f) (e : M ≃ₗ[R] M') :
    IsTensorProduct (f.compr₂ e.toLinearMap) := by
  simp only [IsTensorProduct] at ist ⊢
  rw [TensorProduct.lift_compr₂]
  exact e.bijective.comp ist

/--
lemma `compl₂_comp_linearEquiv` / 引理 `compl₂_comp_linearEquiv`

English:
lemma compl₂_comp_linearEquiv
  given: (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂)
  proof: by
  simp only [IsTensorProduct] at ist ⊢
  rw [← TensorProduct.lift_comp_map]; rw [← LinearMap.rTensor_comp_lTensor]
  exact ist.comp ((e₁.rTensor M₂).bijective.comp (e₂.lTensor N₁).bijective)

中文:
引理 compl₂_comp_linearEquiv
  条件: (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂)
  证明: by
  simp only [IsTensorProduct] at ist ⊢
  rw [← TensorProduct.lift_comp_map]; rw [← LinearMap.rTensor_comp_lTensor]
  exact ist.comp ((e₁.rTensor M₂).bijective.comp (e₂.lTensor N₁).bijective)

Depends on / 依赖: IsTensorProduct, LinearMap, LinearMap.rTensor_comp_lTensor, TensorProduct, TensorProduct.lift_comp_map, bijective, bijective.comp, ist.comp, lTensor, lift_comp_map, rTensor, rTensor_comp_lTensor
-/
lemma compl₂_comp_linearEquiv (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂) :
    IsTensorProduct ((f.comp e₁.toLinearMap).compl₂ e₂.toLinearMap) := by
  simp only [IsTensorProduct] at ist ⊢
  rw [← TensorProduct.lift_comp_map]; rw [← LinearMap.rTensor_comp_lTensor]
  exact ist.comp ((e₁.rTensor M₂).bijective.comp (e₂.lTensor N₁).bijective)

/--
lemma `comp_linearEquiv` / 引理 `comp_linearEquiv`

English:
lemma comp_linearEquiv
  given: (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁)
  proof: ist.compl₂_comp_linearEquiv e₁ (LinearEquiv.refl R M₂)

中文:
引理 comp_linearEquiv
  条件: (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁)
  证明: ist.compl₂_comp_linearEquiv e₁ (LinearEquiv.refl R M₂)

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, ist.compl
-/
lemma comp_linearEquiv (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) :
    IsTensorProduct (f.comp e₁.toLinearMap) :=
  ist.compl₂_comp_linearEquiv e₁ (LinearEquiv.refl R M₂)

/--
lemma `compl₂_linearEquiv` / 引理 `compl₂_linearEquiv`

English:
lemma compl₂_linearEquiv
  given: (ist : IsTensorProduct f) (e₂ : N₂ ≃ₗ[R] M₂)
  proof: ist.compl₂_comp_linearEquiv (LinearEquiv.refl R M₁) e₂

中文:
引理 compl₂_linearEquiv
  条件: (ist : IsTensorProduct f) (e₂ : N₂ ≃ₗ[R] M₂)
  证明: ist.compl₂_comp_linearEquiv (LinearEquiv.refl R M₁) e₂

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, ist.compl
-/
lemma compl₂_linearEquiv (ist : IsTensorProduct f) (e₂ : N₂ ≃ₗ[R] M₂) :
    IsTensorProduct (f.compl₂ e₂.toLinearMap) :=
  ist.compl₂_comp_linearEquiv (LinearEquiv.refl R M₁) e₂

end

end IsTensorProduct

end IsTensorProduct

section IsBaseChange

variable {R : Type*} {M : Type v₁} {N : Type v₂} (S : Type v₃)
variable [AddCommMonoid M] [AddCommMonoid N] [CommSemiring R]
variable [CommSemiring S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
variable (f : M ->ₗ[R] N)

/--
Definition of `IsBaseChange` / `IsBaseChange` 的定义

English:
definition IsBaseChange
  signature: : Prop
  body: IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M ->ₗ[R] N)).flip f).restrictScalars R)

中文:
定义 IsBaseChange
  签名: : 命题
  定义体: IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M ->ₗ[R] N)).flip f).restrictScalars R)

Depends on / 依赖: Algebra, Algebra.linearMap, IsTensorProduct, Module, Module.End, linearMap, restrictScalars
-/
def IsBaseChange : Prop :=
  IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M ->ₗ[R] N)).flip f).restrictScalars R)

variable {S f} (h : IsBaseChange S f)
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module S Q]

section

variable [Module R Q] [IsScalarTower R S Q]

/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors through `f`. -/
noncomputable nonrec def IsBaseChange.lift (g : M ->ₗ[R] Q) : N ->ₗ[S] Q :=
  { h.lift
      (((Algebra.linearMap S <| Module.End S (M ->ₗ[R] Q)).flip g).restrictScalars R) with
    map_smul' := fun r x => by
      let F := ((Algebra.linearMap S <| Module.End S (M ->ₗ[R] Q)).flip g).restrictScalars R
      have hF : forall (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F
      change h.lift F (r • x) = r • h.lift F x
      induction x using h.inductionOn with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s m =>
        change h.lift F (r • s • f m) = r • h.lift F (s • f m)
        rw [← mul_smul]; rw [hF]; rw [hF]; rw [mul_smul]
      | add x₁ x₂ e₁ e₂ => rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }

nonrec theorem IsBaseChange.lift_eq (g : M ->ₗ[R] Q) (x : M) : h.lift g (f x) = g x := by
  have hF : forall (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _
  convert! hF 1 x <;> rw [one_smul]

/--
theorem `IsBaseChange.lift_comp` / 定理 `IsBaseChange.lift_comp`

English:
theorem IsBaseChange.lift_comp
  given: (g : M ->ₗ[R] Q)
  statement: ((h.lift g).restrictScalars R).comp f = g
  proof: LinearMap.ext (h.lift_eq g)

中文:
定理 IsBaseChange.lift_comp
  条件: (g : M ->ₗ[R] Q)
  结论: ((h.lift g).restrictScalars R).comp f = g
  证明: LinearMap.ext (h.lift_eq g)

Depends on / 依赖: LinearMap, LinearMap.ext, h.lift_eq, lift_eq
-/
theorem IsBaseChange.lift_comp (g : M ->ₗ[R] Q) : ((h.lift g).restrictScalars R).comp f = g :=
  LinearMap.ext (h.lift_eq g)

end

section
include h

@[elab_as_elim]
nonrec theorem IsBaseChange.inductionOn (x : N) (motive : N -> Prop) (zero : motive 0)
    (tmul : forall m : M, motive (f m)) (smul : forall (s : S) (n), motive n -> motive (s • n))
    (add : forall n₁ n₂, motive n₁ -> motive n₂ -> motive (n₁ + n₂)) : motive x :=
  h.inductionOn x zero (fun _ _ => smul _ _ (tmul _)) add

/--
theorem `IsBaseChange.algHom_ext` / 定理 `IsBaseChange.algHom_ext`

English:
theorem IsBaseChange.algHom_ext
  given: (g₁ g₂ : N ->ₗ[S] Q) (e : forall x, g₁ (f x) = g₂ (f x))
  statement: g₁ = g₂
  proof: by
  ext x
  refine h.inductionOn x _ ?_ ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'
    rw [g₁.map_smul]; rw [g₂.map_smul]; rw [e']
  · intro x y e₁ e₂
    rw [map_add]; rw [map_add]; rw [e₁]; rw [e₂]

中文:
定理 IsBaseChange.algHom_ext
  条件: (g₁ g₂ : N ->ₗ[S] Q) (e : 对任意 x, g₁ (f x) = g₂ (f x))
  结论: g₁ = g₂
  证明: by
  ext x
  refine h.inductionOn x _ ?_ ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'
    rw [g₁.map_smul]; rw [g₂.map_smul]; rw [e']
  · intro x y e₁ e₂
    rw [map_add]; rw [map_add]; rw [e₁]; rw [e₂]

Depends on / 依赖: h.inductionOn, inductionOn, map_add, map_smul, map_zero
-/
theorem IsBaseChange.algHom_ext (g₁ g₂ : N ->ₗ[S] Q) (e : forall x, g₁ (f x) = g₂ (f x)) : g₁ = g₂ := by
  ext x
  refine h.inductionOn x _ ?_ ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'
    rw [g₁.map_smul]; rw [g₂.map_smul]; rw [e']
  · intro x y e₁ e₂
    rw [map_add]; rw [map_add]; rw [e₁]; rw [e₂]

/--
theorem `IsBaseChange.algHom_ext'` / 定理 `IsBaseChange.algHom_ext'`

English:
theorem IsBaseChange.algHom_ext'
  statement: [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N ->ₗ[S] Q)
  proof: h.algHom_ext g₁ g₂ (LinearMap.congr_fun e)

中文:
定理 IsBaseChange.algHom_ext'
  结论: [模 R Q] [标量塔 R S Q] (g₁ g₂ : N ->ₗ[S] Q)
  证明: h.algHom_ext g₁ g₂ (LinearMap.congr_fun e)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, algHom_ext, congr_fun, h.algHom_ext
-/
theorem IsBaseChange.algHom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N ->ₗ[S] Q)
    (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ = g₂ :=
  h.algHom_ext g₁ g₂ (LinearMap.congr_fun e)

end

variable (R M N S)

/--
theorem `TensorProduct.isBaseChange` / 定理 `TensorProduct.isBaseChange`

English:
theorem TensorProduct.isBaseChange
  statement: IsBaseChange S (TensorProduct.mk R S M 1)
  proof: by
  delta IsBaseChange
  convert! TensorProduct.isTensorProduct R S M using 1
  ext s x
  change s • (1 : S) otimesₜ[R] x = s otimesₜ[R] x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _

中文:
定理 张量积.isBaseChange
  结论: IsBaseChange S (张量积.mk R S M 1)
  证明: by
  delta IsBaseChange
  convert! TensorProduct.isTensorProduct R S M using 1
  ext s x
  change s • (1 : S) otimesₜ[R] x = s otimesₜ[R] x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _

Depends on / 依赖: IsBaseChange, TensorProduct, TensorProduct.isTensorProduct, TensorProduct.smul_tmul, convert, isTensorProduct, mul_one, smul_tmul
-/
theorem TensorProduct.isBaseChange : IsBaseChange S (TensorProduct.mk R S M 1) := by
  delta IsBaseChange
  convert! TensorProduct.isTensorProduct R S M using 1
  ext s x
  change s • (1 : S) otimesₜ[R] x = s otimesₜ[R] x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _

variable {R M N S}

set_option backward.isDefEq.respectTransparency false in
/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable nonrec def IsBaseChange.equiv : S otimes[R] M ≃ₗ[S] N :=
  { h.equiv with
    map_smul' := fun r x => by
      change h.equiv (r • x) = r • h.equiv x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · rw [smul_zero, map_zero, smul_zero]
      · intro x y
        simp [smul_tmul', Algebra.linearMap_apply, smul_comm r x]
      · intro x y hx hy
        rw [map_add]; rw [smul_add]; rw [map_add]; rw [smul_add]; rw [hx]; rw [hy] }

@[simp]
/--
theorem `IsBaseChange.equiv_tmul` / 定理 `IsBaseChange.equiv_tmul`

English:
theorem IsBaseChange.equiv_tmul
  given: (s : S) (m : M)
  statement: h.equiv (s otimesₜ m) = s • f m
  proof: rfl

@[simp]

中文:
定理 IsBaseChange.equiv_tmul
  条件: (s : S) (m : M)
  结论: h.equiv (s otimesₜ m) = s • f m
  证明: rfl

@[simp]
-/
theorem IsBaseChange.equiv_tmul (s : S) (m : M) : h.equiv (s otimesₜ m) = s • f m :=
  rfl

@[simp]
/--
theorem `IsBaseChange.equiv_symm_apply` / 定理 `IsBaseChange.equiv_symm_apply`

English:
theorem IsBaseChange.equiv_symm_apply
  given: (m : M)
  statement: h.equiv.symm (f m) = 1 otimesₜ m
  proof: by
  rw [h.equiv.symm_apply_eq]; rw [h.equiv_tmul]; rw [one_smul]

中文:
定理 IsBaseChange.equiv_symm_apply
  条件: (m : M)
  结论: h.equiv.symm (f m) = 1 otimesₜ m
  证明: by
  rw [h.equiv.symm_apply_eq]; rw [h.equiv_tmul]; rw [one_smul]

Depends on / 依赖: equiv_tmul, h.equiv.symm_apply_eq, h.equiv_tmul, one_smul, symm_apply_eq
-/
theorem IsBaseChange.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 otimesₜ m := by
  rw [h.equiv.symm_apply_eq]; rw [h.equiv_tmul]; rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsBaseChange.of_equiv` / 引理 `IsBaseChange.of_equiv`

English:
lemma IsBaseChange.of_equiv
  given: (e : S otimes[R] M ≃ₗ[S] N) (he : forall x, e (1 otimesₜ x) = f x)
  proof: by
  apply IsTensorProduct.of_equiv (e.restrictScalars R)
  intro x y
  simp [show x otimesₜ[R] y = x • (1 otimesₜ[R] y) by simp [smul_tmul'], he]

中文:
引理 IsBaseChange.of_equiv
  条件: (e : S otimes[R] M ≃ₗ[S] N) (he : 对任意 x, e (1 otimesₜ x) = f x)
  证明: by
  apply IsTensorProduct.of_equiv (e.restrictScalars R)
  intro x y
  simp [show x otimesₜ[R] y = x • (1 otimesₜ[R] y) by simp [smul_tmul'], he]

Depends on / 依赖: IsTensorProduct, IsTensorProduct.of_equiv, e.restrictScalars, of_equiv, restrictScalars, smul_tmul
-/
lemma IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N) (he : forall x, e (1 otimesₜ x) = f x) :
    IsBaseChange S f := by
  apply IsTensorProduct.of_equiv (e.restrictScalars R)
  intro x y
  simp [show x otimesₜ[R] y = x • (1 otimesₜ[R] y) by simp [smul_tmul'], he]

variable (R S) in
/--
theorem `IsBaseChange.linearMap` / 定理 `IsBaseChange.linearMap`

English:
theorem IsBaseChange.linearMap
  statement: IsBaseChange S (Algebra.linearMap R S)
  proof: of_equiv (AlgebraTensorModule.rid R S S) fun x => by
    simpa using (Algebra.algebraMap_eq_smul_one x).symm

中文:
定理 IsBaseChange.linearMap
  结论: IsBaseChange S (代数.linearMap R S)
  证明: of_equiv (AlgebraTensorModule.rid R S S) fun x => by
    simpa using (Algebra.algebraMap_eq_smul_one x).symm

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, AlgebraTensorModule, AlgebraTensorModule.rid, algebraMap_eq_smul_one, of_equiv
-/
theorem IsBaseChange.linearMap : IsBaseChange S (Algebra.linearMap R S) :=
  of_equiv (AlgebraTensorModule.rid R S S) fun x => by
    simpa using (Algebra.algebraMap_eq_smul_one x).symm

variable [Module R Q] [IsScalarTower R S Q] {f' : P ->ₗ[R] Q}

/--
lemma `IsBaseChange.iff_of_equiv_comm` / 引理 `IsBaseChange.iff_of_equiv_comm`

English:
lemma IsBaseChange.iff_of_equiv_comm
  statement: (eM : M ≃ₗ[R] P) (eN : N ≃ₗ[S] Q)
  proof: by
  simp only [IsBaseChange]
  have (m : M) : f' (eM m) = eN (f m) := LinearMap.congr_fun comm m
  refine ⟨fun ist => ?_, fun ist => ?_⟩
  · convert! (ist.compl₂_linearEquiv eM.symm).compr₂_linearEquiv (eN.restrictScalars R)
    ext s m'
    obtain ⟨m, rfl⟩ := eM.surjective m'
    simp [this]
  · convert! (ist.compl₂_linearEquiv eM).compr₂_linearEquiv (eN.symm.restrictScalars R)
    ext s m
    simp [this]

中文:
引理 IsBaseChange.iff_of_equiv_comm
  结论: (eM : M ≃ₗ[R] P) (eN : N ≃ₗ[S] Q)
  证明: by
  simp only [IsBaseChange]
  have (m : M) : f' (eM m) = eN (f m) := LinearMap.congr_fun comm m
  refine ⟨fun ist => ?_, fun ist => ?_⟩
  · convert! (ist.compl₂_linearEquiv eM.symm).compr₂_linearEquiv (eN.restrictScalars R)
    ext s m'
    obtain ⟨m, rfl⟩ := eM.surjective m'
    simp [this]
  · convert! (ist.compl₂_linearEquiv eM).compr₂_linearEquiv (eN.symm.restrictScalars R)
    ext s m
    simp [this]

Depends on / 依赖: IsBaseChange, LinearMap, LinearMap.congr_fun, congr_fun, convert, eM.surjective, eM.symm, eN.restrictScalars, eN.symm.restrictScalars, ist.compl, restrictScalars, surjective
-/
lemma IsBaseChange.iff_of_equiv_comm (eM : M ≃ₗ[R] P) (eN : N ≃ₗ[S] Q)
    (comm : f'.comp eM.toLinearMap = (eN.restrictScalars R).comp f) :
    IsBaseChange S f ↔ IsBaseChange S f' := by
  simp only [IsBaseChange]
  have (m : M) : f' (eM m) = eN (f m) := LinearMap.congr_fun comm m
  refine ⟨fun ist => ?_, fun ist => ?_⟩
  · convert! (ist.compl₂_linearEquiv eM.symm).compr₂_linearEquiv (eN.restrictScalars R)
    ext s m'
    obtain ⟨m, rfl⟩ := eM.surjective m'
    simp [this]
  · convert! (ist.compl₂_linearEquiv eM).compr₂_linearEquiv (eN.symm.restrictScalars R)
    ext s m
    simp [this]

/--
lemma `IsBaseChange.comp_equiv` / 引理 `IsBaseChange.comp_equiv`

English:
lemma IsBaseChange.comp_equiv
  given: (e : M ≃ₗ[R] P) (f : P ->ₗ[R] N) (isb : IsBaseChange S f)
  proof: (IsBaseChange.iff_of_equiv_comm e (LinearEquiv.refl S N) (LinearMap.ext fun y => by simp)).mpr isb

中文:
引理 IsBaseChange.comp_equiv
  条件: (e : M ≃ₗ[R] P) (f : P ->ₗ[R] N) (isb : IsBaseChange S f)
  证明: (IsBaseChange.iff_of_equiv_comm e (LinearEquiv.refl S N) (LinearMap.ext fun y => by simp)).mpr isb

Depends on / 依赖: IsBaseChange, IsBaseChange.iff_of_equiv_comm, LinearEquiv, LinearEquiv.refl, LinearMap, LinearMap.ext, iff_of_equiv_comm
-/
lemma IsBaseChange.comp_equiv (e : M ≃ₗ[R] P) (f : P ->ₗ[R] N) (isb : IsBaseChange S f) :
    IsBaseChange S (f.comp e.toLinearMap) :=
  (IsBaseChange.iff_of_equiv_comm e (LinearEquiv.refl S N) (LinearMap.ext fun y => by simp)).mpr isb

section

variable (A : Type*) [CommSemiring A]
variable [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Module S M] [IsScalarTower R S M]
variable [Module A N] [IsScalarTower S A N] [IsScalarTower R A N]

/--
lemma `isBaseChange_tensorProduct_map` / 引理 `isBaseChange_tensorProduct_map`

English:
lemma isBaseChange_tensorProduct_map
  given: {f : M ->ₗ[S] N} (hf : IsBaseChange A f)
  proof: by
  let e : A otimes[S] (M otimes[R] P) ≃ₗ[A] N otimes[R] P := (AlgebraTensorModule.assoc R S A A M P).symm.trans
    (AlgebraTensorModule.congr hf.equiv (LinearEquiv.refl R P))
  refine IsBaseChange.of_equiv e (fun x => ?_)
  induction x with
  | zero => simp
  | tmul => simp [e, IsBaseChange.equiv_tmul]
  | add _ _ h1 h2 => simp [tmul_add, h1, h2]

中文:
引理 isBaseChange_tensorProduct_map
  条件: {f : M ->ₗ[S] N} (hf : IsBaseChange A f)
  证明: by
  let e : A otimes[S] (M otimes[R] P) ≃ₗ[A] N otimes[R] P := (AlgebraTensorModule.assoc R S A A M P).symm.trans
    (AlgebraTensorModule.congr hf.equiv (LinearEquiv.refl R P))
  refine IsBaseChange.of_equiv e (fun x => ?_)
  induction x with
  | zero => simp
  | tmul => simp [e, IsBaseChange.equiv_tmul]
  | add _ _ h1 h2 => simp [tmul_add, h1, h2]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.assoc, AlgebraTensorModule.congr, IsBaseChange, IsBaseChange.equiv_tmul, IsBaseChange.of_equiv, LinearEquiv, LinearEquiv.refl, equiv_tmul, hf.equiv, of_equiv, otimes, symm.trans, tmul_add
-/
lemma isBaseChange_tensorProduct_map {f : M ->ₗ[S] N} (hf : IsBaseChange A f) :
    IsBaseChange A (AlgebraTensorModule.map f (LinearMap.id (R := R) (M := P))) := by
  let e : A otimes[S] (M otimes[R] P) ≃ₗ[A] N otimes[R] P := (AlgebraTensorModule.assoc R S A A M P).symm.trans
    (AlgebraTensorModule.congr hf.equiv (LinearEquiv.refl R P))
  refine IsBaseChange.of_equiv e (fun x => ?_)
  induction x with
  | zero => simp
  | tmul => simp [e, IsBaseChange.equiv_tmul]
  | add _ _ h1 h2 => simp [tmul_add, h1, h2]

end

variable (f) in
/--
theorem `IsBaseChange.of_lift_unique` / 定理 `IsBaseChange.of_lift_unique`

English:
theorem IsBaseChange.of_lift_unique
  proof: by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S otimes[R] M)
      (ULift.moduleEquiv.symm.toLinearMap.comp <| TensorProduct.mk R S M 1)
  let f' : S otimes[R] M ->ₗ[R] N :=
    TensorProduct.lift (((LinearMap.flip (AlgHom.toLinearMap (Algebra.ofId S
      (Module.End S (M ->ₗ[R] N))))) f).restrictScalars R)
  change Function.Bijective f'
  let f'' : S otimes[R] M ->ₗ[S] N := by
    refine
      { f' with
        map_smul' := fun s x =>
          TensorProduct.induction_on x ?_ (fun s' y => smul_assoc s s' _) fun x y hx hy => ?_ }
    · dsimp; rw [map_zero, smul_zero, map_zero, smul_zero]
    · dsimp at *; rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S otimes[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinearMap f'' (ULift.moduleEquiv.toLinearMap.comp g) ?_ ?_
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective]
    refine (h (ULift.{max v₁ v₃} N) <| ULift.moduleEquiv.symm.toLinearMap.comp f).unique ?_ rfl
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x
    change (g <| (1 : S) • f x).down = _
    rw [one_smul]; rw [hg]
    rfl

中文:
定理 IsBaseChange.of_lift_unique
  证明: by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S otimes[R] M)
      (ULift.moduleEquiv.symm.toLinearMap.comp <| TensorProduct.mk R S M 1)
  let f' : S otimes[R] M ->ₗ[R] N :=
    TensorProduct.lift (((LinearMap.flip (AlgHom.toLinearMap (Algebra.ofId S
      (Module.End S (M ->ₗ[R] N))))) f).restrictScalars R)
  change Function.Bijective f'
  let f'' : S otimes[R] M ->ₗ[S] N := by
    refine
      { f' with
        map_smul' := fun s x =>
          TensorProduct.induction_on x ?_ (fun s' y => smul_assoc s s' _) fun x y hx hy => ?_ }
    · dsimp; rw [map_zero, smul_zero, map_zero, smul_zero]
    · dsimp at *; rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S otimes[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinearMap f'' (ULift.moduleEquiv.toLinearMap.comp g) ?_ ?_
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective]
    refine (h (ULift.{max v₁ v₃} N) <| ULift.moduleEquiv.symm.toLinearMap.comp f).unique ?_ rfl
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x
    change (g <| (1 : S) • f x).down = _
    rw [one_smul]; rw [hg]
    rfl

Depends on / 依赖: AlgHom, AlgHom.toLinearMap, Algebra, Algebra.ofId, Bijective, Function, Function.Bijective, LinearMap, LinearMap.flip, Module, Module.End, TensorProduct, TensorProduct.induction_on, TensorProduct.lift, TensorProduct.mk, ULift.moduleEquiv.symm.toLinearMap.comp, induction_on, map_smul, map_z, moduleEquiv
-/
theorem IsBaseChange.of_lift_unique
    (h : forall (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
      forall [Module R Q] [Module S Q], forall [IsScalarTower R S Q],
        forall g : M ->ₗ[R] Q, exists! g' : N ->ₗ[S] Q, (g'.restrictScalars R).comp f = g) :
    IsBaseChange S f := by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S otimes[R] M)
      (ULift.moduleEquiv.symm.toLinearMap.comp <| TensorProduct.mk R S M 1)
  let f' : S otimes[R] M ->ₗ[R] N :=
    TensorProduct.lift (((LinearMap.flip (AlgHom.toLinearMap (Algebra.ofId S
      (Module.End S (M ->ₗ[R] N))))) f).restrictScalars R)
  change Function.Bijective f'
  let f'' : S otimes[R] M ->ₗ[S] N := by
    refine
      { f' with
        map_smul' := fun s x =>
          TensorProduct.induction_on x ?_ (fun s' y => smul_assoc s s' _) fun x y hx hy => ?_ }
    · dsimp; rw [map_zero, smul_zero, map_zero, smul_zero]
    · dsimp at *; rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S otimes[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinearMap f'' (ULift.moduleEquiv.toLinearMap.comp g) ?_ ?_
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective]
    refine (h (ULift.{max v₁ v₃} N) <| ULift.moduleEquiv.symm.toLinearMap.comp f).unique ?_ rfl
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x
    change (g <| (1 : S) • f x).down = _
    rw [one_smul]; rw [hg]
    rfl

/--
theorem `IsBaseChange.iff_lift_unique` / 定理 `IsBaseChange.iff_lift_unique`

English:
theorem IsBaseChange.iff_lift_unique
  proof: ⟨fun h => by
    intro Q _ _ _ _ g
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.algHom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩

中文:
定理 IsBaseChange.iff_lift_unique
  证明: ⟨fun h => by
    intro Q _ _ _ _ g
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.algHom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩

Depends on / 依赖: IsBaseChange, IsBaseChange.of_lift_unique, algHom_ext, e.trans, h.algHom_ext, h.lift, h.lift_comp, lift_comp, of_lift_unique
-/
theorem IsBaseChange.iff_lift_unique :
    IsBaseChange S f ↔
      forall (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
        forall [Module R Q] [Module S Q],
          forall [IsScalarTower R S Q],
            forall g : M ->ₗ[R] Q, exists! g' : N ->ₗ[S] Q, (g'.restrictScalars R).comp f = g :=
  ⟨fun h => by
    intro Q _ _ _ _ g
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.algHom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsBaseChange.ofEquiv` / 定理 `IsBaseChange.ofEquiv`

English:
theorem IsBaseChange.ofEquiv
  given: (e : M ≃ₗ[R] N)
  statement: IsBaseChange R e.toLinearMap
  proof: by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    change (by let _ := I₂; exact r • q) = (by let _ := I₃; exact r • q)
    dsimp
    rw [← one_smul R q]; rw [smul_smul]; rw [← @smul_assoc _ _ _ (id _) (id _) (id _) I₄]; rw [smul_eq_mul]
  cases this
  refine
    ⟨g.comp e.symm.toLinearMap, by
      ext
      simp, ?_⟩
  rintro y (rfl : _ = _)
  ext
  simp

中文:
定理 IsBaseChange.ofEquiv
  条件: (e : M ≃ₗ[R] N)
  结论: IsBaseChange R e.toLinearMap
  证明: by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    change (by let _ := I₂; exact r • q) = (by let _ := I₃; exact r • q)
    dsimp
    rw [← one_smul R q]; rw [smul_smul]; rw [← @smul_assoc _ _ _ (id _) (id _) (id _) I₄]; rw [smul_eq_mul]
  cases this
  refine
    ⟨g.comp e.symm.toLinearMap, by
      ext
      simp, ?_⟩
  rintro y (rfl : _ = _)
  ext
  simp

Depends on / 依赖: IsBaseChange, IsBaseChange.of_lift_unique, e.symm.toLinearMap, g.comp, of_lift_unique, one_smul, smul_assoc, smul_eq_mul, smul_smul, toLinearMap
-/
theorem IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap := by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    change (by let _ := I₂; exact r • q) = (by let _ := I₃; exact r • q)
    dsimp
    rw [← one_smul R q]; rw [smul_smul]; rw [← @smul_assoc _ _ _ (id _) (id _) (id _) I₄]; rw [smul_eq_mul]
  cases this
  refine
    ⟨g.comp e.symm.toLinearMap, by
      ext
      simp, ?_⟩
  rintro y (rfl : _ = _)
  ext
  simp

variable {T O : Type*} [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [AddCommMonoid O] [Module R O] [Module S O] [Module T O] [IsScalarTower S T O]
variable [IsScalarTower R S O] [IsScalarTower R T O]

/--
theorem `IsBaseChange.comp` / 定理 `IsBaseChange.comp`

English:
theorem IsBaseChange.comp
  statement: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {g : N ->ₗ[S] O}
  proof: by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  let := Module.compHom Q (algebraMap S T)
  have : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def]; rw [mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := IsScalarTower.to₁₂₄ _ _ T _
  refine
    ⟨hg.lift (hf.lift i), by
      ext
      simp [IsBaseChange.lift_eq], ?_⟩
  rintro g' (e : _ = _)
  refine hg.algHom_ext' _ _ (hf.algHom_ext' _ _ ?_)
  rw [IsBaseChange.lift_comp]; rw [IsBaseChange.lift_comp]; rw [← e]
  ext
  rfl

中文:
定理 IsBaseChange.comp
  结论: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {g : N ->ₗ[S] O}
  证明: by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  let := Module.compHom Q (algebraMap S T)
  have : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def]; rw [mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := IsScalarTower.to₁₂₄ _ _ T _
  refine
    ⟨hg.lift (hf.lift i), by
      ext
      simp [IsBaseChange.lift_eq], ?_⟩
  rintro g' (e : _ = _)
  refine hg.algHom_ext' _ _ (hf.algHom_ext' _ _ ?_)
  rw [IsBaseChange.lift_comp]; rw [IsBaseChange.lift_comp]; rw [← e]
  ext
  rfl

Depends on / 依赖: Algebra, Algebra.smul_def, IsBaseChange, IsBaseChange.lift_comp, IsBaseChange.lift_eq, IsBaseChange.of_lift_unique, IsScalarTower, IsScalarTower.to, Module, Module.compHom, algHom_ext, algebraMap, compHom, hf.algHom_ext, hf.lift, hg.algHom_ext, hg.lift, lift_comp, lift_eq, mul_smul
-/
theorem IsBaseChange.comp {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {g : N ->ₗ[S] O}
    (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScalars R).comp f) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  let := Module.compHom Q (algebraMap S T)
  have : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def]; rw [mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := IsScalarTower.to₁₂₄ _ _ T _
  refine
    ⟨hg.lift (hf.lift i), by
      ext
      simp [IsBaseChange.lift_eq], ?_⟩
  rintro g' (e : _ = _)
  refine hg.algHom_ext' _ _ (hf.algHom_ext' _ _ ?_)
  rw [IsBaseChange.lift_comp]; rw [IsBaseChange.lift_comp]; rw [← e]
  ext
  rfl

/--
lemma `IsBaseChange.of_comp` / 引理 `IsBaseChange.of_comp`

English:
lemma IsBaseChange.of_comp
  statement: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S] O}
  proof: by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ r
  let : Module R Q := .restrictScalars R S Q
  have : IsScalarTower R S Q := .restrictScalars R S Q
  have : IsScalarTower R T Q := IsScalarTower.of_algebraMap_smul fun r x => by
    simp [IsScalarTower.algebraMap_apply R S T]
  let r' : M ->ₗ[R] Q := r ∘ₗ f
  let q : O ->ₗ[T] Q := hc.lift r'
  refine ⟨q, ?_, ?_⟩
  · apply hf.algHom_ext'
    simp [r', q, LinearMap.comp_assoc, hc.lift_comp]
  · intro q' hq'
    apply hc.algHom_ext'
    apply_fun LinearMap.restrictScalars R at hq'
    rw [← LinearMap.comp_assoc]
    rw [show q'.restrictScalars R ∘ₗ h.restrictScalars R = _ from hq']; rw [hc.lift_comp]

中文:
引理 IsBaseChange.of_comp
  结论: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S] O}
  证明: by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ r
  let : Module R Q := .restrictScalars R S Q
  have : IsScalarTower R S Q := .restrictScalars R S Q
  have : IsScalarTower R T Q := IsScalarTower.of_algebraMap_smul fun r x => by
    simp [IsScalarTower.algebraMap_apply R S T]
  let r' : M ->ₗ[R] Q := r ∘ₗ f
  let q : O ->ₗ[T] Q := hc.lift r'
  refine ⟨q, ?_, ?_⟩
  · apply hf.algHom_ext'
    simp [r', q, LinearMap.comp_assoc, hc.lift_comp]
  · intro q' hq'
    apply hc.algHom_ext'
    apply_fun LinearMap.restrictScalars R at hq'
    rw [← LinearMap.comp_assoc]
    rw [show q'.restrictScalars R ∘ₗ h.restrictScalars R = _ from hq']; rw [hc.lift_comp]

Depends on / 依赖: IsBaseChange, IsBaseChange.of_lift_unique, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.of_algebraMap_smul, LinearMap, LinearMap.comp_assoc, LinearMap.restrictScalars, Module, algHom_ext, algebraMap_apply, apply_fun, comp_assoc, hc.algHom_ext, hc.lift, hc.lift_comp, hf.algHom_ext, lift_comp, of_algebraMap_smul, of_lift_unique
-/
lemma IsBaseChange.of_comp {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S] O}
    (hc : IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f)) :
    IsBaseChange T h := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ r
  let : Module R Q := .restrictScalars R S Q
  have : IsScalarTower R S Q := .restrictScalars R S Q
  have : IsScalarTower R T Q := IsScalarTower.of_algebraMap_smul fun r x => by
    simp [IsScalarTower.algebraMap_apply R S T]
  let r' : M ->ₗ[R] Q := r ∘ₗ f
  let q : O ->ₗ[T] Q := hc.lift r'
  refine ⟨q, ?_, ?_⟩
  · apply hf.algHom_ext'
    simp [r', q, LinearMap.comp_assoc, hc.lift_comp]
  · intro q' hq'
    apply hc.algHom_ext'
    apply_fun LinearMap.restrictScalars R at hq'
    rw [← LinearMap.comp_assoc]
    rw [show q'.restrictScalars R ∘ₗ h.restrictScalars R = _ from hq']; rw [hc.lift_comp]

/--
lemma `IsBaseChange.comp_iff` / 引理 `IsBaseChange.comp_iff`

English:
lemma IsBaseChange.comp_iff
  given: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S] O}
  proof: ⟨fun hc => IsBaseChange.of_comp hf hc, fun hh => IsBaseChange.comp hf hh⟩

中文:
引理 IsBaseChange.comp_iff
  条件: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S] O}
  证明: ⟨fun hc => IsBaseChange.of_comp hf hc, fun hh => IsBaseChange.comp hf hh⟩

Depends on / 依赖: IsBaseChange, IsBaseChange.comp, IsBaseChange.of_comp, of_comp
-/
lemma IsBaseChange.comp_iff {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S] O} :
    IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f) ↔ IsBaseChange T h :=
  ⟨fun hc => IsBaseChange.of_comp hf hc, fun hh => IsBaseChange.comp hf hh⟩

/--
Definition of `IsBaseChange.tensorEquiv` / `IsBaseChange.tensorEquiv` 的定义

English:
definition IsBaseChange.tensorEquiv
  signature: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) (P : Type*)
  body: LinearEquiv.lTensor P hf.equiv.symm ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S P M

中文:
定义 IsBaseChange.tensorEquiv
  签名: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) (P : 类型)
  定义体: LinearEquiv.lTensor P hf.equiv.symm ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S P M

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, LinearEquiv, LinearEquiv.lTensor, cancelBaseChange, hf.equiv.symm, lTensor
-/
noncomputable def IsBaseChange.tensorEquiv {f : M ->ₗ[R] N} (hf : IsBaseChange S f) (P : Type*)
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] : P otimes[S] N ≃ₗ[S] P otimes[R] M :=
  LinearEquiv.lTensor P hf.equiv.symm ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S P M

/--
theorem `IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap` / 定理 `IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap`

English:
theorem IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap
  proof: by
  ext y
  refine IsTensorProduct.inductionOn hf y (by simp) ?_ (fun _ _ ha hb => by simp [ha, hb])
  intro s m
  rw [hf.map_eq hf]
  simpa using smul_comm x s (f m)

中文:
定理 IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap
  证明: by
  ext y
  refine IsTensorProduct.inductionOn hf y (by simp) ?_ (fun _ _ ha hb => by simp [ha, hb])
  intro s m
  rw [hf.map_eq hf]
  simpa using smul_comm x s (f m)

Depends on / 依赖: IsTensorProduct, IsTensorProduct.inductionOn, hf.map_eq, inductionOn, map_eq, smul_comm
-/
theorem IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap
    {f : M ->ₗ[R] N} (hf : IsBaseChange S f) (x : R) :
    hf.map hf LinearMap.id (LinearMap.lsmul R M x) = LinearMap.lsmul S N (algebraMap R S x) := by
  ext y
  refine IsTensorProduct.inductionOn hf y (by simp) ?_ (fun _ _ ha hb => by simp [ha, hb])
  intro s m
  rw [hf.map_eq hf]
  simpa using smul_comm x s (f m)

variable {R' S' : Type*} [CommSemiring R'] [CommSemiring S']
variable [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

open IsScalarTower (toAlgHom algebraMap_apply)

variable (R S R' S')

/-- A type-class stating that the following diagram of scalar towers
```
R → S
↓ ↓
R' → S'
```
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
@[mk_iff]
/--
Definition of `Algebra.IsPushout` / `Algebra.IsPushout` 的定义

English:
class Algebra.IsPushout
  parameters: : Prop where
  axioms and operations (1):
    - out : IsBaseChange S (toAlgHom R R' S').toLinearMap

中文:
类 代数.是推出
  参数: : 命题 where
  公理与运算 (1 个):
    - out : IsBaseChange S (toAlgHom R R' S').toLinearMap
-/
class Algebra.IsPushout : Prop where
  out : IsBaseChange S (toAlgHom R R' S').toLinearMap

/-- The isomorphism `S' ≃ S ⊗[R] R` given `Algebra.IsPushout R S R' S'`. -/
noncomputable
/--
Definition of `Algebra.IsPushout.equiv` / `Algebra.IsPushout.equiv` 的定义

English:
definition Algebra.IsPushout.equiv
  signature: [h : Algebra.IsPushout R S R' S']
  body: h.out.equiv
  map_mul' x y := by
    dsimp
    induction x with
    | zero => simp
    | add x y _ _ => simp [*, add_mul]
    | tmul a b =>
      induction y with
      | zero => simp
      | add x y _ _ => simp [*, mul_add]
      | tmul x y => simp [IsBaseChange.equiv_tmul, Algebra.smul_def, mul_mul_mul_comm]
  commutes' := by simp [IsBaseChange.equiv_tmul, Algebra.smul_def]

中文:
定义 代数.是推出.equiv
  签名: [h : 代数.是推出 R S R' S']
  定义体: h.out.equiv
  map_mul' x y := by
    dsimp
    induction x with
    | zero => simp
    | add x y _ _ => simp [*, add_mul]
    | tmul a b =>
      induction y with
      | zero => simp
      | add x y _ _ => simp [*, mul_add]
      | tmul x y => simp [IsBaseChange.equiv_tmul, Algebra.smul_def, mul_mul_mul_comm]
  commutes' := by simp [IsBaseChange.equiv_tmul, Algebra.smul_def]

Depends on / 依赖: h.out.equiv
-/
def Algebra.IsPushout.equiv [h : Algebra.IsPushout R S R' S'] : S otimes[R] R' ≃ₐ[S] S' where
  __ := h.out.equiv
  map_mul' x y := by
    dsimp
    induction x with
    | zero => simp
    | add x y _ _ => simp [*, add_mul]
    | tmul a b =>
      induction y with
      | zero => simp
      | add x y _ _ => simp [*, mul_add]
      | tmul x y => simp [IsBaseChange.equiv_tmul, Algebra.smul_def, mul_mul_mul_comm]
  commutes' := by simp [IsBaseChange.equiv_tmul, Algebra.smul_def]

/--
lemma `Algebra.IsPushout.equiv_tmul` / 引理 `Algebra.IsPushout.equiv_tmul`

English:
lemma Algebra.IsPushout.equiv_tmul
  given: [h : Algebra.IsPushout R S R' S'] (a : S) (b : R')
  proof: (h.out.equiv_tmul _ _).trans (Algebra.smul_def _ _)

中文:
引理 代数.是推出.equiv_tmul
  条件: [h : 代数.是推出 R S R' S'] (a : S) (b : R')
  证明: (h.out.equiv_tmul _ _).trans (Algebra.smul_def _ _)

Depends on / 依赖: Algebra, Algebra.smul_def, equiv_tmul, h.out.equiv_tmul, smul_def
-/
lemma Algebra.IsPushout.equiv_tmul [h : Algebra.IsPushout R S R' S'] (a : S) (b : R') :
    equiv R S R' S' (a otimesₜ b) = algebraMap _ _ a * algebraMap _ _ b :=
  (h.out.equiv_tmul _ _).trans (Algebra.smul_def _ _)

/--
lemma `Algebra.IsPushout.equiv_symm_algebraMap_left` / 引理 `Algebra.IsPushout.equiv_symm_algebraMap_left`

English:
lemma Algebra.IsPushout.equiv_symm_algebraMap_left
  given: [Algebra.IsPushout R S R' S'] (a : S)
  proof: by
  rw [(equiv R S R' S').symm_apply_eq]; rw [equiv_tmul]; rw [map_one]; rw [mul_one]

中文:
引理 代数.是推出.equiv_symm_algebraMap_left
  条件: [代数.是推出 R S R' S'] (a : S)
  证明: by
  rw [(equiv R S R' S').symm_apply_eq]; rw [equiv_tmul]; rw [map_one]; rw [mul_one]

Depends on / 依赖: equiv_tmul, map_one, mul_one, symm_apply_eq
-/
lemma Algebra.IsPushout.equiv_symm_algebraMap_left [Algebra.IsPushout R S R' S'] (a : S) :
    (equiv R S R' S').symm (algebraMap S S' a) = a otimesₜ 1 := by
  rw [(equiv R S R' S').symm_apply_eq]; rw [equiv_tmul]; rw [map_one]; rw [mul_one]

/--
lemma `Algebra.IsPushout.equiv_symm_algebraMap_right` / 引理 `Algebra.IsPushout.equiv_symm_algebraMap_right`

English:
lemma Algebra.IsPushout.equiv_symm_algebraMap_right
  given: [Algebra.IsPushout R S R' S'] (a : R')
  proof: by
  rw [(equiv R S R' S').symm_apply_eq]; rw [equiv_tmul]; rw [map_one]; rw [one_mul]

中文:
引理 代数.是推出.equiv_symm_algebraMap_right
  条件: [代数.是推出 R S R' S'] (a : R')
  证明: by
  rw [(equiv R S R' S').symm_apply_eq]; rw [equiv_tmul]; rw [map_one]; rw [one_mul]

Depends on / 依赖: equiv_tmul, map_one, one_mul, symm_apply_eq
-/
lemma Algebra.IsPushout.equiv_symm_algebraMap_right [Algebra.IsPushout R S R' S'] (a : R') :
    (equiv R S R' S').symm (algebraMap R' S' a) = 1 otimesₜ a := by
  rw [(equiv R S R' S').symm_apply_eq]; rw [equiv_tmul]; rw [map_one]; rw [one_mul]

variable {R S R' S'}

@[symm]
/--
theorem `Algebra.IsPushout.symm` / 定理 `Algebra.IsPushout.symm`

English:
theorem Algebra.IsPushout.symm
  given: (h : Algebra.IsPushout R S R' S')
  statement: Algebra.IsPushout R R' S S' where
  proof: .of_equiv
    { __ := (TensorProduct.comm R ..).toAddEquiv.trans (equiv R S R' S').toAddEquiv,
      map_smul' _ x := x.induction_on (by simp) (fun _ _ => by
        simp [equiv_tmul, Algebra.smul_def, mul_left_comm]) (by simp +contextual) }
    fun _ => by simp [equiv_tmul]

中文:
定理 代数.是推出.symm
  条件: (h : 代数.是推出 R S R' S')
  结论: 代数.是推出 R R' S S' where
  证明: .of_equiv
    { __ := (TensorProduct.comm R ..).toAddEquiv.trans (equiv R S R' S').toAddEquiv,
      map_smul' _ x := x.induction_on (by simp) (fun _ _ => by
        simp [equiv_tmul, Algebra.smul_def, mul_left_comm]) (by simp +contextual) }
    fun _ => by simp [equiv_tmul]

Depends on / 依赖: of_equiv
-/
theorem Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPushout R R' S S' where
  out := .of_equiv
    { __ := (TensorProduct.comm R ..).toAddEquiv.trans (equiv R S R' S').toAddEquiv,
      map_smul' _ x := x.induction_on (by simp) (fun _ _ => by
        simp [equiv_tmul, Algebra.smul_def, mul_left_comm]) (by simp +contextual) }
    fun _ => by simp [equiv_tmul]

variable (R S R' S')

/--
theorem `Algebra.IsPushout.comm` / 定理 `Algebra.IsPushout.comm`

English:
theorem Algebra.IsPushout.comm
  statement: Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R R' S S'
  proof: ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩

中文:
定理 代数.是推出.comm
  结论: 代数.是推出 R S R' S' ↔ 代数.是推出 R R' S S'
  证明: ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩

Depends on / 依赖: Algebra, Algebra.IsPushout.symm, IsPushout
-/
theorem Algebra.IsPushout.comm : Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R R' S S' :=
  ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R R S S
  body: .of_equiv (TensorProduct.lid R S) fun _ => by simp

中文:
实例 :
  签名: 代数.是推出 R R S S
  定义体: .of_equiv (TensorProduct.lid R S) fun _ => by simp

Depends on / 依赖: TensorProduct, TensorProduct.lid, of_equiv
-/
instance : Algebra.IsPushout R R S S where
  out := .of_equiv (TensorProduct.lid R S) fun _ => by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R S R S
  body: .symm inferInstance

中文:
实例 :
  签名: 代数.是推出 R S R S
  定义体: .symm inferInstance
-/
instance : Algebra.IsPushout R S R S := .symm inferInstance

variable {R S R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/--
Instance `TensorProduct.isPushout` / 实例 `TensorProduct.isPushout`

English:
instance TensorProduct.isPushout
  signature: {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  body: ⟨TensorProduct.isBaseChange R T S⟩

中文:
实例 张量积.isPushout
  签名: {R S T : 类型} [交换半环 R] [交换半环 S] [交换半环 T]
  定义体: ⟨TensorProduct.isBaseChange R T S⟩

Depends on / 依赖: TensorProduct, TensorProduct.isBaseChange, isBaseChange
-/
instance TensorProduct.isPushout {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R S T (S otimes[R] T) :=
  ⟨TensorProduct.isBaseChange R T S⟩

/--
Instance `TensorProduct.isPushout'` / 实例 `TensorProduct.isPushout'`

English:
instance TensorProduct.isPushout'
  signature: {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  body: Algebra.IsPushout.symm inferInstance

中文:
实例 张量积.isPushout'
  签名: {R S T : 类型} [交换半环 R] [交换半环 S] [交换半环 T]
  定义体: Algebra.IsPushout.symm inferInstance

Depends on / 依赖: Algebra, Algebra.IsPushout.symm, IsPushout
-/
instance TensorProduct.isPushout' {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R T S (S otimes[R] T) :=
  Algebra.IsPushout.symm inferInstance

/--
lemma `Algebra.IsPushout.tensorProduct_tensorProduct` / 引理 `Algebra.IsPushout.tensorProduct_tensorProduct`

English:
lemma Algebra.IsPushout.tensorProduct_tensorProduct
  proof: by
  constructor
  convert! isBaseChange_tensorProduct_map (R := R) (P := S) _ (IsBaseChange.linearMap A B)
  ext s
  simpa using congr($H s)

中文:
引理 代数.是推出.tensorProduct_tensorProduct
  证明: by
  constructor
  convert! isBaseChange_tensorProduct_map (R := R) (P := S) _ (IsBaseChange.linearMap A B)
  ext s
  simpa using congr($H s)

Depends on / 依赖: IsBaseChange, IsBaseChange.linearMap, convert, isBaseChange_tensorProduct_map, linearMap
-/
lemma Algebra.IsPushout.tensorProduct_tensorProduct
    (R S A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra R S]
    {_ : Algebra (A otimes[R] S) (B otimes[R] S)} {_ : IsScalarTower A (A otimes[R] S) (B otimes[R] S)}
    (H : (algebraMap (A otimes[R] S) (B otimes[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsPushout A B (A otimes[R] S) (B otimes[R] S) := by
  constructor
  convert! isBaseChange_tensorProduct_map (R := R) (P := S) _ (IsBaseChange.linearMap A B)
  ext s
  simpa using congr($H s)

/-- If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and `g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomorphism `S' → A`.
-/
@[simps! -isSimp apply]
/--
Definition of `Algebra.pushoutDesc` / `Algebra.pushoutDesc` 的定义

English:
definition Algebra.pushoutDesc
  signature: [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
  body: (Algebra.TensorProduct.lift f g hf).comp
    ((Algebra.IsPushout.equiv R S R' S').symm.toAlgHom.restrictScalars R)

中文:
定义 代数.pushoutDesc
  签名: [H : 代数.是推出 R S R' S'] {A : 类型} [半环 A]
  定义体: (Algebra.TensorProduct.lift f g hf).comp
    ((Algebra.IsPushout.equiv R S R' S').symm.toAlgHom.restrictScalars R)

Depends on / 依赖: Algebra, Algebra.IsPushout.equiv, Algebra.TensorProduct.lift, IsPushout, TensorProduct, restrictScalars, symm.toAlgHom.restrictScalars, toAlgHom
-/
noncomputable def Algebra.pushoutDesc [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (hf : forall x y, f x * g y = g y * f x) :
    S' ->ₐ[R] A :=
  (Algebra.TensorProduct.lift f g hf).comp
    ((Algebra.IsPushout.equiv R S R' S').symm.toAlgHom.restrictScalars R)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Algebra.pushoutDesc_left` / 定理 `Algebra.pushoutDesc_left`

English:
theorem Algebra.pushoutDesc_left
  statement: [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
  proof: by
  simp [Algebra.pushoutDesc_apply]

中文:
定理 代数.pushoutDesc_left
  结论: [代数.是推出 R S R' S'] {A : 类型} [半环 A]
  证明: by
  simp [Algebra.pushoutDesc_apply]

Depends on / 依赖: Algebra, Algebra.pushoutDesc_apply, pushoutDesc_apply
-/
theorem Algebra.pushoutDesc_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) (x : S) :
    Algebra.pushoutDesc S' f g H (algebraMap S S' x) = f x := by
  simp [Algebra.pushoutDesc_apply]

/--
theorem `Algebra.lift_algHom_comp_left` / 定理 `Algebra.lift_algHom_comp_left`

English:
theorem Algebra.lift_algHom_comp_left
  statement: [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
  proof: AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x :)

中文:
定理 代数.lift_algHom_comp_left
  结论: [代数.是推出 R S R' S'] {A : 类型} [半环 A]
  证明: AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x :)

Depends on / 依赖: AlgHom, AlgHom.ext, Algebra, Algebra.pushoutDesc_left, pushoutDesc_left
-/
theorem Algebra.lift_algHom_comp_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R S S') = f :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x :)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Algebra.pushoutDesc_right` / 定理 `Algebra.pushoutDesc_right`

English:
theorem Algebra.pushoutDesc_right
  statement: [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
  proof: by
  simp [Algebra.pushoutDesc_apply, Algebra.IsPushout.equiv_symm_algebraMap_right]

中文:
定理 代数.pushoutDesc_right
  结论: [代数.是推出 R S R' S'] {A : 类型} [半环 A]
  证明: by
  simp [Algebra.pushoutDesc_apply, Algebra.IsPushout.equiv_symm_algebraMap_right]

Depends on / 依赖: Algebra, Algebra.IsPushout.equiv_symm_algebraMap_right, Algebra.pushoutDesc_apply, IsPushout, equiv_symm_algebraMap_right, pushoutDesc_apply
-/
theorem Algebra.pushoutDesc_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) (x : R') :
    Algebra.pushoutDesc S' f g H (algebraMap R' S' x) = g x := by
  simp [Algebra.pushoutDesc_apply, Algebra.IsPushout.equiv_symm_algebraMap_right]

/--
theorem `Algebra.lift_algHom_comp_right` / 定理 `Algebra.lift_algHom_comp_right`

English:
theorem Algebra.lift_algHom_comp_right
  statement: [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
  proof: AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x :)

@[ext (iff := false)]

中文:
定理 代数.lift_algHom_comp_right
  结论: [代数.是推出 R S R' S'] {A : 类型} [半环 A]
  证明: AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x :)

@[ext (iff := false)]

Depends on / 依赖: AlgHom, AlgHom.ext, Algebra, Algebra.pushoutDesc_right, pushoutDesc_right
-/
theorem Algebra.lift_algHom_comp_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R R' S') = g :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x :)

@[ext (iff := false)]
/--
theorem `Algebra.IsPushout.algHom_ext` / 定理 `Algebra.IsPushout.algHom_ext`

English:
theorem Algebra.IsPushout.algHom_ext
  statement: [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
  proof: by
  ext x
  refine H.1.inductionOn x _ ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e
    rw [Algebra.smul_def]; rw [map_mul]; rw [map_mul]; rw [e]
    congr 1
    exact (AlgHom.congr_fun h₂ s :)
  · intro s₁ s₂ e₁ e₂
    rw [map_add]; rw [map_add]; rw [e₁]; rw [e₂]

中文:
定理 代数.是推出.algHom_ext
  结论: [H : 代数.是推出 R S R' S'] {A : 类型} [半环 A]
  证明: by
  ext x
  refine H.1.inductionOn x _ ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e
    rw [Algebra.smul_def]; rw [map_mul]; rw [map_mul]; rw [e]
    congr 1
    exact (AlgHom.congr_fun h₂ s :)
  · intro s₁ s₂ e₁ e₂
    rw [map_add]; rw [map_add]; rw [e₁]; rw [e₂]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, Algebra, Algebra.smul_def, congr_fun, inductionOn, map_add, map_mul, map_zero, smul_def
-/
theorem Algebra.IsPushout.algHom_ext [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] {f g : S' ->ₐ[R] A} (h₁ : f.comp (toAlgHom R R' S') = g.comp (toAlgHom R R' S'))
    (h₂ : f.comp (toAlgHom R S S') = g.comp (toAlgHom R S S')) : f = g := by
  ext x
  refine H.1.inductionOn x _ ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e
    rw [Algebra.smul_def]; rw [map_mul]; rw [map_mul]; rw [e]
    congr 1
    exact (AlgHom.congr_fun h₂ s :)
  · intro s₁ s₂ e₁ e₂
    rw [map_add]; rw [map_add]; rw [e₁]; rw [e₂]

variable (R S R')
/--
lemma `Algebra.IsPushout.comp_iff` / 引理 `Algebra.IsPushout.comp_iff`

English:
lemma Algebra.IsPushout.comp_iff
  statement: {T' : Type*} [CommSemiring T'] [Algebra R T']
  proof: by
  let f : R' ->ₗ[R] S' := (IsScalarTower.toAlgHom R R' S').toLinearMap
  have : IsScalarTower R S T' := .of_algebraMap_eq fun x => by
    rw [algebraMap_apply R S' T']; rw [algebraMap_apply R S S']; rw [← algebraMap_apply S S' T']
  have heq : (toAlgHom S S' T').toLinearMap.restrictScalars R ∘ₗ f =
      (toAlgHom R R' T').toLinearMap := by
    ext x
    simp [f, ← IsScalarTower.algebraMap_apply]
  rw [isPushout_iff]; rw [isPushout_iff]; rw [← heq]; rw [IsBaseChange.comp_iff]
  exact Algebra.IsPushout.out

中文:
引理 代数.是推出.comp_iff
  结论: {T' : 类型} [交换半环 T'] [代数 R T']
  证明: by
  let f : R' ->ₗ[R] S' := (IsScalarTower.toAlgHom R R' S').toLinearMap
  have : IsScalarTower R S T' := .of_algebraMap_eq fun x => by
    rw [algebraMap_apply R S' T']; rw [algebraMap_apply R S S']; rw [← algebraMap_apply S S' T']
  have heq : (toAlgHom S S' T').toLinearMap.restrictScalars R ∘ₗ f =
      (toAlgHom R R' T').toLinearMap := by
    ext x
    simp [f, ← IsScalarTower.algebraMap_apply]
  rw [isPushout_iff]; rw [isPushout_iff]; rw [← heq]; rw [IsBaseChange.comp_iff]
  exact Algebra.IsPushout.out

Depends on / 依赖: Algebra, Algebra.IsPushout.out, IsBaseChange, IsBaseChange.comp_iff, IsPushout, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.toAlgHom, Subsingleton, Subsingleton.uniqueTopologicalSpace, algebraMap_apply, comp_iff, isPushout_iff, of_algebraMap_eq, restrictScalars, toAlgHom, toLinearMap, toLinearMap.restrictScalars, uniqueTopologicalSpace
-/
lemma Algebra.IsPushout.comp_iff {T' : Type*} [CommSemiring T'] [Algebra R T']
    [Algebra S' T'] [Algebra S T'] [Algebra T T'] [Algebra R' T']
    [IsScalarTower R T T'] [IsScalarTower S T T'] [IsScalarTower S S' T']
    [IsScalarTower R R' T'] [IsScalarTower R S' T'] [IsScalarTower R' S' T']
    [Algebra.IsPushout R S R' S'] :
    Algebra.IsPushout R T R' T' ↔ Algebra.IsPushout S T S' T' := by
  let f : R' ->ₗ[R] S' := (IsScalarTower.toAlgHom R R' S').toLinearMap
  have : IsScalarTower R S T' := .of_algebraMap_eq fun x => by
    rw [algebraMap_apply R S' T']; rw [algebraMap_apply R S S']; rw [← algebraMap_apply S S' T']
  have heq : (toAlgHom S S' T').toLinearMap.restrictScalars R ∘ₗ f =
      (toAlgHom R R' T').toLinearMap := by
    ext x
    simp [f, ← IsScalarTower.algebraMap_apply]
  rw [isPushout_iff]; rw [isPushout_iff]; rw [← heq]; rw [IsBaseChange.comp_iff]
  exact Algebra.IsPushout.out

variable {R R' S S'} in
/--
lemma `Algebra.IsPushout.of_equiv` / 引理 `Algebra.IsPushout.of_equiv`

English:
lemma Algebra.IsPushout.of_equiv
  statement: [h : IsPushout R R' S S']
  proof: by
  rw [isPushout_iff] at h ⊢
  refine IsBaseChange.of_equiv (h.equiv ≪≫ₗ e.toLinearEquiv) fun x => ?_
  simpa [h.equiv_tmul] using DFunLike.congr_fun he x

中文:
引理 代数.是推出.of_equiv
  结论: [h : 是推出 R R' S S']
  证明: by
  rw [isPushout_iff] at h ⊢
  refine IsBaseChange.of_equiv (h.equiv ≪≫ₗ e.toLinearEquiv) fun x => ?_
  simpa [h.equiv_tmul] using DFunLike.congr_fun he x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsBaseChange, IsBaseChange.of_equiv, Subsingleton, Subsingleton.discreteTopology, TopologicalSpace, congr_fun, discreteTopology, e.toLinearEquiv, equiv_tmul, h.equiv, h.equiv_tmul, isPushout_iff, of_equiv, toLinearEquiv
-/
lemma Algebra.IsPushout.of_equiv [h : IsPushout R R' S S']
    {T : Type*} [CommSemiring T] [Algebra R' T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R R' T] (e : S' ≃ₐ[R'] T)
    (he : e.toRingHom.comp (algebraMap S S') = algebraMap S T) :
    IsPushout R R' S T := by
  rw [isPushout_iff] at h ⊢
  refine IsBaseChange.of_equiv (h.equiv ≪≫ₗ e.toLinearEquiv) fun x => ?_
  simpa [h.equiv_tmul] using DFunLike.congr_fun he x

namespace Algebra

variable (A B : Type*)
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- (Implementation) If `B = S ⊗[R] A`, this is the canonical `R`-isomorphism:
`B ⊗[A] M ≃ₗ[S] S ⊗[R] M`. See `IsPushout.cancelBaseChange` for the `S`-linear version. -/
noncomputable
/--
Definition of `IsPushout.cancelBaseChangeAux` / `IsPushout.cancelBaseChangeAux` 的定义

English:
definition IsPushout.cancelBaseChangeAux
  signature: : B otimes[A] M ≃ₗ[R] S otimes[R] M
  body: have : IsPushout R A S B := IsPushout.symm inferInstance
  (AlgebraTensorModule.congr ((IsPushout.equiv R A S B).toLinearEquiv).symm
      (LinearEquiv.refl _ _)).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange _ _ A _ _).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R

@[simp]

中文:
定义 是推出.cancelBaseChangeAux
  签名: : B otimes[A] M ≃ₗ[R] S otimes[R] M
  定义体: have : IsPushout R A S B := IsPushout.symm inferInstance
  (AlgebraTensorModule.congr ((IsPushout.equiv R A S B).toLinearEquiv).symm
      (LinearEquiv.refl _ _)).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange _ _ A _ _).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AlgebraTensorModule.congr, IsPushout, IsPushout.equiv, IsPushout.symm, LinearEquiv, LinearEquiv.refl, TensorProduct, _root_, _root_.TensorProduct.comm, cancelBaseChange, restrictScalars, toLinearEquiv
-/
def IsPushout.cancelBaseChangeAux : B otimes[A] M ≃ₗ[R] S otimes[R] M :=
  have : IsPushout R A S B := IsPushout.symm inferInstance
  (AlgebraTensorModule.congr ((IsPushout.equiv R A S B).toLinearEquiv).symm
      (LinearEquiv.refl _ _)).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange _ _ A _ _).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R

@[simp]
/--
lemma `IsPushout.cancelBaseChangeAux_symm_tmul` / 引理 `IsPushout.cancelBaseChangeAux_symm_tmul`

English:
lemma IsPushout.cancelBaseChangeAux_symm_tmul
  given: (s : S) (m : M)
  proof: by
  simp [IsPushout.cancelBaseChangeAux, IsPushout.equiv_tmul]

中文:
引理 是推出.cancelBaseChangeAux_symm_tmul
  条件: (s : S) (m : M)
  证明: by
  simp [IsPushout.cancelBaseChangeAux, IsPushout.equiv_tmul]

Depends on / 依赖: IsPushout, IsPushout.cancelBaseChangeAux, IsPushout.equiv_tmul, cancelBaseChangeAux, equiv_tmul
-/
lemma IsPushout.cancelBaseChangeAux_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChangeAux R S A B M).symm (s otimesₜ m) = algebraMap S B s otimesₜ m := by
  simp [IsPushout.cancelBaseChangeAux, IsPushout.equiv_tmul]

/-- If `B = S ⊗[R] A`, this is the canonical `S`-isomorphism: `B ⊗[A] M ≃ₗ[S] S ⊗[R] M`.
This is the cancelling on the left version of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable
/--
Definition of `IsPushout.cancelBaseChange` / `IsPushout.cancelBaseChange` 的定义

English:
definition IsPushout.cancelBaseChange
  signature: : B otimes[A] M ≃ₗ[S] S otimes[R] M
  body: LinearEquiv.symm
AddEquiv.toLinearEquiv (IsPushout.cancelBaseChangeAux R S A B M).symm by
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s' m => simp [Algebra.smul_def, TensorProduct.smul_tmul']

@[simp]

中文:
定义 是推出.cancelBaseChange
  签名: : B otimes[A] M ≃ₗ[S] S otimes[R] M
  定义体: LinearEquiv.symm
AddEquiv.toLinearEquiv (IsPushout.cancelBaseChangeAux R S A B M).symm by
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s' m => simp [Algebra.smul_def, TensorProduct.smul_tmul']

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.toLinearEquiv, Algebra, Algebra.smul_def, IsPushout, IsPushout.cancelBaseChangeAux, LinearEquiv, LinearEquiv.symm, TensorProduct, TensorProduct.smul_tmul, cancelBaseChangeAux, map_add, smul_add, smul_def, smul_tmul, toLinearEquiv
-/
def IsPushout.cancelBaseChange : B otimes[A] M ≃ₗ[S] S otimes[R] M :=
LinearEquiv.symm
AddEquiv.toLinearEquiv (IsPushout.cancelBaseChangeAux R S A B M).symm by
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s' m => simp [Algebra.smul_def, TensorProduct.smul_tmul']

@[simp]
/--
lemma `IsPushout.cancelBaseChange_tmul` / 引理 `IsPushout.cancelBaseChange_tmul`

English:
lemma IsPushout.cancelBaseChange_tmul
  given: (m : M)
  proof: by
  change ((cancelBaseChangeAux R S A B M).symm).symm (1 otimesₜ[A] m) = 1 otimesₜ[R] m
  simp [cancelBaseChangeAux, TensorProduct.one_def]

@[simp]

中文:
引理 是推出.cancelBaseChange_tmul
  条件: (m : M)
  证明: by
  change ((cancelBaseChangeAux R S A B M).symm).symm (1 otimesₜ[A] m) = 1 otimesₜ[R] m
  simp [cancelBaseChangeAux, TensorProduct.one_def]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.one_def, cancelBaseChangeAux, one_def
-/
lemma IsPushout.cancelBaseChange_tmul (m : M) :
    IsPushout.cancelBaseChange R S A B M (1 otimesₜ m) = 1 otimesₜ m := by
  change ((cancelBaseChangeAux R S A B M).symm).symm (1 otimesₜ[A] m) = 1 otimesₜ[R] m
  simp [cancelBaseChangeAux, TensorProduct.one_def]

@[simp]
/--
lemma `IsPushout.cancelBaseChange_symm_tmul` / 引理 `IsPushout.cancelBaseChange_symm_tmul`

English:
lemma IsPushout.cancelBaseChange_symm_tmul
  given: (s : S) (m : M)
  proof: IsPushout.cancelBaseChangeAux_symm_tmul R S A B M s m

中文:
引理 是推出.cancelBaseChange_symm_tmul
  条件: (s : S) (m : M)
  证明: IsPushout.cancelBaseChangeAux_symm_tmul R S A B M s m

Depends on / 依赖: IsPushout, IsPushout.cancelBaseChangeAux_symm_tmul, cancelBaseChangeAux_symm_tmul
-/
lemma IsPushout.cancelBaseChange_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChange R S A B M).symm (s otimesₜ m) = algebraMap S B s otimesₜ m :=
  IsPushout.cancelBaseChangeAux_symm_tmul R S A B M s m

variable (C : Type*) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

/--
Definition of `IsPushout.cancelBaseChangeAlg` / `IsPushout.cancelBaseChangeAlg` 的定义

English:
definition IsPushout.cancelBaseChangeAlg
  signature: : B otimes[A] C ≃ₐ[S] S otimes[R] C
  body: by
  refine AlgEquiv.symm
    (AlgEquiv.ofLinearEquiv (IsPushout.cancelBaseChange R S A B C).symm ?_ ?_)
  · simp [TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    simp

@[simp]

中文:
定义 是推出.cancelBaseChangeAlg
  签名: : B otimes[A] C ≃ₐ[S] S otimes[R] C
  定义体: by
  refine AlgEquiv.symm
    (AlgEquiv.ofLinearEquiv (IsPushout.cancelBaseChange R S A B C).symm ?_ ?_)
  · simp [TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    simp

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, AlgEquiv.symm, IsPushout, IsPushout.cancelBaseChange, LinearMap, LinearMap.map_mul_of_map_mul_tmul, TensorProduct, TensorProduct.one_def, cancelBaseChange, map_mul_of_map_mul_tmul, ofLinearEquiv, one_def
-/
noncomputable def IsPushout.cancelBaseChangeAlg : B otimes[A] C ≃ₐ[S] S otimes[R] C := by
  refine AlgEquiv.symm
    (AlgEquiv.ofLinearEquiv (IsPushout.cancelBaseChange R S A B C).symm ?_ ?_)
  · simp [TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    simp

@[simp]
/--
lemma `IsPushout.toLinearEquiv_cancelBaseChangeAlg` / 引理 `IsPushout.toLinearEquiv_cancelBaseChangeAlg`

English:
lemma IsPushout.toLinearEquiv_cancelBaseChangeAlg
  proof: by
  rfl

@[simp]

中文:
引理 是推出.toLinearEquiv_cancelBaseChangeAlg
  证明: by
  rfl

@[simp]
-/
lemma IsPushout.toLinearEquiv_cancelBaseChangeAlg :
    (IsPushout.cancelBaseChangeAlg R S A B C).toLinearEquiv =
      IsPushout.cancelBaseChange R S A B C := by
  rfl

@[simp]
/--
lemma `IsPushout.cancelBaseChangeAlg_tmul` / 引理 `IsPushout.cancelBaseChangeAlg_tmul`

English:
lemma IsPushout.cancelBaseChangeAlg_tmul
  given: (c : C)
  proof: by
  simp [cancelBaseChangeAlg]

中文:
引理 是推出.cancelBaseChangeAlg_tmul
  条件: (c : C)
  证明: by
  simp [cancelBaseChangeAlg]

Depends on / 依赖: cancelBaseChangeAlg
-/
lemma IsPushout.cancelBaseChangeAlg_tmul (c : C) :
    IsPushout.cancelBaseChangeAlg R S A B C (1 otimesₜ c) = 1 otimesₜ c := by
  simp [cancelBaseChangeAlg]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `IsPushout.cancelBaseChangeAlg_symm_tmul` / 引理 `IsPushout.cancelBaseChangeAlg_symm_tmul`

English:
lemma IsPushout.cancelBaseChangeAlg_symm_tmul
  given: (s : S) (c : C)
  proof: by
  simp [cancelBaseChangeAlg]

中文:
引理 是推出.cancelBaseChangeAlg_symm_tmul
  条件: (s : S) (c : C)
  证明: by
  simp [cancelBaseChangeAlg]

Depends on / 依赖: cancelBaseChangeAlg
-/
lemma IsPushout.cancelBaseChangeAlg_symm_tmul (s : S) (c : C) :
    (IsPushout.cancelBaseChangeAlg R S A B C).symm (s otimesₜ c) = algebraMap S B s otimesₜ c := by
  simp [cancelBaseChangeAlg]

variable (S : Type*) [CommRing S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]
  [Algebra.IsPushout R S A B]

attribute [local instance] TensorProduct.rightAlgebra in
/--
lemma `IsPushout.cancelBaseChange_symm_comp_lTensor` / 引理 `IsPushout.cancelBaseChange_symm_comp_lTensor`

English:
lemma IsPushout.cancelBaseChange_symm_comp_lTensor
  proof: by
  ext
  simp [← TensorProduct.one_def, ← TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]

中文:
引理 是推出.cancelBaseChange_symm_comp_lTensor
  证明: by
  ext
  simp [← TensorProduct.one_def, ← TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]

Depends on / 依赖: RingHom, RingHom.algebraMap_toAlgebra, TensorProduct, TensorProduct.one_def, TensorProduct.tmul_one_eq_one_tmul, algebraMap_toAlgebra, one_def, tmul_one_eq_one_tmul
-/
lemma IsPushout.cancelBaseChange_symm_comp_lTensor :
    AlgHom.comp (IsPushout.cancelBaseChangeAlg R S A (S otimes[R] A) C).symm.toAlgHom
      (TensorProduct.lTensor _ (IsScalarTower.toAlgHom R A C)) =
      TensorProduct.includeLeft := by
  ext
  simp [← TensorProduct.one_def, ← TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]

end Algebra

end IsBaseChange
