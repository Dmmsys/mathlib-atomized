/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Linear equivalences of tensor products as isometries

These results are separate from the definition of `QuadraticForm.tmul` as that file is very slow.

## Main definitions

* `QuadraticForm.Isometry.tmul`: `TensorProduct.map` as a `QuadraticForm.Isometry`
* `QuadraticForm.tensorComm`: `TensorProduct.comm` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorAssoc`: `TensorProduct.assoc` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorRId`: `TensorProduct.rid` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorLId`: `TensorProduct.lid` as a `QuadraticForm.IsometryEquiv`
-/

@[expose] public section

universe uR uM₁ uM₂ uM₃ uM₄
variable {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃} {M₄ : Type uM₄}

open scoped TensorProduct

open QuadraticMap

namespace QuadraticForm

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Invertible (2 : R)]

@[simp]
/--
theorem `tmul_comp_tensorMap` / 定理 `tmul_comp_tensorMap`

English:
theorem tmul_comp_tensorMap
  proof: by
  have h₁ : Q₁ = Q₂.comp f.toLinearMap := QuadraticMap.ext fun x => (f.map_app x).symm
  have h₃ : Q₃ = Q₄.comp g.toLinearMap := QuadraticMap.ext fun x => (g.map_app x).symm
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₃ m₁' m₃'
  simp [h₁, h₃, associated_tmul]

@[simp

中文:
定理 tmul_comp_tensorMap
  证明: by
  have h₁ : Q₁ = Q₂.comp f.toLinearMap := QuadraticMap.ext fun x => (f.map_app x).symm
  have h₃ : Q₃ = Q₄.comp g.toLinearMap := QuadraticMap.ext fun x => (g.map_app x).symm
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₃ m₁' m₃'
  simp [h₁, h₃, associated_tmul]

@[simp

Depends on / 依赖: QuadraticMap, QuadraticMap.associated_rightInverse, QuadraticMap.ext, associated_rightInverse, associated_tmul, f.map_app, f.toLinearMap, g.map_app, g.toLinearMap, injective, map_app, toLinearMap
-/
theorem tmul_comp_tensorMap
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ ->qᵢ Q₂) (g : Q₃ ->qᵢ Q₄) :
    (Q₂.tmul Q₄).comp (TensorProduct.map f.toLinearMap g.toLinearMap) = Q₁.tmul Q₃ := by
  have h₁ : Q₁ = Q₂.comp f.toLinearMap := QuadraticMap.ext fun x => (f.map_app x).symm
  have h₃ : Q₃ = Q₄.comp g.toLinearMap := QuadraticMap.ext fun x => (g.map_app x).symm
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₃ m₁' m₃'
  simp [h₁, h₃, associated_tmul]

@[simp]
/--
theorem `tmul_tensorMap_apply` / 定理 `tmul_tensorMap_apply`

English:
theorem tmul_tensorMap_apply
  proof: DFunLike.congr_fun (tmul_comp_tensorMap f g) x

中文:
定理 tmul_tensorMap_apply
  证明: DFunLike.congr_fun (tmul_comp_tensorMap f g) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, tmul_comp_tensorMap
-/
theorem tmul_tensorMap_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ ->qᵢ Q₂) (g : Q₃ ->qᵢ Q₄) (x : M₁ otimes[R] M₃) :
    Q₂.tmul Q₄ (TensorProduct.map f.toLinearMap g.toLinearMap x) = Q₁.tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorMap f g) x

namespace Isometry

/--
Definition of `_root_.QuadraticMap.Isometry.tmul` / `_root_.QuadraticMap.Isometry.tmul` 的定义

English:
definition _root_.QuadraticMap.Isometry.tmul
  body: TensorProduct.map f.toLinearMap g.toLinearMap
  map_app' := tmul_tensorMap_apply f g

@[simp]

中文:
定义 _root_.QuadraticMap.Isometry.tmul
  定义体: TensorProduct.map f.toLinearMap g.toLinearMap
  map_app' := tmul_tensorMap_apply f g

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.map, f.toLinearMap, g.toLinearMap, toLinearMap
-/
def _root_.QuadraticMap.Isometry.tmul
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ ->qᵢ Q₂) (g : Q₃ ->qᵢ Q₄) : (Q₁.tmul Q₃) ->qᵢ (Q₂.tmul Q₄) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_app' := tmul_tensorMap_apply f g

@[simp]
/--
theorem `_root_.QuadraticMap.Isometry.tmul_apply` / 定理 `_root_.QuadraticMap.Isometry.tmul_apply`

English:
theorem _root_.QuadraticMap.Isometry.tmul_apply
  proof: rfl

中文:
定理 _root_.QuadraticMap.Isometry.tmul_apply
  证明: rfl
-/
theorem _root_.QuadraticMap.Isometry.tmul_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ ->qᵢ Q₂) (g : Q₃ ->qᵢ Q₄) (x : M₁ otimes[R] M₃) :
    f.tmul g x = TensorProduct.map f.toLinearMap g.toLinearMap x :=
  rfl

end Isometry

section tensorComm

@[simp]
/--
theorem `tmul_comp_tensorComm` / 定理 `tmul_comp_tensorComm`

English:
theorem tmul_comp_tensorComm
  given: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  proof: by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂'
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_comm _ _

@[simp]

中文:
定理 tmul_comp_tensorComm
  条件: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  证明: by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂'
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_comm _ _

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.associated_comp, QuadraticMap.associated_rightInverse, associated_comp, associated_rightInverse, associated_tmul, injective, mul_comm
-/
theorem tmul_comp_tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₂.tmul Q₁).comp (TensorProduct.comm R M₁ M₂) = Q₁.tmul Q₂ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂'
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_comm _ _

@[simp]
/--
theorem `tmul_tensorComm_apply` / 定理 `tmul_tensorComm_apply`

English:
theorem tmul_tensorComm_apply
  proof: DFunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

中文:
定理 tmul_tensorComm_apply
  证明: DFunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, tmul_comp_tensorComm
-/
theorem tmul_tensorComm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (x : M₁ otimes[R] M₂) :
    Q₂.tmul Q₁ (TensorProduct.comm R M₁ M₂ x) = Q₁.tmul Q₂ x :=
  DFunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

/-- `TensorProduct.comm` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/--
Definition of `tensorComm` / `tensorComm` 的定义

English:
definition tensorComm
  signature: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  body: TensorProduct.comm R M₁ M₂
  map_app' := tmul_tensorComm_apply Q₁ Q₂

中文:
定义 tensorComm
  签名: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  定义体: TensorProduct.comm R M₁ M₂
  map_app' := tmul_tensorComm_apply Q₁ Q₂

Depends on / 依赖: TensorProduct, TensorProduct.comm
-/
def tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).IsometryEquiv (Q₂.tmul Q₁) where
  toLinearEquiv := TensorProduct.comm R M₁ M₂
  map_app' := tmul_tensorComm_apply Q₁ Q₂

/--
lemma `tensorComm_apply` / 引理 `tensorComm_apply`

English:
lemma tensorComm_apply
  statement: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  proof: rfl

中文:
引理 tensorComm_apply
  结论: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  证明: rfl
-/
@[simp] lemma tensorComm_apply (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (x : M₁ otimes[R] M₂) :
    tensorComm Q₁ Q₂ x = TensorProduct.comm R M₁ M₂ x :=
  rfl

/--
lemma `tensorComm_symm` / 引理 `tensorComm_symm`

English:
lemma tensorComm_symm
  given: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  proof: rfl

中文:
引理 tensorComm_symm
  条件: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  证明: rfl
-/
@[simp] lemma tensorComm_symm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (tensorComm Q₁ Q₂).symm = tensorComm Q₂ Q₁ :=
  rfl

end tensorComm

section tensorAssoc

@[simp]
/--
theorem `tmul_comp_tensorAssoc` / 定理 `tmul_comp_tensorAssoc`

English:
theorem tmul_comp_tensorAssoc
  proof: by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_assoc _ _ _

@[simp]

中文:
定理 tmul_comp_tensorAssoc
  证明: by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_assoc _ _ _

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.associated_comp, QuadraticMap.associated_rightInverse, associated_comp, associated_rightInverse, associated_tmul, injective, mul_assoc
-/
theorem tmul_comp_tensorAssoc
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    (Q₁.tmul (Q₂.tmul Q₃)).comp (TensorProduct.assoc R M₁ M₂ M₃) = (Q₁.tmul Q₂).tmul Q₃ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_assoc _ _ _

@[simp]
/--
theorem `tmul_tensorAssoc_apply` / 定理 `tmul_tensorAssoc_apply`

English:
theorem tmul_tensorAssoc_apply
  proof: DFunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

中文:
定理 tmul_tensorAssoc_apply
  证明: DFunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, tmul_comp_tensorAssoc
-/
theorem tmul_tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ otimes[R] M₂) otimes[R] M₃) :
    Q₁.tmul (Q₂.tmul Q₃) (TensorProduct.assoc R M₁ M₂ M₃ x) = (Q₁.tmul Q₂).tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

/-- `TensorProduct.assoc` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/--
Definition of `tensorAssoc` / `tensorAssoc` 的定义

English:
definition tensorAssoc
  signature: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
  body: TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_tensorAssoc_apply Q₁ Q₂ Q₃

中文:
定义 tensorAssoc
  签名: (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
  定义体: TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_tensorAssoc_apply Q₁ Q₂ Q₃

Depends on / 依赖: TensorProduct, TensorProduct.assoc
-/
def tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    ((Q₁.tmul Q₂).tmul Q₃).IsometryEquiv (Q₁.tmul (Q₂.tmul Q₃)) where
  toLinearEquiv := TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_tensorAssoc_apply Q₁ Q₂ Q₃

/--
lemma `tensorAssoc_apply` / 引理 `tensorAssoc_apply`

English:
lemma tensorAssoc_apply
  proof: rfl

中文:
引理 tensorAssoc_apply
  证明: rfl
-/
@[simp] lemma tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ otimes[R] M₂) otimes[R] M₃) :
    tensorAssoc Q₁ Q₂ Q₃ x = TensorProduct.assoc R M₁ M₂ M₃ x :=
  rfl

/--
lemma `tensorAssoc_symm_apply` / 引理 `tensorAssoc_symm_apply`

English:
lemma tensorAssoc_symm_apply
  proof: rfl

中文:
引理 tensorAssoc_symm_apply
  证明: rfl
-/
@[simp] lemma tensorAssoc_symm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : M₁ otimes[R] (M₂ otimes[R] M₃)) :
    (tensorAssoc Q₁ Q₂ Q₃).symm x = (TensorProduct.assoc R M₁ M₂ M₃).symm x :=
  rfl

end tensorAssoc

section tensorRId

/--
theorem `comp_tensorRId_eq` / 定理 `comp_tensorRId_eq`

English:
theorem comp_tensorRId_eq
  given: (Q₁ : QuadraticForm R M₁)
  proof: by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₁'
  simp [associated_tmul, QuadraticMap.associated_comp, one_mul]

@[simp]

中文:
定理 comp_tensorRId_eq
  条件: (Q₁ : QuadraticForm R M₁)
  证明: by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₁'
  simp [associated_tmul, QuadraticMap.associated_comp, one_mul]

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.associated_comp, QuadraticMap.associated_rightInverse, associated_comp, associated_rightInverse, associated_tmul, injective, one_mul
-/
theorem comp_tensorRId_eq (Q₁ : QuadraticForm R M₁) :
    Q₁.comp (TensorProduct.rid R M₁) = Q₁.tmul (sq (R := R)) := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₁'
  simp [associated_tmul, QuadraticMap.associated_comp, one_mul]

@[simp]
/--
theorem `tmul_tensorRId_apply` / 定理 `tmul_tensorRId_apply`

English:
theorem tmul_tensorRId_apply
  proof: DFunLike.congr_fun (comp_tensorRId_eq Q₁) x

中文:
定理 tmul_tensorRId_apply
  证明: DFunLike.congr_fun (comp_tensorRId_eq Q₁) x
-/
theorem tmul_tensorRId_apply
    (Q₁ : QuadraticForm R M₁) (x : M₁ otimes[R] R) :
    Q₁ (TensorProduct.rid R M₁ x) = Q₁.tmul (sq (R := R)) x :=
  DFunLike.congr_fun (comp_tensorRId_eq Q₁) x

/-- `TensorProduct.rid` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/--
Definition of `tensorRId` / `tensorRId` 的定义

English:
definition tensorRId
  signature: (Q₁ : QuadraticForm R M₁)
  body: TensorProduct.rid R M₁
  map_app' := tmul_tensorRId_apply Q₁

中文:
定义 tensorRId
  签名: (Q₁ : QuadraticForm R M₁)
  定义体: TensorProduct.rid R M₁
  map_app' := tmul_tensorRId_apply Q₁

Depends on / 依赖: IsometryEquiv
-/
def tensorRId (Q₁ : QuadraticForm R M₁) :
    (Q₁.tmul (sq (R := R))).IsometryEquiv Q₁ where
  toLinearEquiv := TensorProduct.rid R M₁
  map_app' := tmul_tensorRId_apply Q₁

/--
lemma `tensorRId_apply` / 引理 `tensorRId_apply`

English:
lemma tensorRId_apply
  given: (Q₁ : QuadraticForm R M₁) (x : M₁ otimes[R] R)
  proof: rfl

中文:
引理 tensorRId_apply
  条件: (Q₁ : QuadraticForm R M₁) (x : M₁ otimes[R] R)
  证明: rfl
-/
@[simp] lemma tensorRId_apply (Q₁ : QuadraticForm R M₁) (x : M₁ otimes[R] R) :
    tensorRId Q₁ x = TensorProduct.rid R M₁ x :=
  rfl

/--
lemma `tensorRId_symm_apply` / 引理 `tensorRId_symm_apply`

English:
lemma tensorRId_symm_apply
  given: (Q₁ : QuadraticForm R M₁) (x : M₁)
  proof: rfl

中文:
引理 tensorRId_symm_apply
  条件: (Q₁ : QuadraticForm R M₁) (x : M₁)
  证明: rfl
-/
@[simp] lemma tensorRId_symm_apply (Q₁ : QuadraticForm R M₁) (x : M₁) :
    (tensorRId Q₁).symm x = (TensorProduct.rid R M₁).symm x :=
  rfl

end tensorRId

section tensorLId

/--
theorem `comp_tensorLId_eq` / 定理 `comp_tensorLId_eq`

English:
theorem comp_tensorLId_eq
  given: (Q₂ : QuadraticForm R M₂)
  proof: by
  ext
  simp

@[simp]

中文:
定理 comp_tensorLId_eq
  条件: (Q₂ : QuadraticForm R M₂)
  证明: by
  ext
  simp

@[simp]
-/
theorem comp_tensorLId_eq (Q₂ : QuadraticForm R M₂) :
    Q₂.comp (TensorProduct.lid R M₂) = QuadraticForm.tmul (sq (R := R)) Q₂ := by
  ext
  simp

@[simp]
/--
theorem `tmul_tensorLId_apply` / 定理 `tmul_tensorLId_apply`

English:
theorem tmul_tensorLId_apply
  proof: DFunLike.congr_fun (comp_tensorLId_eq Q₂) x

中文:
定理 tmul_tensorLId_apply
  证明: DFunLike.congr_fun (comp_tensorLId_eq Q₂) x
-/
theorem tmul_tensorLId_apply
    (Q₂ : QuadraticForm R M₂) (x : R otimes[R] M₂) :
    Q₂ (TensorProduct.lid R M₂ x) = QuadraticForm.tmul (sq (R := R)) Q₂ x :=
  DFunLike.congr_fun (comp_tensorLId_eq Q₂) x

/-- `TensorProduct.lid` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/--
Definition of `tensorLId` / `tensorLId` 的定义

English:
definition tensorLId
  signature: (Q₂ : QuadraticForm R M₂)
  body: TensorProduct.lid R M₂
  map_app' := tmul_tensorLId_apply Q₂

中文:
定义 tensorLId
  签名: (Q₂ : QuadraticForm R M₂)
  定义体: TensorProduct.lid R M₂
  map_app' := tmul_tensorLId_apply Q₂

Depends on / 依赖: IsometryEquiv
-/
def tensorLId (Q₂ : QuadraticForm R M₂) :
    (QuadraticForm.tmul (sq (R := R)) Q₂).IsometryEquiv Q₂ where
  toLinearEquiv := TensorProduct.lid R M₂
  map_app' := tmul_tensorLId_apply Q₂

/--
lemma `tensorLId_apply` / 引理 `tensorLId_apply`

English:
lemma tensorLId_apply
  given: (Q₂ : QuadraticForm R M₂) (x : R otimes[R] M₂)
  proof: rfl

中文:
引理 tensorLId_apply
  条件: (Q₂ : QuadraticForm R M₂) (x : R otimes[R] M₂)
  证明: rfl
-/
@[simp] lemma tensorLId_apply (Q₂ : QuadraticForm R M₂) (x : R otimes[R] M₂) :
    tensorLId Q₂ x = TensorProduct.lid R M₂ x :=
  rfl

/--
lemma `tensorLId_symm_apply` / 引理 `tensorLId_symm_apply`

English:
lemma tensorLId_symm_apply
  given: (Q₂ : QuadraticForm R M₂) (x : M₂)
  proof: rfl

中文:
引理 tensorLId_symm_apply
  条件: (Q₂ : QuadraticForm R M₂) (x : M₂)
  证明: rfl
-/
@[simp] lemma tensorLId_symm_apply (Q₂ : QuadraticForm R M₂) (x : M₂) :
    (tensorLId Q₂).symm x = (TensorProduct.lid R M₂).symm x :=
  rfl

end tensorLId

end QuadraticForm
