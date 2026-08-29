/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Universal property of the tensor product

Given any bilinear map `f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂`, there is a unique semilinear map
`TensorProduct.lift f : TensorProduct R M N →ₛₗ[σ₁₂] P₂` whose composition with the canonical
bilinear map `TensorProduct.mk` is the given bilinear map `f`. Uniqueness is shown in the theorem
`TensorProduct.lift.unique`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section Module

variable {M N}

-- TODO: use this to implement `lift` and `SMul.aux`. For now we do not do this as it causes
-- performance issues elsewhere.
/--
Definition of `liftAddHom` / `liftAddHom` 的定义

English:
definition liftAddHom
  signature: (f : M ->+ N ->+ P)
  body: (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2))
    AddCon.addConGen_le.2 fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
(AddCon.ker_rel _).2 by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
(AddCon.ker_rel _).2 by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
(AddCon.ker_rel _).2 by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
(AddCon.ker_rel _).2 by simp_rw [map_add, add_comm]

@[simp]

中文:
定义 liftAddHom
  签名: (f : M ->+ N ->+ P)
  定义体: (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2))
    AddCon.addConGen_le.2 fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
(AddCon.ker_rel _).2 by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
(AddCon.ker_rel _).2 by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
(AddCon.ker_rel _).2 by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
(AddCon.ker_rel _).2 by simp_rw [map_add, add_comm]

@[simp]

Depends on / 依赖: AddCon, AddCon.addConGen_le, AddCon.ker_rel, AddMonoidHom, AddMonoidHom.zero_apply, FreeAddMonoid, FreeAddMonoid.lift, FreeAddMonoid.lift_eval_of, TensorProduct, TensorProduct.Eqv, addConGen, addConGen_le, ker_rel, lift_eval_of, map_add, map_zero, of_add_left, of_zero_left, of_zero_right, simp_rw
-/
def liftAddHom (f : M ->+ N ->+ P)
    (hf : forall (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) :
    M otimes[R] N ->+ P :=
(addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2))
    AddCon.addConGen_le.2 fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
(AddCon.ker_rel _).2 by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
(AddCon.ker_rel _).2 by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
(AddCon.ker_rel _).2 by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
(AddCon.ker_rel _).2 by simp_rw [map_add, add_comm]

@[simp]
/--
theorem `liftAddHom_tmul` / 定理 `liftAddHom_tmul`

English:
theorem liftAddHom_tmul
  statement: (f : M ->+ N ->+ P)
  proof: rfl

中文:
定理 liftAddHom_tmul
  结论: (f : M ->+ N ->+ P)
  证明: rfl
-/
theorem liftAddHom_tmul (f : M ->+ N ->+ P)
    (hf : forall (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) (m : M) (n : N) :
    liftAddHom f hf (m otimesₜ n) = f m n :=
  rfl

end Module

variable [Module R P] [Module R Q]

section UniversalProperty

variable {M N}
variable (f : M ->ₗ[R] N ->ₗ[R] P)
variable (f' : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: : M otimes[R] N ->+ P₂
  body: liftAddHom (LinearMap.toAddMonoidHom'.comp <| f'.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smulₛₗ₂, map_smulₛₗ]

中文:
定义 liftAux
  签名: : M otimes[R] N ->+ P₂
  定义体: liftAddHom (LinearMap.toAddMonoidHom'.comp <| f'.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smulₛₗ₂, map_smulₛₗ]

Depends on / 依赖: LinearMap, LinearMap.map_smul, LinearMap.toAddMonoidHom, liftAddHom, toAddMonoidHom
-/
def liftAux : M otimes[R] N ->+ P₂ :=
  liftAddHom (LinearMap.toAddMonoidHom'.comp <| f'.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smulₛₗ₂, map_smulₛₗ]

/--
theorem `liftAux_tmul` / 定理 `liftAux_tmul`

English:
theorem liftAux_tmul
  given: (m n)
  statement: liftAux f' (m otimesₜ n) = f' m n
  proof: rfl

中文:
定理 liftAux_tmul
  条件: (m n)
  结论: liftAux f' (m otimesₜ n) = f' m n
  证明: rfl

Depends on / 依赖: infer_instance, variation_smul
-/
theorem liftAux_tmul (m n) : liftAux f' (m otimesₜ n) = f' m n :=
  rfl

variable {f f'}

@[simp]
/--
theorem `liftAux.smulₛₗ` / 定理 `liftAux.smulₛₗ`

English:
theorem liftAux.smulₛₗ
  given: (r : R) (x)
  statement: liftAux f' (r • x) = σ₁₂ r • liftAux f' x
  proof: TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f' p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f').map_add, ih1, ih2, smul_add]

中文:
定理 liftAux.smulₛₗ
  条件: (r : R) (x)
  结论: liftAux f' (r • x) = σ₁₂ r • liftAux f' x
  证明: TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f' p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f').map_add, ih1, ih2, smul_add]

Depends on / 依赖: TensorProduct, TensorProduct.induction_on, induction_on, liftAux, liftAux_tmul, map_add, simp_rw, smul_add, smul_zero, tmul_smul
-/
theorem liftAux.smulₛₗ (r : R) (x) : liftAux f' (r • x) = σ₁₂ r • liftAux f' x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f' p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f').map_add, ih1, ih2, smul_add]

/--
theorem `liftAux.smul` / 定理 `liftAux.smul`

English:
theorem liftAux.smul
  given: (r : R) (x)
  statement: liftAux f (r • x) = r • liftAux f x
  proof: liftAux.smulₛₗ _ _

中文:
定理 liftAux.smul
  条件: (r : R) (x)
  结论: liftAux f (r • x) = r • liftAux f x
  证明: liftAux.smulₛₗ _ _

Depends on / 依赖: Measure, Measure.coe_nnreal_smul, coe_nnreal_smul, enorm_eq_nnnorm, infer_instance, variation_dirac
-/
theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
  liftAux.smulₛₗ _ _

variable (f') in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : M otimes[R] N ->ₛₗ[σ₁₂] P₂
  body: { liftAux f' with map_smul' := liftAux.smulₛₗ }

@[simp]

中文:
定义 lift
  签名: : M otimes[R] N ->ₛₗ[σ₁₂] P₂
  定义体: { liftAux f' with map_smul' := liftAux.smulₛₗ }

@[simp]

Depends on / 依赖: liftAux, liftAux.smul, map_smul
-/
def lift : M otimes[R] N ->ₛₗ[σ₁₂] P₂ :=
  { liftAux f' with map_smul' := liftAux.smulₛₗ }

@[simp]
/--
theorem `lift.tmul` / 定理 `lift.tmul`

English:
theorem lift.tmul
  given: (x y)
  statement: lift f' (x otimesₜ y) = f' x y
  proof: rfl

@[simp]

中文:
定理 lift.tmul
  条件: (x y)
  结论: lift f' (x otimesₜ y) = f' x y
  证明: rfl

@[simp]
-/
theorem lift.tmul (x y) : lift f' (x otimesₜ y) = f' x y :=
  rfl

@[simp]
/--
theorem `lift.tmul'` / 定理 `lift.tmul'`

English:
theorem lift.tmul'
  given: (x y)
  statement: (lift f').1 (x otimesₜ y) = f' x y
  proof: rfl

中文:
定理 lift.tmul'
  条件: (x y)
  结论: (lift f').1 (x otimesₜ y) = f' x y
  证明: rfl
-/
theorem lift.tmul' (x y) : (lift f').1 (x otimesₜ y) = f' x y :=
  rfl

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y))
  statement: g = h
  proof: LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add]; rw [h.map_add]; rw [ihx]; rw [ihy]

中文:
定理 ext'
  条件: {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : 对任意 x y, g (x otimesₜ y) = h (x otimesₜ y))
  结论: g = h
  证明: LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add]; rw [h.map_add]; rw [ihx]; rw [ihy]

Depends on / 依赖: LinearMap, LinearMap.ext, TensorProduct, TensorProduct.induction_on, g.map_add, h.map_add, induction_on, map_add, map_zero, simp_rw
-/
theorem ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h :=
  LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add]; rw [h.map_add]; rw [ihx]; rw [ihy]

/--
theorem `lift.unique` / 定理 `lift.unique`

English:
theorem lift.unique
  given: {g : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall x y, g (x otimesₜ y) = f' x y)
  statement: g = lift f'
  proof: ext' fun m n => by rw [H, lift.tmul]

中文:
定理 lift.unique
  条件: {g : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : 对任意 x y, g (x otimesₜ y) = f' x y)
  结论: g = lift f'
  证明: ext' fun m n => by rw [H, lift.tmul]
-/
theorem lift.unique {g : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall x y, g (x otimesₜ y) = f' x y) : g = lift f' :=
  ext' fun m n => by rw [H, lift.tmul]

/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: lift (mk R M N) = LinearMap.id
  proof: Eq.symm lift.unique fun _ _ => rfl

中文:
定理 lift_mk
  结论: lift (mk R M N) = 线性映射.id
  证明: Eq.symm lift.unique fun _ _ => rfl

Depends on / 依赖: Eq.symm, lift.unique, unique
-/
theorem lift_mk : lift (mk R M N) = LinearMap.id :=
Eq.symm lift.unique fun _ _ => rfl

/--
theorem `lift_compr₂ₛₗ` / 定理 `lift_compr₂ₛₗ`

English:
theorem lift_compr₂ₛₗ
  given: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (h : P₂ ->ₛₗ[σ₂₃] P₃)
  proof: Eq.symm lift.unique fun _ _ => by simp

中文:
定理 lift_compr₂ₛₗ
  条件: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (h : P₂ ->ₛₗ[σ₂₃] P₃)
  证明: Eq.symm lift.unique fun _ _ => by simp

Depends on / 依赖: Eq.symm, lift.unique, unique
-/
theorem lift_compr₂ₛₗ [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (h : P₂ ->ₛₗ[σ₂₃] P₃) :
    lift (f'.compr₂ₛₗ h) = h.comp (lift f') :=
Eq.symm lift.unique fun _ _ => by simp

/--
theorem `lift_compr₂` / 定理 `lift_compr₂`

English:
theorem lift_compr₂
  given: (g : P ->ₗ[R] Q)
  statement: lift (f.compr₂ g) = g.comp (lift f)
  proof: Eq.symm lift.unique fun _ _ => by simp

中文:
定理 lift_compr₂
  条件: (g : P ->ₗ[R] Q)
  结论: lift (f.compr₂ g) = g.comp (lift f)
  证明: Eq.symm lift.unique fun _ _ => by simp

Depends on / 依赖: Eq.symm, lift.unique, unique
-/
theorem lift_compr₂ (g : P ->ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
Eq.symm lift.unique fun _ _ => by simp

/--
theorem `lift_mk_compr₂ₛₗ` / 定理 `lift_mk_compr₂ₛₗ`

English:
theorem lift_mk_compr₂ₛₗ
  given: (g : M otimes N ->ₛₗ[σ₁₂] P₂)
  statement: lift ((mk R M N).compr₂ₛₗ g) = g
  proof: by
  rw [lift_compr₂ₛₗ g]; rw [lift_mk]; rw [LinearMap.comp_id]

中文:
定理 lift_mk_compr₂ₛₗ
  条件: (g : M otimes N ->ₛₗ[σ₁₂] P₂)
  结论: lift ((mk R M N).compr₂ₛₗ g) = g
  证明: by
  rw [lift_compr₂ₛₗ g]; rw [lift_mk]; rw [LinearMap.comp_id]

Depends on / 依赖: LinearMap, LinearMap.comp_id, comp_id, lift_mk
-/
theorem lift_mk_compr₂ₛₗ (g : M otimes N ->ₛₗ[σ₁₂] P₂) : lift ((mk R M N).compr₂ₛₗ g) = g := by
  rw [lift_compr₂ₛₗ g]; rw [lift_mk]; rw [LinearMap.comp_id]

/--
theorem `lift_mk_compr₂` / 定理 `lift_mk_compr₂`

English:
theorem lift_mk_compr₂
  given: (f : M otimes N ->ₗ[R] P)
  statement: lift ((mk R M N).compr₂ f) = f
  proof: by
  rw [lift_compr₂ f]; rw [lift_mk]; rw [LinearMap.comp_id]

中文:
定理 lift_mk_compr₂
  条件: (f : M otimes N ->ₗ[R] P)
  结论: lift ((mk R M N).compr₂ f) = f
  证明: by
  rw [lift_compr₂ f]; rw [lift_mk]; rw [LinearMap.comp_id]

Depends on / 依赖: LinearMap, LinearMap.comp_id, comp_id, lift_mk
-/
theorem lift_mk_compr₂ (f : M otimes N ->ₗ[R] P) : lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f]; rw [lift_mk]; rw [LinearMap.comp_id]

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h)
  proof: by
  rw [← lift_mk_compr₂ₛₗ g]; rw [H]; rw [lift_mk_compr₂ₛₗ]

中文:
定理 ext
  条件: {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h)
  证明: by
  rw [← lift_mk_compr₂ₛₗ g]; rw [H]; rw [lift_mk_compr₂ₛₗ]
-/
theorem ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) :
    g = h := by
  rw [← lift_mk_compr₂ₛₗ g]; rw [H]; rw [lift_mk_compr₂ₛₗ]

attribute [local ext high] ext

variable (M N P₂ σ₁₂) in
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂ where
  body: lift
  map_add' f g := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]

中文:
定义 uncurry
  签名: : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂ where
  定义体: lift
  map_add' f g := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
-/
def uncurry : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂ where
  toFun := lift
  map_add' f g := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
/--
theorem `uncurry_apply` / 定理 `uncurry_apply`

English:
theorem uncurry_apply
  given: (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  proof: rfl

中文:
定理 uncurry_apply
  条件: (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  证明: rfl
-/
theorem uncurry_apply (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    uncurry σ₁₂ M N P₂ f (m otimesₜ n) = f m n := rfl

variable (M N P₂ σ₁₂)

/--
Definition of `lift.equiv` / `lift.equiv` 的定义

English:
definition lift.equiv
  signature: : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂
  body: { uncurry σ₁₂ M N P₂ with
    invFun := fun f => (mk R M N).compr₂ₛₗ f }

@[simp]

中文:
定义 lift.equiv
  签名: : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂
  定义体: { uncurry σ₁₂ M N P₂ with
    invFun := fun f => (mk R M N).compr₂ₛₗ f }

@[simp]

Depends on / 依赖: invFun, uncurry
-/
def lift.equiv : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂ :=
  { uncurry σ₁₂ M N P₂ with
    invFun := fun f => (mk R M N).compr₂ₛₗ f }

@[simp]
/--
theorem `lift.equiv_apply` / 定理 `lift.equiv_apply`

English:
theorem lift.equiv_apply
  given: (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  proof: uncurry_apply f m n

@[simp]

中文:
定理 lift.equiv_apply
  条件: (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  证明: uncurry_apply f m n

@[simp]

Depends on / 依赖: uncurry_apply
-/
theorem lift.equiv_apply (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lift.equiv σ₁₂ M N P₂ f (m otimesₜ n) = f m n :=
  uncurry_apply f m n

@[simp]
/--
theorem `lift.equiv_symm_apply` / 定理 `lift.equiv_symm_apply`

English:
theorem lift.equiv_symm_apply
  given: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  proof: rfl

中文:
定理 lift.equiv_symm_apply
  条件: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  证明: rfl
-/
theorem lift.equiv_symm_apply (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    (lift.equiv σ₁₂ M N P₂).symm f m n = f (m otimesₜ n) :=
  rfl

/--
Definition of `lcurry` / `lcurry` 的定义

English:
definition lcurry
  signature: : (M otimes[R] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂
  body: (lift.equiv σ₁₂ M N P₂).symm

中文:
定义 lcurry
  签名: : (M otimes[R] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂
  定义体: (lift.equiv σ₁₂ M N P₂).symm

Depends on / 依赖: lift.equiv
-/
def lcurry : (M otimes[R] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂ :=
  (lift.equiv σ₁₂ M N P₂).symm

variable {M N P₂ σ₁₂}

@[simp]
/--
theorem `lcurry_apply` / 定理 `lcurry_apply`

English:
theorem lcurry_apply
  given: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  proof: rfl

中文:
定理 lcurry_apply
  条件: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  证明: rfl
-/
theorem lcurry_apply (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lcurry σ₁₂ M N P₂ f m n = f (m otimesₜ n) :=
  rfl

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂)
  body: lcurry σ₁₂ M N P₂ f

@[simp]

中文:
定义 curry
  签名: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂)
  定义体: lcurry σ₁₂ M N P₂ f

@[simp]

Depends on / 依赖: lcurry
-/
def curry (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂ :=
  lcurry σ₁₂ M N P₂ f

@[simp]
/--
theorem `curry_apply` / 定理 `curry_apply`

English:
theorem curry_apply
  given: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  statement: curry f m n = f (m otimesₜ n)
  proof: rfl

中文:
定理 curry_apply
  条件: (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N)
  结论: curry f m n = f (m otimesₜ n)
  证明: rfl
-/
theorem curry_apply (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) : curry f m n = f (m otimesₜ n) :=
  rfl

/--
theorem `curry_injective` / 定理 `curry_injective`

English:
theorem curry_injective
  proof: fun _ _ H => ext H

中文:
定理 curry_injective
  证明: fun _ _ H => ext H
-/
theorem curry_injective :
    Function.Injective (curry : (M otimes[R] N ->ₛₗ[σ₁₂] P₂) -> M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) :=
  fun _ _ H => ext H

/--
theorem `ext_threefold` / 定理 `ext_threefold`

English:
theorem ext_threefold
  statement: {g h : M otimes[R] N otimes[R] P ->ₛₗ[σ₁₂] P₂}
  proof: by
  ext x y z
  exact H x y z

中文:
定理 ext_threefold
  结论: {g h : M otimes[R] N otimes[R] P ->ₛₗ[σ₁₂] P₂}
  证明: by
  ext x y z
  exact H x y z
-/
theorem ext_threefold {g h : M otimes[R] N otimes[R] P ->ₛₗ[σ₁₂] P₂}
    (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y otimesₜ z)) : g = h := by
  ext x y z
  exact H x y z

/--
theorem `ext_threefold'` / 定理 `ext_threefold'`

English:
theorem ext_threefold'
  statement: {g h : M otimes[R] (N otimes[R] P) ->ₛₗ[σ₁₂] P₂}
  proof: by
  ext x y z
  exact H x y z

中文:
定理 ext_threefold'
  结论: {g h : M otimes[R] (N otimes[R] P) ->ₛₗ[σ₁₂] P₂}
  证明: by
  ext x y z
  exact H x y z
-/
theorem ext_threefold' {g h : M otimes[R] (N otimes[R] P) ->ₛₗ[σ₁₂] P₂}
    (H : forall x y z, g (x otimesₜ (y otimesₜ z)) = h (x otimesₜ (y otimesₜ z))) : g = h := by
  ext x y z
  exact H x y z

-- We'll need this one for checking the pentagon identity!
/--
theorem `ext_fourfold` / 定理 `ext_fourfold`

English:
theorem ext_fourfold
  statement: {g h : M otimes[R] N otimes[R] P otimes[R] Q ->ₛₗ[σ₁₂] P₂}
  proof: by
  ext w x y z
  exact H w x y z

中文:
定理 ext_fourfold
  结论: {g h : M otimes[R] N otimes[R] P otimes[R] Q ->ₛₗ[σ₁₂] P₂}
  证明: by
  ext w x y z
  exact H w x y z
-/
theorem ext_fourfold {g h : M otimes[R] N otimes[R] P otimes[R] Q ->ₛₗ[σ₁₂] P₂}
    (H : forall w x y z, g (w otimesₜ x otimesₜ y otimesₜ z) = h (w otimesₜ x otimesₜ y otimesₜ z)) : g = h := by
  ext w x y z
  exact H w x y z

/--
theorem `ext_fourfold'` / 定理 `ext_fourfold'`

English:
theorem ext_fourfold'
  statement: {φ ψ : M otimes[R] N otimes[R] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂}
  proof: by
  ext m n p q
  exact H m n p q

中文:
定理 ext_fourfold'
  结论: {φ ψ : M otimes[R] N otimes[R] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂}
  证明: by
  ext m n p q
  exact H m n p q
-/
theorem ext_fourfold' {φ ψ : M otimes[R] N otimes[R] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂}
    (H : forall w x y z, φ (w otimesₜ x otimesₜ (y otimesₜ z)) = ψ (w otimesₜ x otimesₜ (y otimesₜ z))) : φ = ψ := by
  ext m n p q
  exact H m n p q

/--
theorem `ext_fourfold''` / 定理 `ext_fourfold''`

English:
theorem ext_fourfold''
  statement: {φ ψ : M otimes[R] (N otimes[R] P) otimes[R] Q ->ₛₗ[σ₁₂] P₂}
  proof: by
  ext m n p q
  exact H m n p q

中文:
定理 ext_fourfold''
  结论: {φ ψ : M otimes[R] (N otimes[R] P) otimes[R] Q ->ₛₗ[σ₁₂] P₂}
  证明: by
  ext m n p q
  exact H m n p q
-/
theorem ext_fourfold'' {φ ψ : M otimes[R] (N otimes[R] P) otimes[R] Q ->ₛₗ[σ₁₂] P₂}
    (H : forall w x y z, φ (w otimesₜ (x otimesₜ y) otimesₜ z) = ψ (w otimesₜ (x otimesₜ y) otimesₜ z)) : φ = ψ := by
  ext m n p q
  exact H m n p q

end UniversalProperty

variable {M N}
section

variable (R M N)

/--
Definition of `comm` / `comm` 的定义

English:
definition comm
  signature: : M otimes[R] N ≃ₗ[R] N otimes[R] M
  body: LinearEquiv.ofLinearMap (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)

@[simp]

中文:
定义 comm
  签名: : M otimes[R] N ≃ₗ[R] N otimes[R] M
  定义体: LinearEquiv.ofLinearMap (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)

@[simp]
-/
protected def comm : M otimes[R] N ≃ₗ[R] N otimes[R] M :=
  LinearEquiv.ofLinearMap (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)

@[simp]
/--
theorem `comm_tmul` / 定理 `comm_tmul`

English:
theorem comm_tmul
  given: (m : M) (n : N)
  statement: (TensorProduct.comm R M N) (m otimesₜ n) = n otimesₜ m
  proof: rfl

@[simp]

中文:
定理 comm_tmul
  条件: (m : M) (n : N)
  结论: (张量积.comm R M N) (m otimesₜ n) = n otimesₜ m
  证明: rfl

@[simp]
-/
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m otimesₜ n) = n otimesₜ m :=
  rfl

@[simp]
/--
lemma `comm_symm` / 引理 `comm_symm`

English:
lemma comm_symm
  statement: (TensorProduct.comm R M N).symm = TensorProduct.comm R N M
  proof: rfl

中文:
引理 comm_symm
  结论: (张量积.comm R M N).symm = 张量积.comm R N M
  证明: rfl
-/
lemma comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M := rfl

/--
theorem `comm_symm_tmul` / 定理 `comm_symm_tmul`

English:
theorem comm_symm_tmul
  given: (m : M) (n : N)
  statement: (TensorProduct.comm R M N).symm (n otimesₜ m) = m otimesₜ n
  proof: rfl

中文:
定理 comm_symm_tmul
  条件: (m : M) (n : N)
  结论: (张量积.comm R M N).symm (n otimesₜ m) = m otimesₜ n
  证明: rfl
-/
theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n otimesₜ m) = m otimesₜ n :=
  rfl

-- Why is the `toLinearMap` necessary ? And why is this slow ?
/--
lemma `lift_comp_comm_eq` / 引理 `lift_comp_comm_eq`

English:
lemma lift_comp_comm_eq
  given: (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂)
  proof: ext rfl

中文:
引理 lift_comp_comm_eq
  条件: (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂)
  证明: ext rfl
-/
lemma lift_comp_comm_eq (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) :
    lift f ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = lift f.flip :=
  ext rfl

attribute [local ext high] ext in
/--
lemma `comm_trans_comm` / 引理 `comm_trans_comm`

English:
lemma comm_trans_comm
  proof: by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

中文:
引理 comm_trans_comm
  证明: by
  apply LinearEquiv.toLinearMap_injective; ext; rfl
-/
@[simp] lemma comm_trans_comm :
    TensorProduct.comm R N M ≪≫ₗ TensorProduct.comm R M N = .refl _ _ := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

/--
lemma `comm_comp_comm` / 引理 `comm_comp_comm`

English:
lemma comm_comp_comm
  proof: by
  simp

@[simp]

中文:
引理 comm_comp_comm
  证明: by
  simp

@[simp]
-/
lemma comm_comp_comm :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id := by
  simp

@[simp]
/--
lemma `comm_comp_comm_assoc` / 引理 `comm_comp_comm_assoc`

English:
lemma comm_comp_comm_assoc
  given: (f : P ->ₗ[R] M otimes[R] N)
  proof: by
  rw [← LinearMap.comp_assoc]; rw [comm_comp_comm]; rw [LinearMap.id_comp]

中文:
引理 comm_comp_comm_assoc
  条件: (f : P ->ₗ[R] M otimes[R] N)
  证明: by
  rw [← LinearMap.comp_assoc]; rw [comm_comp_comm]; rw [LinearMap.id_comp]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, LinearMap.id_comp, comm_comp_comm, comp_assoc, id_comp
-/
lemma comm_comp_comm_assoc (f : P ->ₗ[R] M otimes[R] N) :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc]; rw [comm_comp_comm]; rw [LinearMap.id_comp]

/--
theorem `comm_comm` / 定理 `comm_comm`

English:
theorem comm_comm
  given: (x)
  proof: congr($(comm_trans_comm _ _ _) x)

中文:
定理 comm_comm
  条件: (x)
  证明: congr($(comm_trans_comm _ _ _) x)
-/
@[simp] theorem comm_comm (x) :
    TensorProduct.comm R M N (TensorProduct.comm R N M x) = x :=
  congr($(comm_trans_comm _ _ _) x)

end

section CompatibleSMul

variable (R) (A S M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [CommSemiring A] [Module A M] [Module A N] [SMulCommClass R A M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [SMulCommClass A S M]
  [CompatibleSMul R A M N]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapOfCompatibleSMul` / `mapOfCompatibleSMul` 的定义

English:
definition mapOfCompatibleSMul
  signature: : M otimes[A] N ->ₗ[S] M otimes[R] N where
  body: lift (σ₁₂ := RingHom.id A)
    { toFun := fun m =>
      { __ := mk R M N m
        map_smul' := fun _ _ => (smul_tmul _ _ _).symm }
map_add' := fun _ _ => LinearMap.ext by simp
      map_smul' := fun _ _ => rfl }
  map_smul' s x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y => simp [smul_tmul']

中文:
定义 mapOfCompatibleSMul
  签名: : M otimes[A] N ->ₗ[S] M otimes[R] N where
  定义体: lift (σ₁₂ := RingHom.id A)
    { toFun := fun m =>
      { __ := mk R M N m
        map_smul' := fun _ _ => (smul_tmul _ _ _).symm }
map_add' := fun _ _ => LinearMap.ext by simp
      map_smul' := fun _ _ => rfl }
  map_smul' s x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y => simp [smul_tmul']

Depends on / 依赖: LinearMap, LinearMap.ext, RingHom, RingHom.id, map_add, map_smul, smul_tmul
-/
def mapOfCompatibleSMul : M otimes[A] N ->ₗ[S] M otimes[R] N where
  __ :=
    lift (σ₁₂ := RingHom.id A)
    { toFun := fun m =>
      { __ := mk R M N m
        map_smul' := fun _ _ => (smul_tmul _ _ _).symm }
map_add' := fun _ _ => LinearMap.ext by simp
      map_smul' := fun _ _ => rfl }
  map_smul' s x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y => simp [smul_tmul']

/--
theorem `mapOfCompatibleSMul_tmul` / 定理 `mapOfCompatibleSMul_tmul`

English:
theorem mapOfCompatibleSMul_tmul
  given: (m n)
  statement: mapOfCompatibleSMul R A S M N (m otimesₜ n) = m otimesₜ n
  proof: rfl

中文:
定理 mapOfCompatibleSMul_tmul
  条件: (m n)
  结论: mapOfCompatibleSMul R A S M N (m otimesₜ n) = m otimesₜ n
  证明: rfl
-/
@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R A S M N (m otimesₜ n) = m otimesₜ n :=
  rfl

/--
theorem `mapOfCompatibleSMul_surjective` / 定理 `mapOfCompatibleSMul_surjective`

English:
theorem mapOfCompatibleSMul_surjective
  statement: Function.Surjective (mapOfCompatibleSMul R A S M N)
  proof: fun x => x.induction_on (⟨0, map_zero _⟩) (fun m n => ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simpa using congr($hx + $hy)⟩

中文:
定理 mapOfCompatibleSMul_surjective
  结论: 函数.满射 (mapOfCompatibleSMul R A S M N)
  证明: fun x => x.induction_on (⟨0, map_zero _⟩) (fun m n => ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simpa using congr($hx + $hy)⟩

Depends on / 依赖: induction_on, mapOfCompatibleSMul_tmul, map_zero, x.induction_on
-/
theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R A S M N) :=
  fun x => x.induction_on (⟨0, map_zero _⟩) (fun m n => ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simpa using congr($hx + $hy)⟩

attribute [local instance] SMulCommClass.symm

@[deprecated "with (S := R)" (since := "2026-02-21")]
alias mapOfCompatibleSMul' := mapOfCompatibleSMul

/--
Definition of `equivOfCompatibleSMul` / `equivOfCompatibleSMul` 的定义

English:
definition equivOfCompatibleSMul
  signature: [CompatibleSMul A R M N]
  body: mapOfCompatibleSMul R A S M N
  invFun := mapOfCompatibleSMul A R S M N
  left_inv x := x.induction_on (map_zero _) (fun _ _ => rfl)
    fun _ _ h h' => by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ => rfl)
    fun _ _ h h' => by simpa using congr($h + $h')

中文:
定义 equivOfCompatibleSMul
  签名: [余mpatibleSMul A R M N]
  定义体: mapOfCompatibleSMul R A S M N
  invFun := mapOfCompatibleSMul A R S M N
  left_inv x := x.induction_on (map_zero _) (fun _ _ => rfl)
    fun _ _ h h' => by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ => rfl)
    fun _ _ h h' => by simpa using congr($h + $h')

Depends on / 依赖: mapOfCompatibleSMul
-/
def equivOfCompatibleSMul [CompatibleSMul A R M N] : M otimes[A] N ≃ₗ[S] M otimes[R] N where
  __ := mapOfCompatibleSMul R A S M N
  invFun := mapOfCompatibleSMul A R S M N
  left_inv x := x.induction_on (map_zero _) (fun _ _ => rfl)
    fun _ _ h h' => by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ => rfl)
    fun _ _ h h' => by simpa using congr($h + $h')

end CompatibleSMul

end TensorProduct

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R) in
/--
Definition of `Neg.aux` / `Neg.aux` 的定义

English:
definition Neg.aux
  signature: : M otimes[R] N ->ₗ[R] M otimes[R] N
  body: lift (mk R M N).comp (-LinearMap.id)

中文:
定义 取负.aux
  签名: : M otimes[R] N ->ₗ[R] M otimes[R] N
  定义体: lift (mk R M N).comp (-LinearMap.id)

Depends on / 依赖: LinearMap, LinearMap.id
-/
def Neg.aux : M otimes[R] N ->ₗ[R] M otimes[R] N :=
lift (mk R M N).comp (-LinearMap.id)

/--
Instance `neg` / 实例 `neg`

English:
instance neg
  signature: : Neg (M otimes[R] N) where
  body: Neg.aux R

中文:
实例 neg
  签名: : 取负 (M otimes[R] N) where
  定义体: Neg.aux R

Depends on / 依赖: Neg.aux
-/
instance neg : Neg (M otimes[R] N) where
  neg := Neg.aux R

/--
theorem `neg_add_cancel` / 定理 `neg_add_cancel`

English:
theorem neg_add_cancel
  given: (x : M otimes[R] N)
  statement: -x + x = 0
  proof: x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert! (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx]; rw [hy]; rw [add_zero]

中文:
定理 neg_add_cancel
  条件: (x : M otimes[R] N)
  结论: -x + x = 0
  证明: x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert! (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx]; rw [hy]; rw [add_zero]
-/
protected theorem neg_add_cancel (x : M otimes[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert! (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx]; rw [hy]; rw [add_zero]

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup (M otimes[R] N) where
  body: fun x => TensorProduct.neg_add_cancel x
  zsmul_zero' := by simp
  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]
  zsmul_neg' := fun n x => by
    change (-n.succ : Int) • x = -(((n : Int) + 1) • x)
    rw [← zero_add (_ • x)]; rw [← TensorProduct.neg_add_cancel ((n.succ : Int) • x)]; rw [add_assoc]; rw [← add_smul]; rw [← sub_eq_add_neg]; rw [sub_self]; rw [zero_smul]; rw [add_zero]
    rfl

中文:
实例 addCommGroup
  签名: : 加法交换群 (M otimes[R] N) where
  定义体: fun x => TensorProduct.neg_add_cancel x
  zsmul_zero' := by simp
  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]
  zsmul_neg' := fun n x => by
    change (-n.succ : Int) • x = -(((n : Int) + 1) • x)
    rw [← zero_add (_ • x)]; rw [← TensorProduct.neg_add_cancel ((n.succ : Int) • x)]; rw [add_assoc]; rw [← add_smul]; rw [← sub_eq_add_neg]; rw [sub_self]; rw [zero_smul]; rw [add_zero]
    rfl

Depends on / 依赖: TensorProduct, TensorProduct.neg_add_cancel, neg_add_cancel
-/
instance addCommGroup : AddCommGroup (M otimes[R] N) where
  neg_add_cancel := fun x => TensorProduct.neg_add_cancel x
  zsmul_zero' := by simp
  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]
  zsmul_neg' := fun n x => by
    change (-n.succ : Int) • x = -(((n : Int) + 1) • x)
    rw [← zero_add (_ • x)]; rw [← TensorProduct.neg_add_cancel ((n.succ : Int) • x)]; rw [add_assoc]; rw [← add_smul]; rw [← sub_eq_add_neg]; rw [sub_self]; rw [zero_smul]; rw [add_zero]
    rfl

/--
theorem `neg_tmul` / 定理 `neg_tmul`

English:
theorem neg_tmul
  given: (m : M) (n : N)
  statement: (-m) otimesₜ n = -m otimesₜ[R] n
  proof: rfl

中文:
定理 neg_tmul
  条件: (m : M) (n : N)
  结论: (-m) otimesₜ n = -m otimesₜ[R] n
  证明: rfl
-/
theorem neg_tmul (m : M) (n : N) : (-m) otimesₜ n = -m otimesₜ[R] n :=
  rfl

/--
theorem `tmul_neg` / 定理 `tmul_neg`

English:
theorem tmul_neg
  given: (m : M) (p : P)
  statement: m otimesₜ (-p) = -m otimesₜ[R] p
  proof: (mk R M P _).map_neg _

中文:
定理 tmul_neg
  条件: (m : M) (p : P)
  结论: m otimesₜ (-p) = -m otimesₜ[R] p
  证明: (mk R M P _).map_neg _

Depends on / 依赖: map_neg
-/
theorem tmul_neg (m : M) (p : P) : m otimesₜ (-p) = -m otimesₜ[R] p :=
  (mk R M P _).map_neg _

/--
theorem `tmul_sub` / 定理 `tmul_sub`

English:
theorem tmul_sub
  given: (m : M) (p₁ p₂ : P)
  statement: m otimesₜ (p₁ - p₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
  proof: (mk R M P _).map_sub _ _

中文:
定理 tmul_sub
  条件: (m : M) (p₁ p₂ : P)
  结论: m otimesₜ (p₁ - p₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
  证明: (mk R M P _).map_sub _ _

Depends on / 依赖: map_sub
-/
theorem tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂ :=
  (mk R M P _).map_sub _ _

/--
theorem `sub_tmul` / 定理 `sub_tmul`

English:
theorem sub_tmul
  given: (m₁ m₂ : M) (n : N)
  statement: (m₁ - m₂) otimesₜ n = m₁ otimesₜ[R] n - m₂ otimesₜ[R] n
  proof: (mk R M N).map_sub₂ _ _ _

中文:
定理 sub_tmul
  条件: (m₁ m₂ : M) (n : N)
  结论: (m₁ - m₂) otimesₜ n = m₁ otimesₜ[R] n - m₂ otimesₜ[R] n
  证明: (mk R M N).map_sub₂ _ _ _
-/
theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) otimesₜ n = m₁ otimesₜ[R] n - m₂ otimesₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _

/--
Instance `CompatibleSMul.int` / 实例 `CompatibleSMul.int`

English:
instance CompatibleSMul.int
  signature: : CompatibleSMul R Int M P
  body: ⟨fun r m p =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩

中文:
实例 余mpatibleSMul.int
  签名: : 余mpatibleSMul R 整数 M P
  定义体: ⟨fun r m p =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩

Depends on / 依赖: Int.induction_on, StrongHomClass, StrongHomClass.homClass, add_smul, add_tmul, homClass, induction_on, sub_smul, sub_tmul, tmul_add, tmul_sub
-/
instance CompatibleSMul.int : CompatibleSMul R Int M P :=
  ⟨fun r m p =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩

/--
Instance `CompatibleSMul.unit` / 实例 `CompatibleSMul.unit`

English:
instance CompatibleSMul.unit
  signature: {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
  body: ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

中文:
实例 余mpatibleSMul.unit
  签名: {S} [幺半群 S] [分配乘法作用 S M] [分配乘法作用 S N]
  定义体: ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

Depends on / 依赖: CompatibleSMul, CompatibleSMul.smul_tmul, smul_tmul
-/
instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

end TensorProduct

end Ring
