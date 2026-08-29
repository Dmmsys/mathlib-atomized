/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.SnakeLemma

/-!
# Base change along flat modules preserves equalizers

We show that base change along flat modules (resp. algebras)
preserves kernels and equalizers.

-/

@[expose] public section

universe t u

noncomputable section

open TensorProduct

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
  (f g : N ->ₗ[R] P)

/--
lemma `Module.Flat.ker_lTensor_eq` / 引理 `Module.Flat.ker_lTensor_eq`

English:
lemma Module.Flat.ker_lTensor_eq
  given: [Module.Flat R M]
  proof: by
  rw [← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)

中文:
引理 模.平坦.ker_lTensor_eq
  条件: [模.平坦 R M]
  证明: by
  rw [← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)

Depends on / 依赖: LinearMap, LinearMap.exact_iff, LinearMap.exact_subtype_ker_map, Module, Module.Flat.lTensor_exact, exact_iff, exact_subtype_ker_map, lTensor_exact
-/
lemma Module.Flat.ker_lTensor_eq [Module.Flat R M] :
    LinearMap.ker (AlgebraTensorModule.lTensor S M f) =
      LinearMap.range (AlgebraTensorModule.lTensor S M (LinearMap.ker f).subtype) := by
  rw [← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)

/--
lemma `Module.Flat.eqLocus_lTensor_eq` / 引理 `Module.Flat.eqLocus_lTensor_eq`

English:
lemma Module.Flat.eqLocus_lTensor_eq
  given: [Module.Flat R M]
  proof: by
  rw [LinearMap.eqLocus_eq_ker_sub]; rw [LinearMap.eqLocus_eq_ker_sub]
  rw [← map_sub]; rw [ker_lTensor_eq]

中文:
引理 模.平坦.eqLocus_lTensor_eq
  条件: [模.平坦 R M]
  证明: by
  rw [LinearMap.eqLocus_eq_ker_sub]; rw [LinearMap.eqLocus_eq_ker_sub]
  rw [← map_sub]; rw [ker_lTensor_eq]

Depends on / 依赖: LinearMap, LinearMap.eqLocus_eq_ker_sub, eqLocus_eq_ker_sub, ker_lTensor_eq, map_sub
-/
lemma Module.Flat.eqLocus_lTensor_eq [Module.Flat R M] :
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g) =
      LinearMap.range (AlgebraTensorModule.lTensor S M (LinearMap.eqLocus f g).subtype) := by
  rw [LinearMap.eqLocus_eq_ker_sub]; rw [LinearMap.eqLocus_eq_ker_sub]
  rw [← map_sub]; rw [ker_lTensor_eq]

/--
Definition of `LinearMap.tensorEqLocusBil` / `LinearMap.tensorEqLocusBil` 的定义

English:
definition LinearMap.tensorEqLocusBil
  signature: :
  body: { toFun := fun a => ⟨m otimesₜ a, by simp [show f a = g a from a.property]⟩
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun r x => by simp }
  map_add' x y := by
    ext
    simp [add_tmul]
  map_smul' r x := by
    ext
    simp [smul_tmul']

中文:
定义 线性映射.tensorEqLocusBil
  签名: :
  定义体: { toFun := fun a => ⟨m otimesₜ a, by simp [show f a = g a from a.property]⟩
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun r x => by simp }
  map_add' x y := by
    ext
    simp [add_tmul]
  map_smul' r x := by
    ext
    simp [smul_tmul']

Depends on / 依赖: a.property, add_tmul, map_add, map_smul, property, smul_tmul, tmul_add
-/
def LinearMap.tensorEqLocusBil :
    M ->ₗ[S] LinearMap.eqLocus f g ->ₗ[R]
      LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) where
  toFun m :=
    { toFun := fun a => ⟨m otimesₜ a, by simp [show f a = g a from a.property]⟩
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun r x => by simp }
  map_add' x y := by
    ext
    simp [add_tmul]
  map_smul' r x := by
    ext
    simp [smul_tmul']

/--
Definition of `LinearMap.tensorKerBil` / `LinearMap.tensorKerBil` 的定义

English:
definition LinearMap.tensorKerBil
  signature: :
  body: { toFun := fun a => ⟨m otimesₜ a, by simp⟩
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun r x => by simp }
  map_add' x y := by ext; simp [add_tmul]
  map_smul' r x := by ext y; simp [smul_tmul']

中文:
定义 线性映射.tensorKerBil
  签名: :
  定义体: { toFun := fun a => ⟨m otimesₜ a, by simp⟩
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun r x => by simp }
  map_add' x y := by ext; simp [add_tmul]
  map_smul' r x := by ext y; simp [smul_tmul']

Depends on / 依赖: add_tmul, map_add, map_smul, smul_tmul, tmul_add
-/
def LinearMap.tensorKerBil :
    M ->ₗ[S] LinearMap.ker f ->ₗ[R] LinearMap.ker (AlgebraTensorModule.lTensor S M f) where
  toFun m :=
    { toFun := fun a => ⟨m otimesₜ a, by simp⟩
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun r x => by simp }
  map_add' x y := by ext; simp [add_tmul]
  map_smul' r x := by ext y; simp [smul_tmul']

/--
Definition of `LinearMap.tensorEqLocus` / `LinearMap.tensorEqLocus` 的定义

English:
definition LinearMap.tensorEqLocus
  signature: : M otimes[R] (LinearMap.eqLocus f g) ->ₗ[S]
  body: AlgebraTensorModule.lift (tensorEqLocusBil S M f g)

中文:
定义 线性映射.tensorEqLocus
  签名: : M otimes[R] (线性映射.eqLocus f g) ->ₗ[S]
  定义体: AlgebraTensorModule.lift (tensorEqLocusBil S M f g)

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, tensorEqLocusBil
-/
def LinearMap.tensorEqLocus : M otimes[R] (LinearMap.eqLocus f g) ->ₗ[S]
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) :=
  AlgebraTensorModule.lift (tensorEqLocusBil S M f g)

/--
Definition of `LinearMap.tensorKer` / `LinearMap.tensorKer` 的定义

English:
definition LinearMap.tensorKer
  signature: : M otimes[R] (LinearMap.ker f) ->ₗ[S]
  body: AlgebraTensorModule.lift (f.tensorKerBil S M)

@[simp]

中文:
定义 线性映射.tensorKer
  签名: : M otimes[R] (线性映射.ker f) ->ₗ[S]
  定义体: AlgebraTensorModule.lift (f.tensorKerBil S M)

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, f.tensorKerBil, tensorKerBil
-/
def LinearMap.tensorKer : M otimes[R] (LinearMap.ker f) ->ₗ[S]
    LinearMap.ker (AlgebraTensorModule.lTensor S M f) :=
  AlgebraTensorModule.lift (f.tensorKerBil S M)

@[simp]
/--
lemma `LinearMap.tensorKer_tmul` / 引理 `LinearMap.tensorKer_tmul`

English:
lemma LinearMap.tensorKer_tmul
  given: (m : M) (x : LinearMap.ker f)
  proof: rfl

@[simp]

中文:
引理 线性映射.tensorKer_tmul
  条件: (m : M) (x : 线性映射.ker f)
  证明: rfl

@[simp]
-/
lemma LinearMap.tensorKer_tmul (m : M) (x : LinearMap.ker f) :
    (tensorKer S M f (m otimesₜ[R] x) : M otimes[R] N) = m otimesₜ[R] (x : N) :=
  rfl

@[simp]
/--
lemma `LinearMap.tensorKer_coe` / 引理 `LinearMap.tensorKer_coe`

English:
lemma LinearMap.tensorKer_coe
  given: (x : M otimes[R] (LinearMap.ker f))
  proof: by
  induction x <;> simp_all

@[simp]

中文:
引理 线性映射.tensorKer_coe
  条件: (x : M otimes[R] (线性映射.ker f))
  证明: by
  induction x <;> simp_all

@[simp]
-/
lemma LinearMap.tensorKer_coe (x : M otimes[R] (LinearMap.ker f)) :
    (tensorKer S M f x : M otimes[R] N) = (ker f).subtype.lTensor M x := by
  induction x <;> simp_all

@[simp]
/--
lemma `LinearMap.tensorEqLocus_tmul` / 引理 `LinearMap.tensorEqLocus_tmul`

English:
lemma LinearMap.tensorEqLocus_tmul
  given: (m : M) (x : LinearMap.eqLocus f g)
  proof: rfl

@[simp]

中文:
引理 线性映射.tensorEqLocus_tmul
  条件: (m : M) (x : 线性映射.eqLocus f g)
  证明: rfl

@[simp]
-/
lemma LinearMap.tensorEqLocus_tmul (m : M) (x : LinearMap.eqLocus f g) :
    (tensorEqLocus S M f g (m otimesₜ[R] x) : M otimes[R] N) = m otimesₜ[R] (x : N) :=
  rfl

@[simp]
/--
lemma `LinearMap.tensorEqLocus_coe` / 引理 `LinearMap.tensorEqLocus_coe`

English:
lemma LinearMap.tensorEqLocus_coe
  given: (x : M otimes[R] (LinearMap.eqLocus f g))
  proof: by
  induction x <;> simp_all

中文:
引理 线性映射.tensorEqLocus_coe
  条件: (x : M otimes[R] (线性映射.eqLocus f g))
  证明: by
  induction x <;> simp_all
-/
lemma LinearMap.tensorEqLocus_coe (x : M otimes[R] (LinearMap.eqLocus f g)) :
    (tensorEqLocus S M f g x : M otimes[R] N) = (eqLocus f g).subtype.lTensor M x := by
  induction x <;> simp_all

/--
Definition of `LinearMap.tensorKerInv` / `LinearMap.tensorKerInv` 的定义

English:
definition LinearMap.tensorKerInv
  signature: [Module.Flat R M]
  body: LinearMap.codRestrictOfInjective (LinearMap.ker (AlgebraTensorModule.lTensor S M f)).subtype
    (AlgebraTensorModule.lTensor S M (ker f).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
      (ker f).injective_subtype) (by simp [Module.Flat.ker_lTensor_eq])

中文:
定义 线性映射.tensorKerInv
  签名: [模.平坦 R M]
  定义体: LinearMap.codRestrictOfInjective (LinearMap.ker (AlgebraTensorModule.lTensor S M f)).subtype
    (AlgebraTensorModule.lTensor S M (ker f).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
      (ker f).injective_subtype) (by simp [Module.Flat.ker_lTensor_eq])

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lTensor, LinearMap, LinearMap.codRestrictOfInjective, LinearMap.ker, Module, Module.Flat.ker_lTensor_eq, Module.Flat.lTensor_preserves_injective_linearMap, codRestrictOfInjective, injective_subtype, ker_lTensor_eq, lTensor, lTensor_preserves_injective_linearMap, subtype
-/
def LinearMap.tensorKerInv [Module.Flat R M] :
    ker (AlgebraTensorModule.lTensor S M f) ->ₗ[S] M otimes[R] (ker f) :=
  LinearMap.codRestrictOfInjective (LinearMap.ker (AlgebraTensorModule.lTensor S M f)).subtype
    (AlgebraTensorModule.lTensor S M (ker f).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
      (ker f).injective_subtype) (by simp [Module.Flat.ker_lTensor_eq])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `LinearMap.lTensor_ker_subtype_tensorKerInv` / 引理 `LinearMap.lTensor_ker_subtype_tensorKerInv`

English:
lemma LinearMap.lTensor_ker_subtype_tensorKerInv
  statement: [Module.Flat R M]
  proof: by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorKerInv]

中文:
引理 线性映射.lTensor_ker_subtype_tensorKerInv
  结论: [模.平坦 R M]
  证明: by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorKerInv]
-/
private lemma LinearMap.lTensor_ker_subtype_tensorKerInv [Module.Flat R M]
    (x : ker (AlgebraTensorModule.lTensor S M f)) :
    (lTensor M (ker f).subtype) ((tensorKerInv S M f) x) = x := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorKerInv]

/--
Definition of `LinearMap.tensorEqLocusInv` / `LinearMap.tensorEqLocusInv` 的定义

English:
definition LinearMap.tensorEqLocusInv
  signature: [Module.Flat R M]
  body: LinearMap.codRestrictOfInjective
    (LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g)).subtype
    (AlgebraTensorModule.lTensor S M (eqLocus f g).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
      (eqLocus f g).

中文:
定义 线性映射.tensorEqLocusInv
  签名: [模.平坦 R M]
  定义体: LinearMap.codRestrictOfInjective
    (LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g)).subtype
    (AlgebraTensorModule.lTensor S M (eqLocus f g).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
      (eqLocus f g).

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lTensor, LinearMap, LinearMap.codRestrictOfInjective, LinearMap.eqLocus, Module, Module.Flat.eqLocus_lTensor_eq, Module.Flat.lTensor_preserves_injective_linearMap, codRestrictOfInjective, eqLocus, eqLocus_lTensor_eq, injective_subtype, lTensor, lTensor_preserves_injective_linearMap, subtype
-/
def LinearMap.tensorEqLocusInv [Module.Flat R M] :
    eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) ->ₗ[S]
      M otimes[R] (eqLocus f g) :=
  LinearMap.codRestrictOfInjective
    (LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g)).subtype
    (AlgebraTensorModule.lTensor S M (eqLocus f g).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
      (eqLocus f g).injective_subtype) (by simp [Module.Flat.eqLocus_lTensor_eq])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv` / 引理 `LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv`

English:
lemma LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv
  statement: [Module.Flat R M]
  proof: by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorEqLocusInv]

中文:
引理 线性映射.lTensor_eqLocus_subtype_tensorEqLocusInv
  结论: [模.平坦 R M]
  证明: by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorEqLocusInv]
-/
private lemma LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv [Module.Flat R M]
    (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g)) :
    (lTensor M (eqLocus f g).subtype) (tensorEqLocusInv S M f g x) = x := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorEqLocusInv]

/--
Definition of `LinearMap.tensorKerEquiv` / `LinearMap.tensorKerEquiv` 的定义

English:
definition LinearMap.tensorKerEquiv
  signature: [Module.Flat R M]
  body: LinearEquiv.ofLinearMap (LinearMap.tensorKer S M f) (LinearMap.tensorKerInv S M f)
    (by ext x; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
        (ker f).injective_subtype)
      simp)

@[simp]

中文:
定义 线性映射.tensorKerEquiv
  签名: [模.平坦 R M]
  定义体: LinearEquiv.ofLinearMap (LinearMap.tensorKer S M f) (LinearMap.tensorKerInv S M f)
    (by ext x; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
        (ker f).injective_subtype)
      simp)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.tensorKer, LinearMap.tensorKerInv, Module, Module.Flat.lTensor_preserves_injective_linearMap, injective_subtype, lTensor_preserves_injective_linearMap, ofLinearMap, subtype, tensorKer, tensorKerInv
-/
def LinearMap.tensorKerEquiv [Module.Flat R M] :
    M otimes[R] LinearMap.ker f ≃ₗ[S] LinearMap.ker (AlgebraTensorModule.lTensor S M f) :=
  LinearEquiv.ofLinearMap (LinearMap.tensorKer S M f) (LinearMap.tensorKerInv S M f)
    (by ext x; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
        (ker f).injective_subtype)
      simp)

@[simp]
/--
lemma `LinearMap.tensorKerEquiv_apply` / 引理 `LinearMap.tensorKerEquiv_apply`

English:
lemma LinearMap.tensorKerEquiv_apply
  given: [Module.Flat R M] (x : M otimes[R] ker f)
  proof: rfl

@[simp]

中文:
引理 线性映射.tensorKerEquiv_apply
  条件: [模.平坦 R M] (x : M otimes[R] ker f)
  证明: rfl

@[simp]
-/
lemma LinearMap.tensorKerEquiv_apply [Module.Flat R M] (x : M otimes[R] ker f) :
    tensorKerEquiv S M f x = tensorKer S M f x :=
  rfl

@[simp]
/--
lemma `LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm` / 引理 `LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm`

English:
lemma LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm
  statement: [Module.Flat R M]
  proof: lTensor_ker_subtype_tensorKerInv S M f x

中文:
引理 线性映射.lTensor_ker_subtype_tensorKerEquiv_symm
  结论: [模.平坦 R M]
  证明: lTensor_ker_subtype_tensorKerInv S M f x

Depends on / 依赖: lTensor_ker_subtype_tensorKerInv
-/
lemma LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm [Module.Flat R M]
    (x : ker (AlgebraTensorModule.lTensor S M f)) :
    (lTensor M (ker f).subtype) ((tensorKerEquiv S M f).symm x) = x :=
  lTensor_ker_subtype_tensorKerInv S M f x

/--
Definition of `LinearMap.tensorEqLocusEquiv` / `LinearMap.tensorEqLocusEquiv` 的定义

English:
definition LinearMap.tensorEqLocusEquiv
  signature: [Module.Flat R M]
  body: LinearEquiv.ofLinearMap (LinearMap.tensorEqLocus S M f g) (LinearMap.tensorEqLocusInv S M f g)
    (by ext; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
        (eqLocus f g).injective_subtype)
      simp)

@[simp]

中文:
定义 线性映射.tensorEqLocusEquiv
  签名: [模.平坦 R M]
  定义体: LinearEquiv.ofLinearMap (LinearMap.tensorEqLocus S M f g) (LinearMap.tensorEqLocusInv S M f g)
    (by ext; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
        (eqLocus f g).injective_subtype)
      simp)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.tensorEqLocus, LinearMap.tensorEqLocusInv, Module, Module.Flat.lTensor_preserves_injective_linearMap, eqLocus, injective_subtype, lTensor_preserves_injective_linearMap, ofLinearMap, subtype, tensorEqLocus, tensorEqLocusInv
-/
def LinearMap.tensorEqLocusEquiv [Module.Flat R M] :
    M otimes[R] eqLocus f g ≃ₗ[S]
      eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) :=
  LinearEquiv.ofLinearMap (LinearMap.tensorEqLocus S M f g) (LinearMap.tensorEqLocusInv S M f g)
    (by ext; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
        (eqLocus f g).injective_subtype)
      simp)

@[simp]
/--
lemma `LinearMap.tensorEqLocusEquiv_apply` / 引理 `LinearMap.tensorEqLocusEquiv_apply`

English:
lemma LinearMap.tensorEqLocusEquiv_apply
  given: [Module.Flat R M] (x : M otimes[R] LinearMap.eqLocus f g)
  proof: rfl

@[simp]

中文:
引理 线性映射.tensorEqLocusEquiv_apply
  条件: [模.平坦 R M] (x : M otimes[R] 线性映射.eqLocus f g)
  证明: rfl

@[simp]
-/
lemma LinearMap.tensorEqLocusEquiv_apply [Module.Flat R M] (x : M otimes[R] LinearMap.eqLocus f g) :
    LinearMap.tensorEqLocusEquiv S M f g x = LinearMap.tensorEqLocus S M f g x :=
  rfl

@[simp]
/--
lemma `LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm` / 引理 `LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm`

English:
lemma LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm
  statement: [Module.Flat R M]
  proof: lTensor_eqLocus_subtype_tensorEqLocusInv S M f g x

中文:
引理 线性映射.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm
  结论: [模.平坦 R M]
  证明: lTensor_eqLocus_subtype_tensorEqLocusInv S M f g x

Depends on / 依赖: lTensor_eqLocus_subtype_tensorEqLocusInv
-/
lemma LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm [Module.Flat R M]
    (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g)) :
    (lTensor M (eqLocus f g).subtype) ((tensorEqLocusEquiv S M f g).symm x) = x :=
  lTensor_eqLocus_subtype_tensorEqLocusInv S M f g x

variable {M}

/--
lemma `LinearMap.lTensor_injective_of_exact_of_flat` / 引理 `LinearMap.lTensor_injective_of_exact_of_flat`

English:
lemma LinearMap.lTensor_injective_of_exact_of_flat
  statement: [Module.Flat R P]
  proof: by

中文:
引理 线性映射.lTensor_injective_of_exact_of_flat
  结论: [模.平坦 R P]
  证明: by
-/
lemma LinearMap.lTensor_injective_of_exact_of_flat [Module.Flat R P]
    (f : N ->ₗ[R] P) (hf : Function.Surjective f) (g : M ->ₗ[R] N) (hg : Function.Injective g)
    (H : Function.Exact g f) (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Injective (g.lTensor A) := by
/-
The proof is taking a resolution `0 → K → Q → A → 0` with `Q` flat,
and applying snake lemma on the following diagram to
```
                      0
                      ↓
    K ⊗ M → K ⊗ N → K ⊗ P → 0
      ↓ ↓ ↓
0 → Q ⊗ M → Q ⊗ N → Q ⊗ P
      ↓ ↓
    A ⊗ M → A ⊗ N
      ↓ ↓
      0 0
```
to get `0 → A ⊗ K → A ⊗ M` exact.
-/
  let Q := A ->₀ R
  let π : Q ->ₗ[R] A := Finsupp.linearCombination R fun a => a
  have hπ : Function.Surjective π := Finsupp.linearCombination_surjective _ Function.surjective_id
  let K := LinearMap.ker π
  have := SnakeLemma.exact_δ'_left (K.subtype.rTensor M) (K.subtype.rTensor N) (K.subtype.rTensor P)
    (g.lTensor K) (f.lTensor K) (lTensor_exact K H hf) (g.lTensor Q) (f.lTensor Q)
    (lTensor_exact Q H hf) (by simp) (by simp) (K₃ := Unit) 0
    (by simpa using Module.Flat.rTensor_preserves_injective_linearMap _ K.subtype_injective)
    (π.rTensor M) (rTensor_exact _ (exact_subtype_ker_map π) hπ) (π.rTensor N)
    (rTensor_exact _ (exact_subtype_ker_map π) hπ) (lTensor_surjective K hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg) (g.lTensor A)
    (by simp) (rTensor_surjective _ hπ)
  rw [Subsingleton.elim (SnakeLemma.δ' ..) 0] at this
  simpa using this

/--
Definition of `LinearMap.kerLTensorEquivOfSurjective` / `LinearMap.kerLTensorEquivOfSurjective` 的定义

English:
definition LinearMap.kerLTensorEquivOfSurjective
  signature: [Module.Flat R P]
  body: by
  refine .ofEq _ _ ?_ ≪≫ₗ (LinearEquiv.ofInjective _ (LinearMap.lTensor_injective_of_exact_of_flat
    f hf _ (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map _) _)).symm
  rw [LinearMap.exact_iff.mp (lTensor_exact _ (LinearMap.exact_subtype_ker_map _) hf)]

@[simp]

中文:
定义 线性映射.kerLTensorEquivOfSurjective
  签名: [模.平坦 R P]
  定义体: by
  refine .ofEq _ _ ?_ ≪≫ₗ (LinearEquiv.ofInjective _ (LinearMap.lTensor_injective_of_exact_of_flat
    f hf _ (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map _) _)).symm
  rw [LinearMap.exact_iff.mp (lTensor_exact _ (LinearMap.exact_subtype_ker_map _) hf)]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.exact_iff.mp, LinearMap.exact_subtype_ker_map, LinearMap.ker, LinearMap.lTensor_injective_of_exact_of_flat, exact_iff, exact_subtype_ker_map, lTensor_exact, lTensor_injective_of_exact_of_flat, ofInjective, subtype_injective
-/
def LinearMap.kerLTensorEquivOfSurjective [Module.Flat R P]
    (f : N ->ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] :
    LinearMap.ker (f.lTensor A) ≃ₗ[R] A otimes[R] LinearMap.ker f := by
  refine .ofEq _ _ ?_ ≪≫ₗ (LinearEquiv.ofInjective _ (LinearMap.lTensor_injective_of_exact_of_flat
    f hf _ (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map _) _)).symm
  rw [LinearMap.exact_iff.mp (lTensor_exact _ (LinearMap.exact_subtype_ker_map _) hf)]

@[simp]
/--
lemma `LinearMap.tensorKerEquivOfSurjective_symm_tmul` / 引理 `LinearMap.tensorKerEquivOfSurjective_symm_tmul`

English:
lemma LinearMap.tensorKerEquivOfSurjective_symm_tmul
  statement: [Module.Flat R P]
  proof: rfl

中文:
引理 线性映射.tensorKerEquivOfSurjective_symm_tmul
  结论: [模.平坦 R P]
  证明: rfl
-/
lemma LinearMap.tensorKerEquivOfSurjective_symm_tmul [Module.Flat R P]
    (f : N ->ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] (a y) :
    ((f.kerLTensorEquivOfSurjective hf A).symm (a otimesₜ y)).1 = a otimesₜ y.1 := rfl

end Module

section Algebra

variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (f g : A ->ₐ[R] B)

/--
Definition of `AlgHom.tensorEqualizerAux` / `AlgHom.tensorEqualizerAux` 的定义

English:
definition AlgHom.tensorEqualizerAux
  signature: :
  body: LinearMap.tensorEqLocus S T (f : A ->ₗ[R] B) (g : A ->ₗ[R] B)

private local instance : AddHomClass (A ->ₐ[R] B) A B := inferInstance

@[simp]

中文:
定义 代数态射.tensorEqualizerAux
  签名: :
  定义体: LinearMap.tensorEqLocus S T (f : A ->ₗ[R] B) (g : A ->ₗ[R] B)

private local instance : AddHomClass (A ->ₐ[R] B) A B := inferInstance

@[simp]

Depends on / 依赖: LinearMap, LinearMap.tensorEqLocus, tensorEqLocus
-/
def AlgHom.tensorEqualizerAux :
    T otimes[R] AlgHom.equalizer f g ->ₗ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  LinearMap.tensorEqLocus S T (f : A ->ₗ[R] B) (g : A ->ₗ[R] B)

private local instance : AddHomClass (A ->ₐ[R] B) A B := inferInstance

@[simp]
/--
lemma `AlgHom.coe_tensorEqualizerAux` / 引理 `AlgHom.coe_tensorEqualizerAux`

English:
lemma AlgHom.coe_tensorEqualizerAux
  given: (x : T otimes[R] AlgHom.equalizer f g)
  proof: by
  induction x with
  | zero => rfl
  | tmul => rfl
  | add x y hx hy => simp [hx, hy]

中文:
引理 代数态射.coe_tensorEqualizerAux
  条件: (x : T otimes[R] 代数态射.equalizer f g)
  证明: by
  induction x with
  | zero => rfl
  | tmul => rfl
  | add x y hx hy => simp [hx, hy]
-/
private lemma AlgHom.coe_tensorEqualizerAux (x : T otimes[R] AlgHom.equalizer f g) :
    (AlgHom.tensorEqualizerAux S T f g x : T otimes[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S T) (AlgHom.equalizer f g).val x := by
  induction x with
  | zero => rfl
  | tmul => rfl
  | add x y hx hy => simp [hx, hy]

/--
lemma `AlgHom.tensorEqualizerAux_mul` / 引理 `AlgHom.tensorEqualizerAux_mul`

English:
lemma AlgHom.tensorEqualizerAux_mul
  given: (x y : T otimes[R] AlgHom.equalizer f g)
  proof: by
  apply Subtype.ext
  rw [AlgHom.coe_tensorEqualizerAux]
  simp

中文:
引理 代数态射.tensorEqualizerAux_mul
  条件: (x y : T otimes[R] 代数态射.equalizer f g)
  证明: by
  apply Subtype.ext
  rw [AlgHom.coe_tensorEqualizerAux]
  simp

Depends on / 依赖: AlgHom, AlgHom.coe_tensorEqualizerAux, Subtype, Subtype.ext, coe_tensorEqualizerAux
-/
lemma AlgHom.tensorEqualizerAux_mul (x y : T otimes[R] AlgHom.equalizer f g) :
    AlgHom.tensorEqualizerAux S T f g (x * y) =
      AlgHom.tensorEqualizerAux S T f g x *
        AlgHom.tensorEqualizerAux S T f g y := by
  apply Subtype.ext
  rw [AlgHom.coe_tensorEqualizerAux]
  simp

/--
Definition of `AlgHom.tensorEqualizer` / `AlgHom.tensorEqualizer` 的定义

English:
definition AlgHom.tensorEqualizer
  signature: :
  body: AlgHom.ofLinearMap (AlgHom.tensorEqualizerAux S T f g)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]

中文:
定义 代数态射.tensorEqualizer
  签名: :
  定义体: AlgHom.ofLinearMap (AlgHom.tensorEqualizerAux S T f g)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, AlgHom.tensorEqualizerAux, AlgHom.tensorEqualizerAux_mul, ofLinearMap, tensorEqualizerAux, tensorEqualizerAux_mul
-/
def AlgHom.tensorEqualizer :
    T otimes[R] AlgHom.equalizer f g ->ₐ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  AlgHom.ofLinearMap (AlgHom.tensorEqualizerAux S T f g)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]
/--
lemma `AlgHom.coe_tensorEqualizer` / 引理 `AlgHom.coe_tensorEqualizer`

English:
lemma AlgHom.coe_tensorEqualizer
  given: (x : T otimes[R] AlgHom.equalizer f g)
  proof: AlgHom.coe_tensorEqualizerAux S T f g x

中文:
引理 代数态射.coe_tensorEqualizer
  条件: (x : T otimes[R] 代数态射.equalizer f g)
  证明: AlgHom.coe_tensorEqualizerAux S T f g x

Depends on / 依赖: AlgHom, AlgHom.coe_tensorEqualizerAux, coe_tensorEqualizerAux
-/
lemma AlgHom.coe_tensorEqualizer (x : T otimes[R] AlgHom.equalizer f g) :
    (AlgHom.tensorEqualizer S T f g x : T otimes[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S T) (AlgHom.equalizer f g).val x :=
  AlgHom.coe_tensorEqualizerAux S T f g x

/--
Definition of `AlgHom.tensorEqualizerEquiv` / `AlgHom.tensorEqualizerEquiv` 的定义

English:
definition AlgHom.tensorEqualizerEquiv
  signature: [Module.Flat R T]
  body: AlgEquiv.ofLinearEquiv (LinearMap.tensorEqLocusEquiv S T f.toLinearMap g.toLinearMap)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]

中文:
定义 代数态射.tensorEqualizerEquiv
  签名: [模.平坦 R T]
  定义体: AlgEquiv.ofLinearEquiv (LinearMap.tensorEqLocusEquiv S T f.toLinearMap g.toLinearMap)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, AlgHom, AlgHom.tensorEqualizerAux_mul, LinearMap, LinearMap.tensorEqLocusEquiv, f.toLinearMap, g.toLinearMap, ofLinearEquiv, tensorEqLocusEquiv, tensorEqualizerAux_mul, toLinearMap
-/
def AlgHom.tensorEqualizerEquiv [Module.Flat R T] :
    T otimes[R] AlgHom.equalizer f g ≃ₐ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  AlgEquiv.ofLinearEquiv (LinearMap.tensorEqLocusEquiv S T f.toLinearMap g.toLinearMap)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]
/--
lemma `AlgHom.tensorEqualizerEquiv_apply` / 引理 `AlgHom.tensorEqualizerEquiv_apply`

English:
lemma AlgHom.tensorEqualizerEquiv_apply
  statement: [Module.Flat R T]
  proof: rfl

中文:
引理 代数态射.tensorEqualizerEquiv_apply
  结论: [模.平坦 R T]
  证明: rfl
-/
lemma AlgHom.tensorEqualizerEquiv_apply [Module.Flat R T]
    (x : T otimes[R] AlgHom.equalizer f g) :
    AlgHom.tensorEqualizerEquiv S T f g x = AlgHom.tensorEqualizer S T f g x :=
  rfl

variable (R A) in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Definition of `Algebra.kerTensorProductMapIdToAlgHomEquiv` / `Algebra.kerTensorProductMapIdToAlgHomEquiv` 的定义

English:
definition Algebra.kerTensorProductMapIdToAlgHomEquiv
  body: by
  let φ : A otimes[R] S ->ₐ[A] A otimes[R] T :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ePp : A otimes[R] S ≃ₐ[S] S otimes[R] A :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₃ : (RingHom.ker φ) ≃ₗ[R] A otimes[R] (RingHom.ker (alg

中文:
定义 代数.kerTensorProductMapIdToAlgHomEquiv
  定义体: by
  let φ : A otimes[R] S ->ₐ[A] A otimes[R] T :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ePp : A otimes[R] S ≃ₐ[S] S otimes[R] A :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₃ : (RingHom.ker φ) ≃ₗ[R] A otimes[R] (RingHom.ker (alg

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, Algebra.TensorProduct.map, IsScalarTower, IsScalarTower.toAlgHom, LinearMap, LinearMap.kerLTensorEquivOfSurjective, RingHom, RingHom.ker, TensorProduct, algebraMap, commutes, kerLTensorEquivOfSurjective, otimes, restrictScalars, toAlgHom, toLinearMap
-/
def Algebra.kerTensorProductMapIdToAlgHomEquiv
    [Module.Flat R T] (h₁ : Function.Surjective (algebraMap S T)) :
    RingHom.ker (Algebra.TensorProduct.map (.id A A) (IsScalarTower.toAlgHom R S T)) ≃ₗ[A otimes[R] S]
      (A otimes[R] S) otimes[S] (RingHom.ker (algebraMap S T)) := by
  let φ : A otimes[R] S ->ₐ[A] A otimes[R] T :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ePp : A otimes[R] S ≃ₐ[S] S otimes[R] A :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₃ : (RingHom.ker φ) ≃ₗ[R] A otimes[R] (RingHom.ker (algebraMap S T)) :=
    (LinearMap.kerLTensorEquivOfSurjective (IsScalarTower.toAlgHom R S T).toLinearMap
      h₁ A).restrictScalars R
  let e₄' : (RingHom.ker φ) ≃ₗ[R] (A otimes[R] S) otimes[S] (RingHom.ker (algebraMap S T)) :=
    e₃ ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ S _ _).symm.restrictScalars R ≪≫ₗ
      (AlgebraTensorModule.congr (.refl S _) ePp.symm.toLinearEquiv).restrictScalars R ≪≫ₗ
      (_root_.TensorProduct.comm _ _ _).restrictScalars R
  let e₄ : (A otimes[R] S) otimes[S] (RingHom.ker (algebraMap S T)) ≃ₗ[A otimes[R] S] (RingHom.ker φ) :=
    { __ := e₄'.symm, map_smul' r' x := by
        dsimp
        induction x with
        | zero => simp only [smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, LinearEquiv.map_add, *]
        | tmul x y =>
        induction x with
        | zero => simp only [zero_tmul, smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, add_tmul, LinearEquiv.map_add, *]
        | tmul x z =>
        induction r' with
        | zero => simp only [zero_smul, LinearEquiv.map_zero]
        | add x y _ _ => simp only [add_smul, LinearEquiv.map_add, *]
        | tmul r s =>
        rw [smul_tmul']
        ext1
        dsimp [e₄', ePp, φ]
        change ((r * x) otimesₜ[R] ((s * z) * y.1)) = (r otimesₜ[R] s) * (x otimesₜ[R] (z * y.1))
        rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_assoc] }
  exact e₄.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/--
lemma `Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply` / 引理 `Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply`

English:
lemma Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply
  statement: [Module.Flat R T]
  proof: rfl

中文:
引理 代数.kerTensorProductMapIdToAlgHomEquiv_symm_apply
  结论: [模.平坦 R T]
  证明: rfl
-/
lemma Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply [Module.Flat R T]
    (h₁ : Function.Surjective (algebraMap S T)) (x y z) :
    ((kerTensorProductMapIdToAlgHomEquiv R S T A h₁).symm ((x otimesₜ y) otimesₜ z)).1 =
      x otimesₜ (y * z.1) := rfl

end Algebra

namespace RingHom

/--
Definition of `HasStableEqualizers` / `HasStableEqualizers` 的定义

English:
definition HasStableEqualizers
  signature: (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)
  body: forall {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A ->ₐ[R] B), P (algebraMap R A) -> P (algebraMap R B) ->
    Function.Bijective (f.tensorEqualizer R S g)

中文:
定义 HasStableEqualizers
  签名: (P : 对任意 {R S : 类型u} [交换环 R] [交换环 S], (R ->+* S) -> 命题)
  定义体: forall {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A ->ₐ[R] B), P (algebraMap R A) -> P (algebraMap R B) ->
    Function.Bijective (f.tensorEqualizer R S g)

Depends on / 依赖: Algebra, Bijective, CommRing, Function, Function.Bijective, algebraMap, f.tensorEqualizer, tensorEqualizer
-/
def HasStableEqualizers (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop) : Prop :=
  forall {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A ->ₐ[R] B), P (algebraMap R A) -> P (algebraMap R B) ->
    Function.Bijective (f.tensorEqualizer R S g)

end RingHom
