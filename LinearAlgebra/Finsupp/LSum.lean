/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Tactic.ApplyFun

/-!
# Sums as a linear map

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Data.Finsupp.Basic`.

## Main definitions

* `Finsupp.lsum`: `Finsupp.sum` or `Finsupp.liftAddHom` as a `LinearMap`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section SMul

variable {α : Type*} {β : Type*} {R R₂ : Type*} {M M₂ : Type*}

/--
theorem `smul_sum` / 定理 `smul_sum`

English:
theorem smul_sum
  given: [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α ->₀ β} {c : R} {h : α -> β -> M}
  proof: Finset.smul_sum

@[simp]

中文:
定理 smul_sum
  条件: [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α ->₀ β} {c : R} {h : α -> β -> M}
  证明: Finset.smul_sum

@[simp]

Depends on / 依赖: Finset, Finset.smul_sum, smul_sum
-/
theorem smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α ->₀ β} {c : R} {h : α -> β -> M} :
    c • v.sum h = v.sum fun a b => c • h a b :=
  Finset.smul_sum

@[simp]
/--
theorem `sum_smul_index_semilinearMap'` / 定理 `sum_smul_index_semilinearMap'`

English:
theorem sum_smul_index_semilinearMap'
  statement: [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M]
  proof: by
  rw [Finsupp.sum_smul_index']; rw [Finsupp.smul_sum]
  · simp only [map_smulₛₗ]
  · intro i
    exact (h i).map_zero

中文:
定理 sum_smul_index_semilinearMap'
  结论: [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M]
  证明: by
  rw [Finsupp.sum_smul_index']; rw [Finsupp.smul_sum]
  · simp only [map_smulₛₗ]
  · intro i
    exact (h i).map_zero

Depends on / 依赖: Finsupp, Finsupp.smul_sum, Finsupp.sum_smul_index, map_zero, smul_sum, sum_smul_index
-/
theorem sum_smul_index_semilinearMap' [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R₂ M₂] {σ : R ->+* R₂} {v : α ->₀ M} {c : R} {h : α -> M ->ₛₗ[σ] M₂} :
    ((c • v).sum fun a => h a) = σ c • v.sum fun a => h a := by
  rw [Finsupp.sum_smul_index']; rw [Finsupp.smul_sum]
  · simp only [map_smulₛₗ]
  · intro i
    exact (h i).map_zero

/--
theorem `sum_smul_index_linearMap'` / 定理 `sum_smul_index_linearMap'`

English:
theorem sum_smul_index_linearMap'
  statement: [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]
  proof: sum_smul_index_semilinearMap'

中文:
定理 sum_smul_index_linearMap'
  结论: [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]
  证明: sum_smul_index_semilinearMap'

Depends on / 依赖: sum_smul_index_semilinearMap
-/
theorem sum_smul_index_linearMap' [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]
    [Module R M₂] {v : α ->₀ M} {c : R} {h : α -> M ->ₗ[R] M₂} :
    ((c • v).sum fun a => h a) = c • v.sum fun a => h a :=
  sum_smul_index_semilinearMap'

end SMul

variable {α : Type*} {M N P : Type*} {R R₂ R₃ : Type*} {S : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R₂ N]
variable [AddCommMonoid P] [Module R₃ P]

variable {σ : R ->+* R₂} {σ_inv : R₂ ->+* R}

section CompatibleSMul

variable (R S M N ι : Type*)
variable [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]

/--
Instance `_root_.LinearMap.CompatibleSMul.finsupp_dom` / 实例 `_root_.LinearMap.CompatibleSMul.finsupp_dom`

English:
instance _root_.LinearMap.CompatibleSMul.finsupp_dom
  signature: [SMulZeroClass R M] [DistribSMul R N]
  body: by
    conv_rhs => rw [← sum_single m, map_finsuppSum, smul_sum]
    erw [← sum_single (r • m), sum_mapRange_index single_zero, map_finsuppSum]
    congr; ext i m; exact (f.comp <| lsingle i).map_smul_of_tower r m

中文:
实例 _root_.LinearMap.CompatibleSMul.finsupp_dom
  签名: [SMulZeroClass R M] [DistribSMul R N]
  定义体: by
    conv_rhs => rw [← sum_single m, map_finsuppSum, smul_sum]
    erw [← sum_single (r • m), sum_mapRange_index single_zero, map_finsuppSum]
    congr; ext i m; exact (f.comp <| lsingle i).map_smul_of_tower r m

Depends on / 依赖: conv_rhs, f.comp, lsingle, map_finsuppSum, map_smul_of_tower, single_zero, smul_sum, sum_mapRange_index, sum_single
-/
instance _root_.LinearMap.CompatibleSMul.finsupp_dom [SMulZeroClass R M] [DistribSMul R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul (ι ->₀ M) N R S where
  map_smul f r m := by
    conv_rhs => rw [← sum_single m, map_finsuppSum, smul_sum]
    erw [← sum_single (r • m), sum_mapRange_index single_zero, map_finsuppSum]
    congr; ext i m; exact (f.comp <| lsingle i).map_smul_of_tower r m

/--
Instance `_root_.LinearMap.CompatibleSMul.finsupp_cod` / 实例 `_root_.LinearMap.CompatibleSMul.finsupp_cod`

English:
instance _root_.LinearMap.CompatibleSMul.finsupp_cod
  signature: [SMul R M] [SMulZeroClass R N]
  body: by ext i; apply ((lapply i).comp f).map_smul_of_tower

中文:
实例 _root_.LinearMap.CompatibleSMul.finsupp_cod
  签名: [SMul R M] [SMulZeroClass R N]
  定义体: by ext i; apply ((lapply i).comp f).map_smul_of_tower

Depends on / 依赖: lapply, map_smul_of_tower
-/
instance _root_.LinearMap.CompatibleSMul.finsupp_cod [SMul R M] [SMulZeroClass R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι ->₀ N) R S where
  map_smul f r m := by ext i; apply ((lapply i).comp f).map_smul_of_tower

end CompatibleSMul

section LSum

variable (S)
variable [Module S N] [SMulCommClass R₂ S N]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lsum` / `lsum` 的定义

English:
definition lsum
  signature: : (α -> M ->ₛₗ[σ] N) ≃ₗ[S] (α ->₀ M) ->ₛₗ[σ] N where
  body: { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
  

中文:
定义 lsum
  签名: : (α -> M ->ₛₗ[σ] N) ≃ₗ[S] (α ->₀ M) ->ₛₗ[σ] N where
  定义体: { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
  

Depends on / 依赖: F.comp, d.sum, invFun, left_inv, liftAddHom, lsingle, map_add, map_smul, right_inv, smul_sum, sum_smul_index, toAddMonoidHom
-/
def lsum : (α -> M ->ₛₗ[σ] N) ≃ₗ[S] (α ->₀ M) ->ₛₗ[σ] N where
  toFun F :=
    { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
    ext x y
    simp
  map_add' F G := by
    ext x y
    simp
  map_smul' F G := by
    ext x y
    simp

@[simp]
/--
theorem `coe_lsum` / 定理 `coe_lsum`

English:
theorem coe_lsum
  given: (f : α -> M ->ₛₗ[σ] N)
  statement: (lsum S f : (α ->₀ M) -> N) = fun d => d.sum fun i => f i
  proof: rfl

中文:
定理 coe_lsum
  条件: (f : α -> M ->ₛₗ[σ] N)
  结论: (lsum S f : (α ->₀ M) -> N) = fun d => d.sum fun i => f i
  证明: rfl
-/
theorem coe_lsum (f : α -> M ->ₛₗ[σ] N) : (lsum S f : (α ->₀ M) -> N) = fun d => d.sum fun i => f i :=
  rfl

/--
theorem `lsum_apply` / 定理 `lsum_apply`

English:
theorem lsum_apply
  given: (f : α -> M ->ₛₗ[σ] N) (l : α ->₀ M)
  statement: Finsupp.lsum S f l = l.sum fun b => f b
  proof: rfl

中文:
定理 lsum_apply
  条件: (f : α -> M ->ₛₗ[σ] N) (l : α ->₀ M)
  结论: Finsupp.lsum S f l = l.sum fun b => f b
  证明: rfl
-/
theorem lsum_apply (f : α -> M ->ₛₗ[σ] N) (l : α ->₀ M) : Finsupp.lsum S f l = l.sum fun b => f b :=
  rfl

/--
theorem `lsum_single` / 定理 `lsum_single`

English:
theorem lsum_single
  given: (f : α -> M ->ₛₗ[σ] N) (i : α) (m : M)
  proof: Finsupp.sum_single_index (f i).map_zero

中文:
定理 lsum_single
  条件: (f : α -> M ->ₛₗ[σ] N) (i : α) (m : M)
  证明: Finsupp.sum_single_index (f i).map_zero

Depends on / 依赖: Finsupp, Finsupp.sum_single_index, map_zero, sum_single_index
-/
theorem lsum_single (f : α -> M ->ₛₗ[σ] N) (i : α) (m : M) :
    Finsupp.lsum S f (Finsupp.single i m) = f i m :=
  Finsupp.sum_single_index (f i).map_zero

/--
theorem `lsum_comp_lsingle` / 定理 `lsum_comp_lsingle`

English:
theorem lsum_comp_lsingle
  given: (f : α -> M ->ₛₗ[σ] N) (i : α)
  proof: by ext; simp

中文:
定理 lsum_comp_lsingle
  条件: (f : α -> M ->ₛₗ[σ] N) (i : α)
  证明: by ext; simp
-/
@[simp] theorem lsum_comp_lsingle (f : α -> M ->ₛₗ[σ] N) (i : α) :
    Finsupp.lsum S f ∘ₛₗ lsingle i = f i := by ext; simp

/--
theorem `lsum_symm_apply` / 定理 `lsum_symm_apply`

English:
theorem lsum_symm_apply
  given: (f : (α ->₀ M) ->ₛₗ[σ] N) (x : α)
  statement: (lsum S).symm f x = f.comp (lsingle x)
  proof: rfl

中文:
定理 lsum_symm_apply
  条件: (f : (α ->₀ M) ->ₛₗ[σ] N) (x : α)
  结论: (lsum S).symm f x = f.comp (lsingle x)
  证明: rfl
-/
theorem lsum_symm_apply (f : (α ->₀ M) ->ₛₗ[σ] N) (x : α) : (lsum S).symm f x = f.comp (lsingle x) :=
  rfl

end LSum

section

variable (M) (R) (X : Type*) (S)
variable [Module S M] [SMulCommClass R S M]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (X -> M) ≃+ ((X ->₀ R) ->ₗ[R] M)
  body: (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R Nat M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[Nat] _).toAddEquiv

@[simp]

中文:
定义 lift
  签名: : (X -> M) ≃+ ((X ->₀ R) ->ₗ[R] M)
  定义体: (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R Nat M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[Nat] _).toAddEquiv

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.arrowCongr, Equiv.refl, arrowCongr, ringLmapEquivSelf, toAddEquiv, toAddEquiv.symm
-/
noncomputable def lift : (X -> M) ≃+ ((X ->₀ R) ->ₗ[R] M) :=
  (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R Nat M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[Nat] _).toAddEquiv

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (f) (x)
  statement: ((lift M R X).symm f) x = f (single x 1)
  proof: rfl

@[simp]

中文:
定理 lift_symm_apply
  条件: (f) (x)
  结论: ((lift M R X).symm f) x = f (single x 1)
  证明: rfl

@[simp]
-/
theorem lift_symm_apply (f) (x) : ((lift M R X).symm f) x = f (single x 1) :=
  rfl

@[simp]
/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (f) (g)
  statement: ((lift M R X) f) g = g.sum fun x r => r • f x
  proof: rfl

中文:
定理 lift_apply
  条件: (f) (g)
  结论: ((lift M R X) f) g = g.sum fun x r => r • f x
  证明: rfl
-/
theorem lift_apply (f) (g) : ((lift M R X) f) g = g.sum fun x r => r • f x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `llift` / `llift` 的定义

English:
definition llift
  signature: : (X -> M) ≃ₗ[S] (X ->₀ R) ->ₗ[R] M
  body: { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }

@[simp]

中文:
定义 llift
  签名: : (X -> M) ≃ₗ[S] (X ->₀ R) ->ₗ[R] M
  定义体: { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }

@[simp]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.smul_apply, Pi.smul_apply, coe_comp, comp_apply, intros, lift_apply, lsingle_apply, map_smul, one_smul, smul_apply, sum_single_index, zero_smul
-/
noncomputable def llift : (X -> M) ≃ₗ[S] (X ->₀ R) ->ₗ[R] M :=
  { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }

@[simp]
/--
theorem `llift_apply` / 定理 `llift_apply`

English:
theorem llift_apply
  given: (f : X -> M) (x : X ->₀ R)
  statement: llift M R S X f x = lift M R X f x
  proof: rfl

@[simp]

中文:
定理 llift_apply
  条件: (f : X -> M) (x : X ->₀ R)
  结论: llift M R S X f x = lift M R X f x
  证明: rfl

@[simp]
-/
theorem llift_apply (f : X -> M) (x : X ->₀ R) : llift M R S X f x = lift M R X f x :=
  rfl

@[simp]
/--
theorem `llift_symm_apply` / 定理 `llift_symm_apply`

English:
theorem llift_symm_apply
  given: (f : (X ->₀ R) ->ₗ[R] M) (x : X)
  proof: rfl

中文:
定理 llift_symm_apply
  条件: (f : (X ->₀ R) ->ₗ[R] M) (x : X)
  证明: rfl
-/
theorem llift_symm_apply (f : (X ->₀ R) ->ₗ[R] M) (x : X) :
    (llift M R S X).symm f x = f (single x 1) :=
  rfl

end

/--
Definition of `domLCongr` / `domLCongr` 的定义

English:
definition domLCongr
  signature: {α₁ α₂ : Type*} (e : α₁ ≃ α₂)
  body: (Finsupp.domCongr e : (α₁ ->₀ M) ≃+ (α₂ ->₀ M)).toLinearEquiv by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using! (lmapDomain M R e).map_smul

@[simp]

中文:
定义 domLCongr
  签名: {α₁ α₂ : 类型} (e : α₁ ≃ α₂)
  定义体: (Finsupp.domCongr e : (α₁ ->₀ M) ≃+ (α₂ ->₀ M)).toLinearEquiv by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using! (lmapDomain M R e).map_smul

@[simp]
-/
protected def domLCongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) : (α₁ ->₀ M) ≃ₗ[R] α₂ ->₀ M :=
(Finsupp.domCongr e : (α₁ ->₀ M) ≃+ (α₂ ->₀ M)).toLinearEquiv by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using! (lmapDomain M R e).map_smul

@[simp]
/--
theorem `domLCongr_apply` / 定理 `domLCongr_apply`

English:
theorem domLCongr_apply
  given: {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ ->₀ M)
  proof: rfl

@[simp]

中文:
定理 domLCongr_apply
  条件: {α₁ : 类型} {α₂ : 类型} (e : α₁ ≃ α₂) (v : α₁ ->₀ M)
  证明: rfl

@[simp]
-/
theorem domLCongr_apply {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ ->₀ M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v :=
  rfl

@[simp]
/--
theorem `domLCongr_refl` / 定理 `domLCongr_refl`

English:
theorem domLCongr_refl
  statement: Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α ->₀ M)
  proof: LinearEquiv.ext fun _ => equivMapDomain_refl _

中文:
定理 domLCongr_refl
  结论: Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α ->₀ M)
  证明: LinearEquiv.ext fun _ => equivMapDomain_refl _

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, equivMapDomain_refl
-/
theorem domLCongr_refl : Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α ->₀ M) :=
  LinearEquiv.ext fun _ => equivMapDomain_refl _

/--
theorem `domLCongr_trans` / 定理 `domLCongr_trans`

English:
theorem domLCongr_trans
  given: {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃)
  proof: LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

@[simp]

中文:
定理 domLCongr_trans
  条件: {α₁ α₂ α₃ : 类型} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃)
  证明: LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, equivMapDomain_trans
-/
theorem domLCongr_trans {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
    (Finsupp.domLCongr f).trans (Finsupp.domLCongr f₂) =
      (Finsupp.domLCongr (f.trans f₂) : (_ ->₀ M) ≃ₗ[R] _) :=
  LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

@[simp]
/--
theorem `domLCongr_symm` / 定理 `domLCongr_symm`

English:
theorem domLCongr_symm
  given: {α₁ α₂ : Type*} (f : α₁ ≃ α₂)
  proof: LinearEquiv.ext fun _ => rfl

中文:
定理 domLCongr_symm
  条件: {α₁ α₂ : 类型} (f : α₁ ≃ α₂)
  证明: LinearEquiv.ext fun _ => rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.ext
-/
theorem domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) :
    ((Finsupp.domLCongr f).symm : (_ ->₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm :=
  LinearEquiv.ext fun _ => rfl

/--
theorem `domLCongr_single` / 定理 `domLCongr_single`

English:
theorem domLCongr_single
  given: {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M)
  proof: by
  simp

中文:
定理 domLCongr_single
  条件: {α₁ : 类型} {α₂ : 类型} (e : α₁ ≃ α₂) (i : α₁) (m : M)
  证明: by
  simp
-/
theorem domLCongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) m := by
  simp

section Equiv

variable [RingHomInvPair σ σ_inv] [RingHomInvPair σ_inv σ]

/--
Definition of `lcongr` / `lcongr` 的定义

English:
definition lcongr
  signature: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N)
  body: (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)

@[simp]

中文:
定义 lcongr
  签名: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N)
  定义体: (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.domLCongr, domLCongr, linearEquiv, mapRange, mapRange.linearEquiv
-/
def lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) : (ι ->₀ M) ≃ₛₗ[σ] κ ->₀ N :=
  (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)

@[simp]
/--
theorem `lcongr_single` / 定理 `lcongr_single`

English:
theorem lcongr_single
  given: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (i : ι) (m : M)
  proof: by simp [lcongr]

@[simp]

中文:
定理 lcongr_single
  条件: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (i : ι) (m : M)
  证明: by simp [lcongr]

@[simp]

Depends on / 依赖: lcongr
-/
theorem lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (i : ι) (m : M) :
    lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single (e₁ i) (e₂ m) := by simp [lcongr]

@[simp]
/--
theorem `lcongr_apply_apply` / 定理 `lcongr_apply_apply`

English:
theorem lcongr_apply_apply
  given: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (f : ι ->₀ M) (k : κ)
  proof: rfl

中文:
定理 lcongr_apply_apply
  条件: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (f : ι ->₀ M) (k : κ)
  证明: rfl
-/
theorem lcongr_apply_apply {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (f : ι ->₀ M) (k : κ) :
    lcongr e₁ e₂ f k = e₂ (f (e₁.symm k)) :=
  rfl

/--
theorem `lcongr_symm_single` / 定理 `lcongr_symm_single`

English:
theorem lcongr_symm_single
  given: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (k : κ) (n : N)
  proof: by
  apply_fun (lcongr e₁ e₂ : (ι ->₀ M) -> (κ ->₀ N)) using (lcongr e₁ e₂).injective
  simp

@[simp]

中文:
定理 lcongr_symm_single
  条件: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (k : κ) (n : N)
  证明: by
  apply_fun (lcongr e₁ e₂ : (ι ->₀ M) -> (κ ->₀ N)) using (lcongr e₁ e₂).injective
  simp

@[simp]

Depends on / 依赖: apply_fun, injective, lcongr
-/
theorem lcongr_symm_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (k : κ) (n : N) :
    (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (e₂.symm n) := by
  apply_fun (lcongr e₁ e₂ : (ι ->₀ M) -> (κ ->₀ N)) using (lcongr e₁ e₂).injective
  simp

@[simp]
/--
theorem `lcongr_symm` / 定理 `lcongr_symm`

English:
theorem lcongr_symm
  given: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N)
  proof: by
  ext
  rfl

中文:
定理 lcongr_symm
  条件: {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N)
  证明: by
  ext
  rfl
-/
theorem lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) :
    (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm := by
  ext
  rfl

end Equiv

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/--
theorem `Submodule.finsuppSum_mem` / 定理 `Submodule.finsuppSum_mem`

English:
theorem Submodule.finsuppSum_mem
  statement: {ι β : Type*} [Zero β] (S : Submodule R M) (f : ι ->₀ β)
  proof: AddSubmonoidClass.finsuppSum_mem S f g h

中文:
定理 Submodule.finsuppSum_mem
  结论: {ι β : 类型} [Zero β] (S : Submodule R M) (f : ι ->₀ β)
  证明: AddSubmonoidClass.finsuppSum_mem S f g h
-/
protected theorem Submodule.finsuppSum_mem {ι β : Type*} [Zero β] (S : Submodule R M) (f : ι ->₀ β)
    (g : ι -> β -> M) (h : forall c, f c != 0 -> g c (f c) in S) : f.sum g in S :=
  AddSubmonoidClass.finsuppSum_mem S f g h

end

namespace LinearMap

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFunOnFintypeSurjective`
/--
Definition of `splittingOfFinsuppSurjective` / `splittingOfFinsuppSurjective` 的定义

English:
definition splittingOfFinsuppSurjective
  signature: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  body: Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose

中文:
定义 splittingOfFinsuppSurjective
  签名: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  定义体: Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose

Depends on / 依赖: Finsupp, Finsupp.lift, Finsupp.single, single
-/
def splittingOfFinsuppSurjective (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) : (α ->₀ R) ->ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose

/--
theorem `splittingOfFinsuppSurjective_splits` / 定理 `splittingOfFinsuppSurjective_splits`

English:
theorem splittingOfFinsuppSurjective_splits
  given: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  proof: by
  ext x
  dsimp [splittingOfFinsuppSurjective]
  congr
  rw [sum_single_index]; rw [one_smul]
  · exact (s (Finsupp.single x 1)).choose_spec
  · rw [zero_smul]

中文:
定理 splittingOfFinsuppSurjective_splits
  条件: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  证明: by
  ext x
  dsimp [splittingOfFinsuppSurjective]
  congr
  rw [sum_single_index]; rw [one_smul]
  · exact (s (Finsupp.single x 1)).choose_spec
  · rw [zero_smul]

Depends on / 依赖: Finsupp, Finsupp.single, choose_spec, one_smul, single, splittingOfFinsuppSurjective, sum_single_index, zero_smul
-/
theorem splittingOfFinsuppSurjective_splits (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) :
    f.comp (splittingOfFinsuppSurjective f s) = LinearMap.id := by
  ext x
  dsimp [splittingOfFinsuppSurjective]
  congr
  rw [sum_single_index]; rw [one_smul]
  · exact (s (Finsupp.single x 1)).choose_spec
  · rw [zero_smul]

/--
theorem `leftInverse_splittingOfFinsuppSurjective` / 定理 `leftInverse_splittingOfFinsuppSurjective`

English:
theorem leftInverse_splittingOfFinsuppSurjective
  given: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  proof: fun g =>
  LinearMap.congr_fun (splittingOfFinsuppSurjective_splits f s) g

中文:
定理 leftInverse_splittingOfFinsuppSurjective
  条件: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  证明: fun g =>
  LinearMap.congr_fun (splittingOfFinsuppSurjective_splits f s) g
-/
theorem leftInverse_splittingOfFinsuppSurjective (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) :
    LeftInverse f (splittingOfFinsuppSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFinsuppSurjective_splits f s) g

/--
theorem `splittingOfFinsuppSurjective_injective` / 定理 `splittingOfFinsuppSurjective_injective`

English:
theorem splittingOfFinsuppSurjective_injective
  given: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  proof: (leftInverse_splittingOfFinsuppSurjective f s).injective

中文:
定理 splittingOfFinsuppSurjective_injective
  条件: (f : M ->ₗ[R] α ->₀ R) (s : Surjective f)
  证明: (leftInverse_splittingOfFinsuppSurjective f s).injective

Depends on / 依赖: injective, leftInverse_splittingOfFinsuppSurjective
-/
theorem splittingOfFinsuppSurjective_injective (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) :
    Injective (splittingOfFinsuppSurjective f s) :=
  (leftInverse_splittingOfFinsuppSurjective f s).injective

end LinearMap

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] {σ₁₂ : R ->+* R₂}
variable [Module R M] [Module R₂ M₂]
variable {γ : Type*} [Zero γ]

section Finsupp

/--
theorem `coe_finsupp_sum` / 定理 `coe_finsupp_sum`

English:
theorem coe_finsupp_sum
  given: (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂)
  proof: rfl

@[simp]

中文:
定理 coe_finsupp_sum
  条件: (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂)
  证明: rfl

@[simp]
-/
theorem coe_finsupp_sum (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl

@[simp]
/--
theorem `finsupp_sum_apply` / 定理 `finsupp_sum_apply`

English:
theorem finsupp_sum_apply
  given: (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂) (b : M)
  proof: sum_apply _ _ _

中文:
定理 finsupp_sum_apply
  条件: (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂) (b : M)
  证明: sum_apply _ _ _

Depends on / 依赖: sum_apply
-/
theorem finsupp_sum_apply (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _

end Finsupp

end AddCommMonoid

end LinearMap

namespace Submodule

variable {S : Type*} [Semiring S] [Module R S] [SMulCommClass R R S]

section
variable [SMulCommClass R S S]

/--
Definition of `mulLeftMap` / `mulLeftMap` 的定义

English:
definition mulLeftMap
  signature: {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι -> M)
  body: Finsupp.lsum R fun i => (m i).1 • N.subtype

中文:
定义 mulLeftMap
  签名: {M : Submodule R S} (N : Submodule R S) {ι : 类型} (m : ι -> M)
  定义体: Finsupp.lsum R fun i => (m i).1 • N.subtype

Depends on / 依赖: Finsupp, Finsupp.lsum, N.subtype, subtype
-/
def mulLeftMap {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι -> M) :
    (ι ->₀ N) ->ₗ[R] S := Finsupp.lsum R fun i => (m i).1 • N.subtype

/--
theorem `mulLeftMap_apply` / 定理 `mulLeftMap_apply`

English:
theorem mulLeftMap_apply
  given: {M N : Submodule R S} {ι : Type*} (m : ι -> M) (n : ι ->₀ N)
  proof: rfl

@[simp]

中文:
定理 mulLeftMap_apply
  条件: {M N : Submodule R S} {ι : 类型} (m : ι -> M) (n : ι ->₀ N)
  证明: rfl

@[simp]
-/
theorem mulLeftMap_apply {M N : Submodule R S} {ι : Type*} (m : ι -> M) (n : ι ->₀ N) :
    mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) => (m i).1 * n.1 := rfl

@[simp]
/--
theorem `mulLeftMap_apply_single` / 定理 `mulLeftMap_apply_single`

English:
theorem mulLeftMap_apply_single
  given: {M N : Submodule R S} {ι : Type*} (m : ι -> M) (i : ι) (n : N)
  proof: by
  simp [mulLeftMap]

中文:
定理 mulLeftMap_apply_single
  条件: {M N : Submodule R S} {ι : 类型} (m : ι -> M) (i : ι) (n : N)
  证明: by
  simp [mulLeftMap]

Depends on / 依赖: mulLeftMap
-/
theorem mulLeftMap_apply_single {M N : Submodule R S} {ι : Type*} (m : ι -> M) (i : ι) (n : N) :
    mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1 := by
  simp [mulLeftMap]

end

variable [IsScalarTower R S S]

/--
Definition of `mulRightMap` / `mulRightMap` 的定义

English:
definition mulRightMap
  signature: (M : Submodule R S) {N : Submodule R S} {ι : Type*} (n : ι -> N)
  body: Finsupp.lsum R fun i => MulOpposite.op (n i).1 • M.subtype

中文:
定义 mulRightMap
  签名: (M : Submodule R S) {N : Submodule R S} {ι : 类型} (n : ι -> N)
  定义体: Finsupp.lsum R fun i => MulOpposite.op (n i).1 • M.subtype

Depends on / 依赖: Finsupp, Finsupp.lsum, M.subtype, MulOpposite, MulOpposite.op, subtype
-/
def mulRightMap (M : Submodule R S) {N : Submodule R S} {ι : Type*} (n : ι -> N) :
    (ι ->₀ M) ->ₗ[R] S := Finsupp.lsum R fun i => MulOpposite.op (n i).1 • M.subtype

/--
theorem `mulRightMap_apply` / 定理 `mulRightMap_apply`

English:
theorem mulRightMap_apply
  given: {M N : Submodule R S} {ι : Type*} (n : ι -> N) (m : ι ->₀ M)
  proof: rfl

@[simp]

中文:
定理 mulRightMap_apply
  条件: {M N : Submodule R S} {ι : 类型} (n : ι -> N) (m : ι ->₀ M)
  证明: rfl

@[simp]
-/
theorem mulRightMap_apply {M N : Submodule R S} {ι : Type*} (n : ι -> N) (m : ι ->₀ M) :
    mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) => m.1 * (n i).1 := rfl

@[simp]
/--
theorem `mulRightMap_apply_single` / 定理 `mulRightMap_apply_single`

English:
theorem mulRightMap_apply_single
  given: {M N : Submodule R S} {ι : Type*} (n : ι -> N) (i : ι) (m : M)
  proof: by
  simp [mulRightMap]

中文:
定理 mulRightMap_apply_single
  条件: {M N : Submodule R S} {ι : 类型} (n : ι -> N) (i : ι) (m : M)
  证明: by
  simp [mulRightMap]

Depends on / 依赖: mulRightMap
-/
theorem mulRightMap_apply_single {M N : Submodule R S} {ι : Type*} (n : ι -> N) (i : ι) (m : M) :
    mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1 := by
  simp [mulRightMap]

/--
theorem `mulLeftMap_eq_mulRightMap_of_commute` / 定理 `mulLeftMap_eq_mulRightMap_of_commute`

English:
theorem mulLeftMap_eq_mulRightMap_of_commute
  statement: [SMulCommClass R S S]
  proof: by
  ext i n; simp [(hc i n).eq]

中文:
定理 mulLeftMap_eq_mulRightMap_of_commute
  结论: [SMulCommClass R S S]
  证明: by
  ext i n; simp [(hc i n).eq]
-/
theorem mulLeftMap_eq_mulRightMap_of_commute [SMulCommClass R S S]
    {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι -> M)
    (hc : forall (i : ι) (n : N), Commute (m i).1 n.1) : mulLeftMap N m = mulRightMap N m := by
  ext i n; simp [(hc i n).eq]

/--
theorem `mulLeftMap_eq_mulRightMap` / 定理 `mulLeftMap_eq_mulRightMap`

English:
theorem mulLeftMap_eq_mulRightMap
  statement: {S : Type*} [CommSemiring S] [Module R S] [SMulCommClass R R S]
  proof: mulLeftMap_eq_mulRightMap_of_commute N m fun _ _ => mul_comm _ _

中文:
定理 mulLeftMap_eq_mulRightMap
  结论: {S : 类型} [CommSemiring S] [Module R S] [SMulCommClass R R S]
  证明: mulLeftMap_eq_mulRightMap_of_commute N m fun _ _ => mul_comm _ _

Depends on / 依赖: mulLeftMap_eq_mulRightMap_of_commute, mul_comm
-/
theorem mulLeftMap_eq_mulRightMap {S : Type*} [CommSemiring S] [Module R S] [SMulCommClass R R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {M : Submodule R S} (N : Submodule R S)
    {ι : Type*} (m : ι -> M) : mulLeftMap N m = mulRightMap N m :=
  mulLeftMap_eq_mulRightMap_of_commute N m fun _ _ => mul_comm _ _

end Submodule
