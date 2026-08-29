/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.UniformSpace.ProdApproximation

/-!
# Abstract measures on topological spaces

We define an "abstract measure" on `X`, with values in a normed ring `R`, to be an `R`-linear
functional on continuous maps `X → R`. This is an important construction in p-adic analysis (where
the Iwasawa algebra is defined as the space of abstract measures on `ℤ_[p]` with values in `ℚ_[p]`).
-/

public section

open ContinuousMap

variable {X Y R E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Module R E] --[ContinuousSMul R E]

section Defs

/-!
### Basic definitions
-/

variable (X R E) in
/--
Definition of `AbstractMeasure` / `AbstractMeasure` 的定义

English:
definition AbstractMeasure
  body: C(X, R) ->L[R] E

@[inherit_doc]
scoped [AbstractMeasure] notation "D(" X ", " R ")" => AbstractMeasure X R R

中文:
定义 AbstractMeasure
  定义体: C(X, R) ->L[R] E

@[inherit_doc]
scoped [AbstractMeasure] notation "D(" X ", " R ")" => AbstractMeasure X R R
-/
@[expose] def AbstractMeasure := C(X, R) ->L[R] E

@[inherit_doc]
scoped [AbstractMeasure] notation "D(" X ", " R ")" => AbstractMeasure X R R

end Defs

namespace AbstractMeasure

section NoContinuousSMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (AbstractMeasure X R E) C(X, R) E
  body: inferInstanceAs (FunLike (C(X, R) ->L[R] E) C(X, R) E)

中文:
实例 :
  签名: FunLike (AbstractMeasure X R E) C(X, R) E
  定义体: inferInstanceAs (FunLike (C(X, R) ->L[R] E) C(X, R) E)

Depends on / 依赖: FunLike
-/
instance : FunLike (AbstractMeasure X R E) C(X, R) E :=
  inferInstanceAs (FunLike (C(X, R) ->L[R] E) C(X, R) E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousLinearMapClass (AbstractMeasure X R E) R C(X, R) E
  body: inferInstanceAs (ContinuousLinearMapClass (C(X, R) ->L[R] E) R C(X, R) E)

中文:
实例 :
  签名: ContinuousLinearMapClass (AbstractMeasure X R E) R C(X, R) E
  定义体: inferInstanceAs (ContinuousLinearMapClass (C(X, R) ->L[R] E) R C(X, R) E)

Depends on / 依赖: ContinuousLinearMapClass
-/
instance : ContinuousLinearMapClass (AbstractMeasure X R E) R C(X, R) E :=
  inferInstanceAs (ContinuousLinearMapClass (C(X, R) ->L[R] E) R C(X, R) E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (AbstractMeasure X R E)
  body: inferInstanceAs (AddCommGroup (C(X, R) ->L[R] E))

中文:
实例 :
  签名: AddCommGroup (AbstractMeasure X R E)
  定义体: inferInstanceAs (AddCommGroup (C(X, R) ->L[R] E))

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup (AbstractMeasure X R E) :=
  inferInstanceAs (AddCommGroup (C(X, R) ->L[R] E))

/--
Instance `isAddApply` / 实例 `isAddApply`

English:
instance isAddApply
  signature: : IsAddApply (AbstractMeasure X R E) C(X, R) E where
  body: rfl

中文:
实例 isAddApply
  签名: : IsAddApply (AbstractMeasure X R E) C(X, R) E where
  定义体: rfl
-/
instance isAddApply : IsAddApply (AbstractMeasure X R E) C(X, R) E where
  add_apply _ _ _ := rfl

end NoContinuousSMul

section ContinuousSMul

variable [ContinuousSMul R E]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (AbstractMeasure X R E)
  body: inferInstanceAs (Module R (C(X, R) ->L[R] E))

中文:
实例 :
  签名: Module R (AbstractMeasure X R E)
  定义体: inferInstanceAs (Module R (C(X, R) ->L[R] E))

Depends on / 依赖: Module
-/
instance : Module R (AbstractMeasure X R E) :=
  inferInstanceAs (Module R (C(X, R) ->L[R] E))

/--
Instance `isSMulApply` / 实例 `isSMulApply`

English:
instance isSMulApply
  signature: : IsSMulApply R (AbstractMeasure X R E) C(X, R) E where
  body: rfl

中文:
实例 isSMulApply
  签名: : IsSMulApply R (AbstractMeasure X R E) C(X, R) E where
  定义体: rfl
-/
instance isSMulApply : IsSMulApply R (AbstractMeasure X R E) C(X, R) E where
  smul_apply _ _ _ := rfl

/--
Definition of `toCLMEquiv` / `toCLMEquiv` 的定义

English:
definition toCLMEquiv
  signature: : AbstractMeasure X R E ≃ₗ[R] C(X, R) ->L[R] E
  body: LinearEquiv.refl _ _

中文:
定义 toCLMEquiv
  签名: : AbstractMeasure X R E ≃ₗ[R] C(X, R) ->L[R] E
  定义体: LinearEquiv.refl _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def toCLMEquiv : AbstractMeasure X R E ≃ₗ[R] C(X, R) ->L[R] E :=
  LinearEquiv.refl _ _

/--
lemma `coe_toCLMEquiv` / 引理 `coe_toCLMEquiv`

English:
lemma coe_toCLMEquiv
  given: (μ : AbstractMeasure X R E) (f : C(X, R))
  proof: (rfl)

中文:
引理 coe_toCLMEquiv
  条件: (μ : AbstractMeasure X R E) (f : C(X, R))
  证明: (rfl)
-/
@[simp] lemma coe_toCLMEquiv (μ : AbstractMeasure X R E) (f : C(X, R)) :
    toCLMEquiv μ f = μ f :=
  (rfl)

/--
lemma `coe_symm_toCLMEquiv` / 引理 `coe_symm_toCLMEquiv`

English:
lemma coe_symm_toCLMEquiv
  given: (L : C(X, R) ->L[R] E) (f : C(X, R))
  proof: (rfl)

中文:
引理 coe_symm_toCLMEquiv
  条件: (L : C(X, R) ->L[R] E) (f : C(X, R))
  证明: (rfl)
-/
@[simp] lemma coe_symm_toCLMEquiv (L : C(X, R) ->L[R] E) (f : C(X, R)) :
    toCLMEquiv.symm L f = L f :=
  (rfl)

variable (R) in
/--
Definition of `dirac` / `dirac` 的定义

English:
definition dirac
  signature: (x : X)
  body: toCLMEquiv.symm (ContinuousMap.evalCLM R x)

中文:
定义 dirac
  签名: (x : X)
  定义体: toCLMEquiv.symm (ContinuousMap.evalCLM R x)

Depends on / 依赖: ContinuousMap, ContinuousMap.evalCLM, evalCLM, toCLMEquiv, toCLMEquiv.symm
-/
def dirac (x : X) : D(X, R) :=
  toCLMEquiv.symm (ContinuousMap.evalCLM R x)

/--
lemma `dirac_apply` / 引理 `dirac_apply`

English:
lemma dirac_apply
  given: (x : X) (f : C(X, R))
  statement: dirac R x f = f x
  proof: (rfl)

中文:
引理 dirac_apply
  条件: (x : X) (f : C(X, R))
  结论: dirac R x f = f x
  证明: (rfl)
-/
@[simp] lemma dirac_apply (x : X) (f : C(X, R)) : dirac R x f = f x := (rfl)

section Map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : C(X, Y))
  body: μ ∘L f.compCLM R R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 map
  签名: (f : C(X, Y))
  定义体: μ ∘L f.compCLM R R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: compCLM, f.compCLM
-/
def map (f : C(X, Y)) : AbstractMeasure X R E ->ₗ[R] AbstractMeasure Y R E where
  toFun μ := μ ∘L f.compCLM R R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : C(X, Y)) (μ : AbstractMeasure X R E) (g : C(Y, R))
  proof: (rfl)

中文:
引理 map_apply
  条件: (f : C(X, Y)) (μ : AbstractMeasure X R E) (g : C(Y, R))
  证明: (rfl)
-/
@[simp] lemma map_apply (f : C(X, Y)) (μ : AbstractMeasure X R E) (g : C(Y, R)) :
    map f μ g = μ (g.comp f) :=
  (rfl)

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  statement: {Z : Type*} [TopologicalSpace Z]
  proof: (rfl)

@[simp]

中文:
引理 map_map
  结论: {Z : 类型} [TopologicalSpace Z]
  证明: (rfl)

@[simp]
-/
@[simp] lemma map_map {Z : Type*} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (μ : AbstractMeasure X R E) :
    map g (map f μ) = map (g.comp f) μ :=
  (rfl)

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (μ : AbstractMeasure X R E)
  proof: (rfl)

中文:
引理 map_id
  条件: (μ : AbstractMeasure X R E)
  证明: (rfl)
-/
lemma map_id (μ : AbstractMeasure X R E) :
    map (.id X) μ = μ :=
  (rfl)

/--
lemma `map_dirac` / 引理 `map_dirac`

English:
lemma map_dirac
  given: (f : C(X, Y)) (x : X)
  proof: (rfl)

中文:
引理 map_dirac
  条件: (f : C(X, Y)) (x : X)
  证明: (rfl)
-/
@[simp] lemma map_dirac (f : C(X, Y)) (x : X) :
    map f (dirac R x) = dirac R (f x) :=
  (rfl)

end Map

section Prod

/-!
### Product structure
-/

-- note we define `contractSnd` first, because `f.curry` only works one way round

/--
Definition of `contractSnd` / `contractSnd` 的定义

English:
definition contractSnd
  signature: : D(Y, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(X, R)
  body: LinearMap.mk₂ R (fun ν f => comp ν f.curry) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

中文:
定义 contractSnd
  签名: : D(Y, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(X, R)
  定义体: LinearMap.mk₂ R (fun ν f => comp ν f.curry) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

Depends on / 依赖: LinearMap, LinearMap.mk, all_goals, f.curry, finally, intros
-/
def contractSnd : D(Y, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(X, R) :=
  LinearMap.mk₂ R (fun ν f => comp ν f.curry) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

/--
Definition of `contractFst` / `contractFst` 的定义

English:
definition contractFst
  signature: : D(X, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(Y, R)
  body: ((prodSwap.compCLM R R).toLinearMap.lcomp R _).comp contractSnd

中文:
定义 contractFst
  签名: : D(X, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(Y, R)
  定义体: ((prodSwap.compCLM R R).toLinearMap.lcomp R _).comp contractSnd

Depends on / 依赖: compCLM, contractSnd, prodSwap, prodSwap.compCLM, toLinearMap, toLinearMap.lcomp
-/
def contractFst : D(X, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(Y, R) :=
  ((prodSwap.compCLM R R).toLinearMap.lcomp R _).comp contractSnd

variable (μ : D(X, R)) (ν : D(Y, R))

/--
lemma `contractFst_apply` / 引理 `contractFst_apply`

English:
lemma contractFst_apply
  given: (f : C(X × Y, R)) (y : Y)
  proof: (rfl)

中文:
引理 contractFst_apply
  条件: (f : C(X × Y, R)) (y : Y)
  证明: (rfl)
-/
@[simp] lemma contractFst_apply (f : C(X × Y, R)) (y : Y) :
    contractFst μ f y = μ ⟨fun x => f (x, y), by continuity⟩ :=
  (rfl)

/--
lemma `contractSnd_apply` / 引理 `contractSnd_apply`

English:
lemma contractSnd_apply
  given: (f : C(X × Y, R)) (x : X)
  proof: (rfl)

中文:
引理 contractSnd_apply
  条件: (f : C(X × Y, R)) (x : X)
  证明: (rfl)
-/
@[simp] lemma contractSnd_apply (f : C(X × Y, R)) (x : X) :
    contractSnd ν f x = ν ⟨fun y => f (x, y), by continuity⟩ :=
  (rfl)

/--
lemma `contractFst_dirac` / 引理 `contractFst_dirac`

English:
lemma contractFst_dirac
  given: (x : X) (y : Y) (f : C(X × Y, R))
  proof: (rfl)

中文:
引理 contractFst_dirac
  条件: (x : X) (y : Y) (f : C(X × Y, R))
  证明: (rfl)
-/
lemma contractFst_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractFst (dirac R x) f y = f (x, y) :=
  (rfl)

/--
lemma `contractSnd_dirac` / 引理 `contractSnd_dirac`

English:
lemma contractSnd_dirac
  given: (x : X) (y : Y) (f : C(X × Y, R))
  proof: (rfl)

中文:
引理 contractSnd_dirac
  条件: (x : X) (y : Y) (f : C(X × Y, R))
  证明: (rfl)
-/
lemma contractSnd_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractSnd (dirac R y) f x = f (x, y) :=
  (rfl)

section LocallyCompact

variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

/--
Definition of `contractSndCLM` / `contractSndCLM` 的定义

English:
definition contractSndCLM
  signature: : D(Y, R) ->ₗ[R] C(X × Y, R) ->L[R] C(X, R) where
  body: ⟨contractSnd ν, by
    refine continuous_of_continuous_uncurry _ (ν.continuous.comp ?_)
    apply continuous_of_continuous_uncurry
    rw [← (Homeomorph.prodAssoc C(X × Y]; rw [R) X Y).symm.comp_continuous_iff']
    exact ContinuousEval.continuous_eval⟩
map_add' _ _ := ContinuousLinearMap.coe_inject

中文:
定义 contractSndCLM
  签名: : D(Y, R) ->ₗ[R] C(X × Y, R) ->L[R] C(X, R) where
  定义体: ⟨contractSnd ν, by
    refine continuous_of_continuous_uncurry _ (ν.continuous.comp ?_)
    apply continuous_of_continuous_uncurry
    rw [← (Homeomorph.prodAssoc C(X × Y]; rw [R) X Y).symm.comp_continuous_iff']
    exact ContinuousEval.continuous_eval⟩
map_add' _ _ := ContinuousLinearMap.coe_inject

Depends on / 依赖: ContinuousEval, ContinuousEval.continuous_eval, ContinuousLinearMap, ContinuousLinearMap.coe_injective.eq_iff.mp, Homeomorph, Homeomorph.prodAssoc, coe_injective, comp_continuous_iff, continuous, continuous.comp, continuous_eval, continuous_of_continuous_uncurry, contractSnd, contractSnd.map_add, contractSnd.map_smul, eq_iff, map_add, map_smul, prodAssoc, symm.comp_continuous_iff
-/
def contractSndCLM : D(Y, R) ->ₗ[R] C(X × Y, R) ->L[R] C(X, R) where
  toFun ν := ⟨contractSnd ν, by
    refine continuous_of_continuous_uncurry _ (ν.continuous.comp ?_)
    apply continuous_of_continuous_uncurry
    rw [← (Homeomorph.prodAssoc C(X × Y]; rw [R) X Y).symm.comp_continuous_iff']
    exact ContinuousEval.continuous_eval⟩
map_add' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp contractSnd.map_add _ _
map_smul' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp contractSnd.map_smul _ _

/--
Definition of `contractFstCLM` / `contractFstCLM` 的定义

English:
definition contractFstCLM
  signature: : D(X, R) ->ₗ[R] C(X × Y, R) ->L[R] C(Y, R)
  body: ((ContinuousMap.prodSwap.compCLM R R).lcomp _).comp contractSndCLM

中文:
定义 contractFstCLM
  签名: : D(X, R) ->ₗ[R] C(X × Y, R) ->L[R] C(Y, R)
  定义体: ((ContinuousMap.prodSwap.compCLM R R).lcomp _).comp contractSndCLM

Depends on / 依赖: ContinuousMap, ContinuousMap.prodSwap.compCLM, compCLM, contractSndCLM, prodSwap
-/
def contractFstCLM : D(X, R) ->ₗ[R] C(X × Y, R) ->L[R] C(Y, R) :=
  ((ContinuousMap.prodSwap.compCLM R R).lcomp _).comp contractSndCLM

/--
Definition of `prodMk` / `prodMk` 的定义

English:
definition prodMk
  signature: : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R)
  body: (ContinuousLinearMap.llcomp _ _ _ R).comp contractFstCLM

中文:
定义 prodMk
  签名: : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R)
  定义体: (ContinuousLinearMap.llcomp _ _ _ R).comp contractFstCLM

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.llcomp, contractFstCLM, llcomp
-/
def prodMk : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R) :=
  (ContinuousLinearMap.llcomp _ _ _ R).comp contractFstCLM

/--
lemma `prodMk_apply` / 引理 `prodMk_apply`

English:
lemma prodMk_apply
  given: (f : C(X × Y, R))
  proof: (rfl)

中文:
引理 prodMk_apply
  条件: (f : C(X × Y, R))
  证明: (rfl)
-/
@[simp] lemma prodMk_apply (f : C(X × Y, R)) :
  prodMk μ ν f = ν (μ.contractFst f) := (rfl)

/--
lemma `prodMk_prod_apply` / 引理 `prodMk_prod_apply`

English:
lemma prodMk_prod_apply
  given: (f : C(X, R)) (g : C(Y, R))
  proof: by
  simp only [← smul_eq_mul, prodMk_apply, ← map_smul]
  congr 1 with y
  simp_rw [contractFst_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm (μ f) (g y),
    ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (g y) (f x)]
  rfl

中文:
引理 prodMk_prod_apply
  条件: (f : C(X, R)) (g : C(Y, R))
  证明: by
  simp only [← smul_eq_mul, prodMk_apply, ← map_smul]
  congr 1 with y
  simp_rw [contractFst_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm (μ f) (g y),
    ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (g y) (f x)]
  rfl

Depends on / 依赖: ContinuousMap, ContinuousMap.smul_apply, contractFst_apply, map_smul, mul_comm, prodMk_apply, simp_rw, smul_apply, smul_eq_mul
-/
lemma prodMk_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [← smul_eq_mul, prodMk_apply, ← map_smul]
  congr 1 with y
  simp_rw [contractFst_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm (μ f) (g y),
    ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (g y) (f x)]
  rfl

/--
Definition of `prodMk'` / `prodMk'` 的定义

English:
definition prodMk'
  signature: : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R)
  body: ((ContinuousLinearMap.llcomp R _ _ R).comp contractSndCLM).flip

@[simp]

中文:
定义 prodMk'
  签名: : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R)
  定义体: ((ContinuousLinearMap.llcomp R _ _ R).comp contractSndCLM).flip

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.llcomp, contractSndCLM, llcomp
-/
def prodMk' : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R) :=
  ((ContinuousLinearMap.llcomp R _ _ R).comp contractSndCLM).flip

@[simp]
/--
lemma `prodMk'_apply` / 引理 `prodMk'_apply`

English:
lemma prodMk'_apply
  given: (f : C(X × Y, R))
  statement: (μ.prodMk' ν) f = μ (ν.contractSnd f)
  proof: (rfl)

中文:
引理 prodMk'_apply
  条件: (f : C(X × Y, R))
  结论: (μ.prodMk' ν) f = μ (ν.contractSnd f)
  证明: (rfl)
-/
lemma prodMk'_apply (f : C(X × Y, R)) : (μ.prodMk' ν) f = μ (ν.contractSnd f) := (rfl)

/--
lemma `prodMk'_flip` / 引理 `prodMk'_flip`

English:
lemma prodMk'_flip
  given: (f : C(X × Y, R))
  proof: (rfl)

中文:
引理 prodMk'_flip
  条件: (f : C(X × Y, R))
  证明: (rfl)
-/
lemma prodMk'_flip (f : C(X × Y, R)) :
    (μ.prodMk' ν) f = (ν.prodMk μ) (f.comp ContinuousMap.prodSwap) := (rfl)

/--
lemma `prodMk'_prod_apply` / 引理 `prodMk'_prod_apply`

English:
lemma prodMk'_prod_apply
  given: (f : C(X, R)) (g : C(Y, R))
  proof: by
  simp only [prodMk'_apply, mul_comm (μ f) (ν g), ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (ν g) (f x), contractSnd_apply,
    ← smul_eq_mul, ← map_smul]
  rfl

中文:
引理 prodMk'_prod_apply
  条件: (f : C(X, R)) (g : C(Y, R))
  证明: by
  simp only [prodMk'_apply, mul_comm (μ f) (ν g), ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (ν g) (f x), contractSnd_apply,
    ← smul_eq_mul, ← map_smul]
  rfl
-/
lemma prodMk'_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk' μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [prodMk'_apply, mul_comm (μ f) (ν g), ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (ν g) (f x), contractSnd_apply,
    ← smul_eq_mul, ← map_smul]
  rfl

end LocallyCompact

section Profinite

variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y] [TotallyDisconnectedSpace X]
  [T0Space R]

/--
lemma `prodMk_eq_prodMk'` / 引理 `prodMk_eq_prodMk'`

English:
lemma prodMk_eq_prodMk'
  statement: prodMk μ ν = prodMk' μ ν
  proof: by
  apply DFunLike.coe_injective
  apply denseRange_tensorHom.equalizer (by fun_prop) (by fun_prop) (funext fun h => ?_)
  induction h with
  | zero => simp
  | add => grind
  | tmul f g => simp [prodMul_def, prodMk_prod_apply μ, prodMk'_prod_apply μ]

中文:
引理 prodMk_eq_prodMk'
  结论: prodMk μ ν = prodMk' μ ν
  证明: by
  apply DFunLike.coe_injective
  apply denseRange_tensorHom.equalizer (by fun_prop) (by fun_prop) (funext fun h => ?_)
  induction h with
  | zero => simp
  | add => grind
  | tmul f g => simp [prodMul_def, prodMk_prod_apply μ, prodMk'_prod_apply μ]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, _prod_apply, coe_injective, denseRange_tensorHom, denseRange_tensorHom.equalizer, equalizer, fun_prop, prodMk, prodMk_prod_apply, prodMul_def
-/
lemma prodMk_eq_prodMk' : prodMk μ ν = prodMk' μ ν := by
  apply DFunLike.coe_injective
  apply denseRange_tensorHom.equalizer (by fun_prop) (by fun_prop) (funext fun h => ?_)
  induction h with
  | zero => simp
  | add => grind
  | tmul f g => simp [prodMul_def, prodMk_prod_apply μ, prodMk'_prod_apply μ]

end Profinite

end Prod

end ContinuousSMul

end AbstractMeasure

end
