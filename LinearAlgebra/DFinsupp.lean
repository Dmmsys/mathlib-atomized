/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Submonoid
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `Mathlib/Data/DFinsupp/Module.lean`.

In this file we define `LinearMap` versions of various maps:

* `DFinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `DFinsupp.mk` as a linear map;

* `DFinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `DFinsupp.lsum`: `DFinsupp.sum` or `DFinsupp.liftAddHom` as a `LinearMap`.

## Implementation notes

This file should try to mirror `LinearAlgebra.Finsupp` where possible. The API of `Finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

open Module

variable {ι ι' : Type*} {R : Type*} {S : Type*} {M : ι -> Type*} {N : Type*}

namespace DFinsupp

variable [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
variable [AddCommMonoid N] [Module R N]

section DecidableEq
variable [DecidableEq ι]

/--
Definition of `lmk` / `lmk` 的定义

English:
definition lmk
  signature: (s : Finset ι)
  body: mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x

中文:
定义 lmk
  签名: (s : 有限集 ι)
  定义体: mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x
-/
def lmk (s : Finset ι) : (forall i : (↑s : Set ι), M i) ->ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x

/--
Definition of `lsingle` / `lsingle` 的定义

English:
definition lsingle
  signature: (i)
  body: { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }

中文:
定义 lsingle
  签名: (i)
  定义体: { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }

Depends on / 依赖: DFinsupp, DFinsupp.singleAddHom, map_smul, single, singleAddHom, single_smul
-/
def lsingle (i) : M i ->ₗ[R] Π₀ i, M i :=
  { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }

/--
theorem `lhom_ext` / 定理 `lhom_ext`

English:
theorem lhom_ext
  given: ⦃φ ψ
  statement: (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i x, φ (single i x) = ψ (single i x)) : φ = ψ
  proof: LinearMap.toAddMonoidHom_injective addHom_ext h

中文:
定理 lhom_ext
  条件: ⦃φ ψ
  结论: (Π₀ i, M i) ->ₗ[R] N⦄ (h : 对任意 i x, φ (single i x) = ψ (single i x)) : φ = ψ
  证明: LinearMap.toAddMonoidHom_injective addHom_ext h

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_injective, addHom_ext, toAddMonoidHom_injective
-/
theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
LinearMap.toAddMonoidHom_injective addHom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After applying this lemma, if `M = R` then it suffices to verify
`φ (single a 1) = ψ (single a 1)`. -/
@[ext 1100]
/--
theorem `lhom_ext'` / 定理 `lhom_ext'`

English:
theorem lhom_ext'
  given: ⦃φ ψ
  statement: (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
  proof: lhom_ext fun i => LinearMap.congr_fun (h i)

中文:
定理 lhom_ext'
  条件: ⦃φ ψ
  结论: (Π₀ i, M i) ->ₗ[R] N⦄ (h : 对任意 i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
  证明: lhom_ext fun i => LinearMap.congr_fun (h i)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lhom_ext
-/
theorem lhom_ext' ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
    φ = ψ :=
  lhom_ext fun i => LinearMap.congr_fun (h i)

/--
theorem `lmk_apply` / 定理 `lmk_apply`

English:
theorem lmk_apply
  given: (s : Finset ι) (x)
  statement: (lmk s : _ ->ₗ[R] Π₀ i, M i) x = mk s x
  proof: rfl

@[simp]

中文:
定理 lmk_apply
  条件: (s : 有限集 ι) (x)
  结论: (lmk s : _ ->ₗ[R] Π₀ i, M i) x = mk s x
  证明: rfl

@[simp]
-/
theorem lmk_apply (s : Finset ι) (x) : (lmk s : _ ->ₗ[R] Π₀ i, M i) x = mk s x :=
  rfl

@[simp]
/--
theorem `lsingle_apply` / 定理 `lsingle_apply`

English:
theorem lsingle_apply
  given: (i : ι) (x : M i)
  statement: (lsingle i : (M i) ->ₗ[R] _) x = single i x
  proof: rfl

中文:
定理 lsingle_apply
  条件: (i : ι) (x : M i)
  结论: (lsingle i : (M i) ->ₗ[R] _) x = single i x
  证明: rfl
-/
theorem lsingle_apply (i : ι) (x : M i) : (lsingle i : (M i) ->ₗ[R] _) x = single i x :=
  rfl

end DecidableEq

/--
Definition of `lapply` / `lapply` 的定义

English:
definition lapply
  signature: (i : ι)
  body: f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i

@[simp]

中文:
定义 lapply
  签名: (i : ι)
  定义体: f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i

@[simp]
-/
def lapply (i : ι) : (Π₀ i, M i) ->ₗ[R] M i where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i

@[simp]
/--
theorem `lapply_apply` / 定理 `lapply_apply`

English:
theorem lapply_apply
  given: (i : ι) (f : Π₀ i, M i)
  statement: (lapply i : (Π₀ i, M i) ->ₗ[R] _) f = f i
  proof: rfl

中文:
定理 lapply_apply
  条件: (i : ι) (f : Π₀ i, M i)
  结论: (lapply i : (Π₀ i, M i) ->ₗ[R] _) f = f i
  证明: rfl
-/
theorem lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : (Π₀ i, M i) ->ₗ[R] _) f = f i :=
  rfl

/--
theorem `injective_pi_lapply` / 定理 `injective_pi_lapply`

English:
theorem injective_pi_lapply
  statement: Function.Injective (LinearMap.pi (R := R) <| lapply (M := M))
  proof: fun _ _ h => ext fun _ => congr_fun h _

@[simp]

中文:
定理 injective_pi_lapply
  结论: 函数.单射 (线性映射.pi (R := R) <| lapply (M := M))
  证明: fun _ _ h => ext fun _ => congr_fun h _

@[simp]

Depends on / 依赖: lapply
-/
theorem injective_pi_lapply : Function.Injective (LinearMap.pi (R := R) <| lapply (M := M)) :=
  fun _ _ h => ext fun _ => congr_fun h _

@[simp]
/--
theorem `lapply_comp_lsingle_same` / 定理 `lapply_comp_lsingle_same`

English:
theorem lapply_comp_lsingle_same
  given: [DecidableEq ι] (i : ι)
  proof: by ext; simp

@[simp]

中文:
定理 lapply_comp_lsingle_same
  条件: [DecidableEq ι] (i : ι)
  证明: by ext; simp

@[simp]
-/
theorem lapply_comp_lsingle_same [DecidableEq ι] (i : ι) :
    lapply i ∘ₗ lsingle i = (.id : M i ->ₗ[R] M i) := by ext; simp

@[simp]
/--
theorem `lapply_comp_lsingle_of_ne` / 定理 `lapply_comp_lsingle_of_ne`

English:
theorem lapply_comp_lsingle_of_ne
  given: [DecidableEq ι] (i i' : ι) (h : i != i')
  proof: by ext; simp [h.symm]

中文:
定理 lapply_comp_lsingle_of_ne
  条件: [DecidableEq ι] (i i' : ι) (h : i != i')
  证明: by ext; simp [h.symm]

Depends on / 依赖: h.symm
-/
theorem lapply_comp_lsingle_of_ne [DecidableEq ι] (i i' : ι) (h : i != i') :
    lapply i ∘ₗ lsingle i' = (0 : M i' ->ₗ[R] M i) := by ext; simp [h.symm]

section Lsum

variable (S)
variable [DecidableEq ι]

instance {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
    {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] :
    EquivLike (LinearEquiv σ M M₂) M M₂ :=
  inferInstance

/-- `DFinsupp.equivCongrLeft` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.domLCongr`. -/
@[simps! apply]
/--
Definition of `domLCongr` / `domLCongr` 的定义

English:
definition domLCongr
  signature: (e : ι ≃ ι')
  body: DFinsupp.equivCongrLeft e
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

中文:
定义 domLCongr
  签名: (e : ι ≃ ι')
  定义体: DFinsupp.equivCongrLeft e
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

Depends on / 依赖: DFinsupp, DFinsupp.equivCongrLeft, equivCongrLeft
-/
def domLCongr (e : ι ≃ ι') : (Π₀ i, M i) ≃ₗ[R] (Π₀ i, M (e.symm i)) where
  __ := DFinsupp.equivCongrLeft e
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `DFinsupp.sigmaCurryEquiv` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.curryLinearEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `sigmaCurryLEquiv` / `sigmaCurryLEquiv` 的定义

English:
definition sigmaCurryLEquiv
  signature: {α : ι -> Type*} {M : (i : ι) -> α i -> Type*}
  body: DFinsupp.sigmaCurryEquiv
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

中文:
定义 sigmaCurryLEquiv
  签名: {α : ι -> 类型} {M : (i : ι) -> α i -> 类型}
  定义体: DFinsupp.sigmaCurryEquiv
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurryEquiv, sigmaCurryEquiv
-/
def sigmaCurryLEquiv {α : ι -> Type*} {M : (i : ι) -> α i -> Type*}
    [Π i j, AddCommMonoid (M i j)] [Π i j, Module R (M i j)] :
    (Π₀ (i : (x : ι) × α x), M i.fst i.snd) ≃ₗ[R] Π₀ (i : ι) (j : α i), M i j where
  __ := DFinsupp.sigmaCurryEquiv
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `DFinsupp.equivFunOnFintype` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.linearEquivFunOnFintype`. -/
@[simps! apply symm_apply]
/--
Definition of `linearEquivFunOnFintype` / `linearEquivFunOnFintype` 的定义

English:
definition linearEquivFunOnFintype
  signature: [Fintype ι]
  body: equivFunOnFintype
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

中文:
定义 linearEquivFunOnFintype
  签名: [有限类型 ι]
  定义体: equivFunOnFintype
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

Depends on / 依赖: equivFunOnFintype
-/
def linearEquivFunOnFintype [Fintype ι] : (Π₀ i, M i) ≃ₗ[R] (Π i, M i) where
  __ := equivFunOnFintype
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `DFinsupp` version of `Finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
/--
Definition of `lsum` / `lsum` 的定义

English:
definition lsum
  signature: [Semiring S] [Module S N] [SMulCommClass R S N]
  body: { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (DFinsupp.liftAddHom fun (i : ι) => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply DFinsupp.induction f
        · rw [smul_zero, map_zero, smul_zero]
        · intro a b f _ _ hf
        

中文:
定义 lsum
  签名: [半环 S] [模 S N] [标量交换类 R S N]
  定义体: { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (DFinsupp.liftAddHom fun (i : ι) => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply DFinsupp.induction f
        · rw [smul_zero, map_zero, smul_zero]
        · intro a b f _ _ hf
        

Depends on / 依赖: DFinsupp, DFinsupp.induction, DFinsupp.liftAddHom, F.comp, LinearMap, LinearMap.toAddMonoidHom_coe, invFun, left_inv, liftAddHom, lsingle, map_add, map_smul, map_zero, right_inv, single_smul, smul_add, smul_zero, sumAddHom, sumAddHom_single, toAddMonoidHom
-/
def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (forall i, M i ->ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) ->ₗ[R] N where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (DFinsupp.liftAddHom fun (i : ι) => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply DFinsupp.induction f
        · rw [smul_zero, map_zero, smul_zero]
        · intro a b f _ _ hf
          rw [smul_add]; rw [map_add]; rw [map_add]; rw [smul_add]; rw [hf]; rw [← single_smul]; rw [sumAddHom_single]; rw [sumAddHom_single]; rw [LinearMap.toAddMonoidHom_coe]; rw [map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext
    simp
  right_inv F := by
    refine DFinsupp.lhom_ext' (fun i => ?_)
    ext
    simp
  map_add' F G := by
    refine DFinsupp.lhom_ext' (fun i => ?_)
    ext
    simp
  map_smul' c F := by
    refine DFinsupp.lhom_ext' (fun i => ?_)
    ext
    simp

/--
theorem `lsum_single` / 定理 `lsum_single`

English:
theorem lsum_single
  statement: [Semiring S] [Module S N] [SMulCommClass R S N] (F : forall i, M i ->ₗ[R] N) (i)
  proof: by
  simp

中文:
定理 lsum_single
  结论: [半环 S] [模 S N] [标量交换类 R S N] (F : 对任意 i, M i ->ₗ[R] N) (i)
  证明: by
  simp
-/
theorem lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : forall i, M i ->ₗ[R] N) (i)
    (x : M i) : lsum S F (single i x) = F i x := by
  simp

/--
theorem `lsum_lsingle` / 定理 `lsum_lsingle`

English:
theorem lsum_lsingle
  given: [Semiring S] [forall i, Module S (M i)] [forall i, SMulCommClass R S (M i)]
  proof: lhom_ext (lsum_single _ _)

中文:
定理 lsum_lsingle
  条件: [半环 S] [对任意 i, 模 S (M i)] [对任意 i, 标量交换类 R S (M i)]
  证明: lhom_ext (lsum_single _ _)
-/
theorem lsum_lsingle [Semiring S] [forall i, Module S (M i)] [forall i, SMulCommClass R S (M i)] :
    lsum S (lsingle (R := R) (M := M)) = .id :=
  lhom_ext (lsum_single _ _)

/--
theorem `iSup_range_lsingle` / 定理 `iSup_range_lsingle`

English:
theorem iSup_range_lsingle
  statement: ⨆ i, LinearMap.range (lsingle (R := R) (M := M) i) = ⊤
  proof: top_le_iff.mp fun m _ => by
    rw [← LinearMap.id_apply (R := R) m]; rw [← lsum_lsingle Nat]
    exact dfinsuppSumAddHom_mem _ _ _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩

中文:
定理 iSup_range_lsingle
  结论: ⨆ i, 线性映射.range (lsingle (R := R) (M := M) i) = ⊤
  证明: top_le_iff.mp fun m _ => by
    rw [← LinearMap.id_apply (R := R) m]; rw [← lsum_lsingle Nat]
    exact dfinsuppSumAddHom_mem _ _ _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
-/
theorem iSup_range_lsingle : ⨆ i, LinearMap.range (lsingle (R := R) (M := M) i) = ⊤ :=
  top_le_iff.mp fun m _ => by
    rw [← LinearMap.id_apply (R := R) m]; rw [← lsum_lsingle Nat]
    exact dfinsuppSumAddHom_mem _ _ _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩

end Lsum

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/

section mapRange
variable {β β₁ β₂ : ι -> Type*}

section AddCommMonoid
variable [forall i, AddCommMonoid (β i)] [forall i, AddCommMonoid (β₁ i)] [forall i, AddCommMonoid (β₂ i)]
variable [forall i, Module R (β i)] [forall i, Module R (β₁ i)] [forall i, Module R (β₂ i)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mker_mapRangeAddMonoidHom` / 引理 `mker_mapRangeAddMonoidHom`

English:
lemma mker_mapRangeAddMonoidHom
  given: (f : forall i, β₁ i ->+ β₂ i)
  proof: by
  ext
  simp [AddSubmonoid.pi, DFinsupp.ext_iff]

中文:
引理 mker_mapRangeAddMonoidHom
  条件: (f : 对任意 i, β₁ i ->+ β₂ i)
  证明: by
  ext
  simp [AddSubmonoid.pi, DFinsupp.ext_iff]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.pi, DFinsupp, DFinsupp.ext_iff, ext_iff
-/
lemma mker_mapRangeAddMonoidHom (f : forall i, β₁ i ->+ β₂ i) :
    AddMonoidHom.mker (mapRange.addMonoidHom f) =
      (AddSubmonoid.pi Set.univ (fun i => AddMonoidHom.mker (f i))).comap coeFnAddMonoidHom := by
  ext
  simp [AddSubmonoid.pi, DFinsupp.ext_iff]

/--
lemma `mrange_mapRangeAddMonoidHom` / 引理 `mrange_mapRangeAddMonoidHom`

English:
lemma mrange_mapRangeAddMonoidHom
  given: (f : forall i, β₁ i ->+ β₂ i)
  proof: by
  classical
  ext x
  simp only [AddSubmonoid.mem_comap, coeFnAddMonoidHom_apply]
  refine ⟨fun ⟨y, hy⟩ i hi => ?_, fun h => ?_⟩
  · simp [← hy]
  · choose g hg using fun i => h i (Set.mem_univ _)
    use DFinsupp.mk x.support (g ·)
    ext i
    simp only [Finset.coe_sort_coe, mapRange.addMonoid

中文:
引理 mrange_mapRangeAddMonoidHom
  条件: (f : 对任意 i, β₁ i ->+ β₂ i)
  证明: by
  classical
  ext x
  simp only [AddSubmonoid.mem_comap, coeFnAddMonoidHom_apply]
  refine ⟨fun ⟨y, hy⟩ i hi => ?_, fun h => ?_⟩
  · simp [← hy]
  · choose g hg using fun i => h i (Set.mem_univ _)
    use DFinsupp.mk x.support (g ·)
    ext i
    simp only [Finset.coe_sort_coe, mapRange.addMonoid

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_comap, DFinsupp, DFinsupp.mk, DFinsupp.notMem_support_iff.mp, Finset, Finset.coe_sort_coe, Set.mem_univ, addMonoidHom_apply, classical, coeFnAddMonoidHom_apply, coe_sort_coe, mapRange, mapRange.addMonoidHom_apply, mapRange_apply, map_zero, mem_comap, mem_univ, mk_of_mem, mk_of_notMem
-/
lemma mrange_mapRangeAddMonoidHom (f : forall i, β₁ i ->+ β₂ i) :
    AddMonoidHom.mrange (mapRange.addMonoidHom f) =
      (AddSubmonoid.pi Set.univ (fun i => AddMonoidHom.mrange (f i))).comap coeFnAddMonoidHom := by
  classical
  ext x
  simp only [AddSubmonoid.mem_comap, coeFnAddMonoidHom_apply]
  refine ⟨fun ⟨y, hy⟩ i hi => ?_, fun h => ?_⟩
  · simp [← hy]
  · choose g hg using fun i => h i (Set.mem_univ _)
    use DFinsupp.mk x.support (g ·)
    ext i
    simp only [Finset.coe_sort_coe, mapRange.addMonoidHom_apply, mapRange_apply]
    by_cases mem : i in x.support
    · rw [mk_of_mem mem, hg]
    · rw [DFinsupp.notMem_support_iff.mp mem, mk_of_notMem mem, map_zero]

/--
theorem `mapRange_smul` / 定理 `mapRange_smul`

English:
theorem mapRange_smul
  statement: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (r : R)
  proof: by
  ext
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']

中文:
定理 mapRange_smul
  结论: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0) (r : R)
  证明: by
  ext
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']

Depends on / 依赖: Pi.smul_apply, coe_smul, mapRange_apply, smul_apply
-/
theorem mapRange_smul (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (r : R)
    (hf' : forall i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) :
    mapRange f hf (r • g) = r • mapRange f hf g := by
  ext
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']

/-- `DFinsupp.mapRange` as a `LinearMap`. -/
@[simps! apply]
/--
Definition of `mapRange.linearMap` / `mapRange.linearMap` 的定义

English:
definition mapRange.linearMap
  signature: (f : forall i, β₁ i ->ₗ[R] β₂ i)
  body: { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }

中文:
定义 mapRange.linearMap
  签名: (f : 对任意 i, β₁ i ->ₗ[R] β₂ i)
  定义体: { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }

Depends on / 依赖: addMonoidHom, mapRange, mapRange.addMonoidHom, mapRange_smul, map_smul, map_zero, toAddMonoidHom
-/
def mapRange.linearMap (f : forall i, β₁ i ->ₗ[R] β₂ i) : (Π₀ i, β₁ i) ->ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mapRange.linearMap_id` / 定理 `mapRange.linearMap_id`

English:
theorem mapRange.linearMap_id
  proof: by
  ext
  simp [linearMap]

中文:
定理 mapRange.linearMap_id
  证明: by
  ext
  simp [linearMap]

Depends on / 依赖: linearMap
-/
theorem mapRange.linearMap_id :
    (mapRange.linearMap fun i => (LinearMap.id : β₂ i ->ₗ[R] _)) = LinearMap.id := by
  ext
  simp [linearMap]

/--
theorem `mapRange.linearMap_comp` / 定理 `mapRange.linearMap_comp`

English:
theorem mapRange.linearMap_comp
  given: (f : forall i, β₁ i ->ₗ[R] β₂ i) (f₂ : forall i, β i ->ₗ[R] β₁ i)
  proof: LinearMap.ext mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)

中文:
定理 mapRange.linearMap_comp
  条件: (f : 对任意 i, β₁ i ->ₗ[R] β₂ i) (f₂ : 对任意 i, β i ->ₗ[R] β₁ i)
  证明: LinearMap.ext mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)

Depends on / 依赖: LinearMap, LinearMap.ext, mapRange_comp, map_zero
-/
theorem mapRange.linearMap_comp (f : forall i, β₁ i ->ₗ[R] β₂ i) (f₂ : forall i, β i ->ₗ[R] β₁ i) :
    (mapRange.linearMap fun i => (f i).comp (f₂ i)) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
LinearMap.ext mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)

/--
theorem `sum_mapRange_index.linearMap` / 定理 `sum_mapRange_index.linearMap`

English:
theorem sum_mapRange_index.linearMap
  statement: [DecidableEq ι] {f : forall i, β₁ i ->ₗ[R] β₂ i}
  proof: by
  classical simpa [DFinsupp.sumAddHom_apply] using! sum_mapRange_index fun i => by simp

中文:
定理 sum_mapRange_index.linearMap
  结论: [DecidableEq ι] {f : 对任意 i, β₁ i ->ₗ[R] β₂ i}
  证明: by
  classical simpa [DFinsupp.sumAddHom_apply] using! sum_mapRange_index fun i => by simp

Depends on / 依赖: DFinsupp, DFinsupp.sumAddHom_apply, classical, sumAddHom_apply, sum_mapRange_index
-/
theorem sum_mapRange_index.linearMap [DecidableEq ι] {f : forall i, β₁ i ->ₗ[R] β₂ i}
    {h : forall i, β₂ i ->ₗ[R] N} {l : Π₀ i, β₁ i} :
    DFinsupp.lsum Nat h (mapRange.linearMap f l) = DFinsupp.lsum Nat (fun i => (h i).comp (f i)) l := by
  classical simpa [DFinsupp.sumAddHom_apply] using! sum_mapRange_index fun i => by simp

/--
lemma `ker_mapRangeLinearMap` / 引理 `ker_mapRangeLinearMap`

English:
lemma ker_mapRangeLinearMap
  given: (f : forall i, β₁ i ->ₗ[R] β₂ i)
  proof: Submodule.toAddSubmonoid_injective mker_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

中文:
引理 ker_mapRangeLinearMap
  条件: (f : 对任意 i, β₁ i ->ₗ[R] β₂ i)
  证明: Submodule.toAddSubmonoid_injective mker_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

Depends on / 依赖: Submodule, Submodule.toAddSubmonoid_injective, mker_mapRangeAddMonoidHom, toAddMonoidHom, toAddSubmonoid_injective
-/
lemma ker_mapRangeLinearMap (f : forall i, β₁ i ->ₗ[R] β₂ i) :
    LinearMap.ker (mapRange.linearMap f) =
      (Submodule.pi Set.univ (fun i => LinearMap.ker (f i))).comap (coeFnLinearMap R) :=
Submodule.toAddSubmonoid_injective mker_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

/--
lemma `range_mapRangeLinearMap` / 引理 `range_mapRangeLinearMap`

English:
lemma range_mapRangeLinearMap
  given: (f : forall i, β₁ i ->ₗ[R] β₂ i)
  proof: Submodule.toAddSubmonoid_injective mrange_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

中文:
引理 range_mapRangeLinearMap
  条件: (f : 对任意 i, β₁ i ->ₗ[R] β₂ i)
  证明: Submodule.toAddSubmonoid_injective mrange_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

Depends on / 依赖: Submodule, Submodule.toAddSubmonoid_injective, mrange_mapRangeAddMonoidHom, toAddMonoidHom, toAddSubmonoid_injective
-/
lemma range_mapRangeLinearMap (f : forall i, β₁ i ->ₗ[R] β₂ i) :
    LinearMap.range (mapRange.linearMap f) =
      (Submodule.pi Set.univ (LinearMap.range <| f ·)).comap (coeFnLinearMap R) :=
Submodule.toAddSubmonoid_injective mrange_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

/-- `DFinsupp.mapRange.linearMap` as a `LinearEquiv`. -/
@[simps apply]
/--
Definition of `mapRange.linearEquiv` / `mapRange.linearEquiv` 的定义

English:
definition mapRange.linearEquiv
  signature: (e : forall i, β₁ i ≃ₗ[R] β₂ i)
  body: { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }

@[simp]

中文:
定义 mapRange.linearEquiv
  签名: (e : 对任意 i, β₁ i ≃ₗ[R] β₂ i)
  定义体: { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }

@[simp]

Depends on / 依赖: addEquiv, invFun, linearMap, mapRange, mapRange.addEquiv, mapRange.linearMap, map_zero, symm.map_zero, toAddEquiv, toLinearMap
-/
def mapRange.linearEquiv (e : forall i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }

@[simp]
/--
theorem `mapRange.linearEquiv_refl` / 定理 `mapRange.linearEquiv_refl`

English:
theorem mapRange.linearEquiv_refl
  proof: LinearEquiv.ext mapRange_id

中文:
定理 mapRange.linearEquiv_refl
  证明: LinearEquiv.ext mapRange_id

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, mapRange_id
-/
theorem mapRange.linearEquiv_refl :
    (mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = LinearEquiv.refl _ _ :=
  LinearEquiv.ext mapRange_id

/--
theorem `mapRange.linearEquiv_trans` / 定理 `mapRange.linearEquiv_trans`

English:
theorem mapRange.linearEquiv_trans
  given: (f : forall i, β i ≃ₗ[R] β₁ i) (f₂ : forall i, β₁ i ≃ₗ[R] β₂ i)
  proof: LinearEquiv.ext mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)

@[simp]

中文:
定理 mapRange.linearEquiv_trans
  条件: (f : 对任意 i, β i ≃ₗ[R] β₁ i) (f₂ : 对任意 i, β₁ i ≃ₗ[R] β₂ i)
  证明: LinearEquiv.ext mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, mapRange_comp, map_zero
-/
theorem mapRange.linearEquiv_trans (f : forall i, β i ≃ₗ[R] β₁ i) (f₂ : forall i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
LinearEquiv.ext mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)

@[simp]
/--
theorem `mapRange.linearEquiv_symm` / 定理 `mapRange.linearEquiv_symm`

English:
theorem mapRange.linearEquiv_symm
  given: (e : forall i, β₁ i ≃ₗ[R] β₂ i)
  proof: rfl

中文:
定理 mapRange.linearEquiv_symm
  条件: (e : 对任意 i, β₁ i ≃ₗ[R] β₂ i)
  证明: rfl
-/
theorem mapRange.linearEquiv_symm (e : forall i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv e).symm = mapRange.linearEquiv fun i => (e i).symm :=
  rfl

end AddCommMonoid

section AddCommGroup

/--
lemma `ker_mapRangeAddMonoidHom` / 引理 `ker_mapRangeAddMonoidHom`

English:
lemma ker_mapRangeAddMonoidHom
  proof: AddSubgroup.toAddSubmonoid_injective mker_mapRangeAddMonoidHom f

中文:
引理 ker_mapRangeAddMonoidHom
  证明: AddSubgroup.toAddSubmonoid_injective mker_mapRangeAddMonoidHom f

Depends on / 依赖: AddSubgroup, AddSubgroup.toAddSubmonoid_injective, mker_mapRangeAddMonoidHom, toAddSubmonoid_injective
-/
lemma ker_mapRangeAddMonoidHom
    [forall i, AddCommGroup (β₁ i)] [forall i, AddCommMonoid (β₂ i)] (f : forall i, β₁ i ->+ β₂ i) :
    (mapRange.addMonoidHom f).ker =
      (AddSubgroup.pi Set.univ (f · |>.ker)).comap coeFnAddMonoidHom :=
AddSubgroup.toAddSubmonoid_injective mker_mapRangeAddMonoidHom f

/--
lemma `range_mapRangeAddMonoidHom` / 引理 `range_mapRangeAddMonoidHom`

English:
lemma range_mapRangeAddMonoidHom
  proof: AddSubgroup.toAddSubmonoid_injective mrange_mapRangeAddMonoidHom f

中文:
引理 range_mapRangeAddMonoidHom
  证明: AddSubgroup.toAddSubmonoid_injective mrange_mapRangeAddMonoidHom f

Depends on / 依赖: AddSubgroup, AddSubgroup.toAddSubmonoid_injective, mrange_mapRangeAddMonoidHom, toAddSubmonoid_injective
-/
lemma range_mapRangeAddMonoidHom
    [forall i, AddCommGroup (β₁ i)] [forall i, AddCommGroup (β₂ i)] (f : forall i, β₂ i ->+ β₁ i) :
    (mapRange.addMonoidHom f).range =
      (AddSubgroup.pi Set.univ (f · |>.range)).comap coeFnAddMonoidHom :=
AddSubgroup.toAddSubmonoid_injective mrange_mapRangeAddMonoidHom f

end AddCommGroup

end mapRange

section CoprodMap

variable [DecidableEq ι]

/--
Definition of `coprodMap` / `coprodMap` 的定义

English:
definition coprodMap
  signature: (f : forall i : ι, M i ->ₗ[R] N)
  body: (DFinsupp.lsum Nat fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f

中文:
定义 coprodMap
  签名: (f : 对任意 i : ι, M i ->ₗ[R] N)
  定义体: (DFinsupp.lsum Nat fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f

Depends on / 依赖: DFinsupp, DFinsupp.lsum, DFinsupp.mapRange.linearMap, LinearMap, LinearMap.id, linearMap, mapRange
-/
def coprodMap (f : forall i : ι, M i ->ₗ[R] N) : (Π₀ i, M i) ->ₗ[R] N :=
  (DFinsupp.lsum Nat fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f

/--
theorem `coprodMap_apply` / 定理 `coprodMap_apply`

English:
theorem coprodMap_apply
  given: [forall x : N, Decidable (x != 0)] (f : forall i : ι, M i ->ₗ[R] N) (x : Π₀ i, M i)
  proof: DFinsupp.sumAddHom_apply _ _

中文:
定理 coprodMap_apply
  条件: [对任意 x : N, 可判定 (x != 0)] (f : 对任意 i : ι, M i ->ₗ[R] N) (x : Π₀ i, M i)
  证明: DFinsupp.sumAddHom_apply _ _

Depends on / 依赖: DFinsupp, DFinsupp.sumAddHom_apply, sumAddHom_apply
-/
theorem coprodMap_apply [forall x : N, Decidable (x != 0)] (f : forall i : ι, M i ->ₗ[R] N) (x : Π₀ i, M i) :
    coprodMap f x =
      DFinsupp.sum (mapRange (fun i => f i) (fun _ => map_zero _) x) fun _ =>
        id :=
  DFinsupp.sumAddHom_apply _ _

/--
theorem `coprodMap_apply_single` / 定理 `coprodMap_apply_single`

English:
theorem coprodMap_apply_single
  given: (f : forall i : ι, M i ->ₗ[R] N) (i : ι) (x : M i)
  proof: by
  simp [coprodMap]

中文:
定理 coprodMap_apply_single
  条件: (f : 对任意 i : ι, M i ->ₗ[R] N) (i : ι) (x : M i)
  证明: by
  simp [coprodMap]

Depends on / 依赖: coprodMap
-/
theorem coprodMap_apply_single (f : forall i : ι, M i ->ₗ[R] N) (i : ι) (x : M i) :
    coprodMap f (single i x) = f i x := by
  simp [coprodMap]

end CoprodMap

end DFinsupp

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open DFinsupp

section DecidableEq

variable [DecidableEq ι]

/--
theorem `dfinsuppSum_mem` / 定理 `dfinsuppSum_mem`

English:
theorem dfinsuppSum_mem
  statement: {β : ι -> Type*} [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: _root_.dfinsuppSum_mem S f g h

中文:
定理 dfinsuppSum_mem
  结论: {β : ι -> 类型} [对任意 i, 零 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: _root_.dfinsuppSum_mem S f g h

Depends on / 依赖: _root_, _root_.dfinsuppSum_mem, dfinsuppSum_mem
-/
theorem dfinsuppSum_mem {β : ι -> Type*} [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    (S : Submodule R N) (f : Π₀ i, β i) (g : forall i, β i -> N) (h : forall c, f c != 0 -> g c (f c) in S) :
    f.sum g in S :=
  _root_.dfinsuppSum_mem S f g h

/--
theorem `dfinsuppSumAddHom_mem` / 定理 `dfinsuppSumAddHom_mem`

English:
theorem dfinsuppSumAddHom_mem
  statement: {β : ι -> Type*} [forall i, AddZeroClass (β i)] (S : Submodule R N)
  proof: _root_.dfinsuppSumAddHom_mem S f g h

中文:
定理 dfinsuppSumAddHom_mem
  结论: {β : ι -> 类型} [对任意 i, 加法零类 (β i)] (S : 子模 R N)
  证明: _root_.dfinsuppSumAddHom_mem S f g h

Depends on / 依赖: _root_, _root_.dfinsuppSumAddHom_mem, dfinsuppSumAddHom_mem
-/
theorem dfinsuppSumAddHom_mem {β : ι -> Type*} [forall i, AddZeroClass (β i)] (S : Submodule R N)
    (f : Π₀ i, β i) (g : forall i, β i ->+ N) (h : forall c, f c != 0 -> g c (f c) in S) :
    DFinsupp.sumAddHom g f in S :=
  _root_.dfinsuppSumAddHom_mem S f g h

/--
theorem `iSup_eq_range_dfinsupp_lsum` / 定理 `iSup_eq_range_dfinsupp_lsum`

English:
theorem iSup_eq_range_dfinsupp_lsum
  given: (p : ι -> Submodule R N)
  proof: by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    simp only [LinearMap.mem_range, lsum_apply_apply]
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i <= _) (v i).2

中文:
定理 iSup_eq_range_dfinsupp_lsum
  条件: (p : ι -> 子模 R N)
  证明: by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    simp only [LinearMap.mem_range, lsum_apply_apply]
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i <= _) (v i).2

Depends on / 依赖: DFinsupp, DFinsupp.single, DFinsupp.sumAddHom_single, LinearMap, LinearMap.mem_range, dfinsuppSumAddHom_mem, iSup_le, le_antisymm, le_iSup, lsum_apply_apply, mem_range, single, sumAddHom_single
-/
theorem iSup_eq_range_dfinsupp_lsum (p : ι -> Submodule R N) :
    iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    simp only [LinearMap.mem_range, lsum_apply_apply]
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i <= _) (v i).2

/--
theorem `biSup_eq_range_dfinsupp_lsum` / 定理 `biSup_eq_range_dfinsupp_lsum`

English:
theorem biSup_eq_range_dfinsupp_lsum
  given: (p : ι -> Prop) [DecidablePred p] (S : ι -> Submodule R N)
  proof: by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [LinearMap.comp_apply]; rw [filterLinearMap_apply]; rw [filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coe_subtype]
  · rintro x ⟨v, rfl⟩
   

中文:
定理 biSup_eq_range_dfinsupp_lsum
  条件: (p : ι -> 命题) [DecidablePred p] (S : ι -> 子模 R N)
  证明: by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [LinearMap.comp_apply]; rw [filterLinearMap_apply]; rw [filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coe_subtype]
  · rintro x ⟨v, rfl⟩
   

Depends on / 依赖: DFinsupp, DFinsupp.single, LinearMap, LinearMap.comp_apply, LinearMap.toAddMonoidHom_coe, coe_subtype, comp_apply, dfinsuppSumAddHom_mem, filterLinearMap_apply, filter_single_pos, le_antisymm, lsum_apply_apply, mem_iSup_of_mem, single, sumAddHom_single, toAddMonoidHom_coe
-/
theorem biSup_eq_range_dfinsupp_lsum (p : ι -> Prop) [DecidablePred p] (S : ι -> Submodule R N) :
    ⨆ (i) (_ : p i), S i =
      LinearMap.range
        (LinearMap.comp
          (DFinsupp.lsum Nat (fun i => (S i).subtype))
            (DFinsupp.filterLinearMap R _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [LinearMap.comp_apply]; rw [filterLinearMap_apply]; rw [filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coe_subtype]
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    refine mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]

/--
theorem `mem_iSup_iff_exists_dfinsupp` / 定理 `mem_iSup_iff_exists_dfinsupp`

English:
theorem mem_iSup_iff_exists_dfinsupp
  given: (p : ι -> Submodule R N) (x : N)
  proof: SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x

中文:
定理 mem_iSup_iff_存在_dfinsupp
  条件: (p : ι -> 子模 R N) (x : N)
  证明: SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, ext_iff, iSup_eq_range_dfinsupp_lsum
-/
theorem mem_iSup_iff_exists_dfinsupp (p : ι -> Submodule R N) (x : N) :
    x in iSup p ↔
      exists f : Π₀ i, p i, DFinsupp.lsum Nat (fun i => (p i).subtype) f = x :=
  SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x

/--
theorem `mem_iSup_iff_exists_dfinsupp'` / 定理 `mem_iSup_iff_exists_dfinsupp'`

English:
theorem mem_iSup_iff_exists_dfinsupp'
  statement: (p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)]
  proof: by
  rw [mem_iSup_iff_exists_dfinsupp]
  simp_rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coe_subtype]

中文:
定理 mem_iSup_iff_存在_dfinsupp'
  结论: (p : ι -> 子模 R N) [对任意 (i) (x : p i), 可判定 (x != 0)]
  证明: by
  rw [mem_iSup_iff_exists_dfinsupp]
  simp_rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coe_subtype]

Depends on / 依赖: DFinsupp, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, LinearMap, LinearMap.toAddMonoidHom_coe, coe_subtype, lsum_apply_apply, mem_iSup_iff_exists_dfinsupp, simp_rw, sumAddHom_apply, toAddMonoidHom_coe
-/
theorem mem_iSup_iff_exists_dfinsupp' (p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)]
    (x : N) : x in iSup p ↔ exists f : Π₀ i, p i, (f.sum fun _ xi => ↑xi) = x := by
  rw [mem_iSup_iff_exists_dfinsupp]
  simp_rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coe_subtype]

/--
theorem `mem_biSup_iff_exists_dfinsupp` / 定理 `mem_biSup_iff_exists_dfinsupp`

English:
theorem mem_biSup_iff_exists_dfinsupp
  statement: (p : ι -> Prop) [DecidablePred p] (S : ι -> Submodule R N)
  proof: SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x

中文:
定理 mem_biSup_iff_存在_dfinsupp
  结论: (p : ι -> 命题) [DecidablePred p] (S : ι -> 子模 R N)
  证明: SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, biSup_eq_range_dfinsupp_lsum, ext_iff
-/
theorem mem_biSup_iff_exists_dfinsupp (p : ι -> Prop) [DecidablePred p] (S : ι -> Submodule R N)
    (x : N) :
    (x in ⨆ (i) (_ : p i), S i) ↔
      exists f : Π₀ i, S i,
        DFinsupp.lsum Nat (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x

end DecidableEq

/--
lemma `mem_iSup_iff_exists_finsupp` / 引理 `mem_iSup_iff_exists_finsupp`

English:
lemma mem_iSup_iff_exists_finsupp
  given: (p : ι -> Submodule R N) (x : N)
  proof: by
  classical
  rw [mem_iSup_iff_exists_dfinsupp']
  refine ⟨fun ⟨f, hf⟩ => ⟨⟨f.support, fun i => (f i : N), by simp⟩, by simp, hf⟩, ?_⟩
  rintro ⟨f, hf, rfl⟩
  refine ⟨DFinsupp.mk f.support fun i => ⟨f i, hf i⟩, Finset.sum_congr ?_ fun i hi => ?_⟩
  · ext; simp [mk_eq_zero]
  · simp [Finsupp.mem_s

中文:
引理 mem_iSup_iff_存在_finsupp
  条件: (p : ι -> 子模 R N) (x : N)
  证明: by
  classical
  rw [mem_iSup_iff_exists_dfinsupp']
  refine ⟨fun ⟨f, hf⟩ => ⟨⟨f.support, fun i => (f i : N), by simp⟩, by simp, hf⟩, ?_⟩
  rintro ⟨f, hf, rfl⟩
  refine ⟨DFinsupp.mk f.support fun i => ⟨f i, hf i⟩, Finset.sum_congr ?_ fun i hi => ?_⟩
  · ext; simp [mk_eq_zero]
  · simp [Finsupp.mem_s

Depends on / 依赖: DFinsupp, DFinsupp.mk, Finset, Finset.sum_congr, Finsupp, Finsupp.mem_support_iff.mp, classical, f.support, mem_iSup_iff_exists_dfinsupp, mem_support_iff, mk_eq_zero, sum_congr, support
-/
lemma mem_iSup_iff_exists_finsupp (p : ι -> Submodule R N) (x : N) :
    x in iSup p ↔ exists (f : ι ->₀ N), (forall i, f i in p i) ∧ (f.sum fun _i xi => xi) = x := by
  classical
  rw [mem_iSup_iff_exists_dfinsupp']
  refine ⟨fun ⟨f, hf⟩ => ⟨⟨f.support, fun i => (f i : N), by simp⟩, by simp, hf⟩, ?_⟩
  rintro ⟨f, hf, rfl⟩
  refine ⟨DFinsupp.mk f.support fun i => ⟨f i, hf i⟩, Finset.sum_congr ?_ fun i hi => ?_⟩
  · ext; simp [mk_eq_zero]
  · simp [Finsupp.mem_support_iff.mp hi]

/--
theorem `mem_iSup_finset_iff_exists_sum` / 定理 `mem_iSup_finset_iff_exists_sum`

English:
theorem mem_iSup_finset_iff_exists_sum
  given: {s : Finset ι} (p : ι -> Submodule R N) (a : N)
  proof: by
  classical
    rw [Submodule.mem_iSup_iff_exists_dfinsupp']
    constructor <;> rintro ⟨μ, hμ⟩
    · use fun i => ⟨μ i, (iSup_const_le : _ <= p i) (coe_mem <| μ i)⟩
      rw [← hμ]
      symm
      apply Finset.sum_subset
      · intro x
        contrapose
        intro hx
        rw [mem_suppor

中文:
定理 mem_iSup_finset_iff_存在_sum
  条件: {s : 有限集 ι} (p : ι -> 子模 R N) (a : N)
  证明: by
  classical
    rw [Submodule.mem_iSup_iff_exists_dfinsupp']
    constructor <;> rintro ⟨μ, hμ⟩
    · use fun i => ⟨μ i, (iSup_const_le : _ <= p i) (coe_mem <| μ i)⟩
      rw [← hμ]
      symm
      apply Finset.sum_subset
      · intro x
        contrapose
        intro hx
        rw [mem_suppor

Depends on / 依赖: DFinsupp, DFinsupp.mk, Finset, Finset.sum_subset, Submodule, Submodule.mem_iSup_iff_exists_dfinsupp, classical, coe_mem, coe_zero, contrapose, iSup_const_le, iSup_neg, mem_bot, mem_iSup_iff_exists_dfinsupp, mem_support_iff, not_ne_iff, sum_subset, this.symm
-/
theorem mem_iSup_finset_iff_exists_sum {s : Finset ι} (p : ι -> Submodule R N) (a : N) :
    (a in ⨆ i in s, p i) ↔ exists μ : forall i, p i, (∑ i in s, (μ i : N)) = a := by
  classical
    rw [Submodule.mem_iSup_iff_exists_dfinsupp']
    constructor <;> rintro ⟨μ, hμ⟩
    · use fun i => ⟨μ i, (iSup_const_le : _ <= p i) (coe_mem <| μ i)⟩
      rw [← hμ]
      symm
      apply Finset.sum_subset
      · intro x
        contrapose
        intro hx
        rw [mem_support_iff]; rw [not_ne_iff]
        ext
        rw [coe_zero]; rw [← mem_bot R]
        suffices ⊥ = ⨆ (_ : x in s), p x from this.symm ▸ coe_mem (μ x)
        exact (iSup_neg hx).symm
      · intro x _ hx
        rw [mem_support_iff]; rw [not_ne_iff] at hx
        rw [hx]
        rfl
    · refine ⟨DFinsupp.mk s ?_, ?_⟩
      · rintro ⟨i, hi⟩
        refine ⟨μ i, ?_⟩
        rw [iSup_pos]
        · exact coe_mem _
        · exact hi
      simp only [DFinsupp.sum]
      rw [Finset.sum_subset support_mk_subset]; rw [← hμ]
      · exact Finset.sum_congr rfl fun x hx => by rw [mk_of_mem hx]
      · intro x _ hx
        rw [mem_support_iff]; rw [not_ne_iff] at hx
        rw [hx]
        rfl

end Submodule

open DFinsupp

section Semiring

variable [DecidableEq ι] [Semiring R] [AddCommMonoid N] [Module R N]

/--
theorem `iSupIndep_iff_forall_dfinsupp` / 定理 `iSupIndep_iff_forall_dfinsupp`

English:
theorem iSupIndep_iff_forall_dfinsupp
  given: (p : ι -> Submodule R N)
  proof: by
  simp_rw [iSupIndep_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  refine forall_congr' fun i => Subtype.forall'.trans ?_
  simp_rw [Submodule.coe_eq_zero]

中文:
定理 iSupIndep_iff_对任意_dfinsupp
  条件: (p : ι -> 子模 R N)
  证明: by
  simp_rw [iSupIndep_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  refine forall_congr' fun i => Subtype.forall'.trans ?_
  simp_rw [Submodule.coe_eq_zero]

Depends on / 依赖: Submodule, Submodule.coe_eq_zero, Submodule.disjoint_def, Submodule.mem_biSup_iff_exists_dfinsupp, Subtype, Subtype.forall, coe_eq_zero, disjoint_def, exists_imp, filter_ne_eq_erase, forall_congr, iSupIndep_def, mem_biSup_iff_exists_dfinsupp, simp_rw
-/
theorem iSupIndep_iff_forall_dfinsupp (p : ι -> Submodule R N) :
    iSupIndep p ↔
      forall (i) (x : p i) (v : Π₀ i : ι, ↥(p i)),
        lsum Nat (fun i => (p i).subtype) (erase i v) = x -> x = 0 := by
  simp_rw [iSupIndep_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  refine forall_congr' fun i => Subtype.forall'.trans ?_
  simp_rw [Submodule.coe_eq_zero]

/--
theorem `iSupIndep_of_dfinsupp_lsum_injective` / 定理 `iSupIndep_of_dfinsupp_lsum_injective`

English:
theorem iSupIndep_of_dfinsupp_lsum_injective
  statement: (p : ι -> Submodule R N)
  proof: by
  rw [iSupIndep_iff_forall_dfinsupp]
  intro i x v hv
  replace hv : lsum Nat (fun i => (p i).subtype) (erase i v) =
      lsum Nat (fun i => (p i).subtype) (single i x) := by
    simpa only [lsum_single] using! hv
  have := DFunLike.ext_iff.mp (h hv) i
  simpa [eq_comm] using! this

中文:
定理 iSupIndep_of_dfinsupp_lsum_injective
  结论: (p : ι -> 子模 R N)
  证明: by
  rw [iSupIndep_iff_forall_dfinsupp]
  intro i x v hv
  replace hv : lsum Nat (fun i => (p i).subtype) (erase i v) =
      lsum Nat (fun i => (p i).subtype) (single i x) := by
    simpa only [lsum_single] using! hv
  have := DFunLike.ext_iff.mp (h hv) i
  simpa [eq_comm] using! this

Depends on / 依赖: DFunLike, DFunLike.ext_iff.mp, eq_comm, ext_iff, iSupIndep_iff_forall_dfinsupp, lsum_single, replace, single, subtype
-/
theorem iSupIndep_of_dfinsupp_lsum_injective (p : ι -> Submodule R N)
    (h : Function.Injective (lsum Nat fun i => (p i).subtype)) :
    iSupIndep p := by
  rw [iSupIndep_iff_forall_dfinsupp]
  intro i x v hv
  replace hv : lsum Nat (fun i => (p i).subtype) (erase i v) =
      lsum Nat (fun i => (p i).subtype) (single i x) := by
    simpa only [lsum_single] using! hv
  have := DFunLike.ext_iff.mp (h hv) i
  simpa [eq_comm] using! this

/--
theorem `iSupIndep_of_dfinsuppSumAddHom_injective` / 定理 `iSupIndep_of_dfinsuppSumAddHom_injective`

English:
theorem iSupIndep_of_dfinsuppSumAddHom_injective
  statement: (p : ι -> AddSubmonoid N)
  proof: by
  rw [← iSupIndep_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

中文:
定理 iSupIndep_of_dfinsuppSumAddHom_injective
  结论: (p : ι -> 加法子幺半群 N)
  证明: by
  rw [← iSupIndep_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

Depends on / 依赖: AddSubmonoid, AddSubmonoid.toNatSubmodule, iSupIndep_map_orderIso_iff, iSupIndep_of_dfinsupp_lsum_injective, toNatSubmodule
-/
theorem iSupIndep_of_dfinsuppSumAddHom_injective (p : ι -> AddSubmonoid N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p := by
  rw [← iSupIndep_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

/--
theorem `lsum_comp_mapRange_toSpanSingleton` / 定理 `lsum_comp_mapRange_toSpanSingleton`

English:
theorem lsum_comp_mapRange_toSpanSingleton
  statement: [forall m : R, Decidable (m != 0)] (p : ι -> Submodule R N)
  proof: by
  ext
  simp

中文:
定理 lsum_comp_mapRange_toSpanSingleton
  结论: [对任意 m : R, 可判定 (m != 0)] (p : ι -> 子模 R N)
  证明: by
  ext
  simp
-/
theorem lsum_comp_mapRange_toSpanSingleton [forall m : R, Decidable (m != 0)] (p : ι -> Submodule R N)
    {v : ι -> N} (hv : forall i : ι, v i in p i) :
    (lsum Nat fun i => (p i).subtype : _ ->ₗ[R] _).comp
        ((mapRange.linearMap fun i => LinearMap.toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ :
              _ ->ₗ[R] _).comp
          (finsuppLequivDFinsupp R : (ι ->₀ R) ≃ₗ[R] _).toLinearMap) =
      Finsupp.linearCombination R v := by
  ext
  simp

end Semiring

section Ring

variable [DecidableEq ι] [Ring R] [AddCommGroup N] [Module R N]

/--
theorem `iSupIndep_of_dfinsuppSumAddHom_injective'` / 定理 `iSupIndep_of_dfinsuppSumAddHom_injective'`

English:
theorem iSupIndep_of_dfinsuppSumAddHom_injective'
  statement: (p : ι -> AddSubgroup N)
  proof: by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

中文:
定理 iSupIndep_of_dfinsuppSumAddHom_injective'
  结论: (p : ι -> 加法子群 N)
  证明: by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

Depends on / 依赖: AddSubgroup, AddSubgroup.toIntSubmodule, iSupIndep_map_orderIso_iff, iSupIndep_of_dfinsupp_lsum_injective, toIntSubmodule
-/
theorem iSupIndep_of_dfinsuppSumAddHom_injective' (p : ι -> AddSubgroup N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

/--
theorem `iSupIndep.dfinsupp_lsum_injective` / 定理 `iSupIndep.dfinsupp_lsum_injective`

English:
theorem iSupIndep.dfinsupp_lsum_injective
  given: {p : ι -> Submodule R N} (h : iSupIndep p)
  proof: by
  -- simplify everything down to binders over equalities in `N`
  rw [iSupIndep_iff_forall_dfinsupp] at h
  suffices LinearMap.ker (lsum Nat fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    let thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_

中文:
定理 iSupIndep.dfinsupp_lsum_injective
  条件: {p : ι -> 子模 R N} (h : iSupIndep p)
  证明: by
  -- simplify everything down to binders over equalities in `N`
  rw [iSupIndep_iff_forall_dfinsupp] at h
  suffices LinearMap.ker (lsum Nat fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    let thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_
-/
theorem iSupIndep.dfinsupp_lsum_injective {p : ι -> Submodule R N} (h : iSupIndep p) :
    Function.Injective (lsum Nat fun i => (p i).subtype) := by
  -- simplify everything down to binders over equalities in `N`
  rw [iSupIndep_iff_forall_dfinsupp] at h
  suffices LinearMap.ker (lsum Nat fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    let thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_eq_bot] at this
    exact this
  rw [LinearMap.ker_eq_bot']
  intro m hm
  ext i : 1
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [DFinsupp.zero_apply]; rw [← neg_eq_zero]
  refine h i (-m i) m ?_
  rwa [← erase_add_single i m, map_add, lsum_single, Submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ← Submodule.coe_neg] at hm

/--
theorem `iSupIndep.dfinsuppSumAddHom_injective` / 定理 `iSupIndep.dfinsuppSumAddHom_injective`

English:
theorem iSupIndep.dfinsuppSumAddHom_injective
  given: {p : ι -> AddSubgroup N} (h : iSupIndep p)
  proof: by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective

中文:
定理 iSupIndep.dfinsuppSumAddHom_injective
  条件: {p : ι -> 加法子群 N} (h : iSupIndep p)
  证明: by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective

Depends on / 依赖: AddSubgroup, AddSubgroup.toIntSubmodule, dfinsupp_lsum_injective, h.dfinsupp_lsum_injective, iSupIndep_map_orderIso_iff, toIntSubmodule
-/
theorem iSupIndep.dfinsuppSumAddHom_injective {p : ι -> AddSubgroup N} (h : iSupIndep p) :
    Function.Injective (sumAddHom fun i => (p i).subtype) := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective

/--
theorem `iSupIndep_iff_dfinsupp_lsum_injective` / 定理 `iSupIndep_iff_dfinsupp_lsum_injective`

English:
theorem iSupIndep_iff_dfinsupp_lsum_injective
  given: (p : ι -> Submodule R N)
  proof: ⟨iSupIndep.dfinsupp_lsum_injective, iSupIndep_of_dfinsupp_lsum_injective p⟩

omit [DecidableEq ι] in

中文:
定理 iSupIndep_iff_dfinsupp_lsum_injective
  条件: (p : ι -> 子模 R N)
  证明: ⟨iSupIndep.dfinsupp_lsum_injective, iSupIndep_of_dfinsupp_lsum_injective p⟩

omit [DecidableEq ι] in

Depends on / 依赖: dfinsupp_lsum_injective, iSupIndep, iSupIndep.dfinsupp_lsum_injective, iSupIndep_of_dfinsupp_lsum_injective
-/
theorem iSupIndep_iff_dfinsupp_lsum_injective (p : ι -> Submodule R N) :
    iSupIndep p ↔ Function.Injective (lsum Nat fun i => (p i).subtype) :=
  ⟨iSupIndep.dfinsupp_lsum_injective, iSupIndep_of_dfinsupp_lsum_injective p⟩

omit [DecidableEq ι] in
/--
theorem `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero` / 定理 `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`

English:
theorem iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
  given: (p : ι -> Submodule R N)
  proof: by
  classical
  simp_rw [iSupIndep_def, Submodule.disjoint_def]
  constructor
  · intro h s v hv hv0 i hi
    apply h _ _ (hv i hi)
    rw [← s.add_sum_erase _ hi]; rw [add_eq_zero_iff_neg_eq] at hv0
    rw [← Submodule.neg_mem_iff]; rw [hv0]
    exact SetLike.le_def.mp (biSup_mono <| by grind) (Su

中文:
定理 iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
  条件: (p : ι -> 子模 R N)
  证明: by
  classical
  simp_rw [iSupIndep_def, Submodule.disjoint_def]
  constructor
  · intro h s v hv hv0 i hi
    apply h _ _ (hv i hi)
    rw [← s.add_sum_erase _ hi]; rw [add_eq_zero_iff_neg_eq] at hv0
    rw [← Submodule.neg_mem_iff]; rw [hv0]
    exact SetLike.le_def.mp (biSup_mono <| by grind) (Su

Depends on / 依赖: SetLike, SetLike.le_def.mp, Submodule, Submodule.disjoint_def, Submodule.mem_iSup_iff_exists_finsupp, Submodule.neg_mem_iff, Submodule.sum_mem_biSup, add_eq_zero_iff_neg_eq, add_sum_erase, biSup_mono, classical, contrapose, disjoint_def, f.sum, f.support, iSupIndep_def, insert, le_def, mem_iSup_iff_exists_finsupp, neg_mem_iff
-/
theorem iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (p : ι -> Submodule R N) :
    iSupIndep p ↔ forall (s : Finset ι) (v : ι -> N),
    (forall i in s, v i in p i) -> (∑ i in s, v i = 0) -> forall i in s, v i = 0 := by
  classical
  simp_rw [iSupIndep_def, Submodule.disjoint_def]
  constructor
  · intro h s v hv hv0 i hi
    apply h _ _ (hv i hi)
    rw [← s.add_sum_erase _ hi]; rw [add_eq_zero_iff_neg_eq] at hv0
    rw [← Submodule.neg_mem_iff]; rw [hv0]
    exact SetLike.le_def.mp (biSup_mono <| by grind) (Submodule.sum_mem_biSup <| by grind)
  · intro h i x hx hsup
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp ..).mp hsup
    contrapose! h
    use insert i f.support, fun j => if j = i then -f.sum fun _ x => x else f j
    refine ⟨fun j hj => ?_, ?_, by grind⟩
    · beta_reduce
      split_ifs with h
      · exact (p j).neg_mem (h ▸ hx)
      · simpa [h] using hf j
    · specialize hf i
      simp at hf
      grind [Finsupp.sum, Finset.sum_congr]

@[deprecated (since := "2026-04-08")]
alias iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero := iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero

omit [DecidableEq ι] in
/--
theorem `iSupIndep_iff_finsetSum_eq_imp_eq` / 定理 `iSupIndep_iff_finsetSum_eq_imp_eq`

English:
theorem iSupIndep_iff_finsetSum_eq_imp_eq
  given: (p : ι -> Submodule R N)
  proof: by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  constructor
  · intro h s v w hvw
    simpa [sub_eq_zero] using h s (v - w) fun i hi => (p i).sub_mem (hvw i hi).1 (hvw i hi).2
  · intro h s v hv hv0
    specialize h s v 0
    simp_all

@[deprecated (since := "2026-04-08")]
alias iSupIndep_if

中文:
定理 iSupIndep_iff_finsetSum_eq_imp_eq
  条件: (p : ι -> 子模 R N)
  证明: by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  constructor
  · intro h s v w hvw
    simpa [sub_eq_zero] using h s (v - w) fun i hi => (p i).sub_mem (hvw i hi).1 (hvw i hi).2
  · intro h s v hv hv0
    specialize h s v 0
    simp_all

@[deprecated (since := "2026-04-08")]
alias iSupIndep_if

Depends on / 依赖: iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero, specialize, sub_eq_zero, sub_mem
-/
theorem iSupIndep_iff_finsetSum_eq_imp_eq (p : ι -> Submodule R N) :
    iSupIndep p ↔ forall (s : Finset ι) (v w : ι -> N),
    (forall i in s, v i in p i ∧ w i in p i) -> (∑ i in s, v i = ∑ i in s, w i) -> forall i in s, v i = w i := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  constructor
  · intro h s v w hvw
    simpa [sub_eq_zero] using h s (v - w) fun i hi => (p i).sub_mem (hvw i hi).1 (hvw i hi).2
  · intro h s v hv hv0
    specialize h s v 0
    simp_all

@[deprecated (since := "2026-04-08")]
alias iSupIndep_iff_finset_sum_eq_imp_eq := iSupIndep_iff_finsetSum_eq_imp_eq

/--
theorem `iSupIndep_iff_dfinsuppSumAddHom_injective` / 定理 `iSupIndep_iff_dfinsuppSumAddHom_injective`

English:
theorem iSupIndep_iff_dfinsuppSumAddHom_injective
  given: (p : ι -> AddSubgroup N)
  proof: ⟨iSupIndep.dfinsuppSumAddHom_injective, iSupIndep_of_dfinsuppSumAddHom_injective' p⟩

中文:
定理 iSupIndep_iff_dfinsuppSumAddHom_injective
  条件: (p : ι -> 加法子群 N)
  证明: ⟨iSupIndep.dfinsuppSumAddHom_injective, iSupIndep_of_dfinsuppSumAddHom_injective' p⟩

Depends on / 依赖: dfinsuppSumAddHom_injective, iSupIndep, iSupIndep.dfinsuppSumAddHom_injective, iSupIndep_of_dfinsuppSumAddHom_injective
-/
theorem iSupIndep_iff_dfinsuppSumAddHom_injective (p : ι -> AddSubgroup N) :
    iSupIndep p ↔ Function.Injective (sumAddHom fun i => (p i).subtype) :=
  ⟨iSupIndep.dfinsuppSumAddHom_injective, iSupIndep_of_dfinsuppSumAddHom_injective' p⟩

/--
Definition of `iSupIndep.linearEquiv` / `iSupIndep.linearEquiv` 的定义

English:
definition iSupIndep.linearEquiv
  signature: {p : ι -> Submodule R N} (ind : iSupIndep p)
  body: .ofBijective _ ⟨ind.dfinsupp_lsum_injective, by
    rwa [← LinearMap.range_eq_top, ← Submodule.iSup_eq_range_dfinsupp_lsum]⟩

中文:
定义 iSupIndep.linearEquiv
  签名: {p : ι -> 子模 R N} (ind : iSupIndep p)
  定义体: .ofBijective _ ⟨ind.dfinsupp_lsum_injective, by
    rwa [← LinearMap.range_eq_top, ← Submodule.iSup_eq_range_dfinsupp_lsum]⟩
-/
@[simps! apply] noncomputable def iSupIndep.linearEquiv {p : ι -> Submodule R N} (ind : iSupIndep p)
    (iSup_top : ⨆ i, p i = ⊤) : (Π₀ i, p i) ≃ₗ[R] N :=
  .ofBijective _ ⟨ind.dfinsupp_lsum_injective, by
    rwa [← LinearMap.range_eq_top, ← Submodule.iSup_eq_range_dfinsupp_lsum]⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `iSupIndep.linearEquiv_symm_apply` / 定理 `iSupIndep.linearEquiv_symm_apply`

English:
theorem iSupIndep.linearEquiv_symm_apply
  statement: {p : ι -> Submodule R N} (ind : iSupIndep p)
  proof: by
  simp [← LinearEquiv.eq_symm_apply, iSupIndep.linearEquiv]

中文:
定理 iSupIndep.linearEquiv_symm_apply
  结论: {p : ι -> 子模 R N} (ind : iSupIndep p)
  证明: by
  simp [← LinearEquiv.eq_symm_apply, iSupIndep.linearEquiv]

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_symm_apply, eq_symm_apply, iSupIndep, iSupIndep.linearEquiv, linearEquiv
-/
theorem iSupIndep.linearEquiv_symm_apply {p : ι -> Submodule R N} (ind : iSupIndep p)
    (iSup_top : ⨆ i, p i = ⊤) {i : ι} {x : N} (h : x in p i) :
    (ind.linearEquiv iSup_top).symm x = .single i ⟨x, h⟩ := by
  simp [← LinearEquiv.eq_symm_apply, iSupIndep.linearEquiv]

/--
theorem `iSupIndep.linearIndependent` / 定理 `iSupIndep.linearIndependent`

English:
theorem iSupIndep.linearIndependent
  statement: [IsDomain R] [IsTorsionFree R N] {ι : Type*}
  proof: by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let a :=
    DFinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDFinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext

中文:
定理 iSupIndep.linearIndependent
  结论: [是整环 R] [是无挠 R N] {ι : 类型}
  证明: by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let a :=
    DFinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDFinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.linearMap, LinearMap, LinearMap.toSpanSingleton, Pi.zero_apply, ZeroMemClass, ZeroMemClass.coe_zero, classical, coe_zero, dfinsupp_lsum_injective, hp.dfinsupp_lsum_injective, l.toDFinsupp, linearIndependent_iff, linearMap, lsum_comp_mapRange_toSpanSingleton, mapRange, smul_eq_zero, smul_left_injective, toDFinsupp, toSpanSingleton
-/
theorem iSupIndep.linearIndependent [IsDomain R] [IsTorsionFree R N] {ι : Type*}
    (p : ι -> Submodule R N) (hp : iSupIndep p) {v : ι -> N} (hv : forall i, v i in p i)
    (hv' : forall i, v i != 0) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let a :=
    DFinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDFinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext i
  apply smul_left_injective R (hv' i)
  have : l i • v i = a i := rfl
  simp only [coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero, smul_eq_zero, ha] at this
  simpa

/--
theorem `iSupIndep_iff_linearIndependent_of_ne_zero` / 定理 `iSupIndep_iff_linearIndependent_of_ne_zero`

English:
theorem iSupIndep_iff_linearIndependent_of_ne_zero
  statement: [IsDomain R] [IsTorsionFree R N]
  proof: hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero
  mpr hv := hv.iSupIndep_span_singleton

中文:
定理 iSupIndep_iff_linearIndependent_of_ne_zero
  结论: [是整环 R] [是无挠 R N]
  证明: hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero
  mpr hv := hv.iSupIndep_span_singleton

Depends on / 依赖: Submodule, Submodule.mem_span_singleton_self, h_ne_zero, hv.linearIndependent, linearIndependent, mem_span_singleton_self
-/
theorem iSupIndep_iff_linearIndependent_of_ne_zero [IsDomain R] [IsTorsionFree R N]
    {ι : Type*} {v : ι -> N} (h_ne_zero : forall i, v i != 0) :
    iSupIndep (R ∙ v ·) ↔ LinearIndependent R v where
  mp hv := hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero
  mpr hv := hv.iSupIndep_span_singleton

end Ring

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}
variable {ι : Type*}
variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {σ₁₂ : R ->+* R₂}
variable [Module R M] [Module R₂ M₂]

open Submodule

section DFinsupp

open DFinsupp

variable {γ : ι -> Type*} [DecidableEq ι]

section Sum

variable [forall i, Zero (γ i)] [forall (i) (x : γ i), Decidable (x != 0)]

/--
theorem `coe_dfinsuppSum` / 定理 `coe_dfinsuppSum`

English:
theorem coe_dfinsuppSum
  given: (t : Π₀ i, γ i) (g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂)
  proof: rfl

@[simp]

中文:
定理 coe_dfinsuppSum
  条件: (t : Π₀ i, γ i) (g : 对任意 i, γ i -> M ->ₛₗ[σ₁₂] M₂)
  证明: rfl

@[simp]
-/
theorem coe_dfinsuppSum (t : Π₀ i, γ i) (g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl

@[simp]
/--
theorem `dfinsuppSum_apply` / 定理 `dfinsuppSum_apply`

English:
theorem dfinsuppSum_apply
  given: (t : Π₀ i, γ i) (g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂) (b : M)
  proof: sum_apply _ _ _

中文:
定理 dfinsuppSum_apply
  条件: (t : Π₀ i, γ i) (g : 对任意 i, γ i -> M ->ₛₗ[σ₁₂] M₂) (b : M)
  证明: sum_apply _ _ _

Depends on / 依赖: sum_apply
-/
theorem dfinsuppSum_apply (t : Π₀ i, γ i) (g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _

end Sum

section SumAddHom

variable [forall i, AddZeroClass (γ i)]

@[simp]
/--
theorem `map_dfinsuppSumAddHom` / 定理 `map_dfinsuppSumAddHom`

English:
theorem map_dfinsuppSumAddHom
  given: (f : M ->ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : forall i, γ i ->+ M}
  proof: f.toAddMonoidHom.map_dfinsuppSumAddHom _ _

中文:
定理 map_dfinsuppSumAddHom
  条件: (f : M ->ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : 对任意 i, γ i ->+ M}
  证明: f.toAddMonoidHom.map_dfinsuppSumAddHom _ _

Depends on / 依赖: f.toAddMonoidHom.map_dfinsuppSumAddHom, map_dfinsuppSumAddHom, toAddMonoidHom
-/
theorem map_dfinsuppSumAddHom (f : M ->ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : forall i, γ i ->+ M} :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddMonoidHom.comp (g i)) t :=
  f.toAddMonoidHom.map_dfinsuppSumAddHom _ _

end SumAddHom

end DFinsupp

end AddCommMonoid

end LinearMap

namespace LinearEquiv

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}

section DFinsupp

open DFinsupp

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} {τ₂₁ : R₂ ->+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable {γ : ι -> Type*} [DecidableEq ι]

@[simp]
/--
theorem `map_dfinsuppSumAddHom` / 定理 `map_dfinsuppSumAddHom`

English:
theorem map_dfinsuppSumAddHom
  statement: [forall i, AddZeroClass (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
  proof: f.toAddEquiv.map_dfinsuppSumAddHom _ _

中文:
定理 map_dfinsuppSumAddHom
  结论: [对任意 i, 加法零类 (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
  证明: f.toAddEquiv.map_dfinsuppSumAddHom _ _

Depends on / 依赖: f.toAddEquiv.map_dfinsuppSumAddHom, map_dfinsuppSumAddHom, toAddEquiv
-/
theorem map_dfinsuppSumAddHom [forall i, AddZeroClass (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
    (g : forall i, γ i ->+ M) :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddEquiv.toAddMonoidHom.comp (g i)) t :=
  f.toAddEquiv.map_dfinsuppSumAddHom _ _

end DFinsupp

end LinearEquiv
