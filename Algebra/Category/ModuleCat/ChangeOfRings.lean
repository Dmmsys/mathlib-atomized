/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Change Of Rings

## Main definitions

* `ModuleCat.restrictScalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrictScalars : ModuleCat S ⥤ ModuleCat R` is defined by `M ↦ M` where an `S`-module `M`
  is seen as an `R`-module by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as
  well.

* `ModuleCat.extendScalars`: given **commutative** rings `R, S` and ring homomorphism
  `f : R ⟶ S`, then `extendScalars : ModuleCat R ⥤ ModuleCat S` is defined by `M ↦ S ⨂ M` where the
  module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

* `ModuleCat.coextendScalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`
  then `coextendScalars : ModuleCat R ⥤ ModuleCat S` is defined by `M ↦ (S →ₗ[R] M)` where `S` is
  seen as an `R`-module by restriction of scalars and `l ↦ l ∘ _`.

## Main results

* `ModuleCat.extendRestrictScalarsAdj`: given commutative rings `R, S` and a ring
  homomorphism `f : R →+* S`, the extension and restriction of scalars by `f` are adjoint functors.
* `ModuleCat.restrictCoextendScalarsAdj`: given rings `R, S` and a ring homomorphism
  `f : R ⟶ S` then `coextendScalars f` is the right adjoint of `restrictScalars f`.

## Notation
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `R`-module, `s : S` and `m : M`, then `s ⊗ₜ[R, f] m` is the pure tensor
  `s ⊗ m : S ⊗[R, f] M`.
-/

@[expose] public section

suppress_compilation


open CategoryTheory Limits

namespace ModuleCat

universe v u₁ u₂ u₃ w

namespace RestrictScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
variable (M : ModuleCat.{v} S)

/--
Definition of `obj'` / `obj'` 的定义

English:
definition obj'
  signature: : ModuleCat R
  body: let _ := Module.compHom M f
  of R M

中文:
定义 obj'
  签名: : 模范畴 R
  定义体: let _ := Module.compHom M f
  of R M

Depends on / 依赖: F.obj, FGModuleCat, Finite, Module, Module.Finite, Module.Finite.of_surjective, Module.compHom, ModuleCat, ModuleCat.epi_iff_surjective, colimitQuotientCoproduct, compHom, epi_iff_surjective, of_surjective
-/
def obj' : ModuleCat R :=
  let _ := Module.compHom M f
  of R M

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: {M M' : ModuleCat.{v} S} (g : M ⟶ M')
  body: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `RestrictScalars.obj'` needs to be redesigned.
  ofHom (X := obj' f M) (Y := obj' f M')
    { g.hom with map_smul' := fun r => g.hom.map_smul (f r) }

中文:
定义 map'
  签名: {M M' : 模范畴.{v} S} (g : M ⟶ M')
  定义体: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `RestrictScalars.obj'` needs to be redesigned.
  ofHom (X := obj' f M) (Y := obj' f M')
    { g.hom with map_smul' := fun r => g.hom.map_smul (f r) }
-/
def map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `RestrictScalars.obj'` needs to be redesigned.
  ofHom (X := obj' f M) (Y := obj' f M')
    { g.hom with map_smul' := fun r => g.hom.map_smul (f r) }

end RestrictScalars

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  body: RestrictScalars.obj' f
  map := RestrictScalars.map' f

@[simp]

中文:
定义 restrictScalars
  签名: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  定义体: RestrictScalars.obj' f
  map := RestrictScalars.map' f

@[simp]

Depends on / 依赖: RestrictScalars, RestrictScalars.obj
-/
def restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj := RestrictScalars.obj' f
  map := RestrictScalars.map' f

@[simp]
/--
lemma `smul_restrictScalars` / 引理 `smul_restrictScalars`

English:
lemma smul_restrictScalars
  statement: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) (r : R)
  proof: rfl

中文:
引理 smul_restrictScalars
  结论: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S) (r : R)
  证明: rfl

Depends on / 依赖: FGModuleCat, ModuleCat, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
lemma smul_restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) (r : R)
    (M : ModuleCat S) :
    dsimp% ((ModuleCat.restrictScalars f).obj M).smul r = M.smul (f r) :=
  rfl

/--
lemma `forget₂_map_restrictScalars` / 引理 `forget₂_map_restrictScalars`

English:
lemma forget₂_map_restrictScalars
  statement: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  proof: rfl

中文:
引理 forget₂_map_restrictScalars
  结论: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  证明: rfl
-/
lemma forget₂_map_restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
    {M N : ModuleCat S} (g : M ⟶ N) :
    (forget₂ _ Ab).map ((ModuleCat.restrictScalars f).map g) = (forget₂ _ Ab).map g :=
  rfl

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    (restrictScalars.{v} f).Faithful where
  map_injective h := by
    ext x
    simpa only using! DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    (restrictScalars.{v} f).PreservesMonomorphisms where
  preserves _ h := by rwa [mono_iff_injective] at h ⊢

instance {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) :
    (restrictScalars f).ReflectsIsomorphisms :=
  have : (restrictScalars f ⋙ CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms :=
    inferInstanceAs (CategoryTheory.forget (ModuleCat S)).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (CategoryTheory.forget _)

-- Porting note: this should be automatic
-- TODO: this instance gives diamonds if `f : S →+* S`, see `PresheafOfModules.pushforward₀`.
-- The correct solution is probably to define explicit maps between `M` and
-- `(restrictScalars f).obj M`.
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R ->+* S}
{M : ModuleCat.{v} S} : Module S (restrictScalars f).obj M :=
inferInstanceAs Module S M

@[simp]
/--
theorem `restrictScalars.map_apply` / 定理 `restrictScalars.map_apply`

English:
theorem restrictScalars.map_apply
  statement: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  proof: rfl

@[simp]

中文:
定理 restrictScalars.map_apply
  结论: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  证明: rfl

@[simp]
-/
theorem restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) : (restrictScalars f).map g x = g x :=
  rfl

@[simp]
/--
theorem `restrictScalars.smul_def` / 定理 `restrictScalars.smul_def`

English:
theorem restrictScalars.smul_def
  statement: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  proof: rfl

中文:
定理 restrictScalars.smul_def
  结论: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  证明: rfl
-/
theorem restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
    {M : ModuleCat.{v} S} (r : R) (m : (restrictScalars f).obj M) : r • m = f r • show M from m :=
  rfl

/--
theorem `restrictScalars.smul_def'` / 定理 `restrictScalars.smul_def'`

English:
theorem restrictScalars.smul_def'
  statement: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  proof: rfl

中文:
定理 restrictScalars.smul_def'
  结论: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  证明: rfl
-/
theorem restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
    {M : ModuleCat.{v} S} (r : R) (m : M) :
    r • (show (restrictScalars f).obj M from m) = f r • m :=
  rfl


instance (priority := 100) sMulCommClass_mk {R : Type u₁} {S : Type u₂} [Ring R] [CommRing S]
    (f : R ->+* S) (M : Type v) [I : AddCommGroup M] [Module S M] :
    haveI : SMul R M := (RestrictScalars.obj' f (ModuleCat.of S M)).isModule.toSMul
    SMulCommClass R S M :=
  @SMulCommClass.mk R S M (_) _
    fun r s m => (by simp [← mul_smul, mul_comm] : f r • s • m = s • f r • m)

set_option backward.isDefEq.respectTransparency false in
/-- Semilinear maps `M →ₛₗ[f] N` identify to
morphisms `M ⟶ (ModuleCat.restrictScalars f).obj N`. -/
@[simps]
/--
Definition of `semilinearMapAddEquiv` / `semilinearMapAddEquiv` 的定义

English:
definition semilinearMapAddEquiv
  signature: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  body: ofHom (Y := (ModuleCat.restrictScalars f).obj N)
    { toFun := g
      map_add' := by simp
      map_smul' := by simp }
  invFun g :=
    { toFun := g
      map_add' := by simp
      map_smul' := g.hom.map_smul }
  map_add' _ _ := rfl

中文:
定义 semilinearMapAddEquiv
  签名: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  定义体: ofHom (Y := (ModuleCat.restrictScalars f).obj N)
    { toFun := g
      map_add' := by simp
      map_smul' := by simp }
  invFun g :=
    { toFun := g
      map_add' := by simp
      map_smul' := g.hom.map_smul }
  map_add' _ _ := rfl

Depends on / 依赖: Finite, Module, Module.Finite
-/
def semilinearMapAddEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
    (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) :
    (M ->ₛₗ[f] N) ≃+ (M ⟶ (ModuleCat.restrictScalars f).obj N) where
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
toFun g := ofHom (Y := (ModuleCat.restrictScalars f).obj N)
    { toFun := g
      map_add' := by simp
      map_smul' := by simp }
  invFun g :=
    { toFun := g
      map_add' := by simp
      map_smul' := g.hom.map_smul }
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `restrictScalarsCongr` / `restrictScalarsCongr` 的定义

English:
definition restrictScalarsCongr
  body: NatIso.ofComponents (fun X => LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars f).obj X) (X₂ := (ModuleCat.restrictScalars g).obj X)
    { __ := AddEquiv.refl _, map_smul' _ _ := by subst e; rfl }) fun _ => by subst e; rfl

@[simp]

中文:
定义 restrictScalarsCongr
  定义体: NatIso.ofComponents (fun X => LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars f).obj X) (X₂ := (ModuleCat.restrictScalars g).obj X)
    { __ := AddEquiv.refl _, map_smul' _ _ := by subst e; rfl }) fun _ => by subst e; rfl

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.refl, LinearEquiv, LinearEquiv.toModuleIso, ModuleCat, ModuleCat.restrictScalars, NatIso, NatIso.ofComponents, map_smul, ofComponents, restrictScalars, toModuleIso
-/
def restrictScalarsCongr
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R ->+* S} (e : f = g) :
    ModuleCat.restrictScalars f ≅ ModuleCat.restrictScalars g :=
  NatIso.ofComponents (fun X => LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars f).obj X) (X₂ := (ModuleCat.restrictScalars g).obj X)
    { __ := AddEquiv.refl _, map_smul' _ _ := by subst e; rfl }) fun _ => by subst e; rfl

@[simp]
/--
lemma `restrictScalarsCongr_symm` / 引理 `restrictScalarsCongr_symm`

English:
lemma restrictScalarsCongr_symm
  proof: rfl

@[simp]

中文:
引理 restrictScalarsCongr_symm
  证明: rfl

@[simp]
-/
lemma restrictScalarsCongr_symm
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R ->+* S} (e : f = g) :
  (restrictScalarsCongr e).symm = restrictScalarsCongr e.symm := rfl

@[simp]
/--
lemma `restrictScalarsCongr_hom_app` / 引理 `restrictScalarsCongr_hom_app`

English:
lemma restrictScalarsCongr_hom_app
  proof: rfl

@[simp]

中文:
引理 restrictScalarsCongr_hom_app
  证明: rfl

@[simp]
-/
lemma restrictScalarsCongr_hom_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R ->+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (restrictScalarsCongr e).hom.app M x = x := rfl

@[simp]
/--
lemma `restrictScalarsCongr_inv_app` / 引理 `restrictScalarsCongr_inv_app`

English:
lemma restrictScalarsCongr_inv_app
  proof: rfl

中文:
引理 restrictScalarsCongr_inv_app
  证明: rfl
-/
lemma restrictScalarsCongr_inv_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R ->+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (restrictScalarsCongr e).inv.app M x = x := rfl

section

variable {R : Type u₁} [Ring R] (f : R ->+* R)

/--
Definition of `restrictScalarsId'App` / `restrictScalarsId'App` 的定义

English:
definition restrictScalarsId'App
  signature: (hf : f = RingHom.id R) (M : ModuleCat R)
  body: LinearEquiv.toModuleIso
    @AddEquiv.toLinearEquiv _ _ _ _ _ _ (((restrictScalars f).obj M).isModule) _
      (by rfl) (fun r x => by subst hf; rfl)

中文:
定义 restrictScalarsId'App
  签名: (hf : f = 环态射.id R) (M : 模范畴 R)
  定义体: LinearEquiv.toModuleIso
    @AddEquiv.toLinearEquiv _ _ _ _ _ _ (((restrictScalars f).obj M).isModule) _
      (by rfl) (fun r x => by subst hf; rfl)

Depends on / 依赖: AddEquiv, AddEquiv.toLinearEquiv, LinearEquiv, LinearEquiv.toModuleIso, isModule, restrictScalars, toLinearEquiv, toModuleIso
-/
def restrictScalarsId'App (hf : f = RingHom.id R) (M : ModuleCat R) :
    (restrictScalars f).obj M ≅ M :=
LinearEquiv.toModuleIso
    @AddEquiv.toLinearEquiv _ _ _ _ _ _ (((restrictScalars f).obj M).isModule) _
      (by rfl) (fun r x => by subst hf; rfl)

variable (hf : f = RingHom.id R)

/--
lemma `restrictScalarsId'App_hom_apply` / 引理 `restrictScalarsId'App_hom_apply`

English:
lemma restrictScalarsId'App_hom_apply
  given: (M : ModuleCat R) (x : M)
  proof: rfl

中文:
引理 restrictScalarsId'App_hom_apply
  条件: (M : 模范畴 R) (x : M)
  证明: rfl
-/
@[simp] lemma restrictScalarsId'App_hom_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).hom x = x :=
  rfl

/--
lemma `restrictScalarsId'App_inv_apply` / 引理 `restrictScalarsId'App_inv_apply`

English:
lemma restrictScalarsId'App_inv_apply
  given: (M : ModuleCat R) (x : M)
  proof: rfl

中文:
引理 restrictScalarsId'App_inv_apply
  条件: (M : 模范畴 R) (x : M)
  证明: rfl
-/
@[simp] lemma restrictScalarsId'App_inv_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).inv x = x :=
  rfl

/-- The restriction of scalars by a ring morphism that is the identity identifies to the
identity functor. -/
@[simps! hom_app inv_app]
/--
Definition of `restrictScalarsId'` / `restrictScalarsId'` 的定义

English:
definition restrictScalarsId'
  signature: : ModuleCat.restrictScalars.{v} f ≅ 𝟭 _
  body: NatIso.ofComponents fun M => restrictScalarsId'App f hf M

@[reassoc]

中文:
定义 restrictScalarsId'
  签名: : 模范畴.restrictScalars.{v} f ≅ 𝟭 _
  定义体: NatIso.ofComponents fun M => restrictScalarsId'App f hf M

@[reassoc]

Depends on / 依赖: Finite, Module, Module.Finite, Module.Finite.equiv_iff, ModuleCat, ModuleCat.of, ModuleCat.piIsoPi, equiv_iff, infer_instance, piIsoPi, toLinearEquiv
-/
def restrictScalarsId' : ModuleCat.restrictScalars.{v} f ≅ 𝟭 _ :=
NatIso.ofComponents fun M => restrictScalarsId'App f hf M

@[reassoc]
/--
lemma `restrictScalarsId'App_hom_naturality` / 引理 `restrictScalarsId'App_hom_naturality`

English:
lemma restrictScalarsId'App_hom_naturality
  given: {M N : ModuleCat R} (φ : M ⟶ N)
  proof: (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]

中文:
引理 restrictScalarsId'App_hom_naturality
  条件: {M N : 模范畴 R} (φ : M ⟶ N)
  证明: (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]

Depends on / 依赖: F.obj, FGModuleCat, Finite, Module, Module.Finite, Module.Finite.of_injective, ModuleCat, ModuleCat.mono_iff_injective, limitSubobjectProduct, mono_iff_injective, of_injective
-/
lemma restrictScalarsId'App_hom_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    (restrictScalars f).map φ ≫ (restrictScalarsId'App f hf N).hom =
      (restrictScalarsId'App f hf M).hom ≫ φ :=
  (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]
/--
lemma `restrictScalarsId'App_inv_naturality` / 引理 `restrictScalarsId'App_inv_naturality`

English:
lemma restrictScalarsId'App_inv_naturality
  given: {M N : ModuleCat R} (φ : M ⟶ N)
  proof: (restrictScalarsId' f hf).inv.naturality φ

中文:
引理 restrictScalarsId'App_inv_naturality
  条件: {M N : 模范畴 R} (φ : M ⟶ N)
  证明: (restrictScalarsId' f hf).inv.naturality φ
-/
lemma restrictScalarsId'App_inv_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    φ ≫ (restrictScalarsId'App f hf N).inv =
      (restrictScalarsId'App f hf M).inv ≫ (restrictScalars f).map φ :=
  (restrictScalarsId' f hf).inv.naturality φ

variable (R)

/--
Definition of `restrictScalarsId` / `restrictScalarsId` 的定义

English:
abbreviation restrictScalarsId
  body: restrictScalarsId'.{v} (RingHom.id R) rfl

中文:
缩写 restrictScalarsId
  定义体: restrictScalarsId'.{v} (RingHom.id R) rfl

Depends on / 依赖: RingHom, RingHom.id, restrictScalarsId
-/
abbrev restrictScalarsId := restrictScalarsId'.{v} (RingHom.id R) rfl

end

section

variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [Ring R₁] [Ring R₂] [Ring R₃]
  (f : R₁ ->+* R₂) (g : R₂ ->+* R₃) (gf : R₁ ->+* R₃)

/--
Definition of `restrictScalarsComp'App` / `restrictScalarsComp'App` 的定义

English:
definition restrictScalarsComp'App
  signature: (hgf : gf = g.comp f) (M : ModuleCat R₃)
  body: (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars gf).obj M))
    (M₂ := ↑((restrictScalars f).obj ((restrictScalars g).obj M)))
    (by rfl)
    (fun r x => by subst hgf; rfl)).toModuleIso

中文:
定义 restrictScalarsComp'App
  签名: (hgf : gf = g.comp f) (M : 模范畴 R₃)
  定义体: (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars gf).obj M))
    (M₂ := ↑((restrictScalars f).obj ((restrictScalars g).obj M)))
    (by rfl)
    (fun r x => by subst hgf; rfl)).toModuleIso

Depends on / 依赖: AddEquiv, AddEquiv.toLinearEquiv, FGModuleCat, ModuleCat, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape, restrictScalars, toLinearEquiv, toModuleIso
-/
def restrictScalarsComp'App (hgf : gf = g.comp f) (M : ModuleCat R₃) :
    (restrictScalars gf).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M) :=
  (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars gf).obj M))
    (M₂ := ↑((restrictScalars f).obj ((restrictScalars g).obj M)))
    (by rfl)
    (fun r x => by subst hgf; rfl)).toModuleIso

variable (hgf : gf = g.comp f)

/--
lemma `restrictScalarsComp'App_hom_apply` / 引理 `restrictScalarsComp'App_hom_apply`

English:
lemma restrictScalarsComp'App_hom_apply
  given: (M : ModuleCat R₃) (x : M)
  proof: rfl

中文:
引理 restrictScalarsComp'App_hom_apply
  条件: (M : 模范畴 R₃) (x : M)
  证明: rfl
-/
@[simp] lemma restrictScalarsComp'App_hom_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).hom x = x :=
  rfl

/--
lemma `restrictScalarsComp'App_inv_apply` / 引理 `restrictScalarsComp'App_inv_apply`

English:
lemma restrictScalarsComp'App_inv_apply
  given: (M : ModuleCat R₃) (x : M)
  proof: rfl

中文:
引理 restrictScalarsComp'App_inv_apply
  条件: (M : 模范畴 R₃) (x : M)
  证明: rfl
-/
@[simp] lemma restrictScalarsComp'App_inv_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).inv x = x :=
  rfl

/-- The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors. -/
@[simps! hom_app inv_app]
/--
Definition of `restrictScalarsComp'` / `restrictScalarsComp'` 的定义

English:
definition restrictScalarsComp'
  signature: :
  body: NatIso.ofComponents fun M => restrictScalarsComp'App f g gf hgf M

@[reassoc]

中文:
定义 restrictScalarsComp'
  签名: :
  定义体: NatIso.ofComponents fun M => restrictScalarsComp'App f g gf hgf M

@[reassoc]

Depends on / 依赖: Additive
-/
def restrictScalarsComp' :
    ModuleCat.restrictScalars.{v} gf ≅
      ModuleCat.restrictScalars g ⋙ ModuleCat.restrictScalars f :=
NatIso.ofComponents fun M => restrictScalarsComp'App f g gf hgf M

@[reassoc]
/--
lemma `restrictScalarsComp'App_hom_naturality` / 引理 `restrictScalarsComp'App_hom_naturality`

English:
lemma restrictScalarsComp'App_hom_naturality
  given: {M N : ModuleCat R₃} (φ : M ⟶ N)
  proof: (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]

中文:
引理 restrictScalarsComp'App_hom_naturality
  条件: {M N : 模范畴 R₃} (φ : M ⟶ N)
  证明: (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]
-/
lemma restrictScalarsComp'App_hom_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (restrictScalars gf).map φ ≫ (restrictScalarsComp'App f g gf hgf N).hom =
      (restrictScalarsComp'App f g gf hgf M).hom ≫
        (restrictScalars f).map ((restrictScalars g).map φ) :=
  (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]
/--
lemma `restrictScalarsComp'App_inv_naturality` / 引理 `restrictScalarsComp'App_inv_naturality`

English:
lemma restrictScalarsComp'App_inv_naturality
  given: {M N : ModuleCat R₃} (φ : M ⟶ N)
  proof: (restrictScalarsComp' f g gf hgf).inv.naturality φ

中文:
引理 restrictScalarsComp'App_inv_naturality
  条件: {M N : 模范畴 R₃} (φ : M ⟶ N)
  证明: (restrictScalarsComp' f g gf hgf).inv.naturality φ
-/
lemma restrictScalarsComp'App_inv_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (restrictScalars f).map ((restrictScalars g).map φ) ≫
        (restrictScalarsComp'App f g gf hgf N).inv =
      (restrictScalarsComp'App f g gf hgf M).inv ≫ (restrictScalars gf).map φ :=
  (restrictScalarsComp' f g gf hgf).inv.naturality φ

/--
Definition of `restrictScalarsComp` / `restrictScalarsComp` 的定义

English:
abbreviation restrictScalarsComp
  body: restrictScalarsComp'.{v} f g _ rfl

中文:
缩写 restrictScalarsComp
  定义体: restrictScalarsComp'.{v} f g _ rfl

Depends on / 依赖: restrictScalarsComp
-/
abbrev restrictScalarsComp := restrictScalarsComp'.{v} f g _ rfl

end

/-- The equivalence of categories `ModuleCat S ≌ ModuleCat R` induced by `e : R ≃+* S`. -/
@[simps]
/--
Definition of `restrictScalarsEquivalenceOfRingEquiv` / `restrictScalarsEquivalenceOfRingEquiv` 的定义

English:
definition restrictScalarsEquivalenceOfRingEquiv
  signature: {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
  body: ModuleCat.restrictScalars e.toRingHom
  inverse := ModuleCat.restrictScalars e.symm
  unitIso := (restrictScalarsId S).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    (restrictScalarsId R)

中文:
定义 restrictScalarsEquivalenceOfRingEquiv
  签名: {R S : 类型} [环 R] [环 S] (e : R ≃+* S)
  定义体: ModuleCat.restrictScalars e.toRingHom
  inverse := ModuleCat.restrictScalars e.symm
  unitIso := (restrictScalarsId S).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    (restrictScalarsId R)

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalars, e.toRingHom, restrictScalars, toRingHom
-/
def restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    ModuleCat S ≌ ModuleCat R where
  functor := ModuleCat.restrictScalars e.toRingHom
  inverse := ModuleCat.restrictScalars e.symm
  unitIso := (restrictScalarsId S).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    (restrictScalarsId R)

/--
Instance `restrictScalars_isEquivalence_of_ringEquiv` / 实例 `restrictScalars_isEquivalence_of_ringEquiv`

English:
instance restrictScalars_isEquivalence_of_ringEquiv
  signature: {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
  body: (restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

中文:
实例 restrictScalars_isEquivalence_of_ringEquiv
  签名: {R S : 类型} [环 R] [环 S] (e : R ≃+* S)
  定义体: (restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, restrictScalarsEquivalenceOfRingEquiv
-/
instance restrictScalars_isEquivalence_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).IsEquivalence :=
  (restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

/--
Definition of `restrictScalarsIsoOfEquiv` / `restrictScalarsIsoOfEquiv` 的定义

English:
definition restrictScalarsIsoOfEquiv
  signature: {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S)
  body: letI : Module R (ModuleCat.of S S) := e.toRingHom.toModule
  LinearEquiv.toModuleIso
    { __ := e.symm
      map_smul' x y := by simp [RingHom.toModule_smul] }

@[simp]

中文:
定义 restrictScalarsIsoOfEquiv
  签名: {R S : 类型v} [环 R] [环 S] (e : R ≃+* S)
  定义体: letI : Module R (ModuleCat.of S S) := e.toRingHom.toModule
  LinearEquiv.toModuleIso
    { __ := e.symm
      map_smul' x y := by simp [RingHom.toModule_smul] }

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.toModuleIso, Module, ModuleCat, ModuleCat.of, RingHom, RingHom.toModule_smul, e.symm, e.toRingHom.toModule, map_smul, toModule, toModuleIso, toModule_smul, toRingHom
-/
def restrictScalarsIsoOfEquiv {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) ≅ ModuleCat.of R R :=
  letI : Module R (ModuleCat.of S S) := e.toRingHom.toModule
  LinearEquiv.toModuleIso
    { __ := e.symm
      map_smul' x y := by simp [RingHom.toModule_smul] }

@[simp]
/--
lemma `restrictScalarsIsoOfEquiv_hom_apply` / 引理 `restrictScalarsIsoOfEquiv_hom_apply`

English:
lemma restrictScalarsIsoOfEquiv_hom_apply
  given: {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (x : S)
  proof: rfl

@[simp]

中文:
引理 restrictScalarsIsoOfEquiv_hom_apply
  条件: {R S : 类型v} [环 R] [环 S] (e : R ≃+* S) (x : S)
  证明: rfl

@[simp]
-/
lemma restrictScalarsIsoOfEquiv_hom_apply {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (x : S) :
    dsimp% (ModuleCat.restrictScalarsIsoOfEquiv e).hom x = e.symm x :=
  rfl

@[simp]
/--
lemma `restrictScalarsIsoOfEquiv_inv_apply` / 引理 `restrictScalarsIsoOfEquiv_inv_apply`

English:
lemma restrictScalarsIsoOfEquiv_inv_apply
  given: {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (x : R)
  proof: rfl

中文:
引理 restrictScalarsIsoOfEquiv_inv_apply
  条件: {R S : 类型v} [环 R] [环 S] (e : R ≃+* S) (x : R)
  证明: rfl
-/
lemma restrictScalarsIsoOfEquiv_inv_apply {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (x : R) :
    dsimp% (ModuleCat.restrictScalarsIsoOfEquiv e).inv x = e x :=
  rfl

instance {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) : (restrictScalars f).Additive where

/--
Instance `restrictScalarsEquivalenceOfRingEquiv_additive` / 实例 `restrictScalarsEquivalenceOfRingEquiv_additive`

English:
instance restrictScalarsEquivalenceOfRingEquiv_additive
  signature: {R S : Type*} [Ring R] [Ring S]

中文:
实例 restrictScalarsEquivalenceOfRingEquiv_additive
  签名: {R S : 类型} [环 R] [环 S]
-/
instance restrictScalarsEquivalenceOfRingEquiv_additive {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).functor.Additive where

namespace Algebra

instance {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S]
    (f : R ->ₐ[R₀] S) : (restrictScalars f.toRingHom).Linear R₀ where
  map_smul {M N} g r₀ := by ext m; exact congr_arg (· • g.hom m) (f.commutes r₀).symm

/--
Instance `restrictScalarsEquivalenceOfRingEquiv_linear` / 实例 `restrictScalarsEquivalenceOfRingEquiv_linear`

English:
instance restrictScalarsEquivalenceOfRingEquiv_linear
  body: inferInstanceAs ((restrictScalars e.toAlgHom.toRingHom).Linear R₀)

中文:
实例 restrictScalarsEquivalenceOfRingEquiv_linear
  定义体: inferInstanceAs ((restrictScalars e.toAlgHom.toRingHom).Linear R₀)

Depends on / 依赖: Linear, e.toAlgHom.toRingHom, restrictScalars, toAlgHom, toRingHom
-/
instance restrictScalarsEquivalenceOfRingEquiv_linear
    {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S]
    (e : R ≃ₐ[R₀] S) :
    (restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor.Linear R₀ :=
  inferInstanceAs ((restrictScalars e.toAlgHom.toRingHom).Linear R₀)

end Algebra

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S)

section ModuleCat.Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

/-- Tensor product of elements along a base change.

This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
without this notation, one needs to work with `s : (restrictScalars f).obj ⟨S⟩`. -/
scoped[ChangeOfRings] notation:100 s:100 " otimesₜ[" R "," f "] " m:101 =>
  @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ f) _ s m

end Unbundled

open ChangeOfRings

namespace ExtendScalars

variable (M : ModuleCat.{v} R)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `obj'` / `obj'` 的定义

English:
definition obj'
  signature: : ModuleCat S
  body: of _ (TensorProduct R ((restrictScalars f).obj (of _ S)) M)

中文:
定义 obj'
  签名: : 模范畴 S
  定义体: of _ (TensorProduct R ((restrictScalars f).obj (of _ S)) M)

Depends on / 依赖: TensorProduct, restrictScalars
-/
def obj' : ModuleCat S :=
  of _ (TensorProduct R ((restrictScalars f).obj (of _ S)) M)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2)
  body: ofHom (@LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l.hom)

中文:
定义 map'
  签名: {M1 M2 : 模范畴.{v} R} (l : M1 ⟶ M2)
  定义体: ofHom (@LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l.hom)

Depends on / 依赖: LinearMap, LinearMap.baseChange, algebraMap, baseChange, l.hom, toAlgebra
-/
def map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) : obj' f M1 ⟶ obj' f M2 :=
  ofHom (@LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l.hom)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map'_id` / 定理 `map'_id`

English:
theorem map'_id
  given: {M : ModuleCat.{v} R}
  statement: map' f (𝟙 M) = 𝟙 _
  proof: by
  simp [map', obj']

中文:
定理 map'_id
  条件: {M : 模范畴.{v} R}
  结论: map' f (𝟙 M) = 𝟙 _
  证明: by
  simp [map', obj']
-/
theorem map'_id {M : ModuleCat.{v} R} : map' f (𝟙 M) = 𝟙 _ := by
  simp [map', obj']

/--
theorem `map'_comp` / 定理 `map'_comp`

English:
theorem map'_comp
  given: {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃)
  proof: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => erw [LinearMap.map_add, LinearMap.map_add]; grind

中文:
定理 map'_comp
  条件: {M₁ M₂ M₃ : 模范畴.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃)
  证明: by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => erw [LinearMap.map_add, LinearMap.map_add]; grind
-/
theorem map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
    map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => erw [LinearMap.map_add, LinearMap.map_add]; grind

end ExtendScalars

/--
Definition of `extendScalars` / `extendScalars` 的定义

English:
definition extendScalars
  signature: {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S)
  body: ExtendScalars.obj' f M
  map l := ExtendScalars.map' f l
  map_id _ := ExtendScalars.map'_id f
  map_comp := ExtendScalars.map'_comp f

中文:
定义 extendScalars
  签名: {R : 类型u₁} {S : 类型u₂} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: ExtendScalars.obj' f M
  map l := ExtendScalars.map' f l
  map_id _ := ExtendScalars.map'_id f
  map_comp := ExtendScalars.map'_comp f

Depends on / 依赖: ExtendScalars, ExtendScalars.obj
-/
def extendScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S) :
    ModuleCat R ⥤ ModuleCat S where
  obj M := ExtendScalars.obj' f M
  map l := ExtendScalars.map' f l
  map_id _ := ExtendScalars.map'_id f
  map_comp := ExtendScalars.map'_comp f

namespace ExtendScalars

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `smul_tmul` / 定理 `smul_tmul`

English:
theorem smul_tmul
  given: {M : ModuleCat.{v} R} (s s' : S) (m : M)
  proof: rfl

@[simp]

中文:
定理 smul_tmul
  条件: {M : 模范畴.{v} R} (s s' : S) (m : M)
  证明: rfl

@[simp]
-/
protected theorem smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s' otimesₜ[R,f] m : (extendScalars f).obj M) = (s * s') otimesₜ[R,f] m :=
  rfl

@[simp]
/--
theorem `map_tmul` / 定理 `map_tmul`

English:
theorem map_tmul
  given: {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M)
  proof: rfl

中文:
定理 map_tmul
  条件: {M M' : 模范畴.{v} R} (g : M ⟶ M') (s : S) (m : M)
  证明: rfl
-/
theorem map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (extendScalars f).map g (s otimesₜ[R,f] m) = s otimesₜ[R,f] g m :=
  rfl

variable {f}

set_option backward.isDefEq.respectTransparency false in
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {M : ModuleCat R} {N : ModuleCat S}
  proof: by
  apply (restrictScalars f).map_injective
  let := f.toAlgebra
  ext : 1
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s otimesₜ m) = β (s otimesₜ m)
  have : s otimesₜ[R] (m : M) = s • (1 : S) otimesₜ[R] m := by
    rw [ExtendScalars.smul_tmul]; rw [mul_one]
  simp only [this, map_smul, h]

中文:
引理 hom_ext
  结论: {M : 模范畴 R} {N : 模范畴 S}
  证明: by
  apply (restrictScalars f).map_injective
  let := f.toAlgebra
  ext : 1
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s otimesₜ m) = β (s otimesₜ m)
  have : s otimesₜ[R] (m : M) = s • (1 : S) otimesₜ[R] m := by
    rw [ExtendScalars.smul_tmul]; rw [mul_one]
  simp only [this, map_smul, h]

Depends on / 依赖: ExtendScalars, ExtendScalars.smul_tmul, TensorProduct, TensorProduct.ext, f.toAlgebra, map_injective, map_smul, mul_one, restrictScalars, smul_tmul, toAlgebra
-/
lemma hom_ext {M : ModuleCat R} {N : ModuleCat S}
    {α β : (extendScalars f).obj M ⟶ N}
    (h : forall (m : M), α ((1 : S) otimesₜ m) = β ((1 : S) otimesₜ m)) : α = β := by
  apply (restrictScalars f).map_injective
  let := f.toAlgebra
  ext : 1
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s otimesₜ m) = β (s otimesₜ m)
  have : s otimesₜ[R] (m : M) = s • (1 : S) otimesₜ[R] m := by
    rw [ExtendScalars.smul_tmul]; rw [mul_one]
  simp only [this, map_smul, h]

end ExtendScalars

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- We use `S'` to denote `S` viewed as `R`-module, via the map `f`.
-- Porting note: this seems to cause problems related to lack of reducibility
-- local notation "S'" => (restrictScalars f).obj ⟨S⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasSMul` / 实例 `hasSMul`

English:
instance hasSMul
  signature: : SMul S (restrictScalars f).obj (of _ S) ->ₗ[R] M where
  body: { toFun := fun s' : S => g (s' * s : S)
      map_add' := fun x y : S => by rw [add_mul, map_add]
      map_smul' := fun r (t : S) => by
        simp [← map_smul, ModuleCat.restrictScalars.smul_def (M := ModuleCat.of _ S), mul_assoc] }

@[simp]

中文:
实例 hasSMul
  签名: : 标量乘法 S (restrictScalars f).obj (of _ S) ->ₗ[R] M where
  定义体: { toFun := fun s' : S => g (s' * s : S)
      map_add' := fun x y : S => by rw [add_mul, map_add]
      map_smul' := fun r (t : S) => by
        simp [← map_smul, ModuleCat.restrictScalars.smul_def (M := ModuleCat.of _ S), mul_assoc] }

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.of, ModuleCat.restrictScalars.smul_def, add_mul, map_add, map_smul, mul_assoc, restrictScalars, smul_def
-/
instance hasSMul : SMul S (restrictScalars f).obj (of _ S) ->ₗ[R] M where
  smul s g :=
    { toFun := fun s' : S => g (s' * s : S)
      map_add' := fun x y : S => by rw [add_mul, map_add]
      map_smul' := fun r (t : S) => by
        simp [← map_smul, ModuleCat.restrictScalars.smul_def (M := ModuleCat.of _ S), mul_assoc] }

@[simp]
/--
theorem `smul_apply'` / 定理 `smul_apply'`

English:
theorem smul_apply'
  given: (s : S) (g : (restrictScalars f).obj (of _ S) ->ₗ[R] M) (s' : S)
  proof: rfl

中文:
定理 smul_apply'
  条件: (s : S) (g : (restrictScalars f).obj (of _ S) ->ₗ[R] M) (s' : S)
  证明: rfl
-/
theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) ->ₗ[R] M) (s' : S) :
    (s • g) s' = g (s' * s : S) :=
  rfl

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: : MulAction S (restrictScalars f).obj (of _ S) ->ₗ[R] M
  body: { CoextendScalars.hasSMul f _ with
    one_smul := fun g => LinearMap.ext fun s : S => by simp
    mul_smul := fun (s t : S) g => LinearMap.ext fun x : S => by simp [mul_assoc] }

中文:
实例 mulAction
  签名: : 乘法作用 S (restrictScalars f).obj (of _ S) ->ₗ[R] M
  定义体: { CoextendScalars.hasSMul f _ with
    one_smul := fun g => LinearMap.ext fun s : S => by simp
    mul_smul := fun (s t : S) g => LinearMap.ext fun x : S => by simp [mul_assoc] }

Depends on / 依赖: CoextendScalars, CoextendScalars.hasSMul, LinearMap, LinearMap.ext, hasSMul, mul_assoc, mul_smul, one_smul
-/
instance mulAction : MulAction S (restrictScalars f).obj (of _ S) ->ₗ[R] M :=
  { CoextendScalars.hasSMul f _ with
    one_smul := fun g => LinearMap.ext fun s : S => by simp
    mul_smul := fun (s t : S) g => LinearMap.ext fun x : S => by simp [mul_assoc] }

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: : DistribMulAction S (restrictScalars f).obj (of _ S) ->ₗ[R] M
  body: { CoextendScalars.mulAction f _ with
    smul_add := fun s g h => LinearMap.ext fun _ : S => by simp
    smul_zero := fun _ => LinearMap.ext fun _ : S => by simp }

中文:
实例 distribMulAction
  签名: : 分配乘法作用 S (restrictScalars f).obj (of _ S) ->ₗ[R] M
  定义体: { CoextendScalars.mulAction f _ with
    smul_add := fun s g h => LinearMap.ext fun _ : S => by simp
    smul_zero := fun _ => LinearMap.ext fun _ : S => by simp }

Depends on / 依赖: CoextendScalars, CoextendScalars.mulAction, LinearMap, LinearMap.ext, mulAction, smul_add, smul_zero
-/
instance distribMulAction : DistribMulAction S (restrictScalars f).obj (of _ S) ->ₗ[R] M :=
  { CoextendScalars.mulAction f _ with
    smul_add := fun s g h => LinearMap.ext fun _ : S => by simp
    smul_zero := fun _ => LinearMap.ext fun _ : S => by simp }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isModule` / 实例 `isModule`

English:
instance isModule
  signature: : Module S (restrictScalars f).obj (of _ S) ->ₗ[R] M
  body: { CoextendScalars.distribMulAction f _ with
    add_smul := fun s1 s2 g => LinearMap.ext fun x : S => by simp [mul_add, map_add]
    zero_smul := fun g => LinearMap.ext fun x : S => by simp [map_zero] }

中文:
实例 isModule
  签名: : 模 S (restrictScalars f).obj (of _ S) ->ₗ[R] M
  定义体: { CoextendScalars.distribMulAction f _ with
    add_smul := fun s1 s2 g => LinearMap.ext fun x : S => by simp [mul_add, map_add]
    zero_smul := fun g => LinearMap.ext fun x : S => by simp [map_zero] }

Depends on / 依赖: CoextendScalars, CoextendScalars.distribMulAction, LinearMap, LinearMap.ext, add_smul, distribMulAction, map_add, map_zero, mul_add, zero_smul
-/
instance isModule : Module S (restrictScalars f).obj (of _ S) ->ₗ[R] M :=
  { CoextendScalars.distribMulAction f _ with
    add_smul := fun s1 s2 g => LinearMap.ext fun x : S => by simp [mul_add, map_add]
    zero_smul := fun g => LinearMap.ext fun x : S => by simp [map_zero] }

end Unbundled

variable (M : ModuleCat.{v} R)

/--
Definition of `obj'` / `obj'` 的定义

English:
definition obj'
  signature: : ModuleCat S
  body: of _ ((restrictScalars f).obj (of _ S) ->ₗ[R] M)

中文:
定义 obj'
  签名: : 模范畴 S
  定义体: of _ ((restrictScalars f).obj (of _ S) ->ₗ[R] M)

Depends on / 依赖: restrictScalars
-/
def obj' : ModuleCat S :=
  of _ ((restrictScalars f).obj (of _ S) ->ₗ[R] M)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h` -/
@[simps!]
/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: {M M' : ModuleCat R} (g : M ⟶ M')
  body: ofHom
  { toFun := fun h => g.hom.comp h
    map_add' := fun _ _ => LinearMap.comp_add _ _ _
    map_smul' := fun s h => by ext; simp }

中文:
定义 map'
  签名: {M M' : 模范畴 R} (g : M ⟶ M')
  定义体: ofHom
  { toFun := fun h => g.hom.comp h
    map_add' := fun _ _ => LinearMap.comp_add _ _ _
    map_smul' := fun s h => by ext; simp }

Depends on / 依赖: LinearMap, LinearMap.comp_add, comp_add, g.hom.comp, map_add, map_smul
-/
def map' {M M' : ModuleCat R} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  ofHom
  { toFun := fun h => g.hom.comp h
    map_add' := fun _ _ => LinearMap.comp_add _ _ _
    map_smul' := fun s h => by ext; simp }

end CoextendScalars

/--
Definition of `coextendScalars` / `coextendScalars` 的定义

English:
definition coextendScalars
  signature: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  body: CoextendScalars.obj' f
  map := CoextendScalars.map' f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

中文:
定义 coextendScalars
  签名: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  定义体: CoextendScalars.obj' f
  map := CoextendScalars.map' f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

Depends on / 依赖: CoextendScalars, CoextendScalars.obj
-/
def coextendScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    ModuleCat R ⥤ ModuleCat S where
  obj := CoextendScalars.obj' f
  map := CoextendScalars.map' f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (M : ModuleCat R)
  body: f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 equiv
  签名: (M : 模范畴 R)
  定义体: f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def equiv (M : ModuleCat R) :
    (coextendScalars f).obj M ≃ₗ[S] ((restrictScalars f).obj (of _ S) ->ₗ[R] M) where
  toFun f := f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance (M : ModuleCat R) : CoeFun ((coextendScalars f).obj M) fun _ => S -> M where
  coe g := equiv f M g

variable {f} in
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {M : ModuleCat R} {g g' : (coextendScalars f).obj M}
  proof: (CoextendScalars.equiv f M).injective h

中文:
引理 ext
  结论: {M : 模范畴 R} {g g' : (coextendScalars f).obj M}
  证明: (CoextendScalars.equiv f M).injective h
-/
@[ext] lemma ext {M : ModuleCat R} {g g' : (coextendScalars f).obj M}
    (h : CoextendScalars.equiv f M g = CoextendScalars.equiv f M g') :
    g = g' := (CoextendScalars.equiv f M).injective h

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S)
  proof: rfl

@[simp]

中文:
定理 smul_apply
  条件: (M : 模范畴 R) (g : (coextendScalars f).obj M) (s s' : S)
  证明: rfl

@[simp]
-/
theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
    (s • g) s' = g (s' * s) :=
  rfl

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S)
  proof: rfl

中文:
定理 map_apply
  条件: {M M' : 模范畴 R} (g : M ⟶ M') (x) (s : S)
  证明: rfl
-/
theorem map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) :
    (coextendScalars f).map g x s = g (x s) :=
  rfl

end CoextendScalars

namespace RestrictionCoextensionAdj

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `HomEquiv.fromRestriction` / `HomEquiv.fromRestriction` 的定义

English:
definition HomEquiv.fromRestriction
  signature: {X : ModuleCat R} {Y : ModuleCat S}
  body: ofHom
  { toFun := fun y : Y => (CoextendScalars.equiv _ _).symm
      { toFun := fun s : S => g <| (s • y : Y)
        map_add' := fun s1 s2 : S => by simp [add_smul]
        map_smul' := fun r (s : S) => by
          rw [← g.hom.map_smul]
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
map_add' (y1 y2 : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun s : S => by simp
map_smul' (s : S) (y : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun t : S => by simp [mul_smul] }

中文:
定义 态射等价.fromRestriction
  签名: {X : 模范畴 R} {Y : 模范畴 S}
  定义体: ofHom
  { toFun := fun y : Y => (CoextendScalars.equiv _ _).symm
      { toFun := fun s : S => g <| (s • y : Y)
        map_add' := fun s1 s2 : S => by simp [add_smul]
        map_smul' := fun r (s : S) => by
          rw [← g.hom.map_smul]
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
map_add' (y1 y2 : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun s : S => by simp
map_smul' (s : S) (y : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun t : S => by simp [mul_smul] }

Depends on / 依赖: CoextendScalars, CoextendScalars.equiv, LinearMap, LinearMap.ext, ModuleCat, ModuleCat.of, ModuleCat.restrictScalars.smul_def, add_smul, g.hom.map_smul, injective, map_add, map_smul, mul_smul, restrictScalars, smul_def
-/
def HomEquiv.fromRestriction {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) : Y ⟶ (coextendScalars f).obj X :=
  ofHom
  { toFun := fun y : Y => (CoextendScalars.equiv _ _).symm
      { toFun := fun s : S => g <| (s • y : Y)
        map_add' := fun s1 s2 : S => by simp [add_smul]
        map_smul' := fun r (s : S) => by
          rw [← g.hom.map_smul]
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
map_add' (y1 y2 : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun s : S => by simp
map_smul' (s : S) (y : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun t : S => by simp [mul_smul] }

/--
lemma `HomEquiv.fromRestriction_hom_apply_apply` / 引理 `HomEquiv.fromRestriction_hom_apply_apply`

English:
lemma HomEquiv.fromRestriction_hom_apply_apply
  statement: {X : ModuleCat R} {Y : ModuleCat S}
  proof: rfl

中文:
引理 态射等价.fromRestriction_hom_apply_apply
  结论: {X : 模范畴 R} {Y : 模范畴 S}
  证明: rfl
-/
@[simp] lemma HomEquiv.fromRestriction_hom_apply_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) (y) (s : S) :
    (HomEquiv.fromRestriction f g).hom y s = g (s • y) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `HomEquiv.toRestriction` / `HomEquiv.toRestriction` 的定义

English:
definition HomEquiv.toRestriction
  signature: {X : ModuleCat R} {Y : ModuleCat S} (g : Y ⟶ (coextendScalars f).obj X)
  body: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (X := (restrictScalars f).obj Y)
  { toFun y := (g y) (1 : S)
    map_add' x y := by simp
    map_smul' r (y : Y) := by
      rw [← map_smul]
      simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S)] }

中文:
定义 态射等价.toRestriction
  签名: {X : 模范畴 R} {Y : 模范畴 S} (g : Y ⟶ (coextendScalars f).obj X)
  定义体: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (X := (restrictScalars f).obj Y)
  { toFun y := (g y) (1 : S)
    map_add' x y := by simp
    map_smul' r (y : Y) := by
      rw [← map_smul]
      simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S)] }
-/
def HomEquiv.toRestriction {X : ModuleCat R} {Y : ModuleCat S} (g : Y ⟶ (coextendScalars f).obj X) :
    (restrictScalars f).obj Y ⟶ X :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (X := (restrictScalars f).obj Y)
  { toFun y := (g y) (1 : S)
    map_add' x y := by simp
    map_smul' r (y : Y) := by
      rw [← map_smul]
      simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S)] }

/--
lemma `HomEquiv.toRestriction_hom_apply` / 引理 `HomEquiv.toRestriction_hom_apply`

English:
lemma HomEquiv.toRestriction_hom_apply
  statement: {X : ModuleCat R} {Y : ModuleCat S}
  proof: rfl

中文:
引理 态射等价.toRestriction_hom_apply
  结论: {X : 模范畴 R} {Y : 模范畴 S}
  证明: rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, GrpCat
-/
@[simp] lemma HomEquiv.toRestriction_hom_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : Y ⟶ (coextendScalars f).obj X) (y) :
    (HomEquiv.toRestriction f g).hom y = g.hom y (1 : S) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `app'` / `app'` 的定义

English:
definition app'
  signature: (Y : ModuleCat S)
  body: { toFun y := (CoextendScalars.equiv _ _).symm
      { toFun (s : S) := s • y
        map_add' _ _ := add_smul _ _ _
        map_smul' r (s : S) := by
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
map_add' y1 y2 := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun s : S => by
        simp [smul_add]
map_smul' s (y : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun t : S => by
        simp [mul_smul] }

中文:
定义 app'
  签名: (Y : 模范畴 S)
  定义体: { toFun y := (CoextendScalars.equiv _ _).symm
      { toFun (s : S) := s • y
        map_add' _ _ := add_smul _ _ _
        map_smul' r (s : S) := by
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
map_add' y1 y2 := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun s : S => by
        simp [smul_add]
map_smul' s (y : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun t : S => by
        simp [mul_smul] }

Depends on / 依赖: CoextendScalars, CoextendScalars.equiv, LinearMap, LinearMap.ext, ModuleCat, ModuleCat.of, ModuleCat.restrictScalars.smul_def, add_smul, injective, map_add, map_smul, mul_smul, restrictScalars, smul_add, smul_def
-/
def app' (Y : ModuleCat S) : Y ->ₗ[S] (restrictScalars f ⋙ coextendScalars f).obj Y :=
  { toFun y := (CoextendScalars.equiv _ _).symm
      { toFun (s : S) := s • y
        map_add' _ _ := add_smul _ _ _
        map_smul' r (s : S) := by
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
map_add' y1 y2 := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun s : S => by
        simp [smul_add]
map_smul' s (y : Y) := (CoextendScalars.equiv _ _).injective
      LinearMap.ext fun t : S => by
        simp [mul_smul] }

/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def unit'
  body: ofHom (app' f Y)
  naturality Y Y' g :=
hom_ext LinearMap.ext fun y : Y => CoextendScalars.ext LinearMap.ext fun s : S => by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): previously simp [CoextendScalars.map_apply]
      simp only [Functor.id_map, Functor.id_obj, Functor.comp_map]
      change s • (g y) = g (s • y)
      rw [map_smul]

中文:
定义 noncomputable
  签名: def unit'
  定义体: ofHom (app' f Y)
  naturality Y Y' g :=
hom_ext LinearMap.ext fun y : Y => CoextendScalars.ext LinearMap.ext fun s : S => by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): previously simp [CoextendScalars.map_apply]
      simp only [Functor.id_map, Functor.id_obj, Functor.comp_map]
      change s • (g y) = g (s • y)
      rw [map_smul]

Depends on / 依赖: f.hom
-/
protected noncomputable def unit' : 𝟭 (ModuleCat S) ⟶ restrictScalars f ⋙ coextendScalars f where
  app Y := ofHom (app' f Y)
  naturality Y Y' g :=
hom_ext LinearMap.ext fun y : Y => CoextendScalars.ext LinearMap.ext fun s : S => by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): previously simp [CoextendScalars.map_apply]
      simp only [Functor.id_map, Functor.id_obj, Functor.comp_map]
      change s • (g y) = g (s • y)
      rw [map_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def counit'
  body: ofHom (X := (restrictScalars f).obj ((coextendScalars f).obj X))
    { toFun g := CoextendScalars.equiv f X g (1 : S)
      map_add' x1 x2 := by simp
      map_smul' r g := by
        dsimp
        rw [CoextendScalars.smul_apply]; rw [one_mul]; rw [← map_smul]
        congr
        change f r = f r • (1 : S)
        simp }

中文:
定义 noncomputable
  签名: def counit'
  定义体: ofHom (X := (restrictScalars f).obj ((coextendScalars f).obj X))
    { toFun g := CoextendScalars.equiv f X g (1 : S)
      map_add' x1 x2 := by simp
      map_smul' r g := by
        dsimp
        rw [CoextendScalars.smul_apply]; rw [one_mul]; rw [← map_smul]
        congr
        change f r = f r • (1 : S)
        simp }
-/
protected noncomputable def counit' : coextendScalars f ⋙ restrictScalars f ⟶ 𝟭 (ModuleCat R) where
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  app X := ofHom (X := (restrictScalars f).obj ((coextendScalars f).obj X))
    { toFun g := CoextendScalars.equiv f X g (1 : S)
      map_add' x1 x2 := by simp
      map_smul' r g := by
        dsimp
        rw [CoextendScalars.smul_apply]; rw [one_mul]; rw [← map_smul]
        congr
        change f r = f r • (1 : S)
        simp }

end RestrictionCoextensionAdj

set_option backward.isDefEq.respectTransparency false in
-- Porting note: very fiddly universes
-- @[simps] Porting note: not in normal form and not used
/--
Definition of `restrictCoextendScalarsAdj` / `restrictCoextendScalarsAdj` 的定义

English:
definition restrictCoextendScalarsAdj
  signature: {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S)
  body: Adjunction.mk' {
    homEquiv := fun X Y =>
      { toFun := RestrictionCoextensionAdj.HomEquiv.fromRestriction.{u₁, u₂, v} f
        invFun := RestrictionCoextensionAdj.HomEquiv.toRestriction.{u₁, u₂, v} f
        left_inv g := by ext; simp
        right_inv g := by ext; simp }
    unit := RestrictionCoextensionAdj.unit'.{u₁, u₂, v} f
    counit := RestrictionCoextensionAdj.counit'.{u₁, u₂, v} f
homEquiv_unit := hom_ext LinearMap.ext fun _ => rfl
    homEquiv_counit {X Y g} := by
      ext
      simp [RestrictionCoextensionAdj.counit'] }

中文:
定义 restrictCoextendScalarsAdj
  签名: {R : 类型u₁} {S : 类型u₂} [环 R] [环 S] (f : R ->+* S)
  定义体: Adjunction.mk' {
    homEquiv := fun X Y =>
      { toFun := RestrictionCoextensionAdj.HomEquiv.fromRestriction.{u₁, u₂, v} f
        invFun := RestrictionCoextensionAdj.HomEquiv.toRestriction.{u₁, u₂, v} f
        left_inv g := by ext; simp
        right_inv g := by ext; simp }
    unit := RestrictionCoextensionAdj.unit'.{u₁, u₂, v} f
    counit := RestrictionCoextensionAdj.counit'.{u₁, u₂, v} f
homEquiv_unit := hom_ext LinearMap.ext fun _ => rfl
    homEquiv_counit {X Y g} := by
      ext
      simp [RestrictionCoextensionAdj.counit'] }

Depends on / 依赖: Adjunction, Adjunction.mk, HomEquiv, LinearMap, LinearMap.ext, RestrictionCoextensionAdj, RestrictionCoextensionAdj.HomEquiv.fromRestriction, RestrictionCoextensionAdj.HomEquiv.toRestriction, RestrictionCoextensionAdj.counit, RestrictionCoextensionAdj.unit, counit, fromRestriction, homEquiv, homEquiv_counit, homEquiv_unit, hom_ext, invFun, left_inv, right_inv, toRestriction
-/
def restrictCoextendScalarsAdj {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    restrictScalars.{max v u₂, u₁, u₂} f ⊣ coextendScalars f :=
  Adjunction.mk' {
    homEquiv := fun X Y =>
      { toFun := RestrictionCoextensionAdj.HomEquiv.fromRestriction.{u₁, u₂, v} f
        invFun := RestrictionCoextensionAdj.HomEquiv.toRestriction.{u₁, u₂, v} f
        left_inv g := by ext; simp
        right_inv g := by ext; simp }
    unit := RestrictionCoextensionAdj.unit'.{u₁, u₂, v} f
    counit := RestrictionCoextensionAdj.counit'.{u₁, u₂, v} f
homEquiv_unit := hom_ext LinearMap.ext fun _ => rfl
    homEquiv_counit {X Y g} := by
      ext
      simp [RestrictionCoextensionAdj.counit'] }

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    (restrictScalars.{max u₂ w} f).IsLeftAdjoint :=
  (restrictCoextendScalarsAdj f).isLeftAdjoint

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* S) :
    (coextendScalars.{u₁, u₂, max u₂ w} f).IsRightAdjoint :=
  (restrictCoextendScalarsAdj f).isRightAdjoint

namespace ExtendRestrictScalarsAdj

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S)

set_option backward.isDefEq.respectTransparency false in
/--
Given `R`-module X and `S`-module Y and a map `g : (extendScalars f).obj X ⟶ Y`, i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrictScalars f).obj Y`, i.e. `R`-linear map `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
@[simps! hom_apply]
/--
Definition of `HomEquiv.toRestrictScalars` / `HomEquiv.toRestrictScalars` 的定义

English:
definition HomEquiv.toRestrictScalars
  signature: {X : ModuleCat R} {Y : ModuleCat S}
  body: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (restrictScalars f).obj Y)
  { toFun := fun x => g <| (1 : S) otimesₜ[R,f] x
    map_add' := fun _ _ => by dsimp; rw [tmul_add, map_add]
    map_smul' := fun r s => by
      dsimp
      rw [RestrictScalars.smul_def]; rw [← LinearMap.map_smul]
      erw [tmul_smul]
      congr }

中文:
定义 态射等价.toRestrictScalars
  签名: {X : 模范畴 R} {Y : 模范畴 S}
  定义体: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (restrictScalars f).obj Y)
  { toFun := fun x => g <| (1 : S) otimesₜ[R,f] x
    map_add' := fun _ _ => by dsimp; rw [tmul_add, map_add]
    map_smul' := fun r s => by
      dsimp
      rw [RestrictScalars.smul_def]; rw [← LinearMap.map_smul]
      erw [tmul_smul]
      congr }
-/
def HomEquiv.toRestrictScalars {X : ModuleCat R} {Y : ModuleCat S}
    (g : (extendScalars f).obj X ⟶ Y) :
    X ⟶ (restrictScalars f).obj Y :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (restrictScalars f).obj Y)
  { toFun := fun x => g <| (1 : S) otimesₜ[R,f] x
    map_add' := fun _ _ => by dsimp; rw [tmul_add, map_add]
    map_smul' := fun r s => by
      dsimp
      rw [RestrictScalars.smul_def]; rw [← LinearMap.map_smul]
      erw [tmul_smul]
      congr }

set_option backward.isDefEq.respectTransparency false in
-- Porting note: forced to break apart fromExtendScalars due to timeouts
/--
The map `S → X →ₗ[R] Y` given by `fun s x => s • (g x)`
-/
@[simps]
/--
Definition of `HomEquiv.evalAt` / `HomEquiv.evalAt` 的定义

English:
definition HomEquiv.evalAt
  signature: {X : ModuleCat R} {Y : ModuleCat S} (s : S)
  body: Module.compHom Y f
    X ->ₗ[R] Y :=
  @LinearMap.mk _ _ _ _ (RingHom.id R) X Y _ _ _ (_)
    { toFun := fun x => s • (g x : Y)
      map_add' := by
        intros
        dsimp only
        rw [map_add]; rw [smul_add] }
    (by
      intro r x
      rw [AddHom.toFun_eq_coe]; rw [AddHom.coe_mk]; rw [RingHom.id_apply]; rw [map_smul]; rw [smul_comm r s (g x : Y)])

中文:
定义 态射等价.evalAt
  签名: {X : 模范畴 R} {Y : 模范畴 S} (s : S)
  定义体: Module.compHom Y f
    X ->ₗ[R] Y :=
  @LinearMap.mk _ _ _ _ (RingHom.id R) X Y _ _ _ (_)
    { toFun := fun x => s • (g x : Y)
      map_add' := by
        intros
        dsimp only
        rw [map_add]; rw [smul_add] }
    (by
      intro r x
      rw [AddHom.toFun_eq_coe]; rw [AddHom.coe_mk]; rw [RingHom.id_apply]; rw [map_smul]; rw [smul_comm r s (g x : Y)])

Depends on / 依赖: Module, Module.compHom, compHom
-/
def HomEquiv.evalAt {X : ModuleCat R} {Y : ModuleCat S} (s : S)
    (g : X ⟶ (restrictScalars f).obj Y) : have : Module R Y := Module.compHom Y f
    X ->ₗ[R] Y :=
  @LinearMap.mk _ _ _ _ (RingHom.id R) X Y _ _ _ (_)
    { toFun := fun x => s • (g x : Y)
      map_add' := by
        intros
        dsimp only
        rw [map_add]; rw [smul_add] }
    (by
      intro r x
      rw [AddHom.toFun_eq_coe]; rw [AddHom.coe_mk]; rw [RingHom.id_apply]; rw [map_smul]; rw [smul_comm r s (g x : Y)])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrictScalars f).obj Y`, i.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e `S`-linear map `S ⨂ X → Y` by
`s ⊗ x ↦ s • g x`.
-/
@[simps! hom_apply]
/--
Definition of `HomEquiv.fromExtendScalars` / `HomEquiv.fromExtendScalars` 的定义

English:
definition HomEquiv.fromExtendScalars
  signature: {X : ModuleCat R} {Y : ModuleCat S}
  body: by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine ofHom
    { toFun z := TensorProduct.lift (σ₁₂ := .id _) ?_ z, map_add' := ?_, map_smul' := ?_ }
  · refine
    { toFun s := HomEquiv.evalAt f s g, map_add' := fun (s₁ s₂ : S) => ?_,
      map_smul' := fun (r : R) (s : S) => ?_ }
    · ext
      dsimp only [m2, evalAt_apply, LinearMap.add_apply]
      rw [← add_smul]
    · ext x
      apply mul_smul (f r) s (g x)
  · simp
  · intro s z
    change lift _ (s • z) = s • lift _ z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x => simp [mul_smul]
    | add _ _ ih1 ih2 => rw [smul_add, map_add, ih1, ih2, map_add, smul_add]

中文:
定义 态射等价.fromExtendScalars
  签名: {X : 模范畴 R} {Y : 模范畴 S}
  定义体: by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine ofHom
    { toFun z := TensorProduct.lift (σ₁₂ := .id _) ?_ z, map_add' := ?_, map_smul' := ?_ }
  · refine
    { toFun s := HomEquiv.evalAt f s g, map_add' := fun (s₁ s₂ : S) => ?_,
      map_smul' := fun (r : R) (s : S) => ?_ }
    · ext
      dsimp only [m2, evalAt_apply, LinearMap.add_apply]
      rw [← add_smul]
    · ext x
      apply mul_smul (f r) s (g x)
  · simp
  · intro s z
    change lift _ (s • z) = s • lift _ z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x => simp [mul_smul]
    | add _ _ ih1 ih2 => rw [smul_add, map_add, ih1, ih2, map_add, smul_add]

Depends on / 依赖: HomEquiv, HomEquiv.evalAt, LinearMap, LinearMap.add_apply, Module, Module.compHom, TensorProduct, TensorProduct.lift, add_apply, add_smul, compHom, evalAt, evalAt_apply, map_add, map_smul, mul_smul
-/
def HomEquiv.fromExtendScalars {X : ModuleCat R} {Y : ModuleCat S}
    (g : X ⟶ (restrictScalars f).obj Y) :
    (extendScalars f).obj X ⟶ Y := by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine ofHom
    { toFun z := TensorProduct.lift (σ₁₂ := .id _) ?_ z, map_add' := ?_, map_smul' := ?_ }
  · refine
    { toFun s := HomEquiv.evalAt f s g, map_add' := fun (s₁ s₂ : S) => ?_,
      map_smul' := fun (r : R) (s : S) => ?_ }
    · ext
      dsimp only [m2, evalAt_apply, LinearMap.add_apply]
      rw [← add_smul]
    · ext x
      apply mul_smul (f r) s (g x)
  · simp
  · intro s z
    change lift _ (s • z) = s • lift _ z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x => simp [mul_smul]
    | add _ _ ih1 ih2 => rw [smul_add, map_add, ih1, ih2, map_add, smul_add]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-module X and `S`-module Y, `S`-linear maps `(extendScalars f).obj X ⟶ Y`
bijectively correspond to `R`-linear maps `X ⟶ (restrictScalars f).obj Y`.
-/
@[simps symm_apply]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {X : ModuleCat R} {Y : ModuleCat S}
  body: HomEquiv.toRestrictScalars.{u₁, u₂, v} f
  invFun := HomEquiv.fromExtendScalars.{u₁, u₂, v} f
  left_inv g := by
    let m1 : Module R S := Module.compHom S f; let m2 : Module R Y := Module.compHom Y f
    apply hom_ext
    apply LinearMap.ext; intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x s =>
      erw [TensorProduct.lift.tmul]
      simp only [LinearMap.coe_mk]
      change S at x
      dsimp
      erw [← map_smul, ExtendScalars.smul_tmul, mul_one x]
      rfl
    | add _ _ ih1 ih2 => rw [map_add, map_add, ih1, ih2]
  right_inv g := by
    let m1 : Module R S := Module.compHom S f; let m2 : Module R Y := Module.compHom Y f
    ext x
    rw [HomEquiv.toRestrictScalars_hom_apply]
    -- This needs to be `erw` because of some unfolding in `fromExtendScalars`
    erw [HomEquiv.fromExtendScalars_hom_apply]
    rw [lift.tmul]; rw [LinearMap.coe_mk]; rw [LinearMap.coe_mk]
    dsimp
    rw [one_smul]

中文:
定义 homEquiv
  签名: {X : 模范畴 R} {Y : 模范畴 S}
  定义体: HomEquiv.toRestrictScalars.{u₁, u₂, v} f
  invFun := HomEquiv.fromExtendScalars.{u₁, u₂, v} f
  left_inv g := by
    let m1 : Module R S := Module.compHom S f; let m2 : Module R Y := Module.compHom Y f
    apply hom_ext
    apply LinearMap.ext; intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x s =>
      erw [TensorProduct.lift.tmul]
      simp only [LinearMap.coe_mk]
      change S at x
      dsimp
      erw [← map_smul, ExtendScalars.smul_tmul, mul_one x]
      rfl
    | add _ _ ih1 ih2 => rw [map_add, map_add, ih1, ih2]
  right_inv g := by
    let m1 : Module R S := Module.compHom S f; let m2 : Module R Y := Module.compHom Y f
    ext x
    rw [HomEquiv.toRestrictScalars_hom_apply]
    -- This needs to be `erw` because of some unfolding in `fromExtendScalars`
    erw [HomEquiv.fromExtendScalars_hom_apply]
    rw [lift.tmul]; rw [LinearMap.coe_mk]; rw [LinearMap.coe_mk]
    dsimp
    rw [one_smul]

Depends on / 依赖: HomEquiv, HomEquiv.toRestrictScalars, toRestrictScalars
-/
def homEquiv {X : ModuleCat R} {Y : ModuleCat S} :
    ((extendScalars f).obj X ⟶ Y) ≃ (X ⟶ (restrictScalars.{max v u₂, u₁, u₂} f).obj Y) where
  toFun := HomEquiv.toRestrictScalars.{u₁, u₂, v} f
  invFun := HomEquiv.fromExtendScalars.{u₁, u₂, v} f
  left_inv g := by
    let m1 : Module R S := Module.compHom S f; let m2 : Module R Y := Module.compHom Y f
    apply hom_ext
    apply LinearMap.ext; intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x s =>
      erw [TensorProduct.lift.tmul]
      simp only [LinearMap.coe_mk]
      change S at x
      dsimp
      erw [← map_smul, ExtendScalars.smul_tmul, mul_one x]
      rfl
    | add _ _ ih1 ih2 => rw [map_add, map_add, ih1, ih2]
  right_inv g := by
    let m1 : Module R S := Module.compHom S f; let m2 : Module R Y := Module.compHom Y f
    ext x
    rw [HomEquiv.toRestrictScalars_hom_apply]
    -- This needs to be `erw` because of some unfolding in `fromExtendScalars`
    erw [HomEquiv.fromExtendScalars_hom_apply]
    rw [lift.tmul]; rw [LinearMap.coe_mk]; rw [LinearMap.coe_mk]
    dsimp
    rw [one_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- @[simps] Porting note: not in normal form and not used
/--
Definition of `Unit.map` / `Unit.map` 的定义

English:
definition Unit.map
  signature: {X : ModuleCat R}
  body: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (extendScalars f ⋙ restrictScalars f).obj X)
  { toFun := fun x => (1 : S) otimesₜ[R,f] x
    map_add' := fun x x' => by dsimp; rw [TensorProduct.tmul_add]
    map_smul' := fun r x => by
      let m1 : Module R S := Module.compHom S f
      dsimp; rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul'] }

中文:
定义 单元.map
  签名: {X : 模范畴 R}
  定义体: -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (extendScalars f ⋙ restrictScalars f).obj X)
  { toFun := fun x => (1 : S) otimesₜ[R,f] x
    map_add' := fun x x' => by dsimp; rw [TensorProduct.tmul_add]
    map_smul' := fun r x => by
      let m1 : Module R S := Module.compHom S f
      dsimp; rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul'] }
-/
def Unit.map {X : ModuleCat R} : X ⟶ (extendScalars f ⋙ restrictScalars f).obj X :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (extendScalars f ⋙ restrictScalars f).obj X)
  { toFun := fun x => (1 : S) otimesₜ[R,f] x
    map_add' := fun x x' => by dsimp; rw [TensorProduct.tmul_add]
    map_smul' := fun r x => by
      let m1 : Module R S := Module.compHom S f
      dsimp; rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul'] }

/--
The natural transformation from identity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
@[simps]
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars.{max v u₂, u₁, u₂} f where
  body: Unit.map.{u₁, u₂, v} f

中文:
定义 unit
  签名: : 𝟭 (模范畴 R) ⟶ extendScalars f ⋙ restrictScalars.{最大值 v u₂, u₁, u₂} f where
  定义体: Unit.map.{u₁, u₂, v} f

Depends on / 依赖: Unit.map
-/
def unit : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars.{max v u₂, u₁, u₂} f where
  app _ := Unit.map.{u₁, u₂, v} f

set_option backward.isDefEq.respectTransparency false in
/-- For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y` -/
@[simps! hom_apply]
/--
Definition of `Counit.map` / `Counit.map` 的定义

English:
definition Counit.map
  signature: {Y : ModuleCat S}
  body: ofHom
  { toFun :=
      letI m1 : Module R S := Module.compHom S f
      letI m2 : Module R Y := Module.compHom Y f
      TensorProduct.lift (σ₁₂ := .id R)
      { toFun := fun s : S =>
        { toFun := fun y : Y => s • y,
          map_add' := smul_add _
          map_smul' := fun r y => by
            change s • f r • y = f r • s • y
            rw [← mul_smul]; rw [mul_comm]; rw [mul_smul] },
        map_add' := fun s₁ s₂ => by
          ext y
          change (s₁ + s₂) • y = s₁ • y + s₂ • y
          rw [add_smul]
        map_smul' := fun r s => by
          ext y
          change (f r • s) • y = (f r) • s • y
          rw [smul_eq_mul]; rw [mul_smul] }
    map_add' := fun _ _ => by rw [map_add]
    map_smul' := fun s z => by
      let m1 : Module R S := Module.compHom S f
      let m2 : Module R Y := Module.compHom Y f
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s' y => simp [mul_smul]
      | add _ _ ih1 ih2 => rw [smul_add, map_add, map_add, ih1, ih2, smul_add] }

中文:
定义 Counit.map
  签名: {Y : 模范畴 S}
  定义体: ofHom
  { toFun :=
      letI m1 : Module R S := Module.compHom S f
      letI m2 : Module R Y := Module.compHom Y f
      TensorProduct.lift (σ₁₂ := .id R)
      { toFun := fun s : S =>
        { toFun := fun y : Y => s • y,
          map_add' := smul_add _
          map_smul' := fun r y => by
            change s • f r • y = f r • s • y
            rw [← mul_smul]; rw [mul_comm]; rw [mul_smul] },
        map_add' := fun s₁ s₂ => by
          ext y
          change (s₁ + s₂) • y = s₁ • y + s₂ • y
          rw [add_smul]
        map_smul' := fun r s => by
          ext y
          change (f r • s) • y = (f r) • s • y
          rw [smul_eq_mul]; rw [mul_smul] }
    map_add' := fun _ _ => by rw [map_add]
    map_smul' := fun s z => by
      let m1 : Module R S := Module.compHom S f
      let m2 : Module R Y := Module.compHom Y f
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s' y => simp [mul_smul]
      | add _ _ ih1 ih2 => rw [smul_add, map_add, map_add, ih1, ih2, smul_add] }

Depends on / 依赖: Module, Module.compHom, TensorProduct, TensorProduct.lift, add_smul, compHom, map_add, map_smul, mul_comm, mul_smul, smul_add, smul_eq_mul
-/
def Counit.map {Y : ModuleCat S} : (restrictScalars f ⋙ extendScalars f).obj Y ⟶ Y :=
  ofHom
  { toFun :=
      letI m1 : Module R S := Module.compHom S f
      letI m2 : Module R Y := Module.compHom Y f
      TensorProduct.lift (σ₁₂ := .id R)
      { toFun := fun s : S =>
        { toFun := fun y : Y => s • y,
          map_add' := smul_add _
          map_smul' := fun r y => by
            change s • f r • y = f r • s • y
            rw [← mul_smul]; rw [mul_comm]; rw [mul_smul] },
        map_add' := fun s₁ s₂ => by
          ext y
          change (s₁ + s₂) • y = s₁ • y + s₂ • y
          rw [add_smul]
        map_smul' := fun r s => by
          ext y
          change (f r • s) • y = (f r) • s • y
          rw [smul_eq_mul]; rw [mul_smul] }
    map_add' := fun _ _ => by rw [map_add]
    map_smul' := fun s z => by
      let m1 : Module R S := Module.compHom S f
      let m2 : Module R Y := Module.compHom Y f
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s' y => simp [mul_smul]
      | add _ _ ih1 ih2 => rw [smul_add, map_add, map_add, ih1, ih2, smul_add] }

/--
lemma `Counit.map_apply_one_tmul` / 引理 `Counit.map_apply_one_tmul`

English:
lemma Counit.map_apply_one_tmul
  given: {Y : ModuleCat S} (y : Y)
  proof: by
  change (1 : S) • y = y
  simp

中文:
引理 Counit.map_apply_one_tmul
  条件: {Y : 模范畴 S} (y : Y)
  证明: by
  change (1 : S) • y = y
  simp
-/
lemma Counit.map_apply_one_tmul {Y : ModuleCat S} (y : Y) :
    Counit.map f ((1 : S) otimesₜ[R] y) = y := by
  change (1 : S) • y = y
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps app]
/--
Definition of `counit` / `counit` 的定义

English:
definition counit
  signature: : restrictScalars.{max v u₂, u₁, u₂} f ⋙ extendScalars f ⟶ 𝟭 (ModuleCat S) where
  body: Counit.map.{u₁, u₂, v} f
  naturality Y Y' g := by
    -- Porting note: this is very annoying; fix instances in concrete categories
    let m1 : Module R S := Module.compHom S f
    let m2 : Module R Y := Module.compHom Y f
    let m2 : Module R Y' := Module.compHom Y' f
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s' y =>
      dsimp
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [Counit.map_hom_apply]
      rw [lift.tmul]; rw [LinearMap.coe_mk]; rw [LinearMap.coe_mk]
      set s' : S := s'
      change s' • g y = g (s' • y)
      rw [map_smul]
    | add _ _ ih₁ ih₂ => rw [map_add, map_add]; congr 1

中文:
定义 counit
  签名: : restrictScalars.{最大值 v u₂, u₁, u₂} f ⋙ extendScalars f ⟶ 𝟭 (模范畴 S) where
  定义体: Counit.map.{u₁, u₂, v} f
  naturality Y Y' g := by
    -- Porting note: this is very annoying; fix instances in concrete categories
    let m1 : Module R S := Module.compHom S f
    let m2 : Module R Y := Module.compHom Y f
    let m2 : Module R Y' := Module.compHom Y' f
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s' y =>
      dsimp
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [Counit.map_hom_apply]
      rw [lift.tmul]; rw [LinearMap.coe_mk]; rw [LinearMap.coe_mk]
      set s' : S := s'
      change s' • g y = g (s' • y)
      rw [map_smul]
    | add _ _ ih₁ ih₂ => rw [map_add, map_add]; congr 1

Depends on / 依赖: Counit, Counit.map
-/
def counit : restrictScalars.{max v u₂, u₁, u₂} f ⋙ extendScalars f ⟶ 𝟭 (ModuleCat S) where
  app _ := Counit.map.{u₁, u₂, v} f
  naturality Y Y' g := by
    -- Porting note: this is very annoying; fix instances in concrete categories
    let m1 : Module R S := Module.compHom S f
    let m2 : Module R Y := Module.compHom Y f
    let m2 : Module R Y' := Module.compHom Y' f
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s' y =>
      dsimp
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [Counit.map_hom_apply]
      rw [lift.tmul]; rw [LinearMap.coe_mk]; rw [LinearMap.coe_mk]
      set s' : S := s'
      change s' • g y = g (s' • y)
      rw [map_smul]
    | add _ _ ih₁ ih₂ => rw [map_add, map_add]; congr 1
end ExtendRestrictScalarsAdj

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `extendRestrictScalarsAdj` / `extendRestrictScalarsAdj` 的定义

English:
definition extendRestrictScalarsAdj
  signature: {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S)
  body: Adjunction.mk' {
    homEquiv := fun _ _ => ExtendRestrictScalarsAdj.homEquiv.{v, u₁, u₂} f
    unit := ExtendRestrictScalarsAdj.unit.{v, u₁, u₂} f
    counit := ExtendRestrictScalarsAdj.counit.{v, u₁, u₂} f
homEquiv_unit := fun {X Y g} => hom_ext LinearMap.ext fun x => by
      dsimp
      rfl
homEquiv_counit := fun {X Y g} => hom_ext LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul =>
          rw [ExtendRestrictScalarsAdj.homEquiv_symm_apply]
          dsimp
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [ExtendRestrictScalarsAdj.Counit.map_hom_apply,
              ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
        | add => rw [map_add, map_add]; congr 1 }

中文:
定义 extendRestrictScalarsAdj
  签名: {R : 类型u₁} {S : 类型u₂} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: Adjunction.mk' {
    homEquiv := fun _ _ => ExtendRestrictScalarsAdj.homEquiv.{v, u₁, u₂} f
    unit := ExtendRestrictScalarsAdj.unit.{v, u₁, u₂} f
    counit := ExtendRestrictScalarsAdj.counit.{v, u₁, u₂} f
homEquiv_unit := fun {X Y g} => hom_ext LinearMap.ext fun x => by
      dsimp
      rfl
homEquiv_counit := fun {X Y g} => hom_ext LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul =>
          rw [ExtendRestrictScalarsAdj.homEquiv_symm_apply]
          dsimp
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [ExtendRestrictScalarsAdj.Counit.map_hom_apply,
              ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
        | add => rw [map_add, map_add]; congr 1 }

Depends on / 依赖: Adjunction, Adjunction.mk, ExtendRestrictScalarsAdj, ExtendRestrictScalarsAdj.counit, ExtendRestrictScalarsAdj.homEquiv, ExtendRestrictScalarsAdj.homEquiv_symm_apply, ExtendRestrictScalarsAdj.unit, LinearMap, LinearMap.ext, TensorProduct, TensorProduct.induction_on, counit, homEquiv, homEquiv_counit, homEquiv_symm_apply, homEquiv_unit, hom_ext, induction_on, map_zero
-/
def extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S) :
    extendScalars.{u₁, u₂, max v u₂} f ⊣ restrictScalars.{max v u₂, u₁, u₂} f :=
  Adjunction.mk' {
    homEquiv := fun _ _ => ExtendRestrictScalarsAdj.homEquiv.{v, u₁, u₂} f
    unit := ExtendRestrictScalarsAdj.unit.{v, u₁, u₂} f
    counit := ExtendRestrictScalarsAdj.counit.{v, u₁, u₂} f
homEquiv_unit := fun {X Y g} => hom_ext LinearMap.ext fun x => by
      dsimp
      rfl
homEquiv_counit := fun {X Y g} => hom_ext LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul =>
          rw [ExtendRestrictScalarsAdj.homEquiv_symm_apply]
          dsimp
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [ExtendRestrictScalarsAdj.Counit.map_hom_apply,
              ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
        | add => rw [map_add, map_add]; congr 1 }

/--
lemma `extendRestrictScalarsAdj_homEquiv_apply` / 引理 `extendRestrictScalarsAdj_homEquiv_apply`

English:
lemma extendRestrictScalarsAdj_homEquiv_apply
  proof: rfl

中文:
引理 extendRestrictScalarsAdj_homEquiv_apply
  证明: rfl
-/
lemma extendRestrictScalarsAdj_homEquiv_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    {f : R ->+* S} {M : ModuleCat.{max v u₂} R} {N : ModuleCat S}
    (φ : (extendScalars f).obj M ⟶ N) (m : M) :
    (extendRestrictScalarsAdj f).homEquiv _ _ φ m = φ ((1 : S) otimesₜ m) :=
  rfl

/--
lemma `extendRestrictScalarsAdj_unit_app_apply` / 引理 `extendRestrictScalarsAdj_unit_app_apply`

English:
lemma extendRestrictScalarsAdj_unit_app_apply
  proof: rfl

中文:
引理 extendRestrictScalarsAdj_unit_app_apply
  证明: rfl
-/
lemma extendRestrictScalarsAdj_unit_app_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R ->+* S) (M : ModuleCat.{max v u₂} R) (m : M) :
    (extendRestrictScalarsAdj f).unit.app M m = (1 : S) otimesₜ[R,f] m :=
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `extendRestrictScalarsAdj_counit_app_apply_one_tmul` / 引理 `extendRestrictScalarsAdj_counit_app_apply_one_tmul`

English:
lemma extendRestrictScalarsAdj_counit_app_apply_one_tmul
  given: (M : ModuleCat S) (m : M)
  proof: by
  apply ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul

中文:
引理 extendRestrictScalarsAdj_counit_app_apply_one_tmul
  条件: (M : 模范畴 S) (m : M)
  证明: by
  apply ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul

Depends on / 依赖: Counit, ExtendRestrictScalarsAdj, ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul, map_apply_one_tmul
-/
lemma extendRestrictScalarsAdj_counit_app_apply_one_tmul (M : ModuleCat S) (m : M) :
    dsimp% (extendRestrictScalarsAdj f).counit.app M ((1 : S) otimesₜ[R] m) = m := by
  apply ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S) :
    (extendScalars.{u₁, u₂, max u₂ w} f).IsLeftAdjoint :=
  (extendRestrictScalarsAdj f).isLeftAdjoint

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R ->+* S) :
    (restrictScalars.{max u₂ w, u₁, u₂} f).IsRightAdjoint :=
  (extendRestrictScalarsAdj f).isRightAdjoint

/--
Instance `preservesLimit_restrictScalars` / 实例 `preservesLimit_restrictScalars`

English:
instance preservesLimit_restrictScalars
  body: ⟨fun {c} hc => ⟨by
    have hc' := isLimitOfPreserves (forget₂ _ AddCommGrpCat) hc
    exact isLimitOfReflects (forget₂ _ AddCommGrpCat) hc'⟩⟩

中文:
实例 preservesLimit_restrictScalars
  定义体: ⟨fun {c} hc => ⟨by
    have hc' := isLimitOfPreserves (forget₂ _ AddCommGrpCat) hc
    exact isLimitOfReflects (forget₂ _ AddCommGrpCat) hc'⟩⟩

Depends on / 依赖: AddCommGrpCat, isLimitOfPreserves, isLimitOfReflects
-/
noncomputable instance preservesLimit_restrictScalars
    {R : Type*} {S : Type*} [Ring R] [Ring S] (f : R ->+* S) {J : Type*} [Category* J]
    (F : J ⥤ ModuleCat.{v} S) [Small.{v} (F ⋙ forget _).sections] :
    PreservesLimit F (restrictScalars f) :=
  ⟨fun {c} hc => ⟨by
    have hc' := isLimitOfPreserves (forget₂ _ AddCommGrpCat) hc
    exact isLimitOfReflects (forget₂ _ AddCommGrpCat) hc'⟩⟩

/--
Instance `preservesColimit_restrictScalars` / 实例 `preservesColimit_restrictScalars`

English:
instance preservesColimit_restrictScalars
  signature: {R S : Type*} [Ring R] [Ring S]
  body: by
  have : HasColimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    inferInstanceAs (HasColimit (F ⋙ forget₂ _ AddCommGrpCat))
  apply preservesColimit_of_preserves_colimit_cocone (HasColimit.isColimitColimitCocone F)
  apply isColimitOfReflects (forget₂ (ModuleCat.{v} R) AddCommGrpCat)
  apply isColimitOfPreserves (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})
  exact HasColimit.isColimitColimitCocone F

中文:
实例 preservesColimit_restrictScalars
  签名: {R S : 类型} [环 R] [环 S]
  定义体: by
  have : HasColimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    inferInstanceAs (HasColimit (F ⋙ forget₂ _ AddCommGrpCat))
  apply preservesColimit_of_preserves_colimit_cocone (HasColimit.isColimitColimitCocone F)
  apply isColimitOfReflects (forget₂ (ModuleCat.{v} R) AddCommGrpCat)
  apply isColimitOfPreserves (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})
  exact HasColimit.isColimitColimitCocone F

Depends on / 依赖: AddCommGrpCat, HasColimit, HasColimit.isColimitColimitCocone, ModuleCat, isColimitColimitCocone, isColimitOfPreserves, isColimitOfReflects, preservesColimit_of_preserves_colimit_cocone, restrictScalars
-/
instance preservesColimit_restrictScalars {R S : Type*} [Ring R] [Ring S]
    (f : R ->+* S) {J : Type*} [Category* J] (F : J ⥤ ModuleCat.{v} S)
    [HasColimit (F ⋙ forget₂ _ AddCommGrpCat)] :
    PreservesColimit F (ModuleCat.restrictScalars.{v} f) := by
  have : HasColimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    inferInstanceAs (HasColimit (F ⋙ forget₂ _ AddCommGrpCat))
  apply preservesColimit_of_preserves_colimit_cocone (HasColimit.isColimitColimitCocone F)
  apply isColimitOfReflects (forget₂ (ModuleCat.{v} R) AddCommGrpCat)
  apply isColimitOfPreserves (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})
  exact HasColimit.isColimitColimitCocone F

variable (R) in
/--
Definition of `extendScalarsId` / `extendScalarsId` 的定义

English:
definition extendScalarsId
  signature: : extendScalars (RingHom.id R) ≅ 𝟭 _
  body: ((conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id).symm
    (restrictScalarsId R)).symm

中文:
定义 extendScalarsId
  签名: : extendScalars (环态射.id R) ≅ 𝟭 _
  定义体: ((conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id).symm
    (restrictScalarsId R)).symm

Depends on / 依赖: Adjunction, Adjunction.id, RingHom, RingHom.id, conjugateIsoEquiv, extendRestrictScalarsAdj, restrictScalarsId
-/
noncomputable def extendScalarsId : extendScalars (RingHom.id R) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id).symm
    (restrictScalarsId R)).symm

/--
lemma `extendScalarsId_inv_app_apply` / 引理 `extendScalarsId_inv_app_apply`

English:
lemma extendScalarsId_inv_app_apply
  given: (M : ModuleCat R) (m : M)
  proof: rfl

中文:
引理 extendScalarsId_inv_app_apply
  条件: (M : 模范畴 R) (m : M)
  证明: rfl
-/
lemma extendScalarsId_inv_app_apply (M : ModuleCat R) (m : M) :
    (extendScalarsId R).inv.app M m = (1 : R) otimesₜ m := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `homEquiv_extendScalarsId` / 引理 `homEquiv_extendScalarsId`

English:
lemma homEquiv_extendScalarsId
  given: (M : ModuleCat R)
  proof: by
  ext m
  rw [extendRestrictScalarsAdj_homEquiv_apply]; rw [← extendScalarsId_inv_app_apply]; rw [← comp_apply]
  simp

中文:
引理 homEquiv_extendScalarsId
  条件: (M : 模范畴 R)
  证明: by
  ext m
  rw [extendRestrictScalarsAdj_homEquiv_apply]; rw [← extendScalarsId_inv_app_apply]; rw [← comp_apply]
  simp

Depends on / 依赖: comp_apply, extendRestrictScalarsAdj_homEquiv_apply, extendScalarsId_inv_app_apply
-/
lemma homEquiv_extendScalarsId (M : ModuleCat R) :
    (extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _ ((extendScalarsId R).hom.app M) =
      (restrictScalarsId R).inv.app M := by
  ext m
  rw [extendRestrictScalarsAdj_homEquiv_apply]; rw [← extendScalarsId_inv_app_apply]; rw [← comp_apply]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `extendScalarsId_hom_app_one_tmul` / 引理 `extendScalarsId_hom_app_one_tmul`

English:
lemma extendScalarsId_hom_app_one_tmul
  given: (M : ModuleCat R) (m : M)
  proof: by
  rw [← extendRestrictScalarsAdj_homEquiv_apply]; rw [homEquiv_extendScalarsId]
  dsimp

中文:
引理 extendScalarsId_hom_app_one_tmul
  条件: (M : 模范畴 R) (m : M)
  证明: by
  rw [← extendRestrictScalarsAdj_homEquiv_apply]; rw [homEquiv_extendScalarsId]
  dsimp

Depends on / 依赖: extendRestrictScalarsAdj_homEquiv_apply, homEquiv_extendScalarsId
-/
lemma extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) :
    (extendScalarsId R).hom.app M ((1 : R) otimesₜ m) = m := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply]; rw [homEquiv_extendScalarsId]
  dsimp

section

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ ->+* R₂) (f₂₃ : R₂ ->+* R₃) (f₃₄ : R₃ ->+* R₄)

/--
Definition of `extendScalarsComp` / `extendScalarsComp` 的定义

English:
definition extendScalarsComp
  signature: :
  body: (conjugateIsoEquiv
    ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂))).symm (restrictScalarsComp f₁₂ f₂₃).symm

中文:
定义 extendScalarsComp
  签名: :
  定义体: (conjugateIsoEquiv
    ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂))).symm (restrictScalarsComp f₁₂ f₂₃).symm

Depends on / 依赖: conjugateIsoEquiv, extendRestrictScalarsAdj, restrictScalarsComp
-/
noncomputable def extendScalarsComp :
    extendScalars (f₂₃.comp f₁₂) ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃ :=
  (conjugateIsoEquiv
    ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂))).symm (restrictScalarsComp f₁₂ f₂₃).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `homEquiv_extendScalarsComp` / 引理 `homEquiv_extendScalarsComp`

English:
lemma homEquiv_extendScalarsComp
  given: (M : ModuleCat R₁)
  proof: by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Functor.comp_obj, Category.assoc, Category.id_comp,
    Category.comp_id, Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

中文:
引理 homEquiv_extendScalarsComp
  条件: (M : 模范畴 R₁)
  证明: by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Functor.comp_obj, Category.assoc, Category.id_comp,
    Category.comp_id, Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

Depends on / 依赖: Adjunction, Adjunction.comp_unit_app, Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Adjunction.unit_naturality_assoc, Category, Category.assoc, Category.comp_id, Category.id_comp, Functor, Functor.comp_obj, Functor.map_comp, comp_id, comp_obj, comp_unit_app, conjugateEquiv, conjugateIsoEquiv, extendScalarsComp, homEquiv_unit, id_comp
-/
lemma homEquiv_extendScalarsComp (M : ModuleCat R₁) :
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂)).homEquiv _ _
      ((extendScalarsComp f₁₂ f₂₃).hom.app M) =
      (extendRestrictScalarsAdj f₁₂).unit.app M ≫
        (restrictScalars f₁₂).map ((extendRestrictScalarsAdj f₂₃).unit.app _) ≫
        (restrictScalarsComp f₁₂ f₂₃).inv.app _ := by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Functor.comp_obj, Category.assoc, Category.id_comp,
    Category.comp_id, Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extendScalarsComp_hom_app_one_tmul` / 引理 `extendScalarsComp_hom_app_one_tmul`

English:
lemma extendScalarsComp_hom_app_one_tmul
  given: (M : ModuleCat R₁) (m : M)
  proof: by
  rw [← extendRestrictScalarsAdj_homEquiv_apply]; rw [homEquiv_extendScalarsComp]
  rfl

中文:
引理 extendScalarsComp_hom_app_one_tmul
  条件: (M : 模范畴 R₁) (m : M)
  证明: by
  rw [← extendRestrictScalarsAdj_homEquiv_apply]; rw [homEquiv_extendScalarsComp]
  rfl

Depends on / 依赖: extendRestrictScalarsAdj_homEquiv_apply, homEquiv_extendScalarsComp
-/
lemma extendScalarsComp_hom_app_one_tmul (M : ModuleCat R₁) (m : M) :
    (extendScalarsComp f₁₂ f₂₃).hom.app M ((1 : R₃) otimesₜ m) =
      (1 : R₃) otimesₜ[R₂,f₂₃] ((1 : R₂) otimesₜ[R₁,f₁₂] m) := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply]; rw [homEquiv_extendScalarsComp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `extendScalars_assoc` / 引理 `extendScalars_assoc`

English:
lemma extendScalars_assoc
  proof: by
  ext M m
  have h₁ := extendScalarsComp_hom_app_one_tmul (f₂₃.comp f₁₂) f₃₄ M m
  have h₂ := extendScalarsComp_hom_app_one_tmul f₁₂ (f₃₄.comp f₂₃) M m
  have h₃ := extendScalarsComp_hom_app_one_tmul f₂₃ f₃₄
  have h₄ := extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ M m
  dsimp at h₁ h₂ h₃ h₄ ⊢
  rw [h₁]
  erw [h₂]
  rw [h₃]; rw [ExtendScalars.map_tmul]; rw [h₄]

中文:
引理 extendScalars_assoc
  证明: by
  ext M m
  have h₁ := extendScalarsComp_hom_app_one_tmul (f₂₃.comp f₁₂) f₃₄ M m
  have h₂ := extendScalarsComp_hom_app_one_tmul f₁₂ (f₃₄.comp f₂₃) M m
  have h₃ := extendScalarsComp_hom_app_one_tmul f₂₃ f₃₄
  have h₄ := extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ M m
  dsimp at h₁ h₂ h₃ h₄ ⊢
  rw [h₁]
  erw [h₂]
  rw [h₃]; rw [ExtendScalars.map_tmul]; rw [h₄]

Depends on / 依赖: ExtendScalars, ExtendScalars.map_tmul, extendScalarsComp_hom_app_one_tmul, map_tmul
-/
lemma extendScalars_assoc :
    (extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (extendScalarsComp f₁₂ f₂₃).hom _ =
        (extendScalarsComp f₁₂ (f₃₄.comp f₂₃)).hom ≫
          Functor.whiskerLeft _ (extendScalarsComp f₂₃ f₃₄).hom ≫
            (Functor.associator _ _ _).inv := by
  ext M m
  have h₁ := extendScalarsComp_hom_app_one_tmul (f₂₃.comp f₁₂) f₃₄ M m
  have h₂ := extendScalarsComp_hom_app_one_tmul f₁₂ (f₃₄.comp f₂₃) M m
  have h₃ := extendScalarsComp_hom_app_one_tmul f₂₃ f₃₄
  have h₄ := extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ M m
  dsimp at h₁ h₂ h₃ h₄ ⊢
  rw [h₁]
  erw [h₂]
  rw [h₃]; rw [ExtendScalars.map_tmul]; rw [h₄]

/--
lemma `extendScalars_assoc'` / 引理 `extendScalars_assoc'`

English:
lemma extendScalars_assoc'
  proof: by
  rw [extendScalars_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc, ← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.id_comp]

中文:
引理 extendScalars_assoc'
  证明: by
  rw [extendScalars_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc, ← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, Functor, Functor.whiskerLeft_comp_assoc, Functor.whiskerLeft_id, Iso.hom_inv_id, Iso.inv_hom_id_assoc, extendScalars_assoc_assoc, hom_inv_id, id_comp, inv_hom_id_assoc, whiskerLeft_comp_assoc, whiskerLeft_id
-/
lemma extendScalars_assoc' :
    (extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (extendScalarsComp f₁₂ f₂₃).hom _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (extendScalarsComp f₂₃ f₃₄).inv ≫
            (extendScalarsComp f₁₂ (f₃₄.comp f₂₃)).inv = 𝟙 _ := by
  rw [extendScalars_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc, ← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `extendScalars_id_comp` / 引理 `extendScalars_id_comp`

English:
lemma extendScalars_id_comp
  proof: by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul (RingHom.id R₁) f₁₂ M m]
  rw [ExtendScalars.map_tmul]
  erw [extendScalarsId_hom_app_one_tmul]
  rfl

中文:
引理 extendScalars_id_comp
  证明: by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul (RingHom.id R₁) f₁₂ M m]
  rw [ExtendScalars.map_tmul]
  erw [extendScalarsId_hom_app_one_tmul]
  rfl

Depends on / 依赖: ExtendScalars, ExtendScalars.map_tmul, RingHom, RingHom.id, extendScalarsComp_hom_app_one_tmul, extendScalarsId_hom_app_one_tmul, map_tmul
-/
lemma extendScalars_id_comp :
    (extendScalarsComp (RingHom.id R₁) f₁₂).hom ≫ Functor.whiskerRight (extendScalarsId R₁).hom _ ≫
      (Functor.leftUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul (RingHom.id R₁) f₁₂ M m]
  rw [ExtendScalars.map_tmul]
  erw [extendScalarsId_hom_app_one_tmul]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `extendScalars_comp_id` / 引理 `extendScalars_comp_id`

English:
lemma extendScalars_comp_id
  proof: by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul f₁₂ (RingHom.id R₂) M m,
    extendScalarsId_hom_app_one_tmul]
  rfl

中文:
引理 extendScalars_comp_id
  证明: by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul f₁₂ (RingHom.id R₂) M m,
    extendScalarsId_hom_app_one_tmul]
  rfl

Depends on / 依赖: RingHom, RingHom.id, extendScalarsComp_hom_app_one_tmul, extendScalarsId_hom_app_one_tmul
-/
lemma extendScalars_comp_id :
    (extendScalarsComp f₁₂ (RingHom.id R₂)).hom ≫ Functor.whiskerLeft _ (extendScalarsId R₂).hom ≫
      (Functor.rightUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul f₁₂ (RingHom.id R₂) M m,
    extendScalarsId_hom_app_one_tmul]
  rfl

end

end ModuleCat

end ModuleCat
