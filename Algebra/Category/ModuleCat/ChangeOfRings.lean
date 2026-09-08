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

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
variable (M : ModuleCat.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
`r • m := f r • m` (`Module.compHom`). This is called restriction of scalars. -/
/-
**ModuleCat.RestrictScalars.obj'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.RestrictSc
alars`。
形式化陈述：obj' : ModuleCat R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by de
fining
`r • m := f r • m` (`Module.compHom`). This is called restriction of scalars.
-/
def obj' : ModuleCat R :=
  let _ := Module.compHom M f
  of R M

/-- Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
/-
**ModuleCat.RestrictScalars.map'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.RestrictSc
alars`。
形式化陈述：map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M'
参数：g : M ⟶ M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear
 between `M` and
`M'` by means of restriction of scalars.
-/
def map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `RestrictScalars.obj'` needs to be redesigned.
  ofHom (X := obj' f M) (Y := obj' f M')
    { g.hom with map_smul' := fun r => g.hom.map_smul (f r) }

end RestrictScalars

/-- The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
/-
**ModuleCat.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* 
S) : ModuleCat.{v} S ⥤ ModuleCat.{v} R where obj
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of scalars operation is functorial. For any `f : R →+* S` a ring
 homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj := RestrictScalars.obj' f
  map := RestrictScalars.map' f

@[simp]
/-
**ModuleCat.smul_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：smul_restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R 
->+* S) (r : R) (M : ModuleCat S) : dsimp% ((ModuleCat.restrictScalars f).obj M)
.smul r = M.smul (f r)
参数：f : R ->+* S；r : R；M : ModuleCat S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) (r : R)
    (M : ModuleCat S) :
    dsimp% ((ModuleCat.restrictScalars f).obj M).smul r = M.smul (f r) :=
  rfl
/-
**ModuleCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_map_restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M N : ModuleCat S} (g : M ⟶ N) :
    (forget₂ _ Ab).map ((ModuleCat.restrictScalars f).map g) = (forget₂ _ Ab).map g :=
  rfl
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{v} f).Faithful where
  map_injective h := by
    ext x
    simpa only using! DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{v} f).PreservesMonomorphisms where
  preserves _ h := by rwa [mono_iff_injective] at h ⊢
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars f).ReflectsIsomorphisms :=
  have : (restrictScalars f ⋙ CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms :=
    inferInstanceAs (CategoryTheory.forget (ModuleCat S)).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (CategoryTheory.forget _)

-- Porting note: this should be automatic
-- TODO: this instance gives diamonds if `f : S →+* S`, see `PresheafOfModules.pushforward₀`.
-- The correct solution is probably to define explicit maps between `M` and
-- `(restrictScalars f).obj M`.
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} : Module S <| (restrictScalars f).obj M :=
  inferInstanceAs <| Module S M

@[simp]
/-
**ModuleCat.restrictScalars.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.restr
ictScalars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R] [inst_1 : Ring S] (f : R →+*
 S) {M M' : ModuleCat S} (g : M ⟶ M')   (x : ↑((ModuleCat.restrictScalars f).obj
 M)),   (CategoryTheory.ConcreteCategory.hom ((ModuleCat.restrictScalars f).map 
g)) x =     (CategoryTheory.ConcreteCategory.hom g) x
参数：f : R →+* S；g : M ⟶ M'；x : ↑((ModuleCat.restrictScalars f).obj M)；CategoryThe
ory.ConcreteCategory.hom ((ModuleCat.restrictScalars f).map g)；CategoryTheory.Co
ncreteCategory.hom g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) : (restrictScalars f).map g x = g x :=
  rfl

@[simp]
/-
**ModuleCat.restrictScalars.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.restri
ctScalars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R] [inst_1 : Ring S] (f : R →+*
 S) {M : ModuleCat S} (r : R)   (m : ↑((ModuleCat.restrictScalars f).obj M)),   
r • m =     f r •       have this := m;       this
参数：f : R →+* S；r : R；m : ↑((ModuleCat.restrictScalars f).obj M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : (restrictScalars f).obj M) : r • m = f r • show M from m :=
  rfl
/-
**ModuleCat.restrictScalars.smul_def'** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.restr
ictScalars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R] [inst_1 : Ring S] (f : R →+*
 S) {M : ModuleCat S} (r : R) (m : ↑M),   (r •       have this := m;       this)
 =     f r • m
参数：f : R →+* S；r : R；m : ↑M；r •       have this := m;       this。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : M) :
    r • (show (restrictScalars f).obj M from m) = f r • m :=
  rfl
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) sMulCommClass_mk {R : Type u₁} {S : Type u₂} [Ring R] [CommRing S]
    (f : R →+* S) (M : Type v) [I : AddCommGroup M] [Module S M] :
    haveI : SMul R M := (RestrictScalars.obj' f (ModuleCat.of S M)).isModule.toSMul
    SMulCommClass R S M :=
  @SMulCommClass.mk R S M (_) _
    fun r s m => (by simp [← mul_smul, mul_comm] : f r • s • m = s • f r • m)

set_option backward.isDefEq.respectTransparency false in
/-- Semilinear maps `M →ₛₗ[f] N` identify to
morphisms `M ⟶ (ModuleCat.restrictScalars f).obj N`. -/
@[simps]
/-
**ModuleCat.semilinearMapAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：semilinearMapAddEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R
 ->+* S) (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) : (M ->ₛₗ[f] N) ≃+ (M ⟶ (Mo
duleCat.restrictScalars f).obj N) where -- TODO: after https://github.com/leanpr
over-community/mathlib4/pull/19511 we need to hint `(Y
参数：f : R ->+* S；M : ModuleCat.{v} R；N : ModuleCat.{v} S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Semilinear maps `M →ₛₗ[f] N` identify to
morphisms `M ⟶ (ModuleCat.restrictScalars f).obj N`.
-/
def semilinearMapAddEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) :
    (M →ₛₗ[f] N) ≃+ (M ⟶ (ModuleCat.restrictScalars f).obj N) where
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  toFun g := ofHom (Y := (ModuleCat.restrictScalars f).obj N) <|
    { toFun := g
      map_add' := by simp
      map_smul' := by simp }
  invFun g :=
    { toFun := g
      map_add' := by simp
      map_smul' := g.hom.map_smul }
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restrictions scalars along equal ring homomorphisms are naturally isomorphic. -/
/-
**ModuleCat.restrictScalarsCongr** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsCongr {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : 
R ->+* S} (e : f = g) : ModuleCat.restrictScalars f ≅ ModuleCat.restrictScalars 
g
参数：e : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrictions scalars along equal ring homomorphisms are naturally isomorphic.
-/
def restrictScalarsCongr
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g) :
    ModuleCat.restrictScalars f ≅ ModuleCat.restrictScalars g :=
  NatIso.ofComponents (fun X ↦ LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars f).obj X) (X₂ := (ModuleCat.restrictScalars g).obj X)
    { __ := AddEquiv.refl _, map_smul' _ _ := by subst e; rfl }) fun _ ↦ by subst e; rfl

@[simp]
/-
**ModuleCat.restrictScalarsCongr_symm** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsCongr_symm {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f
 g : R ->+* S} (e : f = g) : (restrictScalarsCongr e).symm = restrictScalarsCong
r e.symm
参数：e : f = g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalarsCongr_symm
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g) :
  (restrictScalarsCongr e).symm = restrictScalarsCongr e.symm := rfl

@[simp]
/-
**ModuleCat.restrictScalarsCongr_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsCongr_hom_app {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
 {f g : R ->+* S} (e : f = g) (M : ModuleCat S) (x : M) : (restrictScalarsCongr 
e).hom.app M x = x
参数：e : f = g；M : ModuleCat S；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalarsCongr_hom_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (restrictScalarsCongr e).hom.app M x = x := rfl

@[simp]
/-
**ModuleCat.restrictScalarsCongr_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsCongr_inv_app {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
 {f g : R ->+* S} (e : f = g) (M : ModuleCat S) (x : M) : (restrictScalarsCongr 
e).inv.app M x = x
参数：e : f = g；M : ModuleCat S；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalarsCongr_inv_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (restrictScalarsCongr e).inv.app M x = x := rfl

section

variable {R : Type u₁} [Ring R] (f : R →+* R)

/-- For an `R`-module `M`, the restriction of scalars of `M` by the identity morphism identifies
to `M`. -/
/-
**ModuleCat.restrictScalarsId'App** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：{R : Type u₁} →   [inst : Ring R] → (f : R →+* R) → f = RingHom.id R → (M 
: ModuleCat R) → (ModuleCat.restrictScalars f).obj M ≅ M
参数：f : R →+* R；M : ModuleCat R；ModuleCat.restrictScalars f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `R`-module `M`, the restriction of scalars of `M` by the identity morphis
m identifies
to `M`.
-/
def restrictScalarsId'App (hf : f = RingHom.id R) (M : ModuleCat R) :
    (restrictScalars f).obj M ≅ M :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _ (((restrictScalars f).obj M).isModule) _
      (by rfl) (fun r x ↦ by subst hf; rfl)

variable (hf : f = RingHom.id R)
/-
**ModuleCat.restrictScalarsId'App_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat
`。
形式化陈述：∀ {R : Type u₁} [inst : Ring R] (f : R →+* R) (hf : f = RingHom.id R) (M :
 ModuleCat R) (x : ↑M),   (CategoryTheory.ConcreteCategory.hom (ModuleCat.restri
ctScalarsId'App f hf M).hom) x = x
参数：f : R →+* R；hf : f = RingHom.id R；M : ModuleCat R；x : ↑M；CategoryTheory.Concr
eteCategory.hom (ModuleCat.restrictScalarsId'App f hf M).hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalarsId'App_hom_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).hom x = x :=
  rfl
/-
**ModuleCat.restrictScalarsId'App_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat
`。
形式化陈述：∀ {R : Type u₁} [inst : Ring R] (f : R →+* R) (hf : f = RingHom.id R) (M :
 ModuleCat R) (x : ↑M),   (CategoryTheory.ConcreteCategory.hom (ModuleCat.restri
ctScalarsId'App f hf M).inv) x = x
参数：f : R →+* R；hf : f = RingHom.id R；M : ModuleCat R；x : ↑M；CategoryTheory.Concr
eteCategory.hom (ModuleCat.restrictScalarsId'App f hf M).inv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalarsId'App_inv_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).inv x = x :=
  rfl

/-- The restriction of scalars by a ring morphism that is the identity identifies to the
identity functor. -/
@[simps! hom_app inv_app]
/-
**ModuleCat.restrictScalarsId'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsId'App (hf : f = RingHom.id R) (M : ModuleCat R) : (restric
tScalars f).obj M ≅ M
参数：hf : f = RingHom.id R；M : ModuleCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of scalars by a ring morphism that is the identity identifies to
 the
identity functor.
-/
def restrictScalarsId' : ModuleCat.restrictScalars.{v} f ≅ 𝟭 _ :=
    NatIso.ofComponents <| fun M ↦ restrictScalarsId'App f hf M

@[reassoc]
/-
**ModuleCat.restrictScalarsId'App_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Modu
leCat`。
形式化陈述：∀ {R : Type u₁} [inst : Ring R] (f : R →+* R) (hf : f = RingHom.id R) {M N
 : ModuleCat R} (φ : M ⟶ N),   CategoryTheory.CategoryStruct.comp ((ModuleCat.re
strictScalars f).map φ)       (ModuleCat.restrictScalarsId'App f hf N).hom =    
 CategoryTheory.CategoryStruct.comp (ModuleCat.restrictScalarsId'App f hf M).hom
 φ
参数：f : R →+* R；hf : f = RingHom.id R；φ : M ⟶ N；(ModuleCat.restrictScalars f).map
 φ；ModuleCat.restrictScalarsId'App f hf N；ModuleCat.restrictScalarsId'App f hf M
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma restrictScalarsId'App_hom_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    (restrictScalars f).map φ ≫ (restrictScalarsId'App f hf N).hom =
      (restrictScalarsId'App f hf M).hom ≫ φ :=
  (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]
/-
**ModuleCat.restrictScalarsId'App_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Modu
leCat`。
形式化陈述：∀ {R : Type u₁} [inst : Ring R] (f : R →+* R) (hf : f = RingHom.id R) {M N
 : ModuleCat R} (φ : M ⟶ N),   CategoryTheory.CategoryStruct.comp φ (ModuleCat.r
estrictScalarsId'App f hf N).inv =     CategoryTheory.CategoryStruct.comp (Modul
eCat.restrictScalarsId'App f hf M).inv       ((ModuleCat.restrictScalars f).map 
φ)
参数：f : R →+* R；hf : f = RingHom.id R；φ : M ⟶ N；ModuleCat.restrictScalarsId'App f
 hf N；ModuleCat.restrictScalarsId'App f hf M；(ModuleCat.restrictScalars f).map φ
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma restrictScalarsId'App_inv_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    φ ≫ (restrictScalarsId'App f hf N).inv =
      (restrictScalarsId'App f hf M).inv ≫ (restrictScalars f).map φ :=
  (restrictScalarsId' f hf).inv.naturality φ

variable (R)

/-- The restriction of scalars by the identity morphism identifies to the
identity functor. -/
/-
**ModuleCat.restrictScalarsId** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsId
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of scalars by the identity morphism identifies to the
identity functor.
-/
abbrev restrictScalarsId := restrictScalarsId'.{v} (RingHom.id R) rfl

end

section

variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [Ring R₁] [Ring R₂] [Ring R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃)

/-- For each `R₃`-module `M`, restriction of scalars of `M` by a composition of ring morphisms
identifies to successively restricting scalars. -/
/-
**ModuleCat.restrictScalarsComp'App** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：{R₁ : Type u₁} →   {R₂ : Type u₂} →     {R₃ : Type u₃} →       [inst : Rin
g R₁] →         [inst_1 : Ring R₂] →           [inst_2 : Ring R₃] →             
(f : R₁ →+* R₂) →               (g : R₂ →+* R₃) →                 (gf : R₁ →+* R
₃) →                   gf = g.comp f →                     (M : ModuleCat R₃) → 
                      (ModuleCat.restrictScalars gf).obj M ≅                    
     (ModuleCat.restrictScalars f).obj ((ModuleCat.restrictScalars g).obj M)
参数：f : R₁ →+* R₂；g : R₂ →+* R₃；gf : R₁ →+* R₃；M : ModuleCat R₃；ModuleCat.restric
tScalars gf；ModuleCat.restrictScalars f；(ModuleCat.restrictScalars g).obj M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `R₃`-module `M`, restriction of scalars of `M` by a composition of ring
 morphisms
identifies to successively restricting scalars.
-/
def restrictScalarsComp'App (hgf : gf = g.comp f) (M : ModuleCat R₃) :
    (restrictScalars gf).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M) :=
  (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars gf).obj M))
    (M₂ := ↑((restrictScalars f).obj ((restrictScalars g).obj M)))
    (by rfl)
    (fun r x ↦ by subst hgf; rfl)).toModuleIso

variable (hgf : gf = g.comp f)
/-
**ModuleCat.restrictScalarsComp'App_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleC
at`。
形式化陈述：∀ {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [inst : Ring R₁] [inst_1 : 
Ring R₂] [inst_2 : Ring R₃] (f : R₁ →+* R₂)   (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (
hgf : gf = g.comp f) (M : ModuleCat R₃) (x : ↑M),   (CategoryTheory.ConcreteCate
gory.hom (ModuleCat.restrictScalarsComp'App f g gf hgf M).hom) x = x
参数：f : R₁ →+* R₂；g : R₂ →+* R₃；gf : R₁ →+* R₃；hgf : gf = g.comp f；M : ModuleCat 
R₃；x : ↑M；CategoryTheory.ConcreteCategory.hom (ModuleCat.restrictScalarsComp'App
 f g gf hgf M).hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalarsComp'App_hom_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).hom x = x :=
  rfl
/-
**ModuleCat.restrictScalarsComp'App_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleC
at`。
形式化陈述：∀ {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [inst : Ring R₁] [inst_1 : 
Ring R₂] [inst_2 : Ring R₃] (f : R₁ →+* R₂)   (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (
hgf : gf = g.comp f) (M : ModuleCat R₃) (x : ↑M),   (CategoryTheory.ConcreteCate
gory.hom (ModuleCat.restrictScalarsComp'App f g gf hgf M).inv) x = x
参数：f : R₁ →+* R₂；g : R₂ →+* R₃；gf : R₁ →+* R₃；hgf : gf = g.comp f；M : ModuleCat 
R₃；x : ↑M；CategoryTheory.ConcreteCategory.hom (ModuleCat.restrictScalarsComp'App
 f g gf hgf M).inv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalarsComp'App_inv_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).inv x = x :=
  rfl

/-- The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors. -/
@[simps! hom_app inv_app]
/-
**ModuleCat.restrictScalarsComp'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsComp'App (hgf : gf = g.comp f) (M : ModuleCat R₃) : (restri
ctScalars gf).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M)
参数：hgf : gf = g.comp f；M : ModuleCat R₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors.
-/
def restrictScalarsComp' :
    ModuleCat.restrictScalars.{v} gf ≅
      ModuleCat.restrictScalars g ⋙ ModuleCat.restrictScalars f :=
  NatIso.ofComponents <| fun M ↦ restrictScalarsComp'App f g gf hgf M

@[reassoc]
/-
**ModuleCat.restrictScalarsComp'App_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Mo
duleCat`。
形式化陈述：∀ {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [inst : Ring R₁] [inst_1 : 
Ring R₂] [inst_2 : Ring R₃] (f : R₁ →+* R₂)   (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (
hgf : gf = g.comp f) {M N : ModuleCat R₃} (φ : M ⟶ N),   CategoryTheory.Category
Struct.comp ((ModuleCat.restrictScalars gf).map φ)       (ModuleCat.restrictScal
arsComp'App f g gf hgf N).hom =     CategoryTheory.CategoryStruct.comp (ModuleCa
t.restrictScalarsComp'App f g gf hgf M).hom       ((ModuleCat.restrictScalars f)
.map ((ModuleCat.restrictScalars g).map φ))
参数：f : R₁ →+* R₂；g : R₂ →+* R₃；gf : R₁ →+* R₃；hgf : gf = g.comp f；φ : M ⟶ N；(Mod
uleCat.restrictScalars gf).map φ；ModuleCat.restrictScalarsComp'App f g gf hgf N；
ModuleCat.restrictScalarsComp'App f g gf hgf M；(ModuleCat.restrictScalars f).map
 ((ModuleCat.restrictScalars g).map φ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma restrictScalarsComp'App_hom_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (restrictScalars gf).map φ ≫ (restrictScalarsComp'App f g gf hgf N).hom =
      (restrictScalarsComp'App f g gf hgf M).hom ≫
        (restrictScalars f).map ((restrictScalars g).map φ) :=
  (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]
/-
**ModuleCat.restrictScalarsComp'App_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Mo
duleCat`。
形式化陈述：∀ {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [inst : Ring R₁] [inst_1 : 
Ring R₂] [inst_2 : Ring R₃] (f : R₁ →+* R₂)   (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (
hgf : gf = g.comp f) {M N : ModuleCat R₃} (φ : M ⟶ N),   CategoryTheory.Category
Struct.comp ((ModuleCat.restrictScalars f).map ((ModuleCat.restrictScalars g).ma
p φ))       (ModuleCat.restrictScalarsComp'App f g gf hgf N).inv =     CategoryT
heory.CategoryStruct.comp (ModuleCat.restrictScalarsComp'App f g gf hgf M).inv  
     ((ModuleCat.restrictScalars gf).map φ)
参数：f : R₁ →+* R₂；g : R₂ →+* R₃；gf : R₁ →+* R₃；hgf : gf = g.comp f；φ : M ⟶ N；(Mod
uleCat.restrictScalars f).map ((ModuleCat.restrictScalars g).map φ)；ModuleCat.re
strictScalarsComp'App f g gf hgf N；ModuleCat.restrictScalarsComp'App f g gf hgf 
M；(ModuleCat.restrictScalars gf).map φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma restrictScalarsComp'App_inv_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (restrictScalars f).map ((restrictScalars g).map φ) ≫
        (restrictScalarsComp'App f g gf hgf N).inv =
      (restrictScalarsComp'App f g gf hgf M).inv ≫ (restrictScalars gf).map φ :=
  (restrictScalarsComp' f g gf hgf).inv.naturality φ

/-- The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors. -/
/-
**ModuleCat.restrictScalarsComp** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsComp
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors.
-/
abbrev restrictScalarsComp := restrictScalarsComp'.{v} f g _ rfl

end

/-- The equivalence of categories `ModuleCat S ≌ ModuleCat R` induced by `e : R ≃+* S`. -/
@[simps]
/-
**ModuleCat.restrictScalarsEquivalenceOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Mod
uleCat`。
形式化陈述：restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [Ring R] [Ring S] (e :
 R ≃+* S) : ModuleCat S ≌ ModuleCat R where functor
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `ModuleCat S ≌ ModuleCat R` induced by `e : R ≃+* 
S`.
-/
def restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    ModuleCat S ≌ ModuleCat R where
  functor := ModuleCat.restrictScalars e.toRingHom
  inverse := ModuleCat.restrictScalars e.symm
  unitIso := (restrictScalarsId S).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    (restrictScalarsId R)
/-
**ModuleCat.restrictScalars_isEquivalence_of_ringEquiv** 是 Mathlib 中的一个实例，位于命名空间
 `ModuleCat`。
形式化陈述：restrictScalars_isEquivalence_of_ringEquiv {R S : Type*} [Ring R] [Ring S]
 (e : R ≃+* S) : (ModuleCat.restrictScalars e.toRingHom).IsEquivalence
参数：e : R ≃+* S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance restrictScalars_isEquivalence_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).IsEquivalence :=
  (restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

/-- If `R` and `S` are isomorphic rings, `S` viewed as an `R`-module is isomorphic to `R`. -/
/-
**ModuleCat.restrictScalarsIsoOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictScalarsIsoOfEquiv {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) :
 (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) ≅ ModuleCat.of R
 R
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` and `S` are isomorphic rings, `S` viewed as an `R`-module is isomorphic t
o `R`.
-/
def restrictScalarsIsoOfEquiv {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) ≅ ModuleCat.of R R :=
  letI : Module R (ModuleCat.of S S) := e.toRingHom.toModule
  LinearEquiv.toModuleIso
    { __ := e.symm
      map_smul' x y := by simp [RingHom.toModule_smul] }

@[simp]
/-
**ModuleCat.restrictScalarsIsoOfEquiv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Modul
eCat`。
形式化陈述：restrictScalarsIsoOfEquiv_hom_apply {R S : Type v} [Ring R] [Ring S] (e : 
R ≃+* S) (x : S) : dsimp% (ModuleCat.restrictScalarsIsoOfEquiv e).hom x = e.symm
 x
参数：e : R ≃+* S；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma restrictScalarsIsoOfEquiv_hom_apply {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (x : S) :
    dsimp% (ModuleCat.restrictScalarsIsoOfEquiv e).hom x = e.symm x :=
  rfl

@[simp]
/-
**ModuleCat.restrictScalarsIsoOfEquiv_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Modul
eCat`。
形式化陈述：restrictScalarsIsoOfEquiv_inv_apply {R S : Type v} [Ring R] [Ring S] (e : 
R ≃+* S) (x : R) : dsimp% (ModuleCat.restrictScalarsIsoOfEquiv e).inv x = e x
参数：e : R ≃+* S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma restrictScalarsIsoOfEquiv_inv_apply {R S : Type v} [Ring R] [Ring S] (e : R ≃+* S) (x : R) :
    dsimp% (ModuleCat.restrictScalarsIsoOfEquiv e).inv x = e x :=
  rfl
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : (restrictScalars f).Additive where
/-
**ModuleCat.restrictScalarsEquivalenceOfRingEquiv_additive** 是 Mathlib 中的一个定理，位于
命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [inst_1 : Ring S] (e : R ≃
+* S),   (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.Additive
参数：e : R ≃+* S；ModuleCat.restrictScalarsEquivalenceOfRingEquiv e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance restrictScalarsEquivalenceOfRingEquiv_additive {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).functor.Additive where

namespace Algebra

/-
**ModuleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S]
    (f : R →ₐ[R₀] S) : (restrictScalars f.toRingHom).Linear R₀ where
  map_smul {M N} g r₀ := by ext m; exact congr_arg (· • g.hom m) (f.commutes r₀).symm
/-
**ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear** 是 Mathlib 中的一
个实例，位于命名空间 `ModuleCat.Algebra`。
形式化陈述：restrictScalarsEquivalenceOfRingEquiv_linear {R₀ R S : Type*} [CommSemirin
g R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S] (e : R ≃ₐ[R₀] S) : (restri
ctScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor.Linear R₀
参数：e : R ≃ₐ[R₀] S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance restrictScalarsEquivalenceOfRingEquiv_linear
    {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S]
    (e : R ≃ₐ[R₀] S) :
    (restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor.Linear R₀ :=
  inferInstanceAs ((restrictScalars e.toAlgHom.toRingHom).Linear R₀)

end Algebra

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

section ModuleCat.Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

/-- Tensor product of elements along a base change.

This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
without this notation, one needs to work with `s : (restrictScalars f).obj ⟨S⟩`. -/
scoped[ChangeOfRings] notation:100 s:100 " ⊗ₜ[" R "," f "] " m:101 =>
  @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ f) _ s m

end Unbundled

open ChangeOfRings

namespace ExtendScalars

variable (M : ModuleCat.{v} R)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars turns an `R`-module into an `S`-module by M ↦ S ⨂ M
-/
/-
**ModuleCat.ExtendScalars.obj'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.ExtendScalar
s`。
形式化陈述：obj' : ModuleCat S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of scalars turns an `R`-module into an `S`-module by M ↦ S ⨂ M
-/
def obj' : ModuleCat S :=
  of _ (TensorProduct R ((restrictScalars f).obj (of _ S)) M)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
/-
**ModuleCat.ExtendScalars.map'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.ExtendScalar
s`。
形式化陈述：map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) : obj' f M1 ⟶ obj' f M2
参数：l : M1 ⟶ M2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) : obj' f M1 ⟶ obj' f M2 :=
  ofHom (@LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l.hom)

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.ExtendScalars.map'_id** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.ExtendSca
lars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] (f
 : R →+* S) {M : ModuleCat R},   ModuleCat.ExtendScalars.map' f (CategoryTheory.
CategoryStruct.id M) =     CategoryTheory.CategoryStruct.id (ModuleCat.ExtendSca
lars.obj' f M)
参数：f : R →+* S；CategoryTheory.CategoryStruct.id M；ModuleCat.ExtendScalars.obj' f
 M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearMap.baseChange_id`：baseChange_id : (.id : M ->ₗ[R] M).baseChange A
 = .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map'_id {M : ModuleCat.{v} R} : map' f (𝟙 M) = 𝟙 _ := by
  simp [map', obj']
/-
**ModuleCat.ExtendScalars.map'_comp** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.ExtendS
calars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] (f
 : R →+* S) {M₁ M₂ M₃ : ModuleCat R}   (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃),   Module
Cat.ExtendScalars.map' f (CategoryTheory.CategoryStruct.comp l₁₂ l₂₃) =     Cate
goryTheory.CategoryStruct.comp (ModuleCat.ExtendScalars.map' f l₁₂) (ModuleCat.E
xtendScalars.map' f l₂₃)
参数：f : R →+* S；l₁₂ : M₁ ⟶ M₂；l₂₃ : M₂ ⟶ M₃；CategoryTheory.CategoryStruct.comp l₁
₂ l₂₃；ModuleCat.ExtendScalars.map' f l₁₂；ModuleCat.ExtendScalars.map' f l₂₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
    map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => erw [LinearMap.map_add, LinearMap.map_add]; grind

end ExtendScalars

/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
/-
**ModuleCat.extendScalars** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：extendScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R
 ->+* S) : ModuleCat R ⥤ ModuleCat S where obj M
参数：f : R ->+* S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.ExtendScalars.map'_id`：∀ {R : Type u₁} {S : Type u₂} [inst : C
ommRing R] [inst_1 : CommRing S] (f : R →+* S) {M : ModuleCat R},   ModuleCat.Ex
tendScalars.map' f (C…
· 使用定理 `ModuleCat.ExtendScalars.map'_comp`：∀ {R : Type u₁} {S : Type u₂} [inst :
 CommRing R] [inst_1 : CommRing S] (f : R →+* S) {M₁ M₂ M₃ : ModuleCat R}   (l₁₂
 : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶…

--- 原说明 ---
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def extendScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S where
  obj M := ExtendScalars.obj' f M
  map l := ExtendScalars.map' f l
  map_id _ := ExtendScalars.map'_id f
  map_comp := ExtendScalars.map'_comp f

namespace ExtendScalars

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ModuleCat.ExtendScalars.smul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.ExtendS
calars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] (f
 : R →+* S) {M : ModuleCat R} (s s' : S)   (m : ↑M), s • s' ⊗ₜ[R] m = (s * s') ⊗
ₜ[R] m
参数：f : R →+* S；s s' : S；m : ↑M；s * s'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.sMulCommClass_mk`：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R
] [inst_1 : CommRing S] (f : R →+* S) (M : Type v) [I : AddCommGroup M]   [inst_
2 : _root_.Modul…
-/
protected theorem smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s' ⊗ₜ[R,f] m : (extendScalars f).obj M) = (s * s') ⊗ₜ[R,f] m :=
  rfl

@[simp]
/-
**ModuleCat.ExtendScalars.map_tmul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.ExtendSc
alars`。
形式化陈述：map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) : (extendSc
alars f).map g (s otimesₜ[R,f] m) = s otimesₜ[R,f] g m
参数：g : M ⟶ M'；s : S；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (extendScalars f).map g (s ⊗ₜ[R,f] m) = s ⊗ₜ[R,f] g m :=
  rfl

variable {f}

set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**ModuleCat.ExtendScalars.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.ExtendSca
lars`。
形式化陈述：hom_ext {M : ModuleCat R} {N : ModuleCat S} {α β : (extendScalars f).obj M
 ⟶ N} (h : forall (m : M), α ((1 : S) otimesₜ m) = β ((1 : S) otimesₜ m)) : α = 
β
参数：extendScalars f；h : forall (m : M), α ((1 : S) otimesₜ m) = β ((1 : S) otimes
ₜ m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `ModuleCat.instFaithfulRestrictScalars`：∀ {R : Type u₁} {S : Type u₂} [in
st : Ring R] [inst_1 : Ring S] (f : R →+* S), (ModuleCat.restrictScalars f).Fait
hful
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.sMulCommClass_mk`：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R
] [inst_1 : CommRing S] (f : R →+* S) (M : Type v) [I : AddCommGroup M]   [inst_
2 : _root_.Modul…
· 使用定理 `ModuleCat.ExtendScalars.smul_tmul`：∀ {R : Type u₁} {S : Type u₂} [inst :
 CommRing R] [inst_1 : CommRing S] (f : R →+* S) {M : ModuleCat R} (s s' : S)   
(m : ↑M), s • s' ⊗ₜ[R] …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_ext {M : ModuleCat R} {N : ModuleCat S}
    {α β : (extendScalars f).obj M ⟶ N}
    (h : ∀ (m : M), α ((1 : S) ⊗ₜ m) = β ((1 : S) ⊗ₜ m)) : α = β := by
  apply (restrictScalars f).map_injective
  let := f.toAlgebra
  ext : 1
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s ⊗ₜ m) = β (s ⊗ₜ m)
  have : s ⊗ₜ[R] (m : M) = s • (1 : S) ⊗ₜ[R] m := by
    rw [ExtendScalars.smul_tmul, mul_one]
  simp only [this, map_smul, h]

end ExtendScalars

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- We use `S'` to denote `S` viewed as `R`-module, via the map `f`.
-- Porting note: this seems to cause problems related to lack of reducibility
-- local notation "S'" => (restrictScalars f).obj ⟨S⟩

set_option backward.isDefEq.respectTransparency false in
/-- Given an `R`-module M, consider Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
-/
/-
**ModuleCat.CoextendScalars.hasSMul** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Coexten
dScalars`。
形式化陈述：hasSMul : SMul S (restrictScalars f).obj (of _ S) ->ₗ[R] M where smul s g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-module M, consider Hom(S, M) -- the `R`-linear maps between S (as a
n `R`-module by
means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g 
(x • s)`
-/
instance hasSMul : SMul S <| (restrictScalars f).obj (of _ S) →ₗ[R] M where
  smul s g :=
    { toFun := fun s' : S => g (s' * s : S)
      map_add' := fun x y : S => by rw [add_mul, map_add]
      map_smul' := fun r (t : S) => by
        simp [← map_smul, ModuleCat.restrictScalars.smul_def (M := ModuleCat.of _ S), mul_assoc] }

@[simp]
/-
**ModuleCat.CoextendScalars.smul_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Coe
xtendScalars`。
形式化陈述：smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) ->ₗ[R] M) (s' : 
S) : (s • g) s' = g (s' * s : S)
参数：s : S；g : (restrictScalars f).obj (of _ S) ->ₗ[R] M；s' : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
    (s • g) s' = g (s' * s : S) :=
  rfl
/-
**ModuleCat.CoextendScalars.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Coext
endScalars`。
形式化陈述：mulAction : MulAction S (restrictScalars f).obj (of _ S) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction : MulAction S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.hasSMul f _ with
    one_smul := fun g => LinearMap.ext fun s : S => by simp
    mul_smul := fun (s t : S) g => LinearMap.ext fun x : S => by simp [mul_assoc] }

set_option backward.isDefEq.respectTransparency.types false in
/-
**ModuleCat.CoextendScalars.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCa
t.CoextendScalars`。
形式化陈述：distribMulAction : DistribMulAction S (restrictScalars f).obj (of _ S) ->ₗ
[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction : DistribMulAction S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.mulAction f _ with
    smul_add := fun s g h => LinearMap.ext fun _ : S => by simp
    smul_zero := fun _ => LinearMap.ext fun _ : S => by simp }

set_option backward.isDefEq.respectTransparency false in
/-- `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
-/
/-
**ModuleCat.CoextendScalars.isModule** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Coexte
ndScalars`。
形式化陈述：isModule : Module S (restrictScalars f).obj (of _ S) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-mod
ule structure on
Hom(S, M).
-/
instance isModule : Module S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.distribMulAction f _ with
    add_smul := fun s1 s2 g => LinearMap.ext fun x : S => by simp [mul_add, map_add]
    zero_smul := fun g => LinearMap.ext fun x : S => by simp [map_zero] }

end Unbundled

variable (M : ModuleCat.{v} R)

/-- If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-module with
scalar multiplication defined by `s • l := x ↦ l (x • s)`.

This is an implementation detail: use `(coextendScalars f).obj` instead.
-/
/-
**ModuleCat.CoextendScalars.obj'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.CoextendSc
alars`。
形式化陈述：obj' : ModuleCat S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-m
odule with
scalar multiplication defined by `s • l := x ↦ l (x • s)`.

This is an implementation detail: use `(coextendScalars f).obj` instead.
-/
def obj' : ModuleCat S :=
  of _ ((restrictScalars f).obj (of _ S) →ₗ[R] M)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h` -/
@[simps!]
/-
**ModuleCat.CoextendScalars.map'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.CoextendSc
alars`。
形式化陈述：map' {M M' : ModuleCat R} (g : M ⟶ M') : obj' f M ⟶ obj' f M'
参数：g : M ⟶ M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-
linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h`
-/
def map' {M M' : ModuleCat R} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  ofHom
  { toFun := fun h => g.hom.comp h
    map_add' := fun _ _ => LinearMap.comp_add _ _ _
    map_smul' := fun s h => by ext; simp }

end CoextendScalars

/--
For any rings `R, S` and a ring homomorphism `f : R →+* S`, there is a functor from `R`-module to
`S`-module defined by `M ↦ (S →ₗ[R] M)` where `S` is considered as an `R`-module via restriction of
scalars and `g : M ⟶ M'` is sent to `h ↦ g ∘ h`.

The definition of `(coextendScalars f).obj` is given by `CoextendScalars.equiv`.
-/
/-
**ModuleCat.coextendScalars** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：coextendScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R ->+* 
S) : ModuleCat R ⥤ ModuleCat S where obj
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any rings `R, S` and a ring homomorphism `f : R →+* S`, there is a functor f
rom `R`-module to
`S`-module defined by `M ↦ (S →ₗ[R] M)` where `S` is considered as an `R`-module
 via restriction of
scalars and `g : M ⟶ M'` is sent to `h ↦ g ∘ h`.

The definition of `(coextendScalars f).obj` is given by `CoextendScalars.equiv`.
-/
def coextendScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S where
  obj := CoextendScalars.obj' f
  map := CoextendScalars.map' f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- The carrier of `(coextendScalars f).obj M` is `S →ₗ[R] M` where `S` is considered as an
`R`-module via restriction of scalars. -/
/-
**ModuleCat.CoextendScalars.equiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.CoextendS
calars`。
形式化陈述：equiv (M : ModuleCat R) : (coextendScalars f).obj M ≃ₗ[S] ((restrictScalar
s f).obj (of _ S) ->ₗ[R] M) where toFun f
参数：M : ModuleCat R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The carrier of `(coextendScalars f).obj M` is `S →ₗ[R] M` where `S` is considere
d as an
`R`-module via restriction of scalars.
-/
def equiv (M : ModuleCat R) :
    (coextendScalars f).obj M ≃ₗ[S] ((restrictScalars f).obj (of _ S) →ₗ[R] M) where
  toFun f := f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**ModuleCat.CoextendScalars.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.CoextendScalar
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : ModuleCat R) : CoeFun ((coextendScalars f).obj M) fun _ => S → M where
  coe g := equiv f M g

variable {f} in
/-
**ModuleCat.CoextendScalars.ext** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.CoextendSca
lars`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R] [inst_1 : Ring S] {f : R →+*
 S} {M : ModuleCat R}   {g g' : ↑((ModuleCat.coextendScalars f).obj M)},   (Modu
leCat.CoextendScalars.equiv f M) g = (ModuleCat.CoextendScalars.equiv f M) g' → 
g = g'
参数：(ModuleCat.coextendScalars f).obj M；ModuleCat.CoextendScalars.equiv f M；Modul
eCat.CoextendScalars.equiv f M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
@[ext] lemma ext {M : ModuleCat R} {g g' : (coextendScalars f).obj M}
    (h : CoextendScalars.equiv f M g = CoextendScalars.equiv f M g') :
    g = g' := (CoextendScalars.equiv f M).injective h
/-
**ModuleCat.CoextendScalars.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Coex
tendScalars`。
形式化陈述：smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) : 
(s • g) s' = g (s' * s)
参数：M : ModuleCat R；g : (coextendScalars f).obj M；s s' : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
    (s • g) s' = g (s' * s) :=
  rfl

@[simp]
/-
**ModuleCat.CoextendScalars.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Coext
endScalars`。
形式化陈述：map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) : (coextendScalars
 f).map g x s = g (x s)
参数：g : M ⟶ M'；x；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) :
    (coextendScalars f).map g x s = g (x s) :=
  rfl

end CoextendScalars

namespace RestrictionCoextensionAdj

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-module X and `S`-module Y, any `g : (restrictScalars f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextendScalars f).obj X` by sending `y ↦ (s ↦ g (s • y))`
-/
/-
**ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction** 是 Mathlib 中的一个定
义，位于命名空间 `ModuleCat.RestrictionCoextensionAdj.HomEquiv`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : Ring R] →       [inst_1 : Ri
ng S] →         (f : R →+* S) →           {X : ModuleCat R} →             {Y : M
oduleCat S} → ((ModuleCat.restrictScalars f).obj Y ⟶ X) → (Y ⟶ (ModuleCat.coexte
ndScalars f).obj X)
参数：f : R →+* S；(ModuleCat.restrictScalars f).obj Y ⟶ X；Y ⟶ (ModuleCat.coextendSc
alars f).obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-module X and `S`-module Y, any `g : (restrictScalars f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextendScalars f).obj X` by sending `y ↦ (s ↦ g (s • y))`
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
    map_add' (y1 y2 : Y) := (CoextendScalars.equiv _ _).injective <|
      LinearMap.ext fun s : S => by simp
    map_smul' (s : S) (y : Y) := (CoextendScalars.equiv _ _).injective <|
      LinearMap.ext fun t : S => by simp [mul_smul] }

/-- This should be autogenerated by `@[simps]` but we need to give `s` the correct type here. -/
/-
**ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction_hom_apply_apply**
 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.RestrictionCoextensionAdj.HomEquiv`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R] [inst_1 : Ring S] (f : R →+*
 S) {X : ModuleCat R} {Y : ModuleCat S}   (g : (ModuleCat.restrictScalars f).obj
 Y ⟶ X) (y : ↑Y) (s : S),   ((ModuleCat.CoextendScalars.equiv f X)         ((Mod
uleCat.Hom.hom (ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction f g
)) y))       s =     (CategoryTheory.ConcreteCategory.hom g) (s • y)
参数：f : R →+* S；g : (ModuleCat.restrictScalars f).obj Y ⟶ X；y : ↑Y；s : S；(ModuleC
at.CoextendScalars.equiv f X)         ((ModuleCat.Hom.hom (ModuleCat.Restriction
CoextensionAdj.HomEquiv.fromRestriction f g)) y)；CategoryTheory.ConcreteCategory
.hom g；s • y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This should be autogenerated by `@[simps]` but we need to give `s` the correct t
ype here.
-/
@[simp] lemma HomEquiv.fromRestriction_hom_apply_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) (y) (s : S) :
    (HomEquiv.fromRestriction f g).hom y s = g (s • y) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextendScalars f).obj X`
corresponds to `(restrictScalars f).obj Y ⟶ X` by `y ↦ g y 1`
-/
/-
**ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction** 是 Mathlib 中的一个定义，
位于命名空间 `ModuleCat.RestrictionCoextensionAdj.HomEquiv`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : Ring R] →       [inst_1 : Ri
ng S] →         (f : R →+* S) →           {X : ModuleCat R} →             {Y : M
oduleCat S} → (Y ⟶ (ModuleCat.coextendScalars f).obj X) → ((ModuleCat.restrictSc
alars f).obj Y ⟶ X)
参数：f : R →+* S；Y ⟶ (ModuleCat.coextendScalars f).obj X；(ModuleCat.restrictScalar
s f).obj Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextendScalars f).obj X`
corresponds to `(restrictScalars f).obj Y ⟶ X` by `y ↦ g y 1`
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

/-- This should be autogenerated by `@[simps]` but we need to give `1` the correct type here. -/
/-
**ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_hom_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `ModuleCat.RestrictionCoextensionAdj.HomEquiv`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R] [inst_1 : Ring S] (f : R →+*
 S) {X : ModuleCat R} {Y : ModuleCat S}   (g : Y ⟶ (ModuleCat.coextendScalars f)
.obj X) (y : ↑((ModuleCat.restrictScalars f).obj Y)),   (ModuleCat.Hom.hom (Modu
leCat.RestrictionCoextensionAdj.HomEquiv.toRestriction f g)) y =     ((ModuleCat
.CoextendScalars.equiv f X) ((ModuleCat.Hom.hom g) y)) 1
参数：f : R →+* S；g : Y ⟶ (ModuleCat.coextendScalars f).obj X；y : ↑((ModuleCat.rest
rictScalars f).obj Y)；ModuleCat.Hom.hom (ModuleCat.RestrictionCoextensionAdj.Hom
Equiv.toRestriction f g)；(ModuleCat.CoextendScalars.equiv f X) ((ModuleCat.Hom.h
om g) y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This should be autogenerated by `@[simps]` but we need to give `1` the correct t
ype here.
-/
@[simp] lemma HomEquiv.toRestriction_hom_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : Y ⟶ (coextendScalars f).obj X) (y) :
    (HomEquiv.toRestriction f g).hom y = g.hom y (1 : S) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unit'`, to address timeouts. -/
/-
**ModuleCat.RestrictionCoextensionAdj.app'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.
RestrictionCoextensionAdj`。
形式化陈述：app' (Y : ModuleCat S) : Y ->ₗ[S] (restrictScalars f ⋙ coextendScalars f).
obj Y
参数：Y : ModuleCat S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `unit'`, to address timeouts.
-/
def app' (Y : ModuleCat S) : Y →ₗ[S] (restrictScalars f ⋙ coextendScalars f).obj Y :=
  { toFun y := (CoextendScalars.equiv _ _).symm
      { toFun (s : S) := s • y
        map_add' _ _ := add_smul _ _ _
        map_smul' r (s : S) := by
          simp [ModuleCat.restrictScalars.smul_def (M := ModuleCat.of S S), mul_smul] }
    map_add' y1 y2 := (CoextendScalars.equiv _ _).injective <|
      LinearMap.ext fun s : S => by
        simp [smul_add]
    map_smul' s (y : Y) := (CoextendScalars.equiv _ _).injective <|
      LinearMap.ext fun t : S => by
        simp [mul_smul] }

/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps]
/-
**ModuleCat.RestrictionCoextensionAdj.unit'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat
.RestrictionCoextensionAdj`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : Ring R] →       [inst_1 : Ri
ng S] →         (f : R →+* S) →           CategoryTheory.Functor.id (ModuleCat S
) ⟶ (ModuleCat.restrictScalars f).comp (ModuleCat.coextendScalars f)
参数：f : R →+* S；ModuleCat S；ModuleCat.restrictScalars f；ModuleCat.coextendScalars
 f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from identity functor to the composition of restricti
on and coextension
of scalars.
-/
protected noncomputable def unit' : 𝟭 (ModuleCat S) ⟶ restrictScalars f ⋙ coextendScalars f where
  app Y := ofHom (app' f Y)
  naturality Y Y' g :=
    hom_ext <| LinearMap.ext fun y : Y => CoextendScalars.ext <| LinearMap.ext fun s : S => by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): previously simp [CoextendScalars.map_apply]
      simp only [Functor.id_map, Functor.id_obj, Functor.comp_map]
      change s • (g y) = g (s • y)
      rw [map_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps]
/-
**ModuleCat.RestrictionCoextensionAdj.counit'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleC
at.RestrictionCoextensionAdj`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : Ring R] →       [inst_1 : Ri
ng S] →         (f : R →+* S) →           (ModuleCat.coextendScalars f).comp (Mo
duleCat.restrictScalars f) ⟶ CategoryTheory.Functor.id (ModuleCat R)
参数：f : R →+* S；ModuleCat.coextendScalars f；ModuleCat.restrictScalars f；ModuleCat
 R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from the composition of coextension and restriction o
f scalars to
identity functor.
-/
protected noncomputable def counit' : coextendScalars f ⋙ restrictScalars f ⟶ 𝟭 (ModuleCat R) where
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  app X := ofHom (X := (restrictScalars f).obj ((coextendScalars f).obj X))
    { toFun g := CoextendScalars.equiv f X g (1 : S)
      map_add' x1 x2 := by simp
      map_smul' r g := by
        dsimp
        rw [CoextendScalars.smul_apply, one_mul, ← map_smul]
        congr
        change f r = f r • (1 : S)
        simp }

end RestrictionCoextensionAdj

set_option backward.isDefEq.respectTransparency false in
-- Porting note: very fiddly universes
/-- Restriction of scalars is left adjoint to coextension of scalars. -/
-- @[simps] Porting note: not in normal form and not used
/-
**ModuleCat.restrictCoextendScalarsAdj** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：restrictCoextendScalarsAdj {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (
f : R ->+* S) : restrictScalars.{max v u₂, u₁, u₂} f ⊣ coextendScalars f
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def restrictCoextendScalarsAdj {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    restrictScalars.{max v u₂, u₁, u₂} f ⊣ coextendScalars f :=
  Adjunction.mk' {
    homEquiv := fun X Y ↦
      { toFun := RestrictionCoextensionAdj.HomEquiv.fromRestriction.{u₁, u₂, v} f
        invFun := RestrictionCoextensionAdj.HomEquiv.toRestriction.{u₁, u₂, v} f
        left_inv g := by ext; simp
        right_inv g := by ext; simp }
    unit := RestrictionCoextensionAdj.unit'.{u₁, u₂, v} f
    counit := RestrictionCoextensionAdj.counit'.{u₁, u₂, v} f
    homEquiv_unit := hom_ext <| LinearMap.ext fun _ => rfl
    homEquiv_counit {X Y g} := by
      ext
      simp [RestrictionCoextensionAdj.counit'] }
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{max u₂ w} f).IsLeftAdjoint :=
  (restrictCoextendScalarsAdj f).isLeftAdjoint
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (coextendScalars.{u₁, u₂, max u₂ w} f).IsRightAdjoint :=
  (restrictCoextendScalarsAdj f).isRightAdjoint

namespace ExtendRestrictScalarsAdj

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/--
Given `R`-module X and `S`-module Y and a map `g : (extendScalars f).obj X ⟶ Y`, i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrictScalars f).obj Y`, i.e. `R`-linear map `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
@[simps! hom_apply]
/-
**ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars** 是 Mathlib 中的一个
定义，位于命名空间 `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : CommRing R] →       [inst_1 
: CommRing S] →         (f : R →+* S) →           {X : ModuleCat R} →           
  {Y : ModuleCat S} → ((ModuleCat.extendScalars f).obj X ⟶ Y) → (X ⟶ (ModuleCat.
restrictScalars f).obj Y)
参数：f : R →+* S；(ModuleCat.extendScalars f).obj X ⟶ Y；X ⟶ (ModuleCat.restrictScal
ars f).obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-module X and `S`-module Y and a map `g : (extendScalars f).obj X ⟶ Y`,
 i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrictScalars f).obj Y`, i.e. `R`-linear map
 `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
def HomEquiv.toRestrictScalars {X : ModuleCat R} {Y : ModuleCat S}
    (g : (extendScalars f).obj X ⟶ Y) :
    X ⟶ (restrictScalars f).obj Y :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (restrictScalars f).obj Y)
  { toFun := fun x => g <| (1 : S) ⊗ₜ[R,f] x
    map_add' := fun _ _ => by dsimp; rw [tmul_add, map_add]
    map_smul' := fun r s => by
      dsimp
      rw [RestrictScalars.smul_def, ← LinearMap.map_smul]
      erw [tmul_smul]
      congr }

set_option backward.isDefEq.respectTransparency false in
-- Porting note: forced to break apart fromExtendScalars due to timeouts
/--
The map `S → X →ₗ[R] Y` given by `fun s x => s • (g x)`
-/
@[simps]
/-
**ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.evalAt** 是 Mathlib 中的一个定义，位于命名空间 `
ModuleCat.ExtendRestrictScalarsAdj.HomEquiv`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : CommRing R] →       [inst_1 
: CommRing S] →         (f : R →+* S) →           {X : ModuleCat R} →           
  {Y : ModuleCat S} →               S →                 (X ⟶ (ModuleCat.restrict
Scalars f).obj Y) →                   have this := Module.compHom (↑Y) f;       
            ↑X →ₗ[R] ↑Y
参数：f : R →+* S；X ⟶ (ModuleCat.restrictScalars f).obj Y。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `S → X →ₗ[R] Y` given by `fun s x => s • (g x)`
-/
def HomEquiv.evalAt {X : ModuleCat R} {Y : ModuleCat S} (s : S)
    (g : X ⟶ (restrictScalars f).obj Y) : have : Module R Y := Module.compHom Y f
    X →ₗ[R] Y :=
  @LinearMap.mk _ _ _ _ (RingHom.id R) X Y _ _ _ (_)
    { toFun := fun x => s • (g x : Y)
      map_add' := by
        intros
        dsimp only
        rw [map_add, smul_add] }
    (by
      intro r x
      rw [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, map_smul, smul_comm r s (g x : Y)])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrictScalars f).obj Y`, i.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e `S`-linear map `S ⨂ X → Y` by
`s ⊗ x ↦ s • g x`.
-/
@[simps! hom_apply]
/-
**ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars** 是 Mathlib 中的一个
定义，位于命名空间 `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : CommRing R] →       [inst_1 
: CommRing S] →         (f : R →+* S) →           {X : ModuleCat R} →           
  {Y : ModuleCat S} → (X ⟶ (ModuleCat.restrictScalars f).obj Y) → ((ModuleCat.ex
tendScalars f).obj X ⟶ Y)
参数：f : R →+* S；X ⟶ (ModuleCat.restrictScalars f).obj Y；(ModuleCat.extendScalars 
f).obj X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrictScalars f).obj Y`, i
.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e `S`-linear map `S ⨂ 
X → Y` by
`s ⊗ x ↦ s • g x`.
-/
def HomEquiv.fromExtendScalars {X : ModuleCat R} {Y : ModuleCat S}
    (g : X ⟶ (restrictScalars f).obj Y) :
    (extendScalars f).obj X ⟶ Y := by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine ofHom
    { toFun z := TensorProduct.lift (σ₁₂ := .id _) ?_ z, map_add' := ?_, map_smul' := ?_ }
  · refine
    { toFun s := HomEquiv.evalAt f s g, map_add' := fun (s₁ s₂ : S) ↦ ?_,
      map_smul' := fun (r : R) (s : S) ↦ ?_ }
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
/-
**ModuleCat.ExtendRestrictScalarsAdj.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleC
at.ExtendRestrictScalarsAdj`。
形式化陈述：homEquiv {X : ModuleCat R} {Y : ModuleCat S} : ((extendScalars f).obj X ⟶ 
Y) ≃ (X ⟶ (restrictScalars.{max v u₂, u₁, u₂} f).obj Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-module X and `S`-module Y, `S`-linear maps `(extendScalars f).obj X ⟶ 
Y`
bijectively correspond to `R`-linear maps `X ⟶ (restrictScalars f).obj Y`.
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
    rw [lift.tmul, LinearMap.coe_mk, LinearMap.coe_mk]
    dsimp
    rw [one_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
-- @[simps] Porting note: not in normal form and not used
/-
**ModuleCat.ExtendRestrictScalarsAdj.Unit.map** 是 Mathlib 中的一个定义，位于命名空间 `ModuleC
at.ExtendRestrictScalarsAdj.Unit`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : CommRing R] →       [inst_1 
: CommRing S] →         (f : R →+* S) → {X : ModuleCat R} → X ⟶ ((ModuleCat.exte
ndScalars f).comp (ModuleCat.restrictScalars f)).obj X
参数：f : R →+* S；(ModuleCat.extendScalars f).comp (ModuleCat.restrictScalars f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Unit.map {X : ModuleCat R} : X ⟶ (extendScalars f ⋙ restrictScalars f).obj X :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (extendScalars f ⋙ restrictScalars f).obj X)
  { toFun := fun x => (1 : S) ⊗ₜ[R,f] x
    map_add' := fun x x' => by dsimp; rw [TensorProduct.tmul_add]
    map_smul' := fun r x => by
      let m1 : Module R S := Module.compHom S f
      dsimp; rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul'] }

/--
The natural transformation from identity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
@[simps]
/-
**ModuleCat.ExtendRestrictScalarsAdj.unit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.E
xtendRestrictScalarsAdj`。
形式化陈述：unit : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars.{max v u₂, u₁, 
u₂} f where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from identity functor on `R`-module to the compositio
n of extension and
restriction of scalars.
-/
def unit : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars.{max v u₂, u₁, u₂} f where
  app _ := Unit.map.{u₁, u₂, v} f

set_option backward.isDefEq.respectTransparency false in
/-- For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y` -/
@[simps! hom_apply]
/-
**ModuleCat.ExtendRestrictScalarsAdj.Counit.map** 是 Mathlib 中的一个定义，位于命名空间 `Modul
eCat.ExtendRestrictScalarsAdj.Counit`。
形式化陈述：{R : Type u₁} →   {S : Type u₂} →     [inst : CommRing R] →       [inst_1 
: CommRing S] →         (f : R →+* S) → {Y : ModuleCat S} → ((ModuleCat.restrict
Scalars f).comp (ModuleCat.extendScalars f)).obj Y ⟶ Y
参数：f : R →+* S；(ModuleCat.restrictScalars f).comp (ModuleCat.extendScalars f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y`
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
            rw [← mul_smul, mul_comm, mul_smul] },
        map_add' := fun s₁ s₂ => by
          ext y
          change (s₁ + s₂) • y = s₁ • y + s₂ • y
          rw [add_smul]
        map_smul' := fun r s => by
          ext y
          change (f r • s) • y = (f r) • s • y
          rw [smul_eq_mul, mul_smul] }
    map_add' := fun _ _ => by rw [map_add]
    map_smul' := fun s z => by
      let m1 : Module R S := Module.compHom S f
      let m2 : Module R Y := Module.compHom Y f
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s' y => simp [mul_smul]
      | add _ _ ih1 ih2 => rw [smul_add, map_add, map_add, ih1, ih2, smul_add] }
/-
**ModuleCat.ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul** 是 Mathlib 中的一个定
理，位于命名空间 `ModuleCat.ExtendRestrictScalarsAdj.Counit`。
形式化陈述：∀ {R : Type u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] (f
 : R →+* S) {Y : ModuleCat S} (y : ↑Y),   (CategoryTheory.ConcreteCategory.hom (
ModuleCat.ExtendRestrictScalarsAdj.Counit.map f)) (1 ⊗ₜ[R] y) = y
参数：f : R →+* S；y : ↑Y；CategoryTheory.ConcreteCategory.hom (ModuleCat.ExtendRestr
ictScalarsAdj.Counit.map f)；1 ⊗ₜ[R] y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Counit.map_apply_one_tmul {Y : ModuleCat S} (y : Y) :
    Counit.map f ((1 : S) ⊗ₜ[R] y) = y := by
  change (1 : S) • y = y
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps app]
/-
**ModuleCat.ExtendRestrictScalarsAdj.counit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat
.ExtendRestrictScalarsAdj`。
形式化陈述：counit : restrictScalars.{max v u₂, u₁, u₂} f ⋙ extendScalars f ⟶ 𝟭 (Modul
eCat S) where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from the composition of restriction and extension of 
scalars to the
identity functor on `S`-module.
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
      rw [lift.tmul, LinearMap.coe_mk, LinearMap.coe_mk]
      set s' : S := s'
      change s' • g y = g (s' • y)
      rw [map_smul]
    | add _ _ ih₁ ih₂ => rw [map_add, map_add]; congr 1
end ExtendRestrictScalarsAdj

set_option backward.isDefEq.respectTransparency false in
/-- Given commutative rings `R, S` and a ring hom `f : R →+* S`, the extension and restriction of
scalars by `f` are adjoint to each other.
-/
/-
**ModuleCat.extendRestrictScalarsAdj** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRin
g S] (f : R ->+* S) : extendScalars.{u₁, u₂, max v u₂} f ⊣ restrictScalars.{max 
v u₂, u₁, u₂} f
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given commutative rings `R, S` and a ring hom `f : R →+* S`, the extension and r
estriction of
scalars by `f` are adjoint to each other.
-/
def extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    extendScalars.{u₁, u₂, max v u₂} f ⊣ restrictScalars.{max v u₂, u₁, u₂} f :=
  Adjunction.mk' {
    homEquiv := fun _ _ ↦ ExtendRestrictScalarsAdj.homEquiv.{v, u₁, u₂} f
    unit := ExtendRestrictScalarsAdj.unit.{v, u₁, u₂} f
    counit := ExtendRestrictScalarsAdj.counit.{v, u₁, u₂} f
    homEquiv_unit := fun {X Y g} ↦ hom_ext <| LinearMap.ext fun x => by
      dsimp
      rfl
    homEquiv_counit := fun {X Y g} ↦ hom_ext <| LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul =>
          rw [ExtendRestrictScalarsAdj.homEquiv_symm_apply]
          dsimp
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [ExtendRestrictScalarsAdj.Counit.map_hom_apply,
              ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
        | add => rw [map_add, map_add]; congr 1 }
/-
**ModuleCat.extendRestrictScalarsAdj_homEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `M
oduleCat`。
形式化陈述：extendRestrictScalarsAdj_homEquiv_apply {R : Type u₁} {S : Type u₂} [CommR
ing R] [CommRing S] {f : R ->+* S} {M : ModuleCat.{max v u₂} R} {N : ModuleCat S
} (φ : (extendScalars f).obj M ⟶ N) (m : M) : (extendRestrictScalarsAdj f).homEq
uiv _ _ φ m = φ ((1 : S) otimesₜ m)
参数：φ : (extendScalars f).obj M ⟶ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendRestrictScalarsAdj_homEquiv_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    {f : R →+* S} {M : ModuleCat.{max v u₂} R} {N : ModuleCat S}
    (φ : (extendScalars f).obj M ⟶ N) (m : M) :
    (extendRestrictScalarsAdj f).homEquiv _ _ φ m = φ ((1 : S) ⊗ₜ m) :=
  rfl
/-
**ModuleCat.extendRestrictScalarsAdj_unit_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `M
oduleCat`。
形式化陈述：extendRestrictScalarsAdj_unit_app_apply {R : Type u₁} {S : Type u₂} [CommR
ing R] [CommRing S] (f : R ->+* S) (M : ModuleCat.{max v u₂} R) (m : M) : (exten
dRestrictScalarsAdj f).unit.app M m = (1 : S) otimesₜ[R,f] m
参数：f : R ->+* S；M : ModuleCat.{max v u₂} R；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendRestrictScalarsAdj_unit_app_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{max v u₂} R) (m : M) :
    (extendRestrictScalarsAdj f).unit.app M m = (1 : S) ⊗ₜ[R,f] m :=
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul** 是 Mathlib 中的一个引
理，位于命名空间 `ModuleCat`。
形式化陈述：extendRestrictScalarsAdj_counit_app_apply_one_tmul (M : ModuleCat S) (m : 
M) : dsimp% (extendRestrictScalarsAdj f).counit.app M ((1 : S) otimesₜ[R] m) = m
参数：M : ModuleCat S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul`：∀ {R : Typ
e u₁} {S : Type u₂} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S) {Y :
 ModuleCat S} (y : ↑Y),   (CategoryTheory.Concrete…
-/
lemma extendRestrictScalarsAdj_counit_app_apply_one_tmul (M : ModuleCat S) (m : M) :
    dsimp% (extendRestrictScalarsAdj f).counit.app M ((1 : S) ⊗ₜ[R] m) = m := by
  apply ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    (extendScalars.{u₁, u₂, max u₂ w} f).IsLeftAdjoint :=
  (extendRestrictScalarsAdj f).isLeftAdjoint
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    (restrictScalars.{max u₂ w, u₁, u₂} f).IsRightAdjoint :=
  (extendRestrictScalarsAdj f).isRightAdjoint
/-
**ModuleCat.preservesLimit_restrictScalars** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`
。
形式化陈述：preservesLimit_restrictScalars {R : Type*} {S : Type*} [Ring R] [Ring S] (
f : R ->+* S) {J : Type*} [Category* J] (F : J ⥤ ModuleCat.{v} S) [Small.{v} (F 
⋙ forget _).sections] : PreservesLimit F (restrictScalars f)
参数：f : R ->+* S；F : J ⥤ ModuleCat.{v} S；F ⋙ forget _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance preservesLimit_restrictScalars
    {R : Type*} {S : Type*} [Ring R] [Ring S] (f : R →+* S) {J : Type*} [Category* J]
    (F : J ⥤ ModuleCat.{v} S) [Small.{v} (F ⋙ forget _).sections] :
    PreservesLimit F (restrictScalars f) :=
  ⟨fun {c} hc => ⟨by
    have hc' := isLimitOfPreserves (forget₂ _ AddCommGrpCat) hc
    exact isLimitOfReflects (forget₂ _ AddCommGrpCat) hc'⟩⟩
/-
**ModuleCat.preservesColimit_restrictScalars** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCa
t`。
形式化陈述：preservesColimit_restrictScalars {R S : Type*} [Ring R] [Ring S] (f : R ->
+* S) {J : Type*} [Category* J] (F : J ⥤ ModuleCat.{v} S) [HasColimit (F ⋙ forge
t₂ _ AddCommGrpCat)] : PreservesColimit F (ModuleCat.restrictScalars.{v} f)
参数：f : R ->+* S；F : J ⥤ ModuleCat.{v} S；F ⋙ forget₂ _ AddCommGrpCat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `ModuleCat.HasColimit.instPreservesColimitAddCommGrpCatForget₂LinearMapId
CarrierAddMonoidHomCarrier`：∀ {R : Type w} [inst : Ring R] {J : Type u} [inst_1 
: CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Functor J (ModuleCat R
))   [Ca…
-/
instance preservesColimit_restrictScalars {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {J : Type*} [Category* J] (F : J ⥤ ModuleCat.{v} S)
    [HasColimit (F ⋙ forget₂ _ AddCommGrpCat)] :
    PreservesColimit F (ModuleCat.restrictScalars.{v} f) := by
  have : HasColimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    inferInstanceAs (HasColimit (F ⋙ forget₂ _ AddCommGrpCat))
  apply preservesColimit_of_preserves_colimit_cocone (HasColimit.isColimitColimitCocone F)
  apply isColimitOfReflects (forget₂ (ModuleCat.{v} R) AddCommGrpCat)
  apply isColimitOfPreserves (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})
  exact HasColimit.isColimitColimitCocone F

variable (R) in
/-- The extension of scalars by the identity of a ring is isomorphic to the
identity functor. -/
/-
**ModuleCat.extendScalarsId** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：extendScalarsId : extendScalars (RingHom.id R) ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The extension of scalars by the identity of a ring is isomorphic to the
identity functor.
-/
noncomputable def extendScalarsId : extendScalars (RingHom.id R) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id).symm
    (restrictScalarsId R)).symm
/-
**ModuleCat.extendScalarsId_inv_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：extendScalarsId_inv_app_apply (M : ModuleCat R) (m : M) : (extendScalarsId
 R).inv.app M m = (1 : R) otimesₜ m
参数：M : ModuleCat R；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendScalarsId_inv_app_apply (M : ModuleCat R) (m : M) :
    (extendScalarsId R).inv.app M m = (1 : R) ⊗ₜ m := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.homEquiv_extendScalarsId** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：homEquiv_extendScalarsId (M : ModuleCat R) : (extendRestrictScalarsAdj (Ri
ngHom.id R)).homEquiv _ _ ((extendScalarsId R).hom.app M) = (restrictScalarsId R
).inv.app M
参数：M : ModuleCat R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModuleCat.extendRestrictScalarsAdj_homEquiv_apply`：extendRestrictScalars
Adj_homEquiv_apply {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] {f : R 
->+* S} {M : ModuleCat.{max v u₂} R} {N…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModuleCat.extendScalarsId_inv_app_apply`：extendScalarsId_inv_app_apply (
M : ModuleCat R) (m : M) : (extendScalarsId R).inv.app M m = (1 : R) otimesₜ m
· 使用引理 `ModuleCat.comp_apply`：comp_apply {M N O : ModuleCat.{v} R} (f : M ⟶ N) (
g : N ⟶ O) (x : M) : (f ≫ g) x = g (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `ModuleCat.restrictScalarsId'_inv_app`：∀ {R : Type u₁} [inst : Ring R] (f
 : R →+* R) (hf : f = RingHom.id R) (X : ModuleCat R),   (ModuleCat.restrictScal
arsId' f hf).inv.app X = (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_extendScalarsId (M : ModuleCat R) :
    (extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _ ((extendScalarsId R).hom.app M) =
      (restrictScalarsId R).inv.app M := by
  ext m
  rw [extendRestrictScalarsAdj_homEquiv_apply, ← extendScalarsId_inv_app_apply, ← comp_apply]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.extendScalarsId_hom_app_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCa
t`。
形式化陈述：extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) : (extendScalar
sId R).hom.app M ((1 : R) otimesₜ m) = m
参数：M : ModuleCat R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModuleCat.extendRestrictScalarsAdj_homEquiv_apply`：extendRestrictScalars
Adj_homEquiv_apply {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] {f : R 
->+* S} {M : ModuleCat.{max v u₂} R} {N…
· 使用引理 `ModuleCat.homEquiv_extendScalarsId`：homEquiv_extendScalarsId (M : Module
Cat R) : (extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _ ((extendScalarsI
d R).hom.app M) = (restr…
-/
lemma extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) :
    (extendScalarsId R).hom.app M ((1 : R) ⊗ₜ m) = m := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply,
    homEquiv_extendScalarsId]
  dsimp

section

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

/-- The extension of scalars by a composition of commutative ring morphisms
identifies to the composition of the extension of scalars functors. -/
/-
**ModuleCat.extendScalarsComp** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：extendScalarsComp : extendScalars (f₂₃.comp f₁₂) ≅ extendScalars f₁₂ ⋙ ext
endScalars f₂₃
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The extension of scalars by a composition of commutative ring morphisms
identifies to the composition of the extension of scalars functors.
-/
noncomputable def extendScalarsComp :
    extendScalars (f₂₃.comp f₁₂) ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃ :=
  (conjugateIsoEquiv
    ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂))).symm (restrictScalarsComp f₁₂ f₂₃).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**ModuleCat.homEquiv_extendScalarsComp** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：homEquiv_extendScalarsComp (M : ModuleCat R₁) : (extendRestrictScalarsAdj 
(f₂₃.comp f₁₂)).homEquiv _ _ ((extendScalarsComp f₁₂ f₂₃).hom.app M) = (extendRe
strictScalarsAdj f₁₂).unit.app M ≫ (restrictScalars f₁₂).map ((extendRestrictSca
larsAdj f₂₃).unit.app _) ≫ (restrictScalarsComp f₁₂ f₂₃).inv.app _
参数：M : ModuleCat R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
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
/-
**ModuleCat.extendScalarsComp_hom_app_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Module
Cat`。
形式化陈述：extendScalarsComp_hom_app_one_tmul (M : ModuleCat R₁) (m : M) : (extendSca
larsComp f₁₂ f₂₃).hom.app M ((1 : R₃) otimesₜ m) = (1 : R₃) otimesₜ[R₂,f₂₃] ((1 
: R₂) otimesₜ[R₁,f₁₂] m)
参数：M : ModuleCat R₁；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.sMulCommClass_mk`：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R
] [inst_1 : CommRing S] (f : R →+* S) (M : Type v) [I : AddCommGroup M]   [inst_
2 : _root_.Modul…
· 使用定理 `Semiring.mul_zero`：∀ {α : Type u} [self : Semiring α] (a : α), a * 0 = 0
· 使用定理 `Semiring.zero_mul`：∀ {α : Type u} [self : Semiring α] (a : α), 0 * a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModuleCat.extendRestrictScalarsAdj_homEquiv_apply`：extendRestrictScalars
Adj_homEquiv_apply {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] {f : R 
->+* S} {M : ModuleCat.{max v u₂} R} {N…
· 使用引理 `ModuleCat.homEquiv_extendScalarsComp`：homEquiv_extendScalarsComp (M : Mo
duleCat R₁) : (extendRestrictScalarsAdj (f₂₃.comp f₁₂)).homEquiv _ _ ((extendSca
larsComp f₁₂ f₂₃).hom.app …
-/
lemma extendScalarsComp_hom_app_one_tmul (M : ModuleCat R₁) (m : M) :
    (extendScalarsComp f₁₂ f₂₃).hom.app M ((1 : R₃) ⊗ₜ m) =
      (1 : R₃) ⊗ₜ[R₂,f₂₃] ((1 : R₂) ⊗ₜ[R₁,f₁₂] m) := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply, homEquiv_extendScalarsComp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**ModuleCat.extendScalars_assoc** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：extendScalars_assoc : (extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫ Functor
.whiskerRight (extendScalarsComp f₁₂ f₂₃).hom _ = (extendScalarsComp f₁₂ (f₃₄.co
mp f₂₃)).hom ≫ Functor.whiskerLeft _ (extendScalarsComp f₂₃ f₃₄).hom ≫ (Functor.
associator _ _ _).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ModuleCat.ExtendScalars.hom_ext`：hom_ext {M : ModuleCat R} {N : ModuleCa
t S} {α β : (extendScalars f).obj M ⟶ N} (h : forall (m : M), α ((1 : S) otimesₜ
 m) = β ((1 : S) otim…
· 使用定理 `ModuleCat.sMulCommClass_mk`：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R
] [inst_1 : CommRing S] (f : R →+* S) (M : Type v) [I : AddCommGroup M]   [inst_
2 : _root_.Modul…
· 使用定理 `Semiring.mul_zero`：∀ {α : Type u} [self : Semiring α] (a : α), a * 0 = 0
· 使用定理 `Semiring.zero_mul`：∀ {α : Type u} [self : Semiring α] (a : α), 0 * a = 0
· 使用引理 `ModuleCat.extendScalarsComp_hom_app_one_tmul`：extendScalarsComp_hom_app_
one_tmul (M : ModuleCat R₁) (m : M) : (extendScalarsComp f₁₂ f₂₃).hom.app M ((1 
: R₃) otimesₜ m) = (1 : R₃) otimes…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.ExtendScalars.map_tmul`：map_tmul {M M' : ModuleCat.{v} R} (g :
 M ⟶ M') (s : S) (m : M) : (extendScalars f).map g (s otimesₜ[R,f] m) = s otimes
ₜ[R,f] g m
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
  rw [h₃, ExtendScalars.map_tmul, h₄]

/-- The associativity compatibility for the extension of scalars, in the exact form
that is needed in the definition `CommRingCat.moduleCatExtendScalarsPseudofunctor`
in the file `Mathlib/Algebra/Category/ModuleCat/Pseudofunctor.lean` -/
/-
**ModuleCat.extendScalars_assoc'** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：extendScalars_assoc' : (extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫ Functo
r.whiskerRight (extendScalarsComp f₁₂ f₂₃).hom _ ≫ (Functor.associator _ _ _).ho
m ≫ Functor.whiskerLeft _ (extendScalarsComp f₂₃ f₃₄).inv ≫ (extendScalarsComp f
₁₂ (f₃₄.comp f₂₃)).inv = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.extendScalars_assoc_assoc`：∀ {R₁ R₂ R₃ R₄ : Type u₁} [inst : C
ommRing R₁] [inst_1 : CommRing R₂] [inst_2 : CommRing R₃] [inst_3 : CommRing R₄]
   (f₁₂ : R₁ →+* R₂) (f₂₃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The associativity compatibility for the extension of scalars, in the exact form
that is needed in the definition `CommRingCat.moduleCatExtendScalarsPseudofuncto
r`
in the file `Mathlib/Algebra/Category/ModuleCat/Pseudofunctor.lean`
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
/-
**ModuleCat.extendScalars_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：extendScalars_id_comp : (extendScalarsComp (RingHom.id R₁) f₁₂).hom ≫ Func
tor.whiskerRight (extendScalarsId R₁).hom _ ≫ (Functor.leftUnitor _).hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ModuleCat.ExtendScalars.hom_ext`：hom_ext {M : ModuleCat R} {N : ModuleCa
t S} {α β : (extendScalars f).obj M ⟶ N} (h : forall (m : M), α ((1 : S) otimesₜ
 m) = β ((1 : S) otim…
· 使用定理 `ModuleCat.sMulCommClass_mk`：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R
] [inst_1 : CommRing S] (f : R →+* S) (M : Type v) [I : AddCommGroup M]   [inst_
2 : _root_.Modul…
· 使用定理 `Semiring.mul_zero`：∀ {α : Type u} [self : Semiring α] (a : α), a * 0 = 0
· 使用定理 `Semiring.zero_mul`：∀ {α : Type u} [self : Semiring α] (a : α), 0 * a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModuleCat.extendScalarsComp_hom_app_one_tmul`：extendScalarsComp_hom_app_
one_tmul (M : ModuleCat R₁) (m : M) : (extendScalarsComp f₁₂ f₂₃).hom.app M ((1 
: R₃) otimesₜ m) = (1 : R₃) otimes…
· 使用定理 `ModuleCat.ExtendScalars.map_tmul`：map_tmul {M M' : ModuleCat.{v} R} (g :
 M ⟶ M') (s : S) (m : M) : (extendScalars f).map g (s otimesₜ[R,f] m) = s otimes
ₜ[R,f] g m
· 使用引理 `ModuleCat.extendScalarsId_hom_app_one_tmul`：extendScalarsId_hom_app_one_
tmul (M : ModuleCat R) (m : M) : (extendScalarsId R).hom.app M ((1 : R) otimesₜ 
m) = m
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
/-
**ModuleCat.extendScalars_comp_id** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：extendScalars_comp_id : (extendScalarsComp f₁₂ (RingHom.id R₂)).hom ≫ Func
tor.whiskerLeft _ (extendScalarsId R₂).hom ≫ (Functor.rightUnitor _).hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ModuleCat.ExtendScalars.hom_ext`：hom_ext {M : ModuleCat R} {N : ModuleCa
t S} {α β : (extendScalars f).obj M ⟶ N} (h : forall (m : M), α ((1 : S) otimesₜ
 m) = β ((1 : S) otim…
· 使用定理 `ModuleCat.sMulCommClass_mk`：∀ {R : Type u₁} {S : Type u₂} [inst : Ring R
] [inst_1 : CommRing S] (f : R →+* S) (M : Type v) [I : AddCommGroup M]   [inst_
2 : _root_.Modul…
· 使用定理 `Semiring.mul_zero`：∀ {α : Type u} [self : Semiring α] (a : α), a * 0 = 0
· 使用定理 `Semiring.zero_mul`：∀ {α : Type u} [self : Semiring α] (a : α), 0 * a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModuleCat.extendScalarsComp_hom_app_one_tmul`：extendScalarsComp_hom_app_
one_tmul (M : ModuleCat R₁) (m : M) : (extendScalarsComp f₁₂ f₂₃).hom.app M ((1 
: R₃) otimesₜ m) = (1 : R₃) otimes…
· 使用引理 `ModuleCat.extendScalarsId_hom_app_one_tmul`：extendScalarsId_hom_app_one_
tmul (M : ModuleCat R) (m : M) : (extendScalarsId R).hom.app M ((1 : R) otimesₜ 
m) = m
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

