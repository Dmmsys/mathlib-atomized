/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves of (commutative) rings.

Results specific to sheaves of commutative rings including sheaves of continuous functions
`TopCat.continuousFunctions` with natural operations of `pullback` and `map` and
sub, quotient, and localization operations on sheaves of rings with
- `SubmonoidPresheaf` : A subpresheaf with a submonoid structure on each of the components.
- `LocalizationPresheaf` : The localization of a presheaf of commrings at a `SubmonoidPresheaf`.
- `TotalQuotientPresheaf` : The presheaf of total quotient rings.

As more results accumulate, please consider splitting this file.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

@[expose] public section

universe u v w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.

Note that the universes for `TopCat` and `CommRingCat` must be the same for this argument
to go through.
-/
example (X : TopCat.{u₁}) (F : Presheaf CommRingCat.{u₁} X)
    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :
    F.IsSheaf :=
(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h

open AlgebraicGeometry in
/--
lemma `restrictOpenCommRingCat_apply` / 引理 `restrictOpenCommRingCat_apply`

English:
lemma restrictOpenCommRingCat_apply
  statement: {X : TopCat.{w}}
  proof: rfl

中文:
引理 restrictOpenCommRingCat_apply
  结论: {X : TopCat.{w}}
  证明: rfl

Depends on / 依赖: F.map, homOfLE, restrict_tac
-/
lemma restrictOpenCommRingCat_apply {X : TopCat.{w}}
    {F : Presheaf CommRingCat X} {V : Opens ↑X} (f : CommRingCat.carrier (F.obj (op V)))
    (U : Opens ↑X) (e : U <= V := by restrict_tac) :
    f |_ U = F.map (homOfLE e).op f :=
  rfl

section SubmonoidPresheaf

open scoped nonZeroDivisors

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]

-- note: this was specialized to `CommRingCat` in https://github.com/leanprover-community/mathlib4/issues/19757
/--
Definition of `SubmonoidPresheaf` / `SubmonoidPresheaf` 的定义

English:
structure SubmonoidPresheaf
  parameters: (F : X.Presheaf CommRingCat)
  axioms and operations (2):
    - obj : forall U, Submonoid (F.obj U)
    - map : forall {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U <= (obj V).comap (F.map i).hom

中文:
结构 SubmonoidPresheaf
  参数: (F : X.Presheaf CommRingCat)
  公理与运算 (2 个):
    - obj : 对任意 U, Submonoid (F.obj U)
    - map : 对任意 {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U <= (obj V).comap (F.map i).hom

Depends on / 依赖: CommRingCat, CommRingCat.of, G.obj, Localization
-/
structure SubmonoidPresheaf (F : X.Presheaf CommRingCat) where
  /-- The submonoid structure for each component -/
  obj : forall U, Submonoid (F.obj U)
  map : forall {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U <= (obj V).comap (F.map i).hom

variable {F : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def SubmonoidPresheaf.localizationPresheaf
  body: CommRingCat.of Localization (G.obj U)
map {_ _} i := CommRingCat.ofHom IsLocalization.map _ (F.map i).hom (G.map i)
  map_id U := by
    simp_rw [F.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.ma

中文:
定义 noncomputable
  签名: def SubmonoidPresheaf.localizationPresheaf
  定义体: CommRingCat.of Localization (G.obj U)
map {_ _} i := CommRingCat.ofHom IsLocalization.map _ (F.map i).hom (G.map i)
  map_id U := by
    simp_rw [F.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.ma
-/
protected noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCat where
obj U := CommRingCat.of Localization (G.obj U)
map {_ _} i := CommRingCat.ofHom IsLocalization.map _ (F.map i).hom (G.map i)
  map_id U := by
    simp_rw [F.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.map_comp]
    ext : 1
    dsimp
    rw [IsLocalization.map_comp_map]

instance (U) : Algebra (F.obj U) (G.localizationPresheaf.obj U) :=
inferInstanceAs Algebra (F.obj U) (Localization (G.obj U))

instance (U) : IsLocalization (G.obj U) (G.localizationPresheaf.obj U) :=
inferInstanceAs IsLocalization (G.obj U) (Localization (G.obj U))

set_option backward.isDefEq.respectTransparency false in
/-- The map into the localization presheaf. -/
@[simps app]
/--
Definition of `SubmonoidPresheaf.toLocalizationPresheaf` / `SubmonoidPresheaf.toLocalizationPresheaf` 的定义

English:
definition SubmonoidPresheaf.toLocalizationPresheaf
  signature: : F ⟶ G.localizationPresheaf where
  body: CommRingCat.ofHom algebraMap (F.obj U) (Localization <| G.obj U)
naturality {_ _} i := CommRingCat.hom_ext (IsLocalization.map_comp (G.map i)).symm

中文:
定义 SubmonoidPresheaf.toLocalizationPresheaf
  签名: : F ⟶ G.localizationPresheaf where
  定义体: CommRingCat.ofHom algebraMap (F.obj U) (Localization <| G.obj U)
naturality {_ _} i := CommRingCat.hom_ext (IsLocalization.map_comp (G.map i)).symm

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, F.obj, G.obj, Localization, algebraMap
-/
def SubmonoidPresheaf.toLocalizationPresheaf : F ⟶ G.localizationPresheaf where
app U := CommRingCat.ofHom algebraMap (F.obj U) (Localization <| G.obj U)
naturality {_ _} i := CommRingCat.hom_ext (IsLocalization.map_comp (G.map i)).symm

/--
Instance `epi_toLocalizationPresheaf` / 实例 `epi_toLocalizationPresheaf`

English:
instance epi_toLocalizationPresheaf
  signature: : Epi G.toLocalizationPresheaf
  body: @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

中文:
实例 epi_toLocalizationPresheaf
  签名: : Epi G.toLocalizationPresheaf
  定义体: @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

Depends on / 依赖: G.obj, G.toLocalizationPresheaf, Localization, Localization.epi, NatTrans, NatTrans.epi_of_epi_app, epi_of_epi_app, toLocalizationPresheaf
-/
instance epi_toLocalizationPresheaf : Epi G.toLocalizationPresheaf :=
  @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

variable (F)

/-- Given a submonoid at each of the stalks, we may define a submonoid presheaf consisting of
sections whose restriction onto each stalk falls in the given submonoid. -/
@[simps]
/--
Definition of `submonoidPresheafOfStalk` / `submonoidPresheafOfStalk` 的定义

English:
definition submonoidPresheafOfStalk
  signature: (S : forall x : X, Submonoid (F.stalk x))
  body: ⨅ x : U.unop, Submonoid.comap (F.germ U.unop x.1 x.2).hom (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ V.unop x.1 x.2) s in _
    rw [F.germ_res]
    exact hs ⟨_, i.unop.le x.2⟩

中文:
定义 submonoidPresheafOfStalk
  签名: (S : 对任意 x : X, Submonoid (F.stalk x))
  定义体: ⨅ x : U.unop, Submonoid.comap (F.germ U.unop x.1 x.2).hom (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ V.unop x.1 x.2) s in _
    rw [F.germ_res]
    exact hs ⟨_, i.unop.le x.2⟩

Depends on / 依赖: F.germ, Submonoid, Submonoid.comap, U.unop
-/
noncomputable def submonoidPresheafOfStalk (S : forall x : X, Submonoid (F.stalk x)) :
    F.SubmonoidPresheaf where
  obj U := ⨅ x : U.unop, Submonoid.comap (F.germ U.unop x.1 x.2).hom (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ V.unop x.1 x.2) s in _
    rw [F.germ_res]
    exact hs ⟨_, i.unop.le x.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited F.SubmonoidPresheaf
  body: ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩

中文:
实例 :
  签名: Inhabited F.SubmonoidPresheaf
  定义体: ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩

Depends on / 依赖: F.submonoidPresheafOfStalk, submonoidPresheafOfStalk
-/
noncomputable instance : Inhabited F.SubmonoidPresheaf :=
  ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩

/--
Definition of `totalQuotientPresheaf` / `totalQuotientPresheaf` 的定义

English:
definition totalQuotientPresheaf
  signature: : X.Presheaf CommRingCat.{w}
  body: (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf

中文:
定义 totalQuotientPresheaf
  签名: : X.Presheaf CommRingCat.{w}
  定义体: (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf

Depends on / 依赖: F.stalk, F.submonoidPresheafOfStalk, localizationPresheaf, submonoidPresheafOfStalk
-/
noncomputable def totalQuotientPresheaf : X.Presheaf CommRingCat.{w} :=
  (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf

/--
Definition of `toTotalQuotientPresheaf` / `toTotalQuotientPresheaf` 的定义

English:
definition toTotalQuotientPresheaf
  signature: : F ⟶ F.totalQuotientPresheaf
  body: SubmonoidPresheaf.toLocalizationPresheaf _
deriving Epi

中文:
定义 toTotalQuotientPresheaf
  签名: : F ⟶ F.totalQuotientPresheaf
  定义体: SubmonoidPresheaf.toLocalizationPresheaf _
deriving Epi

Depends on / 依赖: SubmonoidPresheaf, SubmonoidPresheaf.toLocalizationPresheaf, toLocalizationPresheaf
-/
noncomputable def toTotalQuotientPresheaf : F ⟶ F.totalQuotientPresheaf :=
  SubmonoidPresheaf.toLocalizationPresheaf _
deriving Epi

instance (F : X.Sheaf CommRingCat.{w}) : Mono F.presheaf.toTotalQuotientPresheaf := by
  apply +allowSynthFailures NatTrans.mono_of_mono_app
  intro U
  apply ConcreteCategory.mono_of_injective
  dsimp [toTotalQuotientPresheaf]
  -- Porting note: `M` and `S` need to be specified manually, so used a hack to save some typing
  set m := _
  change Function.Injective (algebraMap _ (Localization m))
  refine IsLocalization.injective (M := m) (S := Localization m) ?_
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
  intro s hs t e
  apply section_ext F (unop U)
  intro x hx
  rw [map_zero]
  apply (Submonoid.mem_iInf.mp hs ⟨x, hx⟩).2
  rw [← map_mul]; rw [e]; rw [map_zero]

end SubmonoidPresheaf

end TopCat.Presheaf

section ContinuousFunctions

namespace TopCat

variable (X : TopCat.{v}) (R : TopCommRingCat.{v})

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom n

中文:
实例 :
  签名: 自然数Cast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom n
-/
instance : NatCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  natCast n := ofHom n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom n

中文:
实例 :
  签名: 整数Cast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom n
-/
instance : IntCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  intCast n := ofHom n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom 0

中文:
实例 :
  签名: Zero (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom 0
-/
instance : Zero (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  zero := ofHom 0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom 1

中文:
实例 :
  签名: One (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom 1
-/
instance : One (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  one := ofHom 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom (-f.hom)

中文:
实例 :
  签名: Neg (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom (-f.hom)

Depends on / 依赖: f.hom
-/
instance : Neg (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  neg f := ofHom (-f.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom (f.hom - g.hom)

中文:
实例 :
  签名: Sub (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom (f.hom - g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Sub (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  sub f g := ofHom (f.hom - g.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom (f.hom + g.hom)

中文:
实例 :
  签名: Add (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom (f.hom + g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Add (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  add f g := ofHom (f.hom + g.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom (f.hom * g.hom)

中文:
实例 :
  签名: Mul (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom (f.hom * g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Mul (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  mul f g := ofHom (f.hom * g.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom (n • f.hom)

中文:
实例 :
  签名: SMul 自然数 (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom (n • f.hom)

Depends on / 依赖: f.hom
-/
instance : SMul Nat (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  smul n f := ofHom (n • f.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: ofHom (n • f.hom)

中文:
实例 :
  签名: SMul 整数 (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: ofHom (n • f.hom)

Depends on / 依赖: f.hom
-/
instance : SMul Int (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  smul n f := ofHom (n • f.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) Nat
  body: ofHom (f.hom ^ n)

中文:
实例 :
  签名: Pow (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) 自然数
  定义体: ofHom (f.hom ^ n)

Depends on / 依赖: f.hom
-/
instance : Pow (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) Nat where
  pow f n := ofHom (f.hom ^ n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  body: Function.Injective.commRing _ ConcreteCategory.hom_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

中文:
实例 :
  签名: CommRing (X ⟶ (forget₂ TopCommRingCat TopCat).obj R)
  定义体: Function.Injective.commRing _ ConcreteCategory.hom_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_injective, Function, Function.Injective.commRing, Injective, commRing, hom_injective
-/
instance : CommRing (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) :=
  Function.Injective.commRing _ ConcreteCategory.hom_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

-- TODO upgrade the result to TopCommRing?
/--
Definition of `continuousFunctions` / `continuousFunctions` 的定义

English:
definition continuousFunctions
  signature: (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v})
  body: CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R)

中文:
定义 continuousFunctions
  签名: (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v})
  定义体: CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R)

Depends on / 依赖: CommRingCat, CommRingCat.of, TopCat, TopCommRingCat, X.unop
-/
def continuousFunctions (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v}) : CommRingCat.{v} :=
  CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R)

namespace continuousFunctions

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat)
  body: CommRingCat.ofHom
  { toFun g := f.unop ≫ g
    map_one' := rfl
    map_zero' := rfl
    map_add' := by cat_disch
    map_mul' := by cat_disch }

中文:
定义 pullback
  签名: {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat)
  定义体: CommRingCat.ofHom
  { toFun g := f.unop ≫ g
    map_one' := rfl
    map_zero' := rfl
    map_add' := by cat_disch
    map_mul' := by cat_disch }

Depends on / 依赖: CommRingCat, CommRingCat.ofHom
-/
def pullback {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat) :
    continuousFunctions X R ⟶ continuousFunctions Y R := CommRingCat.ofHom
  { toFun g := f.unop ≫ g
    map_one' := rfl
    map_zero' := rfl
    map_add' := by cat_disch
    map_mul' := by cat_disch }

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S)
  body: CommRingCat.ofHom
  { toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
    map_one' := by ext; exact φ.1.map_one
    map_zero' := by ext; exact φ.1.map_zero
    map_add' _ _ := by ext; exact φ.1.map_add _ _
    map_mul' _ _ := by ext; exact φ.1.map_mul _ _ }

中文:
定义 map
  签名: (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S)
  定义体: CommRingCat.ofHom
  { toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
    map_one' := by ext; exact φ.1.map_one
    map_zero' := by ext; exact φ.1.map_zero
    map_add' _ _ := by ext; exact φ.1.map_add _ _
    map_mul' _ _ := by ext; exact φ.1.map_mul _ _ }

Depends on / 依赖: CommRingCat, CommRingCat.ofHom
-/
def map (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S) :
    continuousFunctions X R ⟶ continuousFunctions X S := CommRingCat.ofHom
  { toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
    map_one' := by ext; exact φ.1.map_one
    map_zero' := by ext; exact φ.1.map_zero
    map_add' _ _ := by ext; exact φ.1.map_add _ _
    map_mul' _ _ := by ext; exact φ.1.map_mul _ _ }

end continuousFunctions

/--
Definition of `commRingYoneda` / `commRingYoneda` 的定义

English:
definition commRingYoneda
  signature: : TopCommRingCat.{u} ⥤ TopCat.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  body: { obj := fun X => continuousFunctions X R
      map := fun {_ _} f => continuousFunctions.pullback f R
      map_id := fun X => by
        ext
        rfl
      map_comp := fun {_ _ _} _ _ => rfl }
  map {_ _} φ :=
    { app := fun X => continuousFunctions.map X φ
      naturality := fun _ _ _ => rf

中文:
定义 commRingYoneda
  签名: : TopCommRingCat.{u} ⥤ TopCat.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  定义体: { obj := fun X => continuousFunctions X R
      map := fun {_ _} f => continuousFunctions.pullback f R
      map_id := fun X => by
        ext
        rfl
      map_comp := fun {_ _ _} _ _ => rfl }
  map {_ _} φ :=
    { app := fun X => continuousFunctions.map X φ
      naturality := fun _ _ _ => rf

Depends on / 依赖: continuousFunctions, continuousFunctions.map, continuousFunctions.pullback, map_comp, map_id, naturality, pullback
-/
def commRingYoneda : TopCommRingCat.{u} ⥤ TopCat.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  obj R :=
    { obj := fun X => continuousFunctions X R
      map := fun {_ _} f => continuousFunctions.pullback f R
      map_id := fun X => by
        ext
        rfl
      map_comp := fun {_ _ _} _ _ => rfl }
  map {_ _} φ :=
    { app := fun X => continuousFunctions.map X φ
      naturality := fun _ _ _ => rfl }
  map_id X := by
    ext
    rfl
  map_comp {_ _ _} _ _ := rfl

/--
Definition of `presheafToTopCommRing` / `presheafToTopCommRing` 的定义

English:
definition presheafToTopCommRing
  signature: (T : TopCommRingCat.{v})
  body: (Opens.toTopCat X).op ⋙ commRingYoneda.obj T

中文:
定义 presheafToTopCommRing
  签名: (T : TopCommRingCat.{v})
  定义体: (Opens.toTopCat X).op ⋙ commRingYoneda.obj T

Depends on / 依赖: Opens.toTopCat, commRingYoneda, commRingYoneda.obj, toTopCat
-/
def presheafToTopCommRing (T : TopCommRingCat.{v}) : X.Presheaf CommRingCat.{v} :=
  (Opens.toTopCat X).op ⋙ commRingYoneda.obj T

end TopCat

end ContinuousFunctions

section Stalks

namespace TopCat.Presheaf

variable {X Y Z : TopCat.{v}}

/--
Instance `algebra_section_stalk` / 实例 `algebra_section_stalk`

English:
instance algebra_section_stalk
  signature: (F : X.Presheaf CommRingCat) {U : Opens X} (x : U)
  body: (F.germ U x.1 x.2).hom.toAlgebra

@[simp]

中文:
实例 algebra_section_stalk
  签名: (F : X.Presheaf CommRingCat) {U : Opens X} (x : U)
  定义体: (F.germ U x.1 x.2).hom.toAlgebra

@[simp]

Depends on / 依赖: F.germ, hom.toAlgebra, toAlgebra
-/
instance algebra_section_stalk (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ U x.1 x.2).hom.toAlgebra

@[simp]
/--
theorem `stalk_open_algebraMap` / 定理 `stalk_open_algebraMap`

English:
theorem stalk_open_algebraMap
  given: {X : TopCat.{v}} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U)
  proof: rfl

中文:
定理 stalk_open_algebraMap
  条件: {X : TopCat.{v}} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U)
  证明: rfl
-/
theorem stalk_open_algebraMap {X : TopCat.{v}} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    algebraMap (F.obj <| op U) (F.stalk x) = (F.germ U x.1 x.2).hom :=
  rfl

end TopCat.Presheaf

end Stalks

noncomputable section Gluing

namespace TopCat.Sheaf

open TopologicalSpace Opposite CategoryTheory

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/--
Definition of `objSupIsoProdEqLocus` / `objSupIsoProdEqLocus` 的定义

English:
definition objSupIsoProdEqLocus
  signature: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  body: (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)

中文:
定义 objSupIsoProdEqLocus
  签名: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  定义体: (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)

Depends on / 依赖: CommRingCat, CommRingCat.pullbackConeIsLimit, F.isLimitPullbackCone, conePointUniqueUpToIso, isLimitPullbackCone, pullbackConeIsLimit
-/
def objSupIsoProdEqLocus {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X) :
F.1.obj (op <| U ⊔ V) ≅ CommRingCat.of
    -- Porting note: Lean 3 is able to figure out the ring homomorphism automatically
    RingHom.eqLocus
      (RingHom.comp (F.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom
        (RingHom.fst (F.obj.obj <| op U) (F.obj.obj <| op V)))
      (RingHom.comp (F.obj.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom
        (RingHom.snd (F.obj.obj <| op U) (F.obj.obj <| op V))) :=
  (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)

/--
theorem `objSupIsoProdEqLocus_hom_fst` / 定理 `objSupIsoProdEqLocus_hom_fst`

English:
theorem objSupIsoProdEqLocus_hom_fst
  statement: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  proof: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

中文:
定理 objSupIsoProdEqLocus_hom_fst
  结论: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  证明: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

Depends on / 依赖: CommRingCat, CommRingCat.pullbackConeIsLimit, ConcreteCategory, ConcreteCategory.congr_hom, F.isLimitPullbackCone, WalkingCospan, WalkingCospan.left, conePointUniqueUpToIso_hom_comp, congr_hom, isLimitPullbackCone, pullbackConeIsLimit
-/
theorem objSupIsoProdEqLocus_hom_fst {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.fst = F.1.map (homOfLE le_sup_left).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

/--
theorem `objSupIsoProdEqLocus_hom_snd` / 定理 `objSupIsoProdEqLocus_hom_snd`

English:
theorem objSupIsoProdEqLocus_hom_snd
  statement: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  proof: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

中文:
定理 objSupIsoProdEqLocus_hom_snd
  结论: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  证明: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

Depends on / 依赖: CommRingCat, CommRingCat.pullbackConeIsLimit, ConcreteCategory, ConcreteCategory.congr_hom, F.isLimitPullbackCone, WalkingCospan, WalkingCospan.right, conePointUniqueUpToIso_hom_comp, congr_hom, isLimitPullbackCone, pullbackConeIsLimit
-/
theorem objSupIsoProdEqLocus_hom_snd {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.snd = F.1.map (homOfLE le_sup_right).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

/--
theorem `objSupIsoProdEqLocus_inv_fst` / 定理 `objSupIsoProdEqLocus_inv_fst`

English:
theorem objSupIsoProdEqLocus_inv_fst
  statement: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  proof: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

中文:
定理 objSupIsoProdEqLocus_inv_fst
  结论: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  证明: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

Depends on / 依赖: CommRingCat, CommRingCat.pullbackConeIsLimit, ConcreteCategory, ConcreteCategory.congr_hom, F.isLimitPullbackCone, WalkingCospan, WalkingCospan.left, conePointUniqueUpToIso_inv_comp, congr_hom, isLimitPullbackCone, pullbackConeIsLimit
-/
theorem objSupIsoProdEqLocus_inv_fst {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    F.1.map (homOfLE le_sup_left).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.1 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

/--
theorem `objSupIsoProdEqLocus_inv_snd` / 定理 `objSupIsoProdEqLocus_inv_snd`

English:
theorem objSupIsoProdEqLocus_inv_snd
  statement: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  proof: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

中文:
定理 objSupIsoProdEqLocus_inv_snd
  结论: {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
  证明: ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

Depends on / 依赖: CommRingCat, CommRingCat.pullbackConeIsLimit, ConcreteCategory, ConcreteCategory.congr_hom, F.isLimitPullbackCone, WalkingCospan, WalkingCospan.right, conePointUniqueUpToIso_inv_comp, congr_hom, isLimitPullbackCone, pullbackConeIsLimit
-/
theorem objSupIsoProdEqLocus_inv_snd {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    F.1.map (homOfLE le_sup_right).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.2 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

/--
theorem `objSupIsoProdEqLocus_inv_eq_iff` / 定理 `objSupIsoProdEqLocus_inv_eq_iff`

English:
theorem objSupIsoProdEqLocus_inv_eq_iff
  statement: {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
  proof: by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]; rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq

中文:
定理 objSupIsoProdEqLocus_inv_eq_iff
  结论: {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
  证明: by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]; rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq

Depends on / 依赖: CommRingCat, CommRingCat.comp_app, CommRingCat.comp_apply, F.eq_of_locally_eq, Functor, Functor.map_comp, TopCat, TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd, and_self, comp_app, comp_apply, homOfLE, homOfLE_comp, inf_le_right, inf_sup_right, le_inf, le_rfl, map_comp, objSupIsoProdEqLocus_inv_fst
-/
theorem objSupIsoProdEqLocus_inv_eq_iff {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
    {U V W UW VW : Opens X} (e : W <= U ⊔ V) (x) (y : F.1.obj (op W))
    (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W) :
    F.1.map (homOfLE e).op ((F.objSupIsoProdEqLocus U V).inv x) = y ↔
    F.1.map (homOfLE (h₁ ▸ inf_le_left : UW <= U)).op x.1.1 =
      F.1.map (homOfLE <| h₁ ▸ inf_le_right).op y ∧
    F.1.map (homOfLE (h₂ ▸ inf_le_left : VW <= V)).op x.1.2 =
      F.1.map (homOfLE <| h₂ ▸ inf_le_right).op y := by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]; rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq₂
      (homOfLE (inf_le_right : U ⊓ W <= W)) (homOfLE (inf_le_right : V ⊓ W <= W)) ?_ _ _ ?_ ?_
    · rw [← inf_sup_right]
      exact le_inf e le_rfl
    · rw [← e₁, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    · rw [← e₂, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]

end TopCat.Sheaf

end Gluing
