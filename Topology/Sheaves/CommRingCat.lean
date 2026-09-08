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
`TopCat.continuousFunctions` with natural operations of  `pullback` and `map` and
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
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个示例，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.

Note that the universes for `TopCat` and `CommRingCat` must be the same for this
 argument
to go through.
-/
example (X : TopCat.{u₁}) (F : Presheaf CommRingCat.{u₁} X)
    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :
    F.IsSheaf :=
(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h

open AlgebraicGeometry in
/-- Unfold `restrictOpen` in the category of commutative rings (with the correct carrier type).

Although unification hints help with applying `TopCat.Presheaf.restrictOpenCommRingCat`,
so it can be safely de-specialized, this lemma needs to be kept to ensure rewrites go right.
-/
/-
**TopCat.Presheaf.restrictOpenCommRingCat_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCa
t.Presheaf`。
形式化陈述：restrictOpenCommRingCat_apply {X : TopCat.{w}} {F : Presheaf CommRingCat X
} {V : Opens ↑X} (f : CommRingCat.carrier (F.obj (op V))) (U : Opens ↑X) (e : U 
<= V
参数：f : CommRingCat.carrier (F.obj (op V))；U : Opens ↑X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold `restrictOpen` in the category of commutative rings (with the correct car
rier type).

Although unification hints help with applying `TopCat.Presheaf.restrictOpenCommR
ingCat`,
so it can be safely de-specialized, this lemma needs to be kept to ensure rewrit
es go right.
-/
lemma restrictOpenCommRingCat_apply {X : TopCat.{w}}
    {F : Presheaf CommRingCat X} {V : Opens ↑X} (f : CommRingCat.carrier (F.obj (op V)))
    (U : Opens ↑X) (e : U ≤ V := by restrict_tac) :
    f |_ U = F.map (homOfLE e).op f :=
  rfl

section SubmonoidPresheaf

open scoped nonZeroDivisors

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]

-- note: this was specialized to `CommRingCat` in https://github.com/leanprover-community/mathlib4/issues/19757
/-- A subpresheaf with a submonoid structure on each of the components. -/
/-
**TopCat.Presheaf.SubmonoidPresheaf** 是 Mathlib 中的一个结构，位于命名空间 `TopCat.Presheaf`。
形式化陈述：SubmonoidPresheaf (F : X.Presheaf CommRingCat) where /-- The submonoid str
ucture for each component -/ obj : forall U, Submonoid (F.obj U) map : forall {U
 V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U <= (obj V).comap (F.map i).hom  variable {F
 : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)  /-- The localization o
f a presheaf of `CommRing`s with respect to a `SubmonoidPresheaf`. -/ protected 
noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCa
t where obj U
参数：F : X.Presheaf CommRingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subpresheaf with a submonoid structure on each of the components.
-/
structure SubmonoidPresheaf (F : X.Presheaf CommRingCat) where
  /-- The submonoid structure for each component -/
  obj : ∀ U, Submonoid (F.obj U)
  map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U ≤ (obj V).comap (F.map i).hom

variable {F : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)

/-- The localization of a presheaf of `CommRing`s with respect to a `SubmonoidPresheaf`. -/
/-
**TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf** 是 Mathlib 中的一个定义，位于命名
空间 `TopCat.Presheaf.SubmonoidPresheaf`。
形式化陈述：{X : TopCat} → {F : TopCat.Presheaf CommRingCat X} → F.SubmonoidPresheaf →
 TopCat.Presheaf CommRingCat X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.SubmonoidPresheaf.map`：∀ {X : TopCat} {F : TopCat.Preshe
af CommRingCat X} (self : F.SubmonoidPresheaf) {U V : (TopologicalSpace.Opens ↑X
)ᵒᵖ}   (i : U ⟶ V), self.ob…

--- 原说明 ---
The localization of a presheaf of `CommRing`s with respect to a `SubmonoidPreshe
af`.
-/
protected noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCat where
  obj U := CommRingCat.of <| Localization (G.obj U)
  map {_ _} i := CommRingCat.ofHom <| IsLocalization.map _ (F.map i).hom (G.map i)
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
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U) : Algebra (F.obj U) (G.localizationPresheaf.obj U) :=
  inferInstanceAs <| Algebra (F.obj U) (Localization (G.obj U))
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U) : IsLocalization (G.obj U) (G.localizationPresheaf.obj U) :=
  inferInstanceAs <| IsLocalization (G.obj U) (Localization (G.obj U))

set_option backward.isDefEq.respectTransparency false in
/-- The map into the localization presheaf. -/
@[simps app]
/-
**TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf** 是 Mathlib 中的一个定义，位于
命名空间 `TopCat.Presheaf.SubmonoidPresheaf`。
形式化陈述：{X : TopCat} → {F : TopCat.Presheaf CommRingCat X} → (G : F.SubmonoidPresh
eaf) → F ⟶ G.localizationPresheaf
参数：G : F.SubmonoidPresheaf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map into the localization presheaf.
-/
def SubmonoidPresheaf.toLocalizationPresheaf : F ⟶ G.localizationPresheaf where
  app U := CommRingCat.ofHom <| algebraMap (F.obj U) (Localization <| G.obj U)
  naturality {_ _} i := CommRingCat.hom_ext <| (IsLocalization.map_comp (G.map i)).symm
/-
**TopCat.Presheaf.epi_toLocalizationPresheaf** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.P
resheaf`。
形式化陈述：epi_toLocalizationPresheaf : Epi G.toLocalizationPresheaf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.epi_of_epi_app`：epi_of_epi_app (α : F ⟶ G) [fora
ll X : C, Epi (α.app X)] : Epi α
-/
instance epi_toLocalizationPresheaf : Epi G.toLocalizationPresheaf :=
  @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

variable (F)

/-- Given a submonoid at each of the stalks, we may define a submonoid presheaf consisting of
sections whose restriction onto each stalk falls in the given submonoid. -/
@[simps]
/-
**TopCat.Presheaf.submonoidPresheafOfStalk** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Pre
sheaf`。
形式化陈述：submonoidPresheafOfStalk (S : forall x : X, Submonoid (F.stalk x)) : F.Sub
monoidPresheaf where obj U
参数：S : forall x : X, Submonoid (F.stalk x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submonoid at each of the stalks, we may define a submonoid presheaf cons
isting of
sections whose restriction onto each stalk falls in the given submonoid.
-/
noncomputable def submonoidPresheafOfStalk (S : ∀ x : X, Submonoid (F.stalk x)) :
    F.SubmonoidPresheaf where
  obj U := ⨅ x : U.unop, Submonoid.comap (F.germ U.unop x.1 x.2).hom (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ V.unop x.1 x.2) s ∈ _
    rw [F.germ_res]
    exact hs ⟨_, i.unop.le x.2⟩
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited F.SubmonoidPresheaf :=
  ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩

/-- The localization of a presheaf of `CommRing`s at locally non-zero-divisor sections. -/
/-
**TopCat.Presheaf.totalQuotientPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：totalQuotientPresheaf : X.Presheaf CommRingCat.{w}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization of a presheaf of `CommRing`s at locally non-zero-divisor sectio
ns.
-/
noncomputable def totalQuotientPresheaf : X.Presheaf CommRingCat.{w} :=
  (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf

/-- The map into the presheaf of total quotient rings -/
/-
**TopCat.Presheaf.toTotalQuotientPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Pres
heaf`。
形式化陈述：toTotalQuotientPresheaf : F ⟶ F.totalQuotientPresheaf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map into the presheaf of total quotient rings
-/
noncomputable def toTotalQuotientPresheaf : F ⟶ F.totalQuotientPresheaf :=
  SubmonoidPresheaf.toLocalizationPresheaf _
deriving Epi
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
  rw [← map_mul, e, map_zero]

end SubmonoidPresheaf

end TopCat.Presheaf

section ContinuousFunctions

namespace TopCat

variable (X : TopCat.{v}) (R : TopCommRingCat.{v})

/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  natCast n := ofHom n
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  intCast n := ofHom n
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  zero := ofHom 0
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  one := ofHom 1
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  neg f := ofHom (-f.hom)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  sub f g := ofHom (f.hom - g.hom)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  add f g := ofHom (f.hom + g.hom)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  mul f g := ofHom (f.hom * g.hom)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  smul n f := ofHom (n • f.hom)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  smul n f := ofHom (n • f.hom)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) ℕ where
  pow f n := ofHom (f.hom ^ n)
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) :=
  Function.Injective.commRing _ ConcreteCategory.hom_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

-- TODO upgrade the result to TopCommRing?
/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
/-
**TopCat.continuousFunctions** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：TopCatᵒᵖ → TopCommRingCat → CommRingCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication.
-/
def continuousFunctions (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v}) : CommRingCat.{v} :=
  CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R)

namespace continuousFunctions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
/-
**TopCat.continuousFunctions.pullback** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.continuo
usFunctions`。
形式化陈述：{X Y : TopCatᵒᵖ} → (X ⟶ Y) → (R : TopCommRingCat) → TopCat.continuousFunct
ions X R ⟶ TopCat.continuousFunctions Y R
参数：X ⟶ Y；R : TopCommRingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back functions into a topological ring along a continuous map is a ring 
homomorphism.
-/
def pullback {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat) :
    continuousFunctions X R ⟶ continuousFunctions Y R := CommRingCat.ofHom
  { toFun g := f.unop ≫ g
    map_one' := rfl
    map_zero' := rfl
    map_add' := by cat_disch
    map_mul' := by cat_disch }

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
/-
**TopCat.continuousFunctions.map** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.continuousFun
ctions`。
形式化陈述：(X : TopCatᵒᵖ) → {R S : TopCommRingCat} → (R ⟶ S) → (TopCat.continuousFunc
tions X R ⟶ TopCat.continuousFunctions X S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism of topological rings can be postcomposed with functions from a so
urce space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on fu
nctions).
-/
def map (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S) :
    continuousFunctions X R ⟶ continuousFunctions X S := CommRingCat.ofHom
  { toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
    map_one' := by ext; exact φ.1.map_one
    map_zero' := by ext; exact φ.1.map_zero
    map_add' _ _ := by ext; exact φ.1.map_add _ _
    map_mul' _ _ := by ext; exact φ.1.map_mul _ _ }

end continuousFunctions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : TopCat` to `R : TopCommRingCat` form a commutative ring, functorial in both `X` and
`R`. -/
/-
**TopCat.commRingYoneda** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：CategoryTheory.Functor TopCommRingCat (CategoryTheory.Functor TopCatᵒᵖ Com
mRingCat)
参数：CategoryTheory.Functor TopCatᵒᵖ CommRingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : TopCat` to `R : TopCommRingCat` form a commutative ring, functorial in
 both `X` and
`R`.
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

/-- The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex-valued functions of `X` as
```
presheafToTopCommRing X (TopCommRingCat.of ℂ)
```
(this requires `import Topology.Instances.Complex`).
-/
/-
**TopCat.presheafToTopCommRing** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：(X : TopCat) → TopCommRingCat → TopCat.Presheaf CommRingCat X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf (of commutative rings), consisting of functions on an open set `U ⊆
 X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex-valued functi
ons of `X` as
```
presheafToTopCommRing X (TopCommRingCat.of ℂ)
```
(this requires `import Topology.Instances.Complex`).
-/
def presheafToTopCommRing (T : TopCommRingCat.{v}) : X.Presheaf CommRingCat.{v} :=
  (Opens.toTopCat X).op ⋙ commRingYoneda.obj T

end TopCat

end ContinuousFunctions

section Stalks

namespace TopCat.Presheaf

variable {X Y Z : TopCat.{v}}

/-
**TopCat.Presheaf.algebra_section_stalk** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：{X : TopCat} →   (F : TopCat.Presheaf CommRingCat X) →     {U : Topologica
lSpace.Opens ↑X} → (x : ↥U) → Algebra ↑(F.obj (Opposite.op U)) ↑(F.stalk ↑x)
参数：F : TopCat.Presheaf CommRingCat X；x : ↥U；F.obj (Opposite.op U)；F.stalk ↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra_section_stalk (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ U x.1 x.2).hom.toAlgebra

@[simp]
/-
**TopCat.Presheaf.stalk_open_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：∀ {X : TopCat} (F : TopCat.Presheaf CommRingCat X) {U : TopologicalSpace.O
pens ↑X} (x : ↥U),   algebraMap ↑(F.obj (Opposite.op U)) ↑(F.stalk ↑x) = CommRin
gCat.Hom.hom (F.germ U ↑x ⋯)
参数：F : TopCat.Presheaf CommRingCat X；x : ↥U；F.obj (Opposite.op U)；F.stalk ↑x；F.g
erm U ↑x ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- `F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps `F(U) × F(V) ⟶ F(U ⊓ V)`. -/
/-
**TopCat.Sheaf.objSupIsoProdEqLocus** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：{X : TopCat} →   (F : TopCat.Sheaf CommRingCat X) →     (U V : Topological
Space.Opens ↑X) →       F.obj.obj (Opposite.op (U ⊔ V)) ≅         CommRingCat.of
           ↥(((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).co
mp                   (RingHom.fst ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Oppo
site.op V)))).eqLocus               ((CommRingCat.Hom.hom (F.obj.map (CategoryTh
eory.homOfLE ⋯).op)).comp                 (RingHom.snd ↑(F.obj.obj (Opposite.op 
U)) ↑(F.obj.obj (Opposite.op V)))))
参数：F : TopCat.Sheaf CommRingCat X；U V : TopologicalSpace.Opens ↑X；Opposite.op (U
 ⊔ V)；((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).comp     
              (RingHom.fst ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Opposite.op
 V)))).eqLocus               ((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.ho
mOfLE ⋯).op)).comp                 (RingHom.snd ↑(F.obj.obj (Opposite.op U)) ↑(F
.obj.obj (Opposite.op V))))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps `F(U) × F(V) ⟶ F(U ⊓ 
V)`.
-/
def objSupIsoProdEqLocus {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X) :
    F.1.obj (op <| U ⊔ V) ≅ CommRingCat.of <|
    -- Porting note: Lean 3 is able to figure out the ring homomorphism automatically
    RingHom.eqLocus
      (RingHom.comp (F.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom
        (RingHom.fst (F.obj.obj <| op U) (F.obj.obj <| op V)))
      (RingHom.comp (F.obj.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom
        (RingHom.snd (F.obj.obj <| op U) (F.obj.obj <| op V))) :=
  (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)
/-
**TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sh
eaf`。
形式化陈述：∀ {X : TopCat} (F : TopCat.Sheaf CommRingCat X) (U V : TopologicalSpace.Op
ens ↑X)   (x : ↑(F.obj.obj (Opposite.op (U ⊔ V)))),   (↑((CategoryTheory.Concret
eCategory.hom (F.objSupIsoProdEqLocus U V).hom) x)).1 =     (CategoryTheory.Conc
reteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)) x
参数：F : TopCat.Sheaf CommRingCat X；U V : TopologicalSpace.Opens ↑X；x : ↑(F.obj.ob
j (Opposite.op (U ⊔ V)))；↑((CategoryTheory.ConcreteCategory.hom (F.objSupIsoProd
EqLocus U V).hom) x)；CategoryTheory.ConcreteCategory.hom (F.obj.map (CategoryThe
ory.homOfLE ⋯).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem objSupIsoProdEqLocus_hom_fst {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.fst = F.1.map (homOfLE le_sup_left).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x
/-
**TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sh
eaf`。
形式化陈述：∀ {X : TopCat} (F : TopCat.Sheaf CommRingCat X) (U V : TopologicalSpace.Op
ens ↑X)   (x : ↑(F.obj.obj (Opposite.op (U ⊔ V)))),   (↑((CategoryTheory.Concret
eCategory.hom (F.objSupIsoProdEqLocus U V).hom) x)).2 =     (CategoryTheory.Conc
reteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)) x
参数：F : TopCat.Sheaf CommRingCat X；U V : TopologicalSpace.Opens ↑X；x : ↑(F.obj.ob
j (Opposite.op (U ⊔ V)))；↑((CategoryTheory.ConcreteCategory.hom (F.objSupIsoProd
EqLocus U V).hom) x)；CategoryTheory.ConcreteCategory.hom (F.obj.map (CategoryThe
ory.homOfLE ⋯).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem objSupIsoProdEqLocus_hom_snd {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.snd = F.1.map (homOfLE le_sup_right).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x
/-
**TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sh
eaf`。
形式化陈述：∀ {X : TopCat} (F : TopCat.Sheaf CommRingCat X) (U V : TopologicalSpace.Op
ens ↑X)   (x :     ↑(CommRingCat.of         ↥(((CommRingCat.Hom.hom (F.obj.map (
CategoryTheory.homOfLE ⋯).op)).comp                 (RingHom.fst ↑(F.obj.obj (Op
posite.op U)) ↑(F.obj.obj (Opposite.op V)))).eqLocus             ((CommRingCat.H
om.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).comp               (RingHom.sn
d ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Opposite.op V))))))),   (CategoryThe
ory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op))       ((Cate
goryTheory.ConcreteCategory.hom (F.objSupIsoProdEqLocus U V).inv) x) =     (↑x).
1
参数：F : TopCat.Sheaf CommRingCat X；U V : TopologicalSpace.Opens ↑X；x :     ↑(Comm
RingCat.of         ↥(((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯)
.op)).comp                 (RingHom.fst ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj
 (Opposite.op V)))).eqLocus             ((CommRingCat.Hom.hom (F.obj.map (Catego
ryTheory.homOfLE ⋯).op)).comp               (RingHom.snd ↑(F.obj.obj (Opposite.o
p U)) ↑(F.obj.obj (Opposite.op V))))))；CategoryTheory.ConcreteCategory.hom (F.ob
j.map (CategoryTheory.homOfLE ⋯).op)；(CategoryTheory.ConcreteCategory.hom (F.obj
SupIsoProdEqLocus U V).inv) x；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem objSupIsoProdEqLocus_inv_fst {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    F.1.map (homOfLE le_sup_left).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.1 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x
/-
**TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sh
eaf`。
形式化陈述：∀ {X : TopCat} (F : TopCat.Sheaf CommRingCat X) (U V : TopologicalSpace.Op
ens ↑X)   (x :     ↑(CommRingCat.of         ↥(((CommRingCat.Hom.hom (F.obj.map (
CategoryTheory.homOfLE ⋯).op)).comp                 (RingHom.fst ↑(F.obj.obj (Op
posite.op U)) ↑(F.obj.obj (Opposite.op V)))).eqLocus             ((CommRingCat.H
om.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).comp               (RingHom.sn
d ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Opposite.op V))))))),   (CategoryThe
ory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op))       ((Cate
goryTheory.ConcreteCategory.hom (F.objSupIsoProdEqLocus U V).inv) x) =     (↑x).
2
参数：F : TopCat.Sheaf CommRingCat X；U V : TopologicalSpace.Opens ↑X；x :     ↑(Comm
RingCat.of         ↥(((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯)
.op)).comp                 (RingHom.fst ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj
 (Opposite.op V)))).eqLocus             ((CommRingCat.Hom.hom (F.obj.map (Catego
ryTheory.homOfLE ⋯).op)).comp               (RingHom.snd ↑(F.obj.obj (Opposite.o
p U)) ↑(F.obj.obj (Opposite.op V))))))；CategoryTheory.ConcreteCategory.hom (F.ob
j.map (CategoryTheory.homOfLE ⋯).op)；(CategoryTheory.ConcreteCategory.hom (F.obj
SupIsoProdEqLocus U V).inv) x；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem objSupIsoProdEqLocus_inv_snd {X : TopCat.{w}} (F : X.Sheaf CommRingCat) (U V : Opens X)
    (x) :
    F.1.map (homOfLE le_sup_right).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.2 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x
/-
**TopCat.Sheaf.objSupIsoProdEqLocus_inv_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat
.Sheaf`。
形式化陈述：∀ {X : TopCat} (F : TopCat.Sheaf CommRingCat X) {U V W UW VW : Topological
Space.Opens ↑X} (e : W ≤ U ⊔ V)   (x :     ↑(CommRingCat.of         ↥(((CommRing
Cat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).comp                 (Rin
gHom.fst ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Opposite.op V)))).eqLocus    
         ((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).comp  
             (RingHom.snd ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Opposite.op 
V)))))))   (y : ↑(F.obj.obj (Opposite.op W))) (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W
),   (CategoryTheory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE e).
op))         ((CategoryTheory.ConcreteCategory.hom (F.objSupIsoProdEqLocus U V).
inv) x) =       y ↔     (CategoryTheory.ConcreteCategory.hom (F.obj.map (Categor
yTheory.homOfLE ⋯).op)) (↑x).1 =         (CategoryTheory.ConcreteCategory.hom (F
.obj.map (CategoryTheory.homOfLE ⋯).op)) y ∧       (CategoryTheory.ConcreteCateg
ory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)) (↑x).2 =         (CategoryThe
ory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)) y
参数：F : TopCat.Sheaf CommRingCat X；e : W ≤ U ⊔ V；x :     ↑(CommRingCat.of        
 ↥(((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)).comp        
         (RingHom.fst ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj (Opposite.op V)))
).eqLocus             ((CommRingCat.Hom.hom (F.obj.map (CategoryTheory.homOfLE ⋯
).op)).comp               (RingHom.snd ↑(F.obj.obj (Opposite.op U)) ↑(F.obj.obj 
(Opposite.op V))))))；y : ↑(F.obj.obj (Opposite.op W))；h₁ : UW = U ⊓ W；h₂ : VW = 
V ⊓ W；CategoryTheory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE e).
op)；(CategoryTheory.ConcreteCategory.hom (F.objSupIsoProdEqLocus U V).inv) x；Cat
egoryTheory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)；↑x；Ca
tegoryTheory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)；Cate
goryTheory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)；↑x；Cat
egoryTheory.ConcreteCategory.hom (F.obj.map (CategoryTheory.homOfLE ⋯).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst`：∀ {X : TopCat} (F : TopCat.Sh
eaf CommRingCat X) (U V : TopologicalSpace.Opens ↑X)   (x :     ↑(CommRingCat.of
         ↥(((CommRingCat.Hom.ho…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd`：∀ {X : TopCat} (F : TopCat.Sh
eaf CommRingCat X) (U V : TopologicalSpace.Opens ↑X)   (x :     ↑(CommRingCat.of
         ↥(((CommRingCat.Hom.ho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `TopCat.Sheaf.eq_of_locally_eq₂`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 : (
X Y : C) → FunLike (…
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem objSupIsoProdEqLocus_inv_eq_iff {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
    {U V W UW VW : Opens X} (e : W ≤ U ⊔ V) (x) (y : F.1.obj (op W))
    (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W) :
    F.1.map (homOfLE e).op ((F.objSupIsoProdEqLocus U V).inv x) = y ↔
    F.1.map (homOfLE (h₁ ▸ inf_le_left : UW ≤ U)).op x.1.1 =
      F.1.map (homOfLE <| h₁ ▸ inf_le_right).op y ∧
    F.1.map (homOfLE (h₂ ▸ inf_le_left : VW ≤ V)).op x.1.2 =
      F.1.map (homOfLE <| h₂ ▸ inf_le_right).op y := by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq₂
      (homOfLE (inf_le_right : U ⊓ W ≤ W)) (homOfLE (inf_le_right : V ⊓ W ≤ W)) ?_ _ _ ?_ ?_
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

