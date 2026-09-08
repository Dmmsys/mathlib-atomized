/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!

# Immersions of schemes

A morphism of schemes `f : X ⟶ Y` is an immersion if the underlying map of topological spaces
is a locally closed embedding, and the induced morphisms of stalks are all surjective. This is true
if and only if it can be factored into a closed immersion followed by an open immersion.

## Main results
- `isImmersion_iff_exists`:
  A morphism is a (locally-closed) immersion if and only if it can be factored into
  a closed immersion followed by a (dominant) open immersion.
- `isImmersion_iff_exists_of_quasiCompact`:
  A quasicompact morphism is a (locally-closed) immersion if and only if it can be factored into
  an open immersion followed by a closed immersion.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is an immersion if
1. the underlying map of topological spaces is an embedding
2. the range of the map is locally closed
3. the induced morphisms of stalks are all surjective. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsImmersion** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is an immersion if
1. the underlying map of topological spaces is an embedding
2. the range of the map is locally closed
3. the induced morphisms of stalks are all surjective.
-/
class IsImmersion (f : X ⟶ Y) : Prop extends IsPreimmersion f where
  isLocallyClosed_range : IsLocallyClosed (Set.range f)
/-
**AlgebraicGeometry.Scheme.Hom.isLocallyClosed_range** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmers
ion f], IsLocallyClosed (Set.range ⇑f)
参数：f : X ⟶ Y；Set.range ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsImmersion.isLocallyClosed_range`：∀ {X Y : AlgebraicG
eometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsImmersion f], IsLocallyC
losed (Set.range ⇑f)
-/
lemma Scheme.Hom.isLocallyClosed_range (f : X ⟶ Y) [IsImmersion f] :
    IsLocallyClosed (Set.range f) :=
  IsImmersion.isLocallyClosed_range

/--
Given an immersion `f : X ⟶ Y`, this is the biggest open set `U ⊆ Y` containing the image of `X`
such that `X` is closed in `U`.
-/
/-
**AlgebraicGeometry.Scheme.Hom.coborderRange** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → [AlgebraicGeometry.IsImme
rsion f] → Y.Opens
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an immersion `f : X ⟶ Y`, this is the biggest open set `U ⊆ Y` containing 
the image of `X`
such that `X` is closed in `U`.
-/
def Scheme.Hom.coborderRange (f : X ⟶ Y) [IsImmersion f] : Y.Opens :=
  ⟨coborder (Set.range f), f.isLocallyClosed_range.isOpen_coborder⟩

/--
The first part of the factorization of an immersion `f : X ⟶ Y` to a closed immersion
`f.liftCoborder : X ⟶ f.coborderRange` and a dominant open immersion `f.coborderRange.ι`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.liftCoborder** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) → [inst : AlgebraicGeomet
ry.IsImmersion f] → X ⟶ ↑(AlgebraicGeometry.Scheme.Hom.coborderRange f)
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.coborderRange f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Scheme.Hom.liftCoborder (f : X ⟶ Y) [IsImmersion f] : X ⟶ f.coborderRange :=
  IsOpenImmersion.lift f.coborderRange.ι f (by simpa using! subset_coborder)

/--
Any (locally-closed) immersion can be factored into
a closed immersion followed by a (dominant) open immersion.
-/
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.liftCoborder_** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any (locally-closed) immersion can be factored into
a closed immersion followed by a (dominant) open immersion.
-/
lemma Scheme.Hom.liftCoborder_ι (f : X ⟶ Y) [IsImmersion f] :
    f.liftCoborder ≫ f.coborderRange.ι = f :=
  IsOpenImmersion.lift_fac _ _ _
/-
**AlgebraicGeometry.Scheme.Hom.liftCoborder_preimage** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.I
sImmersion f]   (U : (↑(AlgebraicGeometry.Scheme.Hom.coborderRange f)).Opens),  
 (TopologicalSpace.Opens.map (AlgebraicGeometry.Scheme.Hom.liftCoborder f).base)
.obj U =     (TopologicalSpace.Opens.map f.base).obj       ((AlgebraicGeometry.S
cheme.Hom.opensFunctor (AlgebraicGeometry.Scheme.Hom.coborderRange f).ι).obj U)
参数：f : X ⟶ Y；U : (↑(AlgebraicGeometry.Scheme.Hom.coborderRange f)).Opens；Topolog
icalSpace.Opens.map (AlgebraicGeometry.Scheme.Hom.liftCoborder f).base；Topologic
alSpace.Opens.map f.base；(AlgebraicGeometry.Scheme.Hom.opensFunctor (AlgebraicGe
ometry.Scheme.Hom.coborderRange f).ι).obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeom…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.comp_preimage`：comp_preimage {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
-/
lemma Scheme.Hom.liftCoborder_preimage [IsImmersion f] (U : f.coborderRange.toScheme.Opens) :
    f.liftCoborder ⁻¹ᵁ U = f ⁻¹ᵁ f.coborderRange.ι ''ᵁ U := by
  conv_rhs => enter [1]; rw [← f.liftCoborder_ι]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.liftCoborder_app** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：liftCoborder_app [IsImmersion f] (U : f.coborderRange.toScheme.Opens) : f.
liftCoborder.app U = f.app (f.coborderRange.ι ''ᵁ U) ≫ X.presheaf.map (eqToHom <
| f.liftCoborder_preimage U).op
参数：U : f.coborderRange.toScheme.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_preimage`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f]   (U : (↑(Al
gebraicGeometry.Scheme.Hom.coborderRange…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.app_eq`：app_eq {X Y : Scheme} (f : X ⟶ Y) {
U V : Y.Opens} (e : U = V) : f.app U = Y.presheaf.map (eqToHom e.symm).op ≫ f.ap
p V ≫ X.presheaf.map (eqT…
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_map_comp`：eqToHom_map_comp (F : C ⥤ D) {X Y Z : C
} (p : X = Y) (q : Y = Z) : F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToH
om <| p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCoborder_app [IsImmersion f] (U : f.coborderRange.toScheme.Opens) :
    f.liftCoborder.app U = f.app (f.coborderRange.ι ''ᵁ U) ≫
      X.presheaf.map (eqToHom <| f.liftCoborder_preimage U).op := by
  rw [Scheme.Hom.congr_app (f.liftCoborder_ι).symm (f.coborderRange.ι ''ᵁ U)]
  simp [Scheme.Hom.app_eq f.liftCoborder (f.coborderRange.ι.preimage_image_eq U),
    ← Functor.map_comp_assoc, -Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsImmersion f] : IsClosedImmersion f.liftCoborder := by
  have : IsPreimmersion (f.liftCoborder ≫ f.coborderRange.ι) := by
    simp only [Scheme.Hom.liftCoborder_ι]; infer_instance
  have : IsPreimmersion f.liftCoborder := .of_comp f.liftCoborder f.coborderRange.ι
  refine .of_isPreimmersion _ ?_
  convert! isClosed_preimage_val_coborder
  apply Set.image_injective.mpr f.coborderRange.ι.isEmbedding.injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, f.liftCoborder_ι]
  exact (Set.image_preimage_eq_of_subset (by simpa using! subset_coborder)).symm
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsImmersion f] : IsDominant f.coborderRange.ι := by
  rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
  exact dense_coborder
/-
**AlgebraicGeometry.isImmersion_eq_inf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：isImmersion_eq_inf : @IsImmersion = (@IsPreimmersion ⊓ topologically fun {
_ _} _ _ f => IsLocallyClosed (Set.range f) : MorphismProperty Scheme)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.isImmersion_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f
 : X ⟶ Y),   AlgebraicGeometry.IsImmersion f ↔ AlgebraicGeometry.IsPreimmersion 
f ∧ IsLocallyClosed (Se…
-/
lemma isImmersion_eq_inf : @IsImmersion = (@IsPreimmersion ⊓
    topologically fun {_ _} _ _ f ↦ IsLocallyClosed (Set.range f) : MorphismProperty Scheme) := by
  ext; exact isImmersion_iff _

namespace IsImmersion

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @IsImmersion := by
  suffices IsZariskiLocalAtTarget
      (topologically fun {X Y} _ _ f ↦ IsLocallyClosed (Set.range f)) from
    isImmersion_eq_inf ▸ inferInstance
  apply +allowSynthFailures topologically_isZariskiLocalAtTarget'
  · refine { precomp := ?_, postcomp := ?_ }
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr i.surjective, Set.image_univ]
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      refine hf.image i.homeomorph.isInducing ?_
      rw [Set.range_eq_univ.mpr i.surjective]
      exact isOpen_univ.isLocallyClosed
  · simp_rw [Set.range_restrictPreimage]
    exact fun _ _ _ hU _ ↦ hU.isLocallyClosed_iff_coe_preimage
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (f : X ⟶ Y) [IsOpenImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isOpenEmbedding.2.isLocallyClosed
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (f : X ⟶ Y) [IsClosedImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isClosedEmbedding.2.isLocallyClosed
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @IsImmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine { __ := (inferInstance : IsPreimmersion (f ≫ g)), isLocallyClosed_range := ?_ }
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact f.isLocallyClosed_range.image g.isEmbedding.isInducing g.isLocallyClosed_range

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsImmersion.comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsImmersion`。
形式化陈述：comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f] [IsImmersion
 g] : IsImmersion (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morphism
Property C}   [self : P.IsStableUnderComposition] {X Y …
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.IsImmersion.instIsMultiplicativeScheme`：CategoryTheory
.MorphismProperty.IsMultiplicative @AlgebraicGeometry.IsImmersion
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f]
    [IsImmersion g] : IsImmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

variable {f} in
/--
A morphism is a (locally-closed) immersion if and only if it can be factored into
a closed immersion followed by an open immersion.
-/
/-
**AlgebraicGeometry.IsImmersion.isImmersion_iff_exists** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.IsImmersion`。
形式化陈述：isImmersion_iff_exists : IsImmersion f ↔ exists (Z : Scheme) (g₁ : X ⟶ Z) 
(g₂ : Z ⟶ Y), IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsClosedImmersionLiftCoborder`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   Algebrai
cGeometry.IsClosedImmersion (AlgebraicGeo…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsClosedImmersion`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], Algebraic
Geometry.IsImmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsOpenImmersion`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeom
etry.IsImmersion f

--- 原说明 ---
A morphism is a (locally-closed) immersion if and only if it can be factored int
o
a closed immersion followed by an open immersion.
-/
lemma isImmersion_iff_exists : IsImmersion f ↔ ∃ (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
    IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  ⟨fun _ ↦ ⟨_, f.liftCoborder, f.coborderRange.ι, inferInstance, inferInstance, f.liftCoborder_ι⟩,
    fun ⟨_, _, _, _, _, e⟩ ↦ e ▸ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsImmersion.isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.IsImmersion`。
形式化陈述：isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsImme
rsion where of_isPullback
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsPullback.paste_horiz_iff`：paste_horiz_iff {X₁₁ X₁₂ X₁₃ 
X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂
₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`：CategoryThe
ory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsClosedImmersio
n
· 使用定理 `AlgebraicGeometry.instIsClosedImmersionLiftCoborder`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   Algebrai
cGeometry.IsClosedImmersion (AlgebraicGeo…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsClosedImmersion`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], Algebraic
Geometry.IsImmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsOpenImmersion`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeom
etry.IsImmersion f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsImmersion where
  of_isPullback := by
    intro X Y Y' S f g f' g' H hg
    let Z := Limits.pullback f g.coborderRange.ι
    let e : Y' ⟶ Z := Limits.pullback.lift g' (f' ≫ g.liftCoborder) (by simpa using H.w.symm)
    have : IsClosedImmersion e := by
      have := (IsPullback.paste_horiz_iff (.of_hasPullback f g.coborderRange.ι)
        (show e ≫ Limits.pullback.snd _ _ = _ from Limits.pullback.lift_snd _ _ _)).mp ?_
      · exact MorphismProperty.of_isPullback this.flip inferInstance
      · simpa [e] using H.flip
    rw [← Limits.pullback.lift_fst (f := f) (g := g.coborderRange.ι) g' (f' ≫ g.liftCoborder)
      (by simpa using H.w.symm)]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsImmersion g] : IsImmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsImmersion f] : IsImmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ ‹_›
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [IsImmersion f] : IsImmersion (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [IsImmersion f] :
    IsImmersion (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (f : X ⟶ Y) [IsImmersion f] : LocallyOfFiniteType f := by
  rw [← f.liftCoborder_ι]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
open Limits Scheme.Pullback in
/-- The diagonal morphism is always an immersion. -/
@[stacks 01KJ]
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal morphism is always an immersion.
-/
instance : IsImmersion (pullback.diagonal f) := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ ↦ range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱
  have : IsImmersion ((pullback.diagonal f ∣_
    diagonalCoverDiagonalRange f 𝒰 𝒱) ≫ Scheme.Opens.ι _) := inferInstance
  rwa [morphismRestrict_ι, H, ← Scheme.topIso_hom,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)] at this

/-- The map `X ×[S] Y ⟶ X ×[T] Y` induced by any `S ⟶ T` is always an immersion. -/
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `X ×[S] Y ⟶ X ×[T] Y` induced by any `S ⟶ T` is always an immersion.
-/
instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) :
    IsImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i) inferInstance
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsImmersion ⊤ :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsImmersion _)
/-
**AlgebraicGeometry.IsImmersion.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.IsImmersion`。
形式化陈述：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion (f ≫ g)] : IsImmersion f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasOfPostcompProperty.of_postcomp`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {W W' : CategoryTheory.Morph
ismProperty C}   [self : W.HasOfPostcompProperty W'] {X…
· 使用定理 `AlgebraicGeometry.IsImmersion.instHasOfPostcompPropertySchemeTopMorphism
Property`：CategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeomet
ry.IsImmersion ⊤
· 使用定理 `trivial`：True
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion (f ≫ g)] :
    IsImmersion f :=
  MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := ⊤) _ g trivial ‹_›
/-
**AlgebraicGeometry.IsImmersion.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.IsImmersion`。
形式化陈述：comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g] : IsImme
rsion (f ≫ g) ↔ IsImmersion f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsImmersion.of_comp`：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [
IsImmersion (f ≫ g)] : IsImmersion f
-/
theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g] :
    IsImmersion (f ≫ g) ↔ IsImmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ (prodIsoPullback X X).hom]
  convert! (inferInstance : IsImmersion (pullback.diagonal (terminal.from X)))
  ext : 1 <;> simp
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f g : X ⟶ Y) : IsImmersion (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @IsImmersion)
    (isPullback_equalizer_prod f g).flip inferInstance
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsImmersion f] : IsImmersion f.toImage :=
  have : IsImmersion (f.toImage ≫ f.imageι) := by simpa
  IsImmersion.of_comp f.toImage f.imageι

set_option backward.isDefEq.respectTransparency false in
open Scheme in
/--
If `f : X ⟶ Y` is a quasi-compact immersion, then `X` is the pullback of the
closed immersion `im f ⟶ Y` and an open immersion `U ⟶ Y`.
-/
/-
**AlgebraicGeometry.IsImmersion.isPullback_toImage_liftCoborder** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.IsImmersion`。
形式化陈述：isPullback_toImage_liftCoborder [IsImmersion f] [QuasiCompact f] : IsPullb
ack f.toImage f.liftCoborder f.imageι f.coborderRange.ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `AlgebraicGeometry.isPullback_of_isClosedImmersion`：∀ {ZX ZY X Y : Algebr
aicGeometry.Scheme} (iX : ZX ⟶ X) (iY : ZY ⟶ Y) (Zf : ZX ⟶ ZY) (f : X ⟶ Y)   [Al
gebraicGeometry.IsClosedImmersion iX] […
· 使用定理 `AlgebraicGeometry.instIsClosedImmersionLiftCoborder`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   Algebrai
cGeometry.IsClosedImmersion (AlgebraicGeo…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instSubschemeι`：∀ {X : AlgebraicGeom
etry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.IsClosedImmersion I.subsc
hemeι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_imageι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Sch
eme.Hom.toImage f) (AlgebraicGeom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Hom.imageι.eq_1`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y),   AlgebraicGeometry.Scheme.Hom.imageι f = (AlgebraicGeometry.S
cheme.Hom.ker f).subschemeι
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`：ker_subschemeι :
 I.subschemeι.ker = I
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`：
ideal_comap_of_isOpenImmersion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersi
on f] (U : X.affineOpens) : (I.comap f).ideal U = (I.ideal ⟨…
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_appIso`：ι_appIso (V) : U.ι.appIso V = I
so.refl _
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instIsAffineHom`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGe
ometry.IsAffineHom f
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_preimage`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f]   (U : (↑(Al
gebraicGeometry.Scheme.Hom.coborderRange…
· 使用引理 `AlgebraicGeometry.liftCoborder_app`：liftCoborder_app [IsImmersion f] (U 
: f.coborderRange.toScheme.Opens) : f.liftCoborder.app U = f.app (f.coborderRang
e.ι ''ᵁ U) ≫ X.presheaf.…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用引理 `RingHom.ker_comp_of_injective`：ker_comp_of_injective [Semiring T] (g : T
 ->+* R) {f : R ->+* S} (hf : Function.Injective f) : ker (f.comp g) = RingHom.k
er g
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : X ⟶ Y` is a quasi-compact immersion, then `X` is the pullback of the
closed immersion `im f ⟶ Y` and an open immersion `U ⟶ Y`.
-/
lemma isPullback_toImage_liftCoborder [IsImmersion f] [QuasiCompact f] :
    IsPullback f.toImage f.liftCoborder f.imageι f.coborderRange.ι := by
  refine (isPullback_of_isClosedImmersion _ _ _ _ (by simp) ?_).flip
  rw [Hom.imageι, IdealSheafData.ker_subschemeι]
  ext U : 2
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso, Iso.refl_inv,
    Hom.ker_apply, RingHom.comap_ker, ← CommRingCat.hom_comp]
  dsimp [Opens.toScheme_presheaf_obj]
  rw [RingHomCompTriple.comp_eq, liftCoborder_app,
    CommRingCat.hom_comp, RingHom.ker_comp_of_injective]
  rw [← ConcreteCategory.mono_iff_injective_of_preservesPullback]
  infer_instance
/-
**AlgebraicGeometry.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Immersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsImmersion f] [QuasiCompact f] : IsOpenImmersion f.toImage :=
  MorphismProperty.of_isPullback (IsImmersion.isPullback_toImage_liftCoborder f).flip inferInstance

variable {f} in
/--
A quasi-compact morphism is a (locally-closed) immersion if and only if it can be factored into
an open immersion followed by a closed immersion.
-/
/-
**AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsImmersion`。
形式化陈述：isImmersion_iff_exists_of_quasiCompact [QuasiCompact f] : IsImmersion f ↔ 
exists (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y), IsOpenImmersion g₁ ∧ IsClosedImme
rsion g₂ ∧ g₁ ≫ g₂ = f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion f]
 [AlgebraicGeometry.QuasiCompact f],   AlgebraicGeometry.IsO…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instSubschemeι`：∀ {X : AlgebraicGeom
etry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.IsClosedImmersion I.subsc
hemeι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_imageι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Sch
eme.Hom.toImage f) (AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsOpenImmersion`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeom
etry.IsImmersion f
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsClosedImmersion`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], Algebraic
Geometry.IsImmersion f

--- 原说明 ---
A quasi-compact morphism is a (locally-closed) immersion if and only if it can b
e factored into
an open immersion followed by a closed immersion.
-/
lemma isImmersion_iff_exists_of_quasiCompact [QuasiCompact f] :
    IsImmersion f ↔ ∃ (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
      IsOpenImmersion g₁ ∧ IsClosedImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  ⟨fun _ ↦ ⟨_, f.toImage, f.imageι, inferInstance, inferInstance, f.toImage_imageι⟩,
    fun ⟨_, _, _, _, _, e⟩ ↦ e ▸ inferInstance⟩

end IsImmersion

end AlgebraicGeometry

