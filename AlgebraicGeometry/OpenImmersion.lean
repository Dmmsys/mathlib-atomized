/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Open immersions of schemes

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpaces
-/
/-
**AlgebraicGeometry.IsOpenImmersion** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：IsOpenImmersion : MorphismProperty (Scheme.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Schemes is an open immersion if it is an open immersion as a morph
ism
of LocallyRingedSpaces
-/
abbrev IsOpenImmersion : MorphismProperty (Scheme.{u}) :=
  fun _ _ f ↦ LocallyRingedSpace.IsOpenImmersion f.toLRSHom
/-
**AlgebraicGeometry.IsOpenImmersion.comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.IsOpenImmersion`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeo
metry.IsOpenImmersion f]   [AlgebraicGeometry.IsOpenImmersion g], AlgebraicGeome
try.IsOpenImmersion (CategoryTheory.CategoryStruct.comp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsOpenImmersion.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (f ≫ g) :=
  LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

namespace LocallyRingedSpace.IsOpenImmersion

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme** 是 Mathlib 中的一个定义
，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：(X : AlgebraicGeometry.LocallyRingedSpace) →   (∀ (x : ↑X.toTopCat),      
 ∃ R f,         x ∈ Set.range ⇑(CategoryTheory.ConcreteCategory.hom f.base) ∧   
        AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f) →     AlgebraicG
eometry.Scheme
参数：x : ↑X.toTopCat；CategoryTheory.ConcreteCategory.hom f.base。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that a locally ringed space is a scheme, it suffices to show that it has
 a jointly
surjective family of open immersions from affine schemes.
-/
protected def scheme (X : LocallyRingedSpace.{u})
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat) (f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    exact Subtype.range_coe_subtype

end LocallyRingedSpace.IsOpenImmersion

/-
**AlgebraicGeometry.IsOpenImmersion.isOpen_range** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.IsOpenImmersion`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOp
enImmersion f], IsOpen (Set.range ⇑f)
参数：f : X ⟶ Y；Set.range ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
-/
theorem IsOpenImmersion.isOpen_range {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f) :=
  H.base_open.isOpen_range

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-
**AlgebraicGeometry.Scheme.Hom.isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：isOpenEmbedding : IsOpenEmbedding f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
-/
theorem isOpenEmbedding : IsOpenEmbedding f :=
  H.base_open

/-- The image of an open immersion as an open set. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Hom.opensRange** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：opensRange : Y.Opens
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an open immersion as an open set.
-/
def opensRange : Y.Opens :=
  ⟨_, f.isOpenEmbedding.isOpen_range⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.mem_opensRange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：mem_opensRange {f : X ⟶ Y} [IsOpenImmersion f] {y : Y} : y in opensRange f
 ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_opensRange {f : X ⟶ Y} [IsOpenImmersion f] {y : Y} :
    y ∈ opensRange f ↔ ∃ x, f x = y := .rfl

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
/-
**AlgebraicGeometry.Scheme.Hom.opensFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：opensFunctor : X.Opens ⥤ Y.Opens
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`.
-/
def opensFunctor : X.Opens ⥤ Y.Opens :=
  LocallyRingedSpace.IsOpenImmersion.opensFunctor f.toLRSHom

/-- The adjunction image-preimage adjunction for an open immersion of schemes. -/
/-
**AlgebraicGeometry.Scheme.Hom.opensFunctorAdjunction** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：opensFunctorAdjunction : f.opensFunctor ⊣ TopologicalSpace.Opens.map f.bas
e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction image-preimage adjunction for an open immersion of schemes.
-/
def opensFunctorAdjunction : f.opensFunctor ⊣ TopologicalSpace.Opens.map f.base :=
  IsOpenMap.adjunction ‹IsOpenImmersion f›.base_open.isOpenMap
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : f.opensFunctor.IsLeftAdjoint :=
  f.opensFunctorAdjunction.isLeftAdjoint
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : f.opensFunctor.IsCocontinuous (Opens.grothendieckTopology _)
    (Opens.grothendieckTopology _) := by
  rw [f.opensFunctorAdjunction.isCocontinuous_iff_coverPreserving]
  exact coverPreserving_opens_map f.base
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : f.opensFunctor.Full :=
  have : Mono f.base := (TopCat.mono_iff_injective f.base).mpr f.isOpenEmbedding.injective
  inferInstanceAs f.isOpenEmbedding.functor.Full
/-
**AlgebraicGeometry.Scheme.Hom.coverPreserving_opensFunctor** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：coverPreserving_opensFunctor : CoverPreserving (Opens.grothendieckTopology
 _) (Opens.grothendieckTopology _) f.opensFunctor
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.coverPreserving`：IsOpenMap.coverPreserving (hf : IsOpenMap f) 
: CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) 
hf.functor
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
-/
lemma coverPreserving_opensFunctor :
    CoverPreserving (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) f.opensFunctor :=
  f.isOpenEmbedding.isOpenMap.coverPreserving
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfShape WalkingCospan (Scheme.Hom.opensFunctor f) := by
  dsimp [Scheme.Hom.opensFunctor]
  infer_instance
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.opensFunctor.PreservesOneHypercovers (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology _) := by
  refine Functor.PreservesOneHypercovers.of_coverPreserving ?_
  exact Scheme.Hom.coverPreserving_opensFunctor f

/-- `f ''ᵁ U` is notation for the image (as an open set) of `U` under an open immersion `f`.
The preferred name in lemmas is `image` and it should be treated as an infix. -/
scoped[AlgebraicGeometry] notation3:90 f:91 " ''ᵁ " U:90 => (Scheme.Hom.opensFunctor f).obj U

/-
**AlgebraicGeometry.Scheme.Hom.coe_image** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOp
enImmersion f] {U : X.Opens},   ↑((AlgebraicGeometry.Scheme.Hom.opensFunctor f).
obj U) = ⇑f '' ↑U
参数：f : X ⟶ Y；(AlgebraicGeometry.Scheme.Hom.opensFunctor f).obj U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_image {U : X.Opens} : f ''ᵁ U = f '' U := rfl
/-
**AlgebraicGeometry.Scheme.Hom.image_mono** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：image_mono {U V : X.Opens} (e : U <= V) : f ''ᵁ U <= f ''ᵁ V
参数：e : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma image_mono {U V : X.Opens} (e : U ≤ V) : f ''ᵁ U ≤ f ''ᵁ V := Set.image_mono e

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.opensFunctor_map_homOfLE** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：opensFunctor_map_homOfLE {U V : X.Opens} (e : U <= V) : (Scheme.Hom.opensF
unctor f).map (homOfLE e) = homOfLE (f.image_mono e)
参数：e : U <= V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opensFunctor_map_homOfLE {U V : X.Opens} (e : U ≤ V) :
    (Scheme.Hom.opensFunctor f).map (homOfLE e) = homOfLE (f.image_mono e) :=
  rfl
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : f.opensFunctor.IsContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  f.isOpenEmbedding.functor_isContinuous

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：image_top_eq_opensRange : f ''ᵁ ⊤ = f.opensRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_top_eq_opensRange : f ''ᵁ ⊤ = f.opensRange := by
  apply Opens.ext
  simp
/-
**AlgebraicGeometry.Scheme.Hom.opensRange_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：opensRange_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion 
f] [IsOpenImmersion g] : (f ≫ g).opensRange = g ''ᵁ f.opensRange
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma opensRange_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g).opensRange = g ''ᵁ f.opensRange :=
  TopologicalSpace.Opens.ext (Set.range_comp g f)
/-
**AlgebraicGeometry.Scheme.Hom.opensRange_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：opensRange_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : f.opensRange = 
⊤
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
lemma opensRange_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    f.opensRange = ⊤ :=
  TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr f.homeomorph.surjective)
/-
**AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：opensRange_comp_of_isIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f
] [IsOpenImmersion g] : (f ≫ g).opensRange = g.opensRange
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.opensRange_comp`：opensRange_comp {X Y Z : S
cheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g)
.opensRange = g ''ᵁ f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Hom.opensRange_of_isIso`：opensRange_of_isIso {X
 Y : Scheme} (f : X ⟶ Y) [IsIso f] : f.opensRange = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
-/
lemma opensRange_comp_of_isIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] [IsOpenImmersion g] : (f ≫ g).opensRange = g.opensRange := by
  rw [opensRange_comp, opensRange_of_isIso, image_top_eq_opensRange]
/-
**AlgebraicGeometry.Scheme.Hom.image_le_opensRange** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：image_le_opensRange (U : X.Opens) : f ''ᵁ U <= f.opensRange
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma image_le_opensRange (U : X.Opens) : f ''ᵁ U ≤ f.opensRange := by
  simpa using f.image_mono le_top

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.preimage_image_eq** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：preimage_image_eq (U : X.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_image_eq (U : X.Opens) : f ⁻¹ᵁ f ''ᵁ U = U := by
  apply Opens.ext
  simp [Set.preimage_image_eq _ f.isOpenEmbedding.injective]
/-
**AlgebraicGeometry.Scheme.Hom.image_le_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.Hom`。
形式化陈述：image_le_image_iff (f : X ⟶ Y) [IsOpenImmersion f] (U U' : X.Opens) : f ''
ᵁ U <= f ''ᵁ U' ↔ U <= U'
参数：f : X ⟶ Y；U U' : X.Opens。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
-/
lemma image_le_image_iff (f : X ⟶ Y) [IsOpenImmersion f] (U U' : X.Opens) :
    f ''ᵁ U ≤ f ''ᵁ U' ↔ U ≤ U' := by
  refine ⟨fun h ↦ ?_, f.image_mono⟩
  rw [← preimage_image_eq f U, ← preimage_image_eq f U']
  apply f.preimage_mono h
/-
**AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：image_preimage_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRa
nge ⊓ U
参数：U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_preimage_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U := by
  apply Opens.ext
  simp [Set.image_preimage_eq_range_inter]
/-
**AlgebraicGeometry.Scheme.Hom.image_preimage_le** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：image_preimage_le (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U <= U
参数：U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma image_preimage_le (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U ≤ U :=
  (f.image_preimage_eq_opensRange_inf U).trans_le inf_le_right
/-
**AlgebraicGeometry.Scheme.Hom.image_injective** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：image_injective : Function.Injective (f ''ᵁ ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
-/
lemma image_injective : Function.Injective (f ''ᵁ ·) := by
  intro U V hUV
  simpa using congrArg (f ⁻¹ᵁ ·) hUV
/-
**AlgebraicGeometry.Scheme.Hom.image_iSup** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：image_iSup {ι : Sort*} (s : ι -> X.Opens) : (f ''ᵁ ⨆ (i : ι), s i) = ⨆ (i 
: ι), f ''ᵁ s i
参数：s : ι -> X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_iSup {ι : Sort*} (s : ι → X.Opens) :
    (f ''ᵁ ⨆ (i : ι), s i) = ⨆ (i : ι), f ''ᵁ s i := by
  ext : 1
  simp [Set.image_iUnion]
/-
**AlgebraicGeometry.Scheme.Hom.image_iSup** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：image_iSup {ι : Sort*} (s : ι -> X.Opens) : (f ''ᵁ ⨆ (i : ι), s i) = ⨆ (i 
: ι), f ''ᵁ s i
参数：s : ι -> X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_iSup₂ {ι : Sort*} {κ : ι → Sort*} (s : (i : ι) → κ i → X.Opens) :
    (f ''ᵁ ⨆ (i : ι), ⨆ (j : κ i), s i j) = ⨆ (i : ι), ⨆ (j : κ i), f ''ᵁ s i j := by
  ext : 1
  simp [Set.image_iUnion₂]

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.comp_image** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：comp_image {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens) [IsOpenI
mmersion f] [IsOpenImmersion g] : (f ≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U
参数：f : X ⟶ Y；g : Y ⟶ Z；U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
lemma comp_image {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens)
    [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U :=
  TopologicalSpace.Opens.ext (Set.image_comp g f U)

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.id_image** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：id_image {X : Scheme} (U : X.Opens) : 𝟙 X ''ᵁ U = U
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
lemma id_image {X : Scheme} (U : X.Opens) : 𝟙 X ''ᵁ U = U :=
  TopologicalSpace.Opens.ext (Set.image_id _)

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.inv_image** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：inv_image {X Y : Scheme} (e : X ≅ Y) (U : Y.Opens) : e.inv ''ᵁ U = e.hom ⁻
¹ᵁ U
参数：e : X ≅ Y；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
lemma inv_image {X Y : Scheme} (e : X ≅ Y) (U : Y.Opens) : e.inv ''ᵁ U = e.hom ⁻¹ᵁ U :=
  TopologicalSpace.Opens.ext <| (Scheme.homeoOfIso e.symm).toEquiv.image_eq_preimage_symm _
/-
**AlgebraicGeometry.Scheme.Hom.inv_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：inv_preimage {X Y : Scheme} (e : X ≅ Y) (U : X.Opens) : e.inv ⁻¹ᵁ U = e.ho
m ''ᵁ U
参数：e : X ≅ Y；U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `AlgebraicGeometry.Scheme.Hom.inv_image`：inv_image {X Y : Scheme} (e : X 
≅ Y) (U : Y.Opens) : e.inv ''ᵁ U = e.hom ⁻¹ᵁ U
-/
lemma inv_preimage {X Y : Scheme} (e : X ≅ Y) (U : X.Opens) : e.inv ⁻¹ᵁ U = e.hom ''ᵁ U :=
  (inv_image e.symm U).symm

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.apply_mem_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：apply_mem_image_iff {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] {U : X.
Opens} {x : X} : f x in f ''ᵁ U ↔ x in U
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
-/
lemma apply_mem_image_iff {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {U : X.Opens} {x : X} : f x ∈ f ''ᵁ U ↔ x ∈ U :=
  f.isOpenEmbedding.injective.mem_set_image

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.preimage_opensRange** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：preimage_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : f
 ⁻¹ᵁ f.opensRange = ⊤
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f ⁻¹ᵁ f.opensRange = ⊤ := by
  simp [Scheme.Hom.opensRange]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : X.Opens) : IsIso (f.app (f ''ᵁ U)) := by delta opensFunctor; infer_instance
/-
**AlgebraicGeometry.Scheme.Hom.isIso_app** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：isIso_app (V : Y.Opens) (hV : V <= f.opensRange) : IsIso (f.app V)
参数：V : Y.Opens；hV : V <= f.opensRange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatAppObjOpensOpensFunctor
`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenIm
mersion f] (U : X.Opens),   CategoryTheory.IsIso (AlgebraicGeo…
-/
lemma isIso_app (V : Y.Opens) (hV : V ≤ f.opensRange) : IsIso (f.app V) := by
  rw [show V = f ''ᵁ f ⁻¹ᵁ V from Opens.ext (Set.image_preimage_eq_of_subset hV).symm]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `Γ(Y, f(U)) ≅ Γ(X, U)` induced by an open immersion `f : X ⟶ Y`. -/
/-
**AlgebraicGeometry.Scheme.Hom.appIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme.Hom`。
形式化陈述：appIso (U) : Γ(Y, f ''ᵁ U) ≅ Γ(X, U)
参数：U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `Γ(Y, f(U)) ≅ Γ(X, U)` induced by an open immersion `f : X ⟶ Y`.
-/
def appIso (U) : Γ(Y, f ''ᵁ U) ≅ Γ(X, U) :=
  (asIso <| LocallyRingedSpace.IsOpenImmersion.invApp f.toLRSHom U).symm

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.appIso_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：appIso_inv_naturality {U V : X.Opens} (i : op U ⟶ op V) : X.presheaf.map i
 ≫ (f.appIso V).inv = (f.appIso U).inv ≫ Y.presheaf.map (f.opensFunctor.op.map i
)
参数：i : op U ⟶ op V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality`：inv_na
turality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : X.presheaf.map i ≫ H.invApp _ (unop V
) = invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
theorem appIso_inv_naturality {U V : X.Opens} (i : op U ⟶ op V) :
    X.presheaf.map i ≫ (f.appIso V).inv =
      (f.appIso U).inv ≫ Y.presheaf.map (f.opensFunctor.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.appIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：appIso_hom (U) : (f.appIso U).hom = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqTo
Hom (preimage_image_eq f U).symm).op
参数：U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.instIsIsoInvApp`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pre
sheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp`：inv_invApp
 (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor f |>.obj U)) ≫ X
.presheaf.map (eqToHom (by simp [Opens.map_def, Se…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
-/
theorem appIso_hom (U) :
    (f.appIso U).hom = f.app (f ''ᵁ U) ≫ X.presheaf.map
      (eqToHom (preimage_image_eq f U).symm).op :=
  (PresheafedSpace.IsOpenImmersion.inv_invApp f.toPshHom U).trans (by rw [eqToHom_op]; rfl)

/-- A variant of `appIso_hom` that uses `Hom.appLE`. -/
/-
**AlgebraicGeometry.Scheme.Hom.appIso_hom'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：appIso_hom' (U) : (f.appIso U).hom = f.appLE (f ''ᵁ U) U (preimage_image_e
q f U).ge
参数：U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op

--- 原说明 ---
A variant of `appIso_hom` that uses `Hom.appLE`.
-/
theorem appIso_hom' (U) :
    (f.appIso U).hom = f.appLE (f ''ᵁ U) U (preimage_image_eq f U).ge :=
  f.appIso_hom U

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.appIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：appIso_hom_naturality {U V : X.Opens} (i : op U ⟶ op V) : dsimp% Y.preshea
f.map (f.opensFunctor.op.map i) ≫ (f.appIso V).hom = (f.appIso U).hom ≫ X.preshe
af.map i
参数：i : op U ⟶ op V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_naturality`：appIso_inv_naturalit
y {U V : X.Opens} (i : op U ⟶ op V) : X.presheaf.map i ≫ (f.appIso V).inv = (f.a
ppIso U).inv ≫ Y.presheaf.map (f.opensFu…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma appIso_hom_naturality {U V : X.Opens} (i : op U ⟶ op V) :
    dsimp% Y.presheaf.map (f.opensFunctor.op.map i) ≫ (f.appIso V).hom =
      (f.appIso U).hom ≫ X.presheaf.map i := by
  simp [← cancel_mono (f.appIso V).inv]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.app_appIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：app_appIso_inv (U) : f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv = Y.presheaf.map (
homOfLE (Set.image_preimage_subset f U.1)).op
参数：U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
theorem app_appIso_inv (U) :
    f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
      Y.presheaf.map (homOfLE (Set.image_preimage_subset f U.1)).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `app_invApp` that gives an `eqToHom` instead of `homOfLE`. -/
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.app_invApp'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：app_invApp' (U) (hU : U <= f.opensRange) : f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).
inv = Y.presheaf.map (eqToHom (Opens.ext <| by simpa [Set.image_preimage_eq_inte
r_range])).op
参数：U；hU : U <= f.opensRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
A variant of `app_invApp` that gives an `eqToHom` instead of `homOfLE`.
-/
theorem app_invApp' (U) (hU : U ≤ f.opensRange) :
    f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
      Y.presheaf.map (eqToHom (Opens.ext <| by simpa [Set.image_preimage_eq_inter_range])).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise nosimp]
/-
**AlgebraicGeometry.Scheme.Hom.appIso_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：appIso_inv_app (U) : (f.appIso U).inv ≫ f.app (f ''ᵁ U) = X.presheaf.map (
eqToHom (preimage_image_eq f U)).op
参数：U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app`：invApp_app
 (U : Opens X) : invApp f U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.preshea
f.map (eqToHom (by simp [Opens.map_def, Set.preima…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
-/
theorem appIso_inv_app (U) :
    (f.appIso U).inv ≫ f.app (f ''ᵁ U) = X.presheaf.map (eqToHom (preimage_image_eq f U)).op :=
  (PresheafedSpace.IsOpenImmersion.invApp_app _ _).trans (by rw [eqToHom_op])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise nosimp]
/-
**AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：appLE_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U : Y
.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) : f.appLE U V e ≫ (f.appIso V).inv = Y.
presheaf.map (homOfLE <| (f.image_mono e).trans (f.image_preimage_eq_opensRange_
inf U ▸ inf_le_right)).op
参数：f : X ⟶ Y；e : V <= f ⁻¹ᵁ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_naturality`：appIso_inv_naturalit
y {U V : X.Opens} (i : op U ⟶ op V) : X.presheaf.map i ≫ (f.appIso V).inv = (f.a
ppIso U).inv ≫ Y.presheaf.map (f.opensFu…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.app_appIso_inv_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f] (U : Y.Opens
) {Z : CommRingCat}   (h :     Y.preshe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma appLE_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e ≫ (f.appIso V).inv =
        Y.presheaf.map (homOfLE <| (f.image_mono e).trans
          (f.image_preimage_eq_opensRange_inf U ▸ inf_le_right)).op := by
  simp only [appLE, Category.assoc, appIso_inv_naturality, Functor.op_obj, Functor.op_map,
    Quiver.Hom.unop_op, opensFunctor_map_homOfLE, app_appIso_inv_assoc, Opens.carrier_eq_coe]
  rw [← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.appIso_inv_appLE** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：appIso_inv_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U V :
 X.Opens} (e : V <= f ⁻¹ᵁ f ''ᵁ U) : (f.appIso U).inv ≫ f.appLE (f ''ᵁ U) V e = 
X.presheaf.map (homOfLE (by rwa [preimage_image_eq] at e)).op
参数：f : X ⟶ Y；e : V <= f ⁻¹ᵁ f ''ᵁ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_app_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens
) {Z : CommRingCat}   (h :     X.preshe…
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma appIso_inv_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ f ''ᵁ U) :
    (f.appIso U).inv ≫ f.appLE (f ''ᵁ U) V e =
        X.presheaf.map (homOfLE (by rwa [preimage_image_eq] at e)).op := by
  simp only [appLE, appIso_inv_app_assoc, eqToHom_op]
  rw [← Functor.map_comp]
  rfl
/-
**AlgebraicGeometry.Scheme.Hom.appIso_inv_app_presheafMap** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：appIso_inv_app_presheafMap (U : X.Opens) : (f.appIso U).inv ≫ f.app _ ≫ X.
presheaf.map (eqToHom (f.preimage_image_eq U).symm).op = 𝟙 _
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_app_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens
) {Z : CommRingCat}   (h :     X.preshe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma appIso_inv_app_presheafMap (U : X.Opens) :
    (f.appIso U).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op = 𝟙 _ := by
  rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.id_appIso** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：id_appIso (U : X.Opens) : (𝟙 X :).appIso U = X.presheaf.mapIso (eqToIso (b
y simp)).op
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_appIso (U : X.Opens) :
    (𝟙 X :).appIso U = X.presheaf.mapIso (eqToIso (by simp)).op := by
  ext; simp [appIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.comp_appIso** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：comp_appIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion 
f] [IsOpenImmersion g] (U : X.Opens) : (f ≫ g).appIso U = Z.presheaf.mapIso (eqT
oIso (by simp)).op ≪≫ g.appIso _ ≪≫ f.appIso U
参数：f : X ⟶ Y；g : Y ⟶ Z；U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_appIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] (U : X.Opens) :
    (f ≫ g).appIso U =
      Z.presheaf.mapIso (eqToIso (by simp)).op ≪≫ g.appIso _ ≪≫ f.appIso U := by
  ext : 1; simp [appIso_hom, app_eq_appLE, appLE_comp_appLE, -comp_appLE]

end Scheme.Hom

/-- The open sets of an open subscheme corresponds to the open sets containing in the image. -/
@[simps]
/-
**AlgebraicGeometry.IsOpenImmersion.opensEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.IsOpenImmersion`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) →     [inst : AlgebraicGe
ometry.IsOpenImmersion f] → X.Opens ≃ { U // U ≤ AlgebraicGeometry.Scheme.Hom.op
ensRange f }
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open sets of an open subscheme corresponds to the open sets containing in th
e image.
-/
def IsOpenImmersion.opensEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.Opens ≃ { U : Y.Opens // U ≤ f.opensRange } where
  toFun U := ⟨f ''ᵁ U, Set.image_subset_range _ _⟩
  invFun U := f ⁻¹ᵁ U
  left_inv _ := Opens.ext (Set.preimage_image_eq _ f.isOpenEmbedding.injective)
  right_inv U := Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2))

namespace Scheme

/-
**AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway** 是 Mathlib 
中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isOpenImmersion_SpecMap_localizationAway {R : CommRingCat.{u}} (f : R) : I
sOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))
))
参数：f : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`：of_stalk_is
o {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.hom.base) [H : fora
ll x : X.1, IsIso (f.hom.stalkMap x)] : SheafedSp…
· 使用定理 `AlgebraicGeometry.isIso_SpecMap_stakMap_localization`：isIso_SpecMap_stak
Map_localization (R : CommRingCat.{u}) (M : Submonoid R) (x : PrimeSpectrum (Loc
alization M)) : IsIso ((Spec.toPresheafedS…
· 使用定理 `PrimeSpectrum.localization_away_isOpenEmbedding`：localization_away_isOpe
nEmbedding (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.A
way r S] : IsOpenEmbedding (comap (al…
-/
instance isOpenImmersion_SpecMap_localizationAway {R : CommRingCat.{u}} (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f :)
  · intro x
    exact isIso_SpecMap_stakMap_localization R (Submonoid.powers f) x
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  isOpenImmersion_SpecMap_localizationAway (R := .of R) f

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {R : CommRingCat} (g : ↑R),   AlgebraicGeometry.Scheme.Hom.opensRange   
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localizatio
n.Away g)))) =     PrimeSpectrum.basicOpen g
参数：g : ↑R；AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Locali
zation.Away g)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
-/
lemma Hom.opensRange_localizationAway {R : CommRingCat.{u}} (g : R) :
    (Spec.map <| CommRingCat.ofHom <| algebraMap R (Localization.Away g)).opensRange =
      PrimeSpectrum.basicOpen g := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range _ g
/-
**AlgebraicGeometry.Scheme._root_.AlgebraicGeometry.IsOpenImmersion.of_isLocaliz
ation** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization {R S} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have e := (IsLocalization.algEquiv (.powers f) S
    (Localization.Away f)).symm.toAlgHom.comp_algebraMap
  rw [← e, CommRingCat.ofHom_comp, Spec.map_comp]
  have H : IsIso (CommRingCat.ofHom (IsLocalization.algEquiv
    (Submonoid.powers f) S (Localization.Away f)).symm.toAlgHom.toRingHom) := by
    exact inferInstanceAs (IsIso <| (IsLocalization.algEquiv
      (Submonoid.powers f) S (Localization.Away f)).toRingEquiv.toCommRingCatIso.inv)
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom] at H ⊢
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：exists_affine_mem_range_and_range_subset {X : Scheme.{u}} {x : X} {U : X.O
pens} (hxU : x in U) : exists R, exists (f : Spec R ⟶ X), IsOpenImmersion f ∧ x 
in Set.range f ∧ Set.range f subseteq U
参数：hxU : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.OpenNhds.isOpenEmbedding`：isOpenEmbedding {x : X} (U : 
OpenNhds x) : IsOpenEmbedding U.1.inclusion'
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem exists_affine_mem_range_and_range_subset
    {X : Scheme.{u}} {x : X} {U : X.Opens} (hxU : x ∈ U) :
    ∃ R, ∃ (f : Spec R ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f ∧ Set.range f ⊆ U := by
  obtain ⟨⟨V, hxV⟩, R, ⟨e⟩⟩ := X.2 x
  have : e.hom.base ⟨x, hxV⟩ ∈ (Opens.map (e.inv.base ≫ V.inclusion')).obj U :=
    show ((e.hom ≫ e.inv).base ⟨x, hxV⟩).1 ∈ U from e.hom_inv_id ▸ hxU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hr'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open this (Opens.is_open' _)
  let f : Spec (.of <| Localization.Away r) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ ⟨e.inv ≫ X.ofRestrict _⟩
  refine ⟨.of (Localization.Away r), f, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  exact ⟨⟨_, hr, congr(($(e.hom_inv_id).base ⟨x, hxV⟩).1)⟩, Set.image_subset_iff.mpr hr'⟩

end Scheme

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace CommRingCat.{u}} (Y : Scheme.{u})
variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

set_option backward.isDefEq.respectTransparency false in
/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toScheme** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toScheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`.
-/
def toScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨R, i, _, h₁, h₂⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨_, H.base_open.isOpen_range⟩) ⟨x, rfl⟩
  refine ⟨R, LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f) _ h₂, ?_, ?_⟩
  · rw [LocallyRingedSpace.IsOpenImmersion.lift_range]; exact h₁
  · delta LocallyRingedSpace.IsOpenImmersion.lift; infer_instance

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toScheme_toLocallyRingedSpac
e** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toScheme_toLocallyRingedSpace : (toScheme Y f).toLocallyRingedSpace = toLo
callyRingedSpace Y.1 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toScheme_toLocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSchemeHom** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSchemeHom : toScheme Y f ⟶ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  ⟨toLocallyRingedSpaceHom _ f⟩

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSchemeHom_toPshHom** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSchemeHom_toPshHom : (toSchemeHom Y f).toPshHom = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSchemeHom_toPshHom : (toSchemeHom Y f).toPshHom = f :=
  rfl
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSchemeHom_isOpenImmersion*
* 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSchemeHom_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (toSchemeH
om Y f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toSchemeHom_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (toSchemeHom Y f) :=
  H
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.scheme_eq_of_locallyRingedSp
ace_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmers
ion`。
形式化陈述：scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme.{u}} (H : X.toLocallyRing
edSpace = Y.toLocallyRingedSpace) : X = Y
参数：H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.OpenNhds.isOpenEmbedding`：isOpenEmbedding {x : X} (U : 
OpenNhds x) : IsOpenEmbedding U.1.inclusion'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme.{u}}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y := by
  cases X; cases Y; congr
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.scheme_toScheme** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：scheme_toScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenIm
mersion f] : toScheme Y f.toPshHom = X
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.scheme_eq_of_locallyRi
ngedSpace_eq`：scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme.{u}} (H : X.toLoc
allyRingedSpace = Y.toLocallyRingedSpace) : X = Y
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.locallyRingedSpace_toL
ocallyRingedSpace`：locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedS
pace} (f : X ⟶ Y) [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace…
-/
theorem scheme_toScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    toScheme Y f.toPshHom = X := by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f.toLRSHom

end ToScheme

end PresheafedSpace.IsOpenImmersion

section Restrict

variable {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X} (h : IsOpenEmbedding f)

/-- The restriction of a Scheme along an open embedding. -/
@[simps! -isSimp carrier, simps! presheaf_obj]
/-
**AlgebraicGeometry.Scheme.restrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.Scheme`。
形式化陈述：{U : TopCat} →   (X : AlgebraicGeometry.Scheme) →     {f : U ⟶ TopCat.of ↥
X} →       Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f) → A
lgebraicGeometry.Scheme
参数：X : AlgebraicGeometry.Scheme；CategoryTheory.ConcreteCategory.hom f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…

--- 原说明 ---
The restriction of a Scheme along an open embedding.
-/
def Scheme.restrict : Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }
/-
**AlgebraicGeometry.Scheme.restrict_toPresheafedSpace** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：∀ {U : TopCat} (X : AlgebraicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h 
: Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f)),   (X.restr
ict h).toPresheafedSpace = X.restrict h
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)；X.restrict h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.restrict_toPresheafedSpace :
    (X.restrict h).toPresheafedSpace = X.toPresheafedSpace.restrict h := rfl

/-- The canonical map from the restriction to the subspace. -/
@[simps! toLRSHom_base, simps! -isSimp toLRSHom_c_app]
/-
**AlgebraicGeometry.Scheme.ofRestrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：{U : TopCat} →   (X : AlgebraicGeometry.Scheme) →     {f : U ⟶ TopCat.of ↥
X} → (h : Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f)) → X
.restrict h ⟶ X
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the restriction to the subspace.
-/
def Scheme.ofRestrict : X.restrict h ⟶ X :=
  ⟨X.toLocallyRingedSpace.ofRestrict h⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.ofRestrict_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：∀ {U : TopCat} (X : AlgebraicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h 
: Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f)) (V : X.Open
s),   AlgebraicGeometry.Scheme.Hom.app (X.ofRestrict h) V = X.presheaf.map (⋯.ad
junction.counit.app V).op
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)；V : X.Opens；X.ofRestrict h；⋯.adjunction.counit.app V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.ofRestrict_app (V) :
    (X.ofRestrict h).app V = X.presheaf.map (h.isOpenMap.adjunction.counit.app V).op :=
  rfl
/-
**AlgebraicGeometry.IsOpenImmersion.ofRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.IsOpenImmersion`。
形式化陈述：∀ {U : TopCat} (X : AlgebraicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h 
: Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f)),   Algebrai
cGeometry.IsOpenImmersion (X.ofRestrict h)
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)；X.ofRestrict h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsOpenImmersion.ofRestrict : IsOpenImmersion (X.ofRestrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance

@[simp]
/-
**AlgebraicGeometry.Scheme.ofRestrict_appLE** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：∀ {U : TopCat} (X : AlgebraicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h 
: Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f)) (V : X.Open
s) (W : (X.restrict h).Opens)   (e : W ≤ (TopologicalSpace.Opens.map (X.ofRestri
ct h).base).obj V),   AlgebraicGeometry.Scheme.Hom.appLE (X.ofRestrict h) V W e 
= X.presheaf.map (CategoryTheory.homOfLE ⋯).op
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)；V : X.Opens；W : (X.restrict h).Opens；e : W ≤ (TopologicalS
pace.Opens.map (X.ofRestrict h).base).obj V；X.ofRestrict h；CategoryTheory.homOfL
E ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.ofRestrict`：∀ {U : TopCat} (X : Algebr
aicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h : Topology.IsOpenEmbedding ⇑(Cat
egoryTheory.ConcreteCategory.hom f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma Scheme.ofRestrict_appLE (V W e) :
    (X.ofRestrict h).appLE V W e = X.presheaf.map
      (homOfLE (show X.ofRestrict h ''ᵁ _ ≤ _ by exact Set.image_subset_iff.mpr e)).op := by
  dsimp [Hom.appLE]
  exact (X.presheaf.map_comp _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.ofRestrict_appIso** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：∀ {U : TopCat} (X : AlgebraicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h 
: Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f)) (U_1 : (X.r
estrict h).Opens),   AlgebraicGeometry.Scheme.Hom.appIso (X.ofRestrict h) U_1 = 
    CategoryTheory.Iso.refl       (X.presheaf.obj (Opposite.op ((AlgebraicGeomet
ry.Scheme.Hom.opensFunctor (X.ofRestrict h)).obj U_1)))
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)；U_1 : (X.restrict h).Opens；X.ofRestrict h；X.presheaf.obj (
Opposite.op ((AlgebraicGeometry.Scheme.Hom.opensFunctor (X.ofRestrict h)).obj U_
1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.ofRestrict`：∀ {U : TopCat} (X : Algebr
aicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h : Topology.IsOpenEmbedding ⇑(Cat
egoryTheory.ConcreteCategory.hom f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom'`：appIso_hom' (U) : (f.appIso U)
.hom = f.appLE (f ''ᵁ U) U (preimage_image_eq f U).ge
· 使用定理 `AlgebraicGeometry.Scheme.ofRestrict_appLE`：∀ {U : TopCat} (X : Algebraic
Geometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h : Topology.IsOpenEmbedding ⇑(Catego
ryTheory.ConcreteCategory.hom f…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.ofRestrict_appIso (U) :
    (X.ofRestrict h).appIso U = Iso.refl _ := by
  ext1
  simp only [Hom.appIso_hom', ofRestrict_appLE, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Iso.refl_hom]

@[simp]
/-
**AlgebraicGeometry.Scheme.restrict_presheaf_map** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：∀ {U : TopCat} (X : AlgebraicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h 
: Topology.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom f))   (V W : (T
opologicalSpace.Opens ↥(X.restrict h))ᵒᵖ) (i : V ⟶ W),   (X.restrict h).presheaf
.map i = X.presheaf.map (CategoryTheory.homOfLE ⋯).op
参数：X : AlgebraicGeometry.Scheme；h : Topology.IsOpenEmbedding ⇑(CategoryTheory.Co
ncreteCategory.hom f)；V W : (TopologicalSpace.Opens ↥(X.restrict h))ᵒᵖ；i : V ⟶ W
；X.restrict h；CategoryTheory.homOfLE ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.restrict_presheaf_map (V W) (i : V ⟶ W) :
    (X.restrict h).presheaf.map i = X.presheaf.map (homOfLE (show X.ofRestrict h ''ᵁ W.unop ≤
      X.ofRestrict h ''ᵁ V.unop from Set.image_mono i.unop.le)).op := rfl

end Restrict

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : IsOpenImmersion f]

/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_isIso [IsIso g] : IsOpenImmersion g :=
  LocallyRingedSpace.IsOpenImmersion.of_isIso _
/-
**AlgebraicGeometry.IsOpenImmersion.isIso** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.IsOpenImmersion`。
形式化陈述：isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [Epi f.base] : Is
Iso f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`：to_iso [h' : E
pi f.base] : IsIso f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `AlgebraicGeometry.Scheme.instFullLocallyRingedSpaceForgetToLocallyRinged
Space`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Full
· 使用定理 `AlgebraicGeometry.Scheme.instFaithfulLocallyRingedSpaceForgetToLocallyRi
ngedSpace`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Faithful
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
-/
theorem isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [Epi f.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.toPshHom ‹_› _) _
/-
**AlgebraicGeometry.IsOpenImmersion.of_isIso_stalkMap** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f) 
[forall x, IsIso (f.stalkMap x)] : IsOpenImmersion f
参数：f : X ⟶ Y；hf : IsOpenEmbedding f；f.stalkMap x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`：of_stalk_is
o {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.hom.base) [H : fora
ll x : X.1, IsIso (f.hom.stalkMap x)] : SheafedSp…
-/
theorem of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f)
    [∀ x, IsIso (f.stalkMap x)] : IsOpenImmersion f :=
  have (x : X) : IsIso (f.toShHom.hom.stalkMap x) := inferInstanceAs (IsIso (f.stalkMap x))
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.toShHom hf

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.stalkMap x) :=
  inferInstanceAs <| IsIso (f.toLRSHom.stalkMap x)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsOpenImmersion.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.IsOpenImmersion`。
形式化陈述：of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g] [
IsOpenImmersion (f ≫ g)] : IsOpenImmersion f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso_stalkMap`：of_isIso_stalkMap {
X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f) [forall x, IsIso (f.stalk
Map x)] : IsOpenImmersion f
· 使用定理 `Topology.IsOpenEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {g : Y → Z} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]  
 [inst_2 : Topological…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
-/
lemma of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    [IsOpenImmersion (f ≫ g)] : IsOpenImmersion f :=
  haveI (x : X) : IsIso (f.stalkMap x) :=
    haveI : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    IsIso.of_isIso_comp_left (f := g.stalkMap (f x)) _
  IsOpenImmersion.of_isIso_stalkMap _ <|
    IsOpenEmbedding.of_comp _ (Scheme.Hom.isOpenEmbedding g) (Scheme.Hom.isOpenEmbedding (f ≫ g))
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @IsOpenImmersion where
  of_postcomp f g _ _ := .of_comp f g
/-
**AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：iff_isIso_stalkMap {X Y : Scheme.{u}} {f : X ⟶ Y} : IsOpenImmersion f ↔ Is
OpenEmbedding f ∧ forall x, IsIso (f.stalkMap x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso_stalkMap`：of_isIso_stalkMap {
X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f) [forall x, IsIso (f.stalk
Map x)] : IsOpenImmersion f
-/
theorem iff_isIso_stalkMap {X Y : Scheme.{u}} {f : X ⟶ Y} :
    IsOpenImmersion f ↔ IsOpenEmbedding f ∧ ∀ x, IsIso (f.stalkMap x) :=
  ⟨fun H ↦ ⟨H.1, fun x ↦ inferInstanceAs <| IsIso (f.toPshHom.stalkMap x)⟩,
    fun ⟨h, _⟩ ↦ .of_isIso_stalkMap f h⟩
/-
**AlgebraicGeometry.IsOpenImmersion._root_.AlgebraicGeometry.isIso_iff_isOpenImm
ersion_and_epi_base** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.base :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => IsOpenImmersion.isIso f⟩
/-
**AlgebraicGeometry.IsOpenImmersion._root_.AlgebraicGeometry.isIso_iff_isIso_sta
lkMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.base ∧ ∀ x, IsIso (f.stalkMap x) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base,
    IsOpenImmersion.iff_isIso_stalkMap, and_comm, ← and_assoc]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to!
      IsIso
        (TopCat.isoOfHomeo
          (Equiv.toHomeomorphOfContinuousOpen
            (.ofBijective _ ⟨h₂.injective, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
            h₂.isOpenMap)).hom
    infer_instance
  · intro H; exact ⟨inferInstance, (TopCat.homeoOfIso (asIso f.base)).isOpenEmbedding⟩

/-- An open immersion induces an isomorphism from the domain onto the image -/
/-
**AlgebraicGeometry.IsOpenImmersion.isoRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.IsOpenImmersion`。
形式化陈述：isoRestrict : X ≅ Z.restrict f.isOpenEmbedding
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f

--- 原说明 ---
An open immersion induces an isomorphism from the domain onto the image
-/
def isoRestrict : X ≅ Z.restrict f.isOpenEmbedding :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom)

local notation "forget" => Scheme.forgetToLocallyRingedSpace
/-
**AlgebraicGeometry.IsOpenImmersion.mono** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeo
metry.IsOpenImmersion`。
形式化陈述：mono : Mono f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.instFullLocallyRingedSpaceForgetToLocallyRinged
Space`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Full
· 使用定理 `AlgebraicGeometry.Scheme.instFaithfulLocallyRingedSpaceForgetToLocallyRi
ngedSpace`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Faithful
-/
instance mono : Mono f :=
  (forget).mono_of_mono_map (inferInstanceAs (Mono f.toLRSHom))
/-
**AlgebraicGeometry.IsOpenImmersion.le_monomorphisms** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：le_monomorphisms : IsOpenImmersion <= MorphismProperty.monomorphisms Schem
e.{u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.infer_property`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Categ
oryTheory.Mono f],   CategoryTheory.MorphismProper…
-/
lemma le_monomorphisms :
    IsOpenImmersion ≤ MorphismProperty.monomorphisms Scheme.{u} := fun _ _ _ _ ↦
  MorphismProperty.monomorphisms.infer_property _
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyRingedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩
/-
**AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_left** 是 Mathlib 中
的一个实例，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
-/
instance hasLimit_cospan_forget_of_left :
    HasLimit (cospan f g ⋙ forget) := by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map f) ((forget).map g)))

open CategoryTheory.Limits.WalkingCospan
/-
**AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_left'** 是 Mathlib 
中的一个实例，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_left' : HasLimit (cospan ((cospan f g ⋙ forget).
map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsOpenImmersionMapSchemeLocallyRin
gedSpaceForgetToLocallyRingedSpace`：∀ {X Z : AlgebraicGeometry.Scheme} (f : X ⟶ 
Z) [H : AlgebraicGeometry.IsOpenImmersion f],   AlgebraicGeometry.LocallyRingedS
pace.IsOpenImmer…
-/
instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance
/-
**AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_right** 是 Mathlib 
中的一个实例，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
-/
instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map g) ((forget).map f)))
/-
**AlgebraicGeometry.IsOpenImmersion.hasLimit_cospan_forget_of_right'** 是 Mathlib
 中的一个实例，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_right' : HasLimit (cospan ((cospan g f ⋙ forget)
.map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsOpenImmersionMapSchemeLocallyRin
gedSpaceForgetToLocallyRingedSpace`：∀ {X Z : AlgebraicGeometry.Scheme} (f : X ⟶ 
Z) [H : AlgebraicGeometry.IsOpenImmersion f],   AlgebraicGeometry.LocallyRingedS
pace.IsOpenImmer…
-/
instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfLeft** 是 Mathlib 中的一个
实例，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instFullLocallyRingedSpaceForgetToLocallyRinged
Space`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Full
· 使用定理 `AlgebraicGeometry.Scheme.instFaithfulLocallyRingedSpaceForgetToLocallyRi
ngedSpace`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Faithful
-/
instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.snd f.toLRSHom g.toLRSHom).toShHom.hom)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfRight** 是 Mathlib 中的一
个实例，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instFullLocallyRingedSpaceForgetToLocallyRinged
Space`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Full
· 使用定理 `AlgebraicGeometry.Scheme.instFaithfulLocallyRingedSpaceForgetToLocallyRi
ngedSpace`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Faithful
-/
instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.fst g.toLRSHom f.toLRSHom).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit _ _
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimit (cospan g f) forget :=
  preservesPullback_symmetry _ _ _
/-
**AlgebraicGeometry.IsOpenImmersion.hasPullback_of_left** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：hasPullback_of_left : HasPullback f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
instance hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget
/-
**AlgebraicGeometry.IsOpenImmersion.hasPullback_of_right** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：hasPullback_of_right : HasPullback g f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
instance hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion (pullback.snd f g) := by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  change LocallyRingedSpace.IsOpenImmersion _
  rw [← this]
  infer_instance
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimit (cospan f g) Scheme.forgetToTop := by
  delta Scheme.forgetToTop
  refine @Limits.comp_preservesLimit _ _ _ _ _ _ (K := cospan f g) _ _ (F := forget)
    (G := LocallyRingedSpace.forgetToTop) ?_ ?_
  · infer_instance
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoCospan.{u} _).symm ?_
  dsimp [LocallyRingedSpace.forgetToTop]
  infer_instance
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullback_symmetry _ _ _
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimit (cospan f g) Scheme.forget := by delta Scheme.forget; infer_instance
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimit (cospan g f) Scheme.forget := by delta Scheme.forget; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：range_pullbackSnd : Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instPreservesLimitSchemeTopCatWalkingC
ospanCospanForgetToTop`：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y 
⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],   CategoryTheory.Limits.Preserve
sLim…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_snd`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `TopCat.pullback_snd_image_fst_preimage`：pullback_snd_image_fst_preimage 
(f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) : (pullback.snd f g) '' (pullback.fst f g) ⁻
¹' U = g ⁻¹' f '' U
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem range_pullbackSnd :
    Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange := by
  rw [← show _ = (pullback.snd f g).base from
    PreservesPullback.iso_hom_snd Scheme.forgetToTop f g, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr, ← @Set.preimage_univ _ _ (pullback.fst f.base g.base)]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw`
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
/-
**AlgebraicGeometry.IsOpenImmersion._root_.AlgebraicGeometry.Scheme.Hom.opensRan
ge_pullbackSnd** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd :
    (pullback.snd f g).opensRange = g ⁻¹ᵁ f.opensRange :=
  Opens.ext (range_pullbackSnd f g)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsOpenImmersion.range_pullbackFst** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：range_pullbackFst : Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instPreservesLimitSchemeTopCatWalkingC
ospanCospanForgetToTop_1`：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : 
Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],   CategoryTheory.Limits.Preser
vesLim…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `TopCat.pullback_fst_image_snd_preimage`：pullback_fst_image_snd_preimage 
(f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) : (pullback.fst f g) '' (pullback.snd f g) ⁻
¹' U = f ⁻¹' g '' U
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem range_pullbackFst :
    Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange := by
  rw [← show _ = (pullback.fst g f).base from
    PreservesPullback.iso_hom_fst Scheme.forgetToTop g f, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr, ← @Set.preimage_univ _ _ (pullback.snd g.base f.base)]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw`
  · erw [TopCat.pullback_fst_image_snd_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
/-
**AlgebraicGeometry.IsOpenImmersion._root_.AlgebraicGeometry.Scheme.Hom.opensRan
ge_pullbackFst** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst :
    (pullback.fst g f).opensRange = g ⁻¹ᵁ f.opensRange :=
  Opens.ext (range_pullbackFst f g)
/-
**AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：range_pullback_to_base_of_left : Set.range (pullback.fst f g ≫ f) = Set.ra
nge f inter Set.range g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`：range_pullbackSnd :
 Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.map_obj`：map_obj (f : X ⟶ Y) (U) (p) : (map f).ob
j ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩
· 使用定理 `TopologicalSpace.Opens.coe_mk`：coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U
, hU⟩ : Opens α) = U
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `TopologicalSpace.Opens.carrier_eq_coe`：∀ {α : Type u_2} [inst : Topologi
calSpace α] (U : TopologicalSpace.Opens α), U.carrier = ↑U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
-/
theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst f g ≫ f) = Set.range f ∩ Set.range g := by
  rw [pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullbackSnd, Opens.map_obj, Opens.coe_mk,
    Set.image_preimage_eq_inter_range, Opens.carrier_eq_coe, Scheme.Hom.coe_opensRange]
/-
**AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：range_pullback_to_base_of_right : Set.range (pullback.fst g f ≫ g) = Set.r
ange g inter Set.range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullbackFst`：range_pullbackFst :
 Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.map_obj`：map_obj (f : X ⟶ Y) (U) (p) : (map f).ob
j ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩
· 使用定理 `TopologicalSpace.Opens.coe_mk`：coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U
, hU⟩ : Opens α) = U
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `TopologicalSpace.Opens.carrier_eq_coe`：∀ {α : Type u_2} [inst : Topologi
calSpace α] (U : TopologicalSpace.Opens α), U.carrier = ↑U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
-/
theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst g f ≫ g) = Set.range g ∩ Set.range f := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_pullbackFst,
    Opens.map_obj, Opens.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm, Opens.carrier_eq_coe, Scheme.Hom.coe_opensRange]
/-
**AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullba
ck** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：image_preimage_eq_preimage_image_of_isPullback {X Y U V : Scheme.{u}} {f :
 X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [IsOpenImmer
sion iU] (H : IsPullback f' iU iV f) (W : V.Opens) : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV 
''ᵁ W
参数：H : IsPullback f' iU iV f；W : V.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`：range_pullbackSnd :
 Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_snd`：isoPullback_inv_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.s
nd _ _
-/
lemma image_preimage_eq_preimage_image_of_isPullback {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (W : V.Opens) : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W := by
  ext x
  by_cases hx : x ∈ Set.range iU
  · obtain ⟨x, rfl⟩ := hx
    simp only [SetLike.mem_coe, Opens.map_coe, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← H.w]
    simp
  · constructor
    · rintro ⟨x, hx, rfl⟩; cases hx ⟨x, rfl⟩
    · rintro ⟨y, hy, e : iV y = f x⟩
      obtain ⟨x, rfl⟩ := (IsOpenImmersion.range_pullbackSnd iV f).ge ⟨y, e⟩
      rw [← H.isoPullback_inv_snd] at hx
      cases hx ⟨_, rfl⟩

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
/-
**AlgebraicGeometry.IsOpenImmersion.lift** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.IsOpenImmersion`。
形式化陈述：lift (H' : Set.range g subseteq Set.range f) : Y ⟶ X
参数：H' : Set.range g subseteq Set.range f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` who
se topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y
 ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g ⊆ Set.range f) : Y ⟶ X :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom H'⟩

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsOpenImmersion.lift_fac** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.IsOpenImmersion`。
形式化陈述：lift_fac (H' : Set.range g subseteq Set.range f) : lift f g H' ≫ f = g
参数：H' : Set.range g subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ext'`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 g : X ⟶ Y},   AlgebraicGeometry.Scheme.Hom.toLRSHom f = AlgebraicGeometry.Schem
e.Hom.toLRSHom g → f = …
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac`：lift_fac 
(H' : Set.range g.base subseteq Set.range f.base) : lift f g H' ≫ f = g
-/
theorem lift_fac (H' : Set.range g ⊆ Set.range f) : lift f g H' ≫ f = g :=
  Scheme.Hom.ext' <| LocallyRingedSpace.IsOpenImmersion.lift_fac f.toLRSHom g.toLRSHom H'
/-
**AlgebraicGeometry.IsOpenImmersion.lift_uniq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.IsOpenImmersion`。
形式化陈述：lift_uniq (H' : Set.range g subseteq Set.range f) (l : Y ⟶ X) (hl : l ≫ f 
= g) : l = lift f g H'
参数：H' : Set.range g subseteq Set.range f；l : Y ⟶ X；hl : l ≫ f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ext'`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 g : X ⟶ Y},   AlgebraicGeometry.Scheme.Hom.toLRSHom f = AlgebraicGeometry.Schem
e.Hom.toLRSHom g → f = …
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq`：lift_uni
q (H' : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g)
 : l = lift f g H'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem lift_uniq (H' : Set.range g ⊆ Set.range f) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
  Scheme.Hom.ext' <| LocallyRingedSpace.IsOpenImmersion.lift_uniq
    f.toLRSHom g.toLRSHom H' l.toLRSHom congr(($hl).toLRSHom)

@[reassoc]
/-
**AlgebraicGeometry.IsOpenImmersion.comp_lift** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.IsOpenImmersion`。
形式化陈述：comp_lift {Y' : Scheme} (g' : Y' ⟶ Y) (H : Set.range g subseteq Set.range 
f) : g' ≫ lift f g H = lift f (g' ≫ g) (.trans (by simp [Set.range_comp_subset_r
ange]) H)
参数：g' : Y' ⟶ Y；H : Set.range g subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_lift {Y' : Scheme} (g' : Y' ⟶ Y) (H : Set.range g ⊆ Set.range f) :
    g' ≫ lift f g H = lift f (g' ≫ g) (.trans (by simp [Set.range_comp_subset_range]) H) := by
  simp [← cancel_mono f]
/-
**AlgebraicGeometry.IsOpenImmersion.isPullback_lift_id** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：isPullback_lift_id {X U Y : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImm
ersion g] (H : Set.range f subseteq Set.range g) : IsPullback (IsOpenImmersion.l
ift g f H) (𝟙 _) g f
参数：f : X ⟶ Y；g : U ⟶ Y；H : Set.range f subseteq Set.range g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用引理 `CategoryTheory.IsPullback.of_id_snd`：of_id_snd : IsPullback f (𝟙 _) (𝟙 _
) f
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
-/
theorem isPullback_lift_id
    {X U Y : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g]
    (H : Set.range f ⊆ Set.range g) :
    IsPullback (IsOpenImmersion.lift g f H) (𝟙 _) g f := by
  convert! IsPullback.of_id_snd.paste_horiz (IsKernelPair.id_of_mono g)
  · exact (Category.comp_id _).symm
  · simp

/-- Two open immersions with equal range are isomorphic. -/
/-
**AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.IsOpenImmersion`。
形式化陈述：isoOfRangeEq [IsOpenImmersion g] (e : Set.range f = Set.range g) : X ≅ Y w
here hom
参数：e : Set.range f = Set.range g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two open immersions with equal range are isomorphic.
-/
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f = Set.range g) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：isoOfRangeEq_hom_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenI
mmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) : (isoOfRangeEq 
f g e).hom ≫ g = f
参数：f : X ⟶ Z；g : Y ⟶ Z；e : Set.range f = Set.range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma isoOfRangeEq_hom_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac _ _ (le_of_eq e)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：isoOfRangeEq_inv_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenI
mmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) : (isoOfRangeEq 
f g e).inv ≫ f = g
参数：f : X ⟶ Z；g : Y ⟶ Z；e : Set.range f = Set.range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isoOfRangeEq_inv_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac _ _ (le_of_eq e.symm)
/-
**AlgebraicGeometry.IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：app_eq_invApp_app_of_comp_eq_aux {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶
 X) (fg : Y ⟶ X) (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) : f ⁻¹ᵁ 
V = fg ⁻¹ᵁ (g ''ᵁ V)
参数：f : Y ⟶ U；g : U ⟶ X；fg : Y ⟶ X；H : fg = f ≫ g；V : U.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem app_eq_invApp_app_of_comp_eq_aux {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) :
    f ⁻¹ᵁ V = fg ⁻¹ᵁ (g ''ᵁ V) := by
  simp_all

set_option backward.isDefEq.respectTransparency false in
/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
/-
**AlgebraicGeometry.IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.IsOpenImmersion`。
形式化陈述：app_eq_appIso_inv_app_of_comp_eq {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶
 X) (fg : Y ⟶ X) (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) : f.app 
V = (g.appIso V).inv ≫ fg.app (g ''ᵁ V) ≫ Y.presheaf.map (eqToHom <| IsOpenImmer
sion.app_eq_invApp_app_of_comp_eq_aux f g fg H V).op
参数：f : Y ⟶ U；g : U ⟶ X；fg : Y ⟶ X；H : fg = f ≫ g；V : U.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux`：app_
eq_invApp_app_of_comp_eq_aux {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : 
Y ⟶ X) (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.O…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_app_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens
) {Z : CommRingCat}   (h :     X.preshe…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.naturality_assoc`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) {U U' : Y.Opens} (i : Opposite.op U' ⟶ Opposite.op U) {Z :
 CommRingCat}   (h : X.presheaf.obj…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
The `fg` argument is to avoid nasty stuff about dependent types.
-/
theorem app_eq_appIso_inv_app_of_comp_eq {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) :
    f.app V = (g.appIso V).inv ≫ fg.app (g ''ᵁ V) ≫ Y.presheaf.map
      (eqToHom <| IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux f g fg H V).op := by
  subst H
  rw [Scheme.Hom.comp_app, Category.assoc, Scheme.Hom.appIso_inv_app_assoc, f.naturality_assoc,
    ← Functor.map_comp, ← op_comp, Quiver.Hom.unop_op, eqToHom_map, eqToHom_trans,
    eqToHom_op, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
/-
**AlgebraicGeometry.IsOpenImmersion.lift_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.IsOpenImmersion`。
形式化陈述：lift_app {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] 
(H) (V : U.Opens) : (lift f g H).app V = (f.appIso V).inv ≫ g.app (f ''ᵁ V) ≫ X.
presheaf.map (eqToHom <| app_eq_invApp_app_of_comp_eq_aux _ _ _ (lift_fac ..).sy
mm V).op
参数：f : U ⟶ Y；g : X ⟶ Y；H；V : U.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq`：app_
eq_appIso_inv_app_of_comp_eq {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : 
Y ⟶ X) (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.O…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
-/
theorem lift_app {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H)
    (V : U.Opens) :
    (lift f g H).app V = (f.appIso V).inv ≫ g.app (f ''ᵁ V) ≫
      X.presheaf.map (eqToHom <| app_eq_invApp_app_of_comp_eq_aux _ _ _ (lift_fac ..).symm V).op :=
  IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq _ _ _ (lift_fac _ _ _).symm _
/-
**AlgebraicGeometry.IsOpenImmersion.isPullback** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.IsOpenImmersion`。
形式化陈述：isPullback {U V X Y : Scheme.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f
 : X ⟶ Y) [IsOpenImmersion iU] [IsOpenImmersion iV] (H : iU ≫ f = g ≫ iV) (H' : 
f ⁻¹ᵁ iV.opensRange = iU.opensRange) : IsPullback g iU iV f
参数：g : U ⟶ V；iU : U ⟶ X；iV : V ⟶ Y；f : X ⟶ Y；H : iU ≫ f = g ≫ iV；H' : f ⁻¹ᵁ iV.o
pensRange = iU.opensRange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instSndScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`：range_pullbackSnd :
 Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac_assoc`：∀ {X Y Z :
 AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [inst : AlgebraicGeometry.IsO
penImmersion f]   [inst_1 : AlgebraicGeometry.IsOp…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac`：isoOfRangeEq_inv
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma isPullback {U V X Y : Scheme.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion iU] [IsOpenImmersion iV] (H : iU ≫ f = g ≫ iV)
    (H' : f ⁻¹ᵁ iV.opensRange = iU.opensRange) : IsPullback g iU iV f := by
  let e := IsOpenImmersion.isoOfRangeEq (pullback.snd iV f) iU
    (by simpa [range_pullbackSnd] using congr(($H').1))
  convert!
    (IsPullback.of_horiz_isIso
          (show CommSq e.inv iU (pullback.snd iV f) (𝟙 X) from ⟨by simp [e]⟩)).paste_horiz
      (IsPullback.of_hasPullback iV f)
  simp [← cancel_mono iV, e, pullback.condition, H]

/-- If `f` is an open immersion `X ⟶ Y`, the global sections of `X`
are naturally isomorphic to the sections of `Y` over the image of `f`. -/
noncomputable
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ΓIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    Γ(X, f ⁻¹ᵁ U) ≅ Γ(Y, f.opensRange ⊓ U) :=
  (f.appIso (f ⁻¹ᵁ U)).symm ≪≫
    Y.presheaf.mapIso (eqToIso <| (f.image_preimage_eq_opensRange_inf U).symm).op

@[simp]
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    (ΓIso f U).inv = f.appLE (f.opensRange ⊓ U) (f ⁻¹ᵁ U)
      (by rw [← f.image_preimage_eq_opensRange_inf, f.preimage_image_eq]) := by
  simp only [ΓIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
    Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

@[reassoc, elementwise]
/-
**AlgebraicGeometry.IsOpenImmersion.map_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ΓIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    Y.presheaf.map (homOfLE inf_le_right).op ≫ (ΓIso f U).inv = f.app U := by
  simp [Scheme.Hom.appLE_eq_app]

@[reassoc, elementwise]
/-
**AlgebraicGeometry.IsOpenImmersion.app_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma app_ΓIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    f.app U ≫ (ΓIso f U).hom = Y.presheaf.map (homOfLE inf_le_right).op := by
  rw [← map_ΓIso_inv]
  simp [-ΓIso_inv]

/-- Given an open immersion `f : U ⟶ X`, the isomorphism between global sections
  of `U` and the sections of `X` at the image of `f`. -/
noncomputable
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ΓIsoTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Γ(X, ⊤) ≅ Γ(Y, f.opensRange) :=
  (f.appIso ⊤).symm ≪≫ Y.presheaf.mapIso (eqToIso f.image_top_eq_opensRange.symm).op
/-
**AlgebraicGeometry.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f]
    (H' : Set.range g ⊆ Set.range f) [IsOpenImmersion g] :
    IsOpenImmersion (IsOpenImmersion.lift f g H') :=
  haveI : IsOpenImmersion (IsOpenImmersion.lift f g H' ≫ f) := by simpa
  IsOpenImmersion.of_comp _ f

end IsOpenImmersion

/-
**AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIso_of_isOpenImmersion_of_opensRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ 
Y) [IsOpenImmersion f] (hf : f.opensRange = ⊤) : IsIso f
参数：f : X ⟶ Y；hf : f.opensRange = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base`：∀ {X Y : Algeb
raicGeometry.Scheme} (f : X ⟶ Y),   CategoryTheory.IsIso f ↔ AlgebraicGeometry.I
sOpenImmersion f ∧ CategoryTheory.Epi f.base
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.ext_iff`：∀ {α : Type u_2} [inst : TopologicalSpac
e α] {U V : TopologicalSpace.Opens α}, U = V ↔ ↑U = ↑V
-/
lemma isIso_of_isOpenImmersion_of_opensRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : f.opensRange = ⊤) : IsIso f := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
  exact TopologicalSpace.Opens.ext_iff.mp hf

section MorphismProperty

/-
**AlgebraicGeometry.isOpenImmersion_isStableUnderComposition** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry`。
形式化陈述：isOpenImmersion_isStableUnderComposition : MorphismProperty.IsStableUnderC
omposition @IsOpenImmersion where comp_mem f g _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isOpenImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsOpenImmersion where
  comp_mem f g _ _ := LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom
/-
**AlgebraicGeometry.isOpenImmersion_respectsIso** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersio
n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition`
：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStableUnd
erComposition] (hP : isomorphisms C <= P) : RespectsIso P
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
-/
instance isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersion := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance
/-
**AlgebraicGeometry.isOpenImmersion_isMultiplicative** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：isOpenImmersion_isMultiplicative : MorphismProperty.IsMultiplicative @IsOp
enImmersion where id_mem _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
-/
instance isOpenImmersion_isMultiplicative :
    MorphismProperty.IsMultiplicative @IsOpenImmersion where
  id_mem _ := inferInstance
/-
**AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange** 是 Mathlib 中的一个实例，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：isOpenImmersion_stableUnderBaseChange : MorphismProperty.IsStableUnderBase
Change @IsOpenImmersion
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.mk'`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProper
ty C} [P.RespectsIso],   (∀ (X Y S : C) (f : X ⟶ …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
-/
instance isOpenImmersion_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion :=
  MorphismProperty.IsStableUnderBaseChange.mk' <| by
    intro X Y Z f g _ H; infer_instance

end MorphismProperty

namespace Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-
**AlgebraicGeometry.Scheme.image_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：image_basicOpen {U : X.Opens} (r : Γ(X, U)) : f ''ᵁ X.basicOpen r = Y.basi
cOpen ((f.appIso U).inv r)
参数：r : Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_app_apply`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens
)   (x : ↑(X.presheaf.obj (Opposite.op …
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem image_basicOpen {U : X.Opens} (r : Γ(X, U)) :
    f ''ᵁ X.basicOpen r = Y.basicOpen ((f.appIso U).inv r) := by
  have e := Scheme.preimage_basicOpen f ((f.appIso U).inv r)
  rw [Scheme.Hom.appIso_inv_app_apply, Scheme.basicOpen_res, inf_eq_right.mpr _] at e
  · rw [← e, f.image_preimage_eq_opensRange_inf, inf_eq_right]
    refine Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range _ _)
  · exact (X.basicOpen_le r).trans (f.preimage_image_eq _).ge
/-
**AlgebraicGeometry.Scheme.image_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：image_zeroLocus {U : X.Opens} (s : Set Γ(X, U)) : f '' X.zeroLocus s = Y.z
eroLocus ((f.appIso U).inv.hom '' s) inter Set.range f
参数：s : Set Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
lemma image_zeroLocus {U : X.Opens} (s : Set Γ(X, U)) :
    f '' X.zeroLocus s = Y.zeroLocus ((f.appIso U).inv.hom '' s) ∩ Set.range f := by
  ext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hx
    simp [f.isOpenEmbedding.injective.mem_set_image, ← Scheme.image_basicOpen]
  · simp only [Set.mem_inter_iff, hx, and_false, iff_false]
    exact fun H ↦ hx (Set.image_subset_range _ _ H)

set_option backward.isDefEq.respectTransparency.types false in
/-- If
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square and `g` is an open immersion, then the stalk map induced by `snd` at `p`
is isomorphic to the stalk map of `f` at `fst p`.
-/
/-
**AlgebraicGeometry.Scheme.stalkMapIsoOfIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：stalkMapIsoOfIsPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
 {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsOpenImmersion g] (p : P
) (x : X
参数：h : IsPullback fst snd f g；p : P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square and `g` is an open immersion, then the stalk map induced by
 `snd` at `p`
is isomorphic to the stalk map of `f` at `fst p`.
-/
noncomputable def stalkMapIsoOfIsPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [IsOpenImmersion g] (p : P) (x : X := fst p) (hx : fst p = x := by cat_disch) :
    Arrow.mk (f.stalkMap x) ≅ Arrow.mk (snd.stalkMap p) :=
  haveI : IsOpenImmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hx, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hx]) ≪≫
      asIso (fst.stalkMap p))
    (by
      subst hx
      simp [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ h.w])

end Scheme

end AlgebraicGeometry

