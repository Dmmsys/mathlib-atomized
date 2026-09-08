/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Families of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of functors. The family is said to jointly reflect
isomorphisms (resp. monomorphisms, resp. epimorphisms) if every `f : X ⟶ Y`
in `C` for which `Fᵢ.map f` is an isomorphism (resp. monomorphism, resp. epimorphism)
for all `i` is an isomorphism.

-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]

/-- A family of functors jointly reflects isomorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an isomorphism, then `f` is an isomorphism. -/
/-
**CategoryTheory.JointlyReflectIsomorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{u_4, u_1} C] →     {I 
: Type u_2} →       {D : I → Type u_3} →         [inst_1 : (i : I) → CategoryThe
ory.Category.{u_5, u_3} (D i)] →           ((i : I) → CategoryTheory.Functor C (
D i)) → Prop
参数：i : I；D i；(i : I) → CategoryTheory.Functor C (D i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functors jointly reflects isomorphisms if for every morphism `f : X 
⟶ Y`
such that the image of `f` under all `F i` is an isomorphism, then `f` is an iso
morphism.
-/
structure JointlyReflectIsomorphisms (F : ∀ i, C ⥤ D i) : Prop where
  isIso {X Y : C} (f : X ⟶ Y) [∀ i, IsIso ((F i).map f)] : IsIso f

/-- A family of functors jointly reflects monomorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an monomorphism, then `f` is an monomorphism. -/
/-
**CategoryTheory.JointlyReflectMonomorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{u_4, u_1} C] →     {I 
: Type u_2} →       {D : I → Type u_3} →         [inst_1 : (i : I) → CategoryThe
ory.Category.{u_5, u_3} (D i)] →           ((i : I) → CategoryTheory.Functor C (
D i)) → Prop
参数：i : I；D i；(i : I) → CategoryTheory.Functor C (D i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functors jointly reflects monomorphisms if for every morphism `f : X
 ⟶ Y`
such that the image of `f` under all `F i` is an monomorphism, then `f` is an mo
nomorphism.
-/
structure JointlyReflectMonomorphisms (F : ∀ i, C ⥤ D i) : Prop where
  mono {X Y : C} (f : X ⟶ Y) [∀ i, Mono ((F i).map f)] : Mono f

/-- A family of functors jointly reflects epimorphisms if for every morphism `f : X ⟶ Y`
such that the image of `f` under all `F i` is an epimorphism, then `f` is an epimorphism. -/
/-
**CategoryTheory.JointlyReflectEpimorphisms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{u_4, u_1} C] →     {I 
: Type u_2} →       {D : I → Type u_3} →         [inst_1 : (i : I) → CategoryThe
ory.Category.{u_5, u_3} (D i)] →           ((i : I) → CategoryTheory.Functor C (
D i)) → Prop
参数：i : I；D i；(i : I) → CategoryTheory.Functor C (D i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functors jointly reflects epimorphisms if for every morphism `f : X 
⟶ Y`
such that the image of `f` under all `F i` is an epimorphism, then `f` is an epi
morphism.
-/
structure JointlyReflectEpimorphisms (F : ∀ i, C ⥤ D i) : Prop where
  epi {X Y : C} (f : X ⟶ Y) [∀ i, Epi ((F i).map f)] : Epi f

/-- A family of functors is jointly faithful if whenever two morphisms `f : X ⟶ Y`
and `g : X ⟶ Y` become equal after applying all functors `F i`, then `f = g`. -/
/-
**CategoryTheory.JointlyFaithful** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{u_4, u_1} C] →     {I 
: Type u_2} →       {D : I → Type u_3} →         [inst_1 : (i : I) → CategoryThe
ory.Category.{u_5, u_3} (D i)] →           ((i : I) → CategoryTheory.Functor C (
D i)) → Prop
参数：i : I；D i；(i : I) → CategoryTheory.Functor C (D i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functors is jointly faithful if whenever two morphisms `f : X ⟶ Y`
and `g : X ⟶ Y` become equal after applying all functors `F i`, then `f = g`.
-/
structure JointlyFaithful (F : ∀ i, C ⥤ D i) : Prop where
  map_injective {X Y : C} {f g : X ⟶ Y} (h : ∀ i, (F i).map f = (F i).map g) : f = g

variable {F : ∀ i, C ⥤ D i}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.JointlyFaithful.of_jointly_reflects_isIso_of_mono** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.JointlyFaithful`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_4, u_1} C] {I : Type u
_2} {D : I → Type u_3}   [inst_1 : (i : I) → CategoryTheory.Category.{u_5, u_3} 
(D i)] {F : (i : I) → CategoryTheory.Functor C (D i)}   [CategoryTheory.Limits.H
asEqualizers C]   [∀ (i : I), CategoryTheory.Limits.PreservesLimitsOfShape Categ
oryTheory.Limits.WalkingParallelPair (F i)],   (∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Categor
yTheory.Mono f],       (∀ (i : I), CategoryTheory.IsIso ((F i).map f)) → Categor
yTheory.IsIso f) →     CategoryTheory.JointlyFaithful F
参数：i : I；D i；i : I；D i；i : I；F i；∀ ⦃X Y : C⦄ (f : X ⟶ Y) [CategoryTheory.Mono f]
,       (∀ (i : I), CategoryTheory.IsIso ((F i).map f)) → CategoryTheory.IsIso f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.eq_of_epi_equalizer`：eq_of_epi_equalizer [HasEqual
izer f g] [Epi (equalizer.ι f g)] : f = g
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
lemma JointlyFaithful.of_jointly_reflects_isIso_of_mono [HasEqualizers C]
    [∀ i, PreservesLimitsOfShape WalkingParallelPair (F i)]
    (hF : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f],
      (∀ i, IsIso ((F i).map f)) → IsIso f) :
    JointlyFaithful F where
  map_injective {X Y} f g hfg :=
    have :=
      hF (equalizer.ι f g) (fun i ↦ by
        let hc := isLimitForkMapOfIsLimit (F i) _ (equalizerIsEqualizer f g)
        obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hc (𝟙 _) (by simpa using hfg i)
        exact ⟨l, Fork.IsLimit.hom_ext hc (by cat_disch), by cat_disch⟩)
    eq_of_epi_equalizer

namespace JointlyReflectIsomorphisms

variable (h : JointlyReflectIsomorphisms F)

include h

/-
**CategoryTheory.JointlyReflectIsomorphisms.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：isIso_iff {X Y : C} (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.JointlyReflectIsomorphisms.isIso`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [ins
t_1 : (i : I) → CategoryTheory.Catego…
-/
lemma isIso_iff {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, IsIso ((F i).map f) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ h.isIso f⟩
/-
**CategoryTheory.JointlyReflectIsomorphisms.mono** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.JointlyReflectIsomorphisms`。
形式化陈述：mono {X Y : C} (f : X ⟶ Y) [hf : forall i, Mono ((F i).map f)] [forall i, 
PreservesLimit (cospan f f) (F i)] [HasPullback f f] : Mono f
参数：f : X ⟶ Y；(F i).map f；cospan f f；F i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.mono_iff_isIso_fst`：mono_iff_isIso_fst (hc : IsLimit c) :
 Mono f ↔ IsIso c.fst
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`：isIso_iff {X Y : C}
 (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma mono {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Mono ((F i).map f)]
    [∀ i, PreservesLimit (cospan f f) (F i)] [HasPullback f f] :
    Mono f := by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc, h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)
/-
**CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectMonomorphisms** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：jointlyReflectMonomorphisms [forall i, PreservesLimitsOfShape WalkingCospa
n (F i)] [HasPullbacks C] : JointlyReflectMonomorphisms F where mono f _
参数：F i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.mono`：mono {X Y : C} (f : X ⟶ 
Y) [hf : forall i, Mono ((F i).map f)] [forall i, PreservesLimit (cospan f f) (F
 i)] [HasPullback f f] : Mono f
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma jointlyReflectMonomorphisms [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
    [HasPullbacks C] :
    JointlyReflectMonomorphisms F where
  mono f _ := h.mono f
/-
**CategoryTheory.JointlyReflectIsomorphisms.epi** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.JointlyReflectIsomorphisms`。
形式化陈述：epi {X Y : C} (f : X ⟶ Y) [hf : forall i, Epi ((F i).map f)] [forall i, Pr
eservesColimit (span f f) (F i)] [HasPushout f f] : Epi f
参数：f : X ⟶ Y；(F i).map f；span f f；F i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.epi_iff_isIso_inl`：epi_iff_isIso_inl (hc : IsColimit c) :
 Epi f ↔ IsIso c.inl
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`：isIso_iff {X Y : C}
 (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma epi {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Epi ((F i).map f)]
    [∀ i, PreservesColimit (span f f) (F i)] [HasPushout f f] : Epi f := by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc, h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)
/-
**CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectEpimorphisms** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：jointlyReflectEpimorphisms [forall i, PreservesColimitsOfShape WalkingSpan
 (F i)] [HasPushouts C] : JointlyReflectEpimorphisms F where epi f _
参数：F i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.epi`：epi {X Y : C} (f : X ⟶ Y)
 [hf : forall i, Epi ((F i).map f)] [forall i, PreservesColimit (span f f) (F i)
] [HasPushout f f] : Epi f
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma jointlyReflectEpimorphisms [∀ i, PreservesColimitsOfShape WalkingSpan (F i)]
    [HasPushouts C] :
    JointlyReflectEpimorphisms F where
  epi f _ := h.epi f
/-
**CategoryTheory.JointlyReflectIsomorphisms.jointlyFaithful** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：jointlyFaithful [forall i, PreservesLimitsOfShape WalkingParallelPair (F i
)] [HasEqualizers C] : JointlyFaithful F
参数：F i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.JointlyFaithful.of_jointly_reflects_isIso_of_mono`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I →
 Type u_3}   [inst_1 : (i : I) → CategoryTheory.Catego…
· 使用定理 `CategoryTheory.JointlyReflectIsomorphisms.isIso`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [ins
t_1 : (i : I) → CategoryTheory.Catego…
-/
lemma jointlyFaithful [∀ i, PreservesLimitsOfShape WalkingParallelPair (F i)] [HasEqualizers C] :
    JointlyFaithful F :=
  .of_jointly_reflects_isIso_of_mono (fun _ _ _ _ _ ↦ h.isIso _)

end JointlyReflectIsomorphisms

/-
**CategoryTheory.JointlyReflectMonomorphisms.mono_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.JointlyReflectMonomorphisms`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_4, u_1} C] {I : Type u
_2} {D : I → Type u_3}   [inst_1 : (i : I) → CategoryTheory.Category.{u_5, u_3} 
(D i)] {F : (i : I) → CategoryTheory.Functor C (D i)},   CategoryTheory.JointlyR
eflectMonomorphisms F →     ∀ [∀ (i : I), (F i).PreservesMonomorphisms] {X Y : C
} (f : X ⟶ Y),       CategoryTheory.Mono f ↔ ∀ (i : I), CategoryTheory.Mono ((F 
i).map f)
参数：i : I；D i；i : I；D i；i : I；F i；f : X ⟶ Y；i : I；(F i).map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.JointlyReflectMonomorphisms.mono`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [ins
t_1 : (i : I) → CategoryTheory.Catego…
-/
lemma JointlyReflectMonomorphisms.mono_iff (h : JointlyReflectMonomorphisms F)
    [∀ i, (F i).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ i, Mono ((F i).map f) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ h.mono f⟩
/-
**CategoryTheory.JointlyReflectEpimorphisms.epi_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.JointlyReflectEpimorphisms`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_4, u_1} C] {I : Type u
_2} {D : I → Type u_3}   [inst_1 : (i : I) → CategoryTheory.Category.{u_5, u_3} 
(D i)] {F : (i : I) → CategoryTheory.Functor C (D i)},   CategoryTheory.JointlyR
eflectEpimorphisms F →     ∀ [∀ (i : I), (F i).PreservesEpimorphisms] {X Y : C} 
(f : X ⟶ Y),       CategoryTheory.Epi f ↔ ∀ (i : I), CategoryTheory.Epi ((F i).m
ap f)
参数：i : I；D i；i : I；D i；i : I；F i；f : X ⟶ Y；i : I；(F i).map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.JointlyReflectEpimorphisms.epi`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [inst_
1 : (i : I) → CategoryTheory.Catego…
-/
lemma JointlyReflectEpimorphisms.epi_iff (h : JointlyReflectEpimorphisms F)
    [∀ i, (F i).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ i, Epi ((F i).map f) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ h.epi f⟩

namespace JointlyFaithful

/-
**CategoryTheory.JointlyFaithful.jointlyReflectMonomorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.JointlyFaithful`。
形式化陈述：jointlyReflectMonomorphisms (h : JointlyFaithful F) : JointlyReflectMonomo
rphisms F where mono {X Y} f _
参数：h : JointlyFaithful F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.JointlyFaithful.map_injective`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [inst_1
 : (i : I) → CategoryTheory.Catego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jointlyReflectMonomorphisms (h : JointlyFaithful F) :
    JointlyReflectMonomorphisms F where
  mono {X Y} f _ := ⟨fun {Z} g₁ g₂ hg ↦ h.map_injective (fun i ↦ by
    simp only [← cancel_mono ((F i).map f), ← Functor.map_comp, hg])⟩
/-
**CategoryTheory.JointlyFaithful.jointlyReflectEpimorphisms** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.JointlyFaithful`。
形式化陈述：jointlyReflectEpimorphisms (h : JointlyFaithful F) : JointlyReflectEpimorp
hisms F where epi {X Y} f _
参数：h : JointlyFaithful F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.JointlyFaithful.map_injective`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [inst_1
 : (i : I) → CategoryTheory.Catego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jointlyReflectEpimorphisms (h : JointlyFaithful F) :
    JointlyReflectEpimorphisms F where
  epi {X Y} f _ := ⟨fun {Z} g₁ g₂ hg ↦ h.map_injective (fun i ↦ by
    simp only [← cancel_epi ((F i).map f), ← Functor.map_comp, hg])⟩
/-
**CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.JointlyFaithful`。
形式化陈述：jointlyReflectsIsomorphisms [Balanced C] (h : JointlyFaithful F) : Jointly
ReflectIsomorphisms F where isIso f _
参数：h : JointlyFaithful F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.JointlyReflectMonomorphisms.mono`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [ins
t_1 : (i : I) → CategoryTheory.Catego…
· 使用引理 `CategoryTheory.JointlyFaithful.jointlyReflectMonomorphisms`：jointlyRefle
ctMonomorphisms (h : JointlyFaithful F) : JointlyReflectMonomorphisms F where mo
no {X Y} f _
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.JointlyReflectEpimorphisms.epi`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [inst_
1 : (i : I) → CategoryTheory.Catego…
· 使用引理 `CategoryTheory.JointlyFaithful.jointlyReflectEpimorphisms`：jointlyReflec
tEpimorphisms (h : JointlyFaithful F) : JointlyReflectEpimorphisms F where epi {
X Y} f _
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Balanced.isIso_of_mono_of_epi`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Balanced C] {X Y : C} (f :
 X ⟶ Y)   [CategoryTheory.Mono f] …
-/
lemma jointlyReflectsIsomorphisms [Balanced C] (h : JointlyFaithful F) :
    JointlyReflectIsomorphisms F where
  isIso f _ :=
    have := h.jointlyReflectMonomorphisms.mono f
    have := h.jointlyReflectEpimorphisms.epi f
    Balanced.isIso_of_mono_of_epi f

end JointlyFaithful

end CategoryTheory

