/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

## TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

@[expose] public section


open CategoryTheory

open Opposite

namespace CategoryTheory.Limits

universe w v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]

-- We hide the "implementation details" inside a namespace
namespace HasLimitOfHasProductsOfHasEqualizers

variable {F : J ⥤ C} {c₁ : Fan F.obj} {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2}
  (s t : c₁.pt ⟶ c₂.pt)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
/-
**CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers`。
形式化陈述：buildLimit (hs : forall f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.
π.app ⟨f.1.1⟩ ≫ F.map f.2) (ht : forall f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app
 ⟨f⟩ = c₁.π.app ⟨f.1.2⟩) (i : Fork s t) : Cone F where pt
参数：hs : forall f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫
 F.map f.2；ht : forall f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨
f.1.2⟩；i : Fork s t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Given the appropriate product and equalizer cones, build the co
ne for `F` which is
limiting if the given cones are also.
-/
def buildLimit
    (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
    (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
    (i : Fork s t) : Cone F where
  pt := i.pt
  π :=
    { app := fun _ => i.ι ≫ c₁.π.app ⟨_⟩
      naturality := fun j₁ j₂ f => by
        dsimp
        rw [Category.id_comp, Category.assoc, ← hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] }

variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
  {i : Fork s t}

set_option backward.isDefEq.respectTransparency false in
/--
(Implementation) Show the cone constructed in `buildLimit` is limiting, provided the cones used in
its construction are.
-/
/-
**CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildIsLimit** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers`
。
形式化陈述：buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) : IsLimi
t (buildLimit s t hs ht i) where lift q
参数：t₁ : IsLimit c₁；t₂ : IsLimit c₂；hi : IsLimit i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Show the cone constructed in `buildLimit` is limiting, provided
 the cones used in
its construction are.
-/
def buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i) where
  lift q := by
    refine hi.lift (Fork.ofι ?_ ?_)
    · refine t₁.lift (Fan.mk _ fun j => ?_)
      apply q.π.app j
    · apply t₂.hom_ext
      intro ⟨j⟩
      simp [hs, ht]
  uniq q m w := hi.hom_ext (i.equalizer_ext (t₁.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

end HasLimitOfHasProductsOfHasEqualizers

open HasLimitOfHasProductsOfHasEqualizers

set_option backward.isDefEq.respectTransparency false in
/-- Given the existence of the appropriate (possibly finite) products and equalizers,
we can construct a limit cone for `F`.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
/-
**CategoryTheory.Limits.limitConeOfEqualizerAndProduct** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：limitConeOfEqualizerAndProduct (F : J ⥤ C) [HasLimit (Discrete.functor F.o
bj)] [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)]
 [HasEqualizers C] : LimitCone F where cone
参数：F : J ⥤ C；Discrete.functor F.obj；Discrete.functor fun f : Σ p : J × J, p.1 ⟶ 
p.2 => F.obj f.1.2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the existence of the appropriate (possibly finite) products and equalizers
,
we can construct a limit cone for `F`.
(This assumes the existence of all equalizers, which is technically stronger tha
n needed.)
-/
noncomputable def limitConeOfEqualizerAndProduct (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    LimitCone F where
  cone := _
  isLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
/-
**CategoryTheory.Limits.hasLimit_of_equalizer_and_product** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimit_of_equalizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor 
F.obj)] [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.
2)] [HasEqualizers C] : HasLimit F
参数：F : J ⥤ C；Discrete.functor F.obj；Discrete.functor fun f : Σ p : J × J, p.1 ⟶ 
p.2 => F.obj f.1.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
Given the existence of the appropriate (possibly finite) products and equalizers
, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger tha
n needed.)
-/
theorem hasLimit_of_equalizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    HasLimit F :=
  HasLimit.mk (limitConeOfEqualizerAndProduct F)

/-- A limit can be realised as a subobject of a product. -/
/-
**CategoryTheory.Limits.limitSubobjectProduct** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：limitSubobjectProduct [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) : limit F ⟶ ∏
ᶜ fun j => F.obj j
参数：F : J ⥤ C。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize`：hasFiniteLimit
s_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] : HasFiniteLimits C where out
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…

--- 原说明 ---
A limit can be realised as a subobject of a product.
-/
noncomputable def limitSubobjectProduct [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    limit F ⟶ ∏ᶜ fun j => F.obj j :=
  have := hasFiniteLimits_of_hasLimitsOfSize C
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.limitSubobjectProduct_mono** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：limitSubobjectProduct_mono [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) : Mono (
limitSubobjectProduct F)
参数：F : J ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasProducts`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasProducts C] 
(J : Type w),   CategoryTheory.Limits.HasProd…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用引理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize`：hasFiniteLimit
s_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] : HasFiniteLimits C where out
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
-/
instance limitSubobjectProduct_mono [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Mono (limitSubobjectProduct F) :=
  mono_comp _ _

/-- Any category with products and equalizers has all limits. -/
@[stacks 002N]
/-
**CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_limits_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizer
s C] : HasLimitsOfSize.{w, w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_equalizer_and_product`：hasLimit_of_equ
alizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)] [HasLimit (Di
screte.functor fun f : Σ p : J × J, p.1 ⟶ p.2…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Any category with products and equalizers has all limits.
-/
theorem has_limits_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] :
    HasLimitsOfSize.{w, w} C :=
  { has_limits_of_shape :=
    fun _ _ => { has_limit := fun F => hasLimit_of_equalizer_and_product F } }

/-- Any category with finite products and equalizers has all finite limits. -/
@[stacks 002O]
/-
**CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C]
 [HasEqualizers C] : HasFiniteLimits C where out _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_equalizer_and_product`：hasLimit_of_equ
alizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)] [HasLimit (Di
screte.functor fun f : Σ p : J × J, p.1 ⟶ p.2…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Any category with finite products and equalizers has all finite limits.
-/
theorem hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C]
    [HasEqualizers C] : HasFiniteLimits C where
  out _ := { has_limit := fun F => hasLimit_of_equalizer_and_product F }

variable {D : Type u₂} [Category.{v₂} D]

section

variable [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C]
  [HasEqualizers C]

variable (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
  -- [PreservesFiniteProducts G]
  [PreservesLimitsOfShape (Discrete.{w} J) G]
  [PreservesLimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimit_of_preservesEqualizers_and_product** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimit_of_preservesEqualizers_and_product : PreservesLimitsOfShape
 J G where preservesLimit {K}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
If a functor preserves equalizers and the appropriate products, it preserves lim
its.
-/
lemma preservesLimit_of_preservesEqualizers_and_product :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := by
    let P := ∏ᶜ K.obj
    let Q := ∏ᶜ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    let s : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    let t : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨f.1.2⟩
    let I := equalizer s t
    let i : I ⟶ P := equalizer.ι s t
    apply preservesLimit_of_preserves_limit_cone
        (buildIsLimit s t (by simp [P, s]) (by simp [P, t]) (limit.isLimit _)
          (limit.isLimit _) (limit.isLimit _))
    apply IsLimit.ofIsoLimit (buildIsLimit _ _ _ _ _ _ _) _
    · exact Fan.mk _ fun j => G.map (Pi.π _ j)
    · exact Fan.mk (G.obj Q) fun f => G.map (Pi.π _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp [P, Q, s, Fan.mk]
      simp only [← G.map_comp, limit.lift_π]
      congr
    · intro f
      dsimp [P, Q, t, Fan.mk]
      simp only [← G.map_comp, limit.lift_π]
      dsimp
    · apply Fork.ofι (G.map i)
      rw [← G.map_comp, ← G.map_comp]
      apply congrArg G.map
      exact equalizer.condition s t
    · apply isLimitOfHasProductOfPreservesLimit
    · apply isLimitOfHasProductOfPreservesLimit
    · apply isLimitForkMapOfIsLimit
      apply equalizerIsEqualizer
    · refine Cone.ext (Iso.refl _) ?_
      intro j; dsimp [P, Q, I, i]; simp

end

/-- If G preserves equalizers and finite products, it preserves finite limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_preservesEqualizers_and_finiteP
roducts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [HasEquali
zers C] [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParalle
lPair G] [PreservesFiniteProducts G] : PreservesFiniteLimits G where preservesFi
niteLimits
参数：G : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preservesEqualizers_and_product`
：preservesLimit_of_preservesEqualizers_and_product : PreservesLimitsOfShape J G 
where preservesLimit {K}
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If G preserves equalizers and finite products, it preserves finite limits.
-/
lemma preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [HasEqualizers C]
    [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [PreservesFiniteProducts G] : PreservesFiniteLimits G where
  preservesFiniteLimits := by
    intros
    apply preservesLimit_of_preservesEqualizers_and_product


/-- If G preserves equalizers and products, it preserves all limits. -/
/-
**CategoryTheory.Limits.preservesLimits_of_preservesEqualizers_and_products** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimits_of_preservesEqualizers_and_products [HasEqualizers C] [Has
Products.{w} C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G] [fora
ll J, PreservesLimitsOfShape (Discrete.{w} J) G] : PreservesLimitsOfSize.{w, w} 
G where preservesLimitsOfShape
参数：G : C ⥤ D；Discrete.{w} J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preservesEqualizers_and_product`
：preservesLimit_of_preservesEqualizers_and_product : PreservesLimitsOfShape J G 
where preservesLimit {K}

--- 原说明 ---
If G preserves equalizers and products, it preserves all limits.
-/
lemma preservesLimits_of_preservesEqualizers_and_products [HasEqualizers C]
    [HasProducts.{w} C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesLimitsOfShape (Discrete.{w} J) G] : PreservesLimitsOfSize.{w, w} G where
  preservesLimitsOfShape := preservesLimit_of_preservesEqualizers_and_product G

section

variable [HasLimitsOfShape (Discrete J) D] [HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) D]
  [HasEqualizers D]

variable (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesLimitsOfShape WalkingParallelPair G]
  [CreatesLimitsOfShape (Discrete.{w} J) G]
  [CreatesLimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

attribute [local instance] preservesLimit_of_preservesEqualizers_and_product in
/-- If a functor creates equalizers and the appropriate products, it creates limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeOfCreatesEqualizersAndProducts** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeOfCreatesEqualizersAndProducts : CreatesLimitsOfShape 
J G where CreatesLimit {K}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
`：hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimi
tsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J…

--- 原说明 ---
If a functor creates equalizers and the appropriate products, it creates limits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating limits" in the literature, and whether or not the condition can be dro
pped seems to depend
on the specific definition that is used.
-/
noncomputable def createsLimitsOfShapeOfCreatesEqualizersAndProducts :
    CreatesLimitsOfShape J G where
  CreatesLimit {K} :=
    have : HasLimitsOfShape (Discrete J) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasEqualizers C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimit K := hasLimit_of_equalizer_and_product K
    createsLimitOfReflectsIsomorphismsOfPreserves

end

/-- If a functor creates equalizers and finite products, it creates finite limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts [HasEqualizers D] 
[HasFiniteProducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesLimitsOfShape
 WalkingParallelPair G] [CreatesFiniteProducts G] : CreatesFiniteLimits G where 
createsFiniteLimits _ _ _
参数：G : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor creates equalizers and finite products, it creates finite limits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating limits" in the literature, and whether or not the condition can be dro
pped seems to depend
on the specific definition that is used.
-/
noncomputable def createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts [HasEqualizers D]
    [HasFiniteProducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape WalkingParallelPair G]
    [CreatesFiniteProducts G] : CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ := createsLimitsOfShapeOfCreatesEqualizersAndProducts G

/-- If a functor creates equalizers and products, it creates limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeOfCreatesEqualizersAndProducts** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsLimitsOfSizeOfCreatesEqualizersAndProducts [HasEqualizers D] [HasPr
oducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesLimitsOfShape Walking
ParallelPair G] [forall J, CreatesLimitsOfShape (Discrete.{w} J) G] : CreatesLim
itsOfSize.{w, w} G where CreatesLimitsOfShape
参数：G : C ⥤ D；Discrete.{w} J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor creates equalizers and products, it creates limits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating limits" in the literature, and whether or not the condition can be dro
pped seems to depend
on the specific definition that is used.
-/
noncomputable def createsLimitsOfSizeOfCreatesEqualizersAndProducts [HasEqualizers D]
    [HasProducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape WalkingParallelPair G] [∀ J, CreatesLimitsOfShape (Discrete.{w} J) G] :
    CreatesLimitsOfSize.{w, w} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfCreatesEqualizersAndProducts G
/-
**CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks
 C] : HasFiniteLimits C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_produc
ts`：hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C] [
HasEqualizers C] : HasFiniteLimits C where out _
· 使用定理 `CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal`：hasFinitePr
oducts_of_has_binary_and_terminal : HasFiniteProducts C
· 使用定理 `hasBinaryProducts_of_hasTerminal_and_pullbacks`：hasBinaryProducts_of_has
Terminal_and_pullbacks [HasTerminal C] [HasPullbacks C] : HasBinaryProducts C
· 使用定理 `CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`
：hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPul
lbacks C] : HasEqualizers C
-/
theorem hasFiniteLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits C :=
  @hasFiniteLimits_of_hasEqualizers_and_finite_products C _
    (@hasFiniteProducts_of_has_binary_and_terminal C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)

/-- If G preserves terminal objects and pullbacks, it preserves all finite limits. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_preservesTerminal_and_pullbacks
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_preservesTerminal_and_pullbacks [HasTerminal C] [
HasPullbacks C] (G : C ⥤ D) [PreservesLimitsOfShape (Discrete.{0} PEmpty) G] [Pr
eservesLimitsOfShape WalkingCospan G] : PreservesFiniteLimits G
参数：G : C ⥤ D；Discrete.{0} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`：hasF
initeLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] : HasF
initeLimits C
· 使用引理 `preservesBinaryProducts_of_preservesTerminal_and_pullbacks`：preservesBin
aryProducts_of_preservesTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] 
[PreservesLimitsOfShape (Discrete.{0} PEmpty) F]…
· 使用引理 `CategoryTheory.Limits.preservesEqualizers_of_preservesPullbacks_and_bina
ryProducts`：preservesEqualizers_of_preservesPullbacks_and_binaryProducts [HasBin
aryProducts C] [HasPullbacks C] [PreservesLimitsOfShape (Discrete Walkin…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_te
rminal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [
inst_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesEqualizers_and_f
initeProducts`：preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [
HasEqualizers C] [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape …
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…

--- 原说明 ---
If G preserves terminal objects and pullbacks, it preserves all finite limits.
-/
lemma preservesFiniteLimits_of_preservesTerminal_and_pullbacks [HasTerminal C]
    [HasPullbacks C] (G : C ⥤ D) [PreservesLimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesLimitsOfShape WalkingCospan G] : PreservesFiniteLimits G := by
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks G
  have : PreservesLimitsOfShape WalkingParallelPair G :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts G
  have : PreservesFiniteProducts G := .of_preserves_binary_and_terminal _
  exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts G

attribute [local instance] preservesFiniteLimits_of_preservesTerminal_and_pullbacks in
/-- If a functor creates terminal objects and pullbacks, it creates finite limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfCreatesTerminalAndPullbacks** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfCreatesTerminalAndPullbacks [HasTerminal D] [HasPullb
acks D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesLimitsOfShape (Discrete.{0}
 PEmpty) G] [CreatesLimitsOfShape WalkingCospan G] : CreatesFiniteLimits G where
 createsFiniteLimits _ _ _
参数：G : C ⥤ D；Discrete.{0} PEmpty。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`：hasF
initeLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] : HasF
initeLimits C

--- 原说明 ---
If a functor creates terminal objects and pullbacks, it creates finite limits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating limits" in the literature, and whether or not the condition can be dro
pped seems to depend
on the specific definition that is used.
-/
noncomputable def createsFiniteLimitsOfCreatesTerminalAndPullbacks [HasTerminal D]
    [HasPullbacks D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape (Discrete.{0} PEmpty) G] [CreatesLimitsOfShape WalkingCospan G] :
    CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ :=
    { CreatesLimit :=
        have : HasTerminal C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasPullbacks C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
        createsLimitOfReflectsIsomorphismsOfPreserves }

/-!
We now dualize the above constructions, resorting to copy-paste.
-/


-- We hide the "implementation details" inside a namespace
namespace HasColimitOfHasCoproductsOfHasCoequalizers

variable {F : J ⥤ C} {c₁ : Cofan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1} {c₂ : Cofan F.obj}
  (s t : c₁.pt ⟶ c₂.pt)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
@[simps]
/-
**CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasC
oequalizers`。
形式化陈述：buildColimit (hs : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F
.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩) (ht : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨
f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩) (i : Cofork s t) : Cocone F where pt
参数：hs : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.a
pp ⟨f.1.2⟩；ht : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨
f.1.1⟩；i : Cofork s t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
def buildColimit
    (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
    (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
    (i : Cofork s t) : Cocone F where
  pt := i.pt
  ι :=
    { app := fun _ => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality := fun j₁ j₂ f => by
        dsimp
        have reassoced (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} {h : _ ⟶ W} :
          c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
            simp only [← Category.assoc, eq_whisker (hs f)]
        rw [Category.comp_id, ← reassoced ⟨⟨_, _⟩, f⟩, i.condition, ← Category.assoc, ht] }

variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
  {i : Cofork s t}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Show the cocone constructed in `buildColimit` is colimiting,
provided the cocones used in its construction are.
-/
/-
**CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimi
t** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.HasColimitOfHasCoproductsOfHa
sCoequalizers`。
形式化陈述：buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) 
: IsColimit (buildColimit s t hs ht i) where desc q
参数：t₁ : IsColimit c₁；t₂ : IsColimit c₂；hi : IsColimit i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Show the cocone constructed in `buildColimit` is colimiting,
provided the cocones used in its construction are.
-/
def buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i) where
  desc q := by
    refine hi.desc (Cofork.ofπ ?_ ?_)
    · refine t₂.desc (Cofan.mk _ fun j => ?_)
      apply q.ι.app j
    · apply t₁.hom_ext
      intro ⟨j⟩
      have reassoced_s (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (hs f)
      have reassoced_t (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ t ≫ h = c₂.ι.app ⟨f.fst.fst⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (ht f)
      simp [reassoced_s, reassoced_t]
  uniq q m w := hi.hom_ext (i.coequalizer_ext (t₂.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

end HasColimitOfHasCoproductsOfHasCoequalizers

open HasColimitOfHasCoproductsOfHasCoequalizers

set_option backward.isDefEq.respectTransparency false in
/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we can construct a colimit cocone for `F`.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
/-
**CategoryTheory.Limits.colimitCoconeOfCoequalizerAndCoproduct** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitCoconeOfCoequalizerAndCoproduct (F : J ⥤ C) [HasColimit (Discrete.f
unctor F.obj)] [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F
.obj f.1.1)] [HasCoequalizers C] : ColimitCocone F where cocone
参数：F : J ⥤ C；Discrete.functor F.obj；Discrete.functor fun f : Σ p : J × J, p.1 ⟶ 
p.2 => F.obj f.1.1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the existence of the appropriate (possibly finite) coproducts and coequali
zers,
we can construct a colimit cocone for `F`.
(This assumes the existence of all coequalizers, which is technically stronger t
han needed.)
-/
noncomputable def colimitCoconeOfCoequalizerAndCoproduct (F : J ⥤ C)
    [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : ColimitCocone F where
  cocone := _
  isColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we know a colimit of `F` exists.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
/-
**CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.
functor F.obj)] [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => 
F.obj f.1.1)] [HasCoequalizers C] : HasColimit F
参数：F : J ⥤ C；Discrete.functor F.obj；Discrete.functor fun f : Σ p : J × J, p.1 ⟶ 
p.2 => F.obj f.1.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
Given the existence of the appropriate (possibly finite) coproducts and coequali
zers,
we know a colimit of `F` exists.
(This assumes the existence of all coequalizers, which is technically stronger t
han needed.)
-/
theorem hasColimit_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : HasColimit F :=
  HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)

/-- A colimit can be realised as a quotient of a coproduct. -/
/-
**CategoryTheory.Limits.colimitQuotientCoproduct** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：colimitQuotientCoproduct [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) : ∐ (fun
 j => F.obj j) ⟶ colimit F
参数：F : J ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize`：hasFiniteC
olimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] : HasFiniteColimits 
C where out
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…

--- 原说明 ---
A colimit can be realised as a quotient of a coproduct.
-/
noncomputable def colimitQuotientCoproduct [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    ∐ (fun j => F.obj j) ⟶ colimit F :=
  have := hasFiniteColimits_of_hasColimitsOfSize C
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.colimitQuotientCoproduct_epi** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：colimitQuotientCoproduct_epi [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) : Ep
i (colimitQuotientCoproduct F)
参数：F : J ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasCoproducts`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproduc
ts C] (J : Type w),   CategoryTheory.Limits.HasCo…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize`：hasFiniteC
olimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] : HasFiniteColimits 
C where out
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance colimitQuotientCoproduct_epi [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Epi (colimitQuotientCoproduct F) :=
  epi_comp _ _

/-- Any category with coproducts and coequalizers has all colimits. -/
@[stacks 002P]
/-
**CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasC
oequalizers C] : HasColimitsOfSize.{w, w} C where has_colimits_of_shape
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct`：hasColimi
t_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
 [HasColimit (Discrete.functor fun f : Σ p : J × J,…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Any category with coproducts and coequalizers has all colimits.
-/
theorem has_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasCoequalizers C] :
    HasColimitsOfSize.{w, w} C where
  has_colimits_of_shape := fun _ _ =>
      { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

/-- Any category with finite coproducts and coequalizers has all finite colimits. -/
@[stacks 002Q]
/-
**CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproduc
ts** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteCopro
ducts C] [HasCoequalizers C] : HasFiniteColimits C where out _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct`：hasColimi
t_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
 [HasColimit (Discrete.functor fun f : Σ p : J × J,…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Any category with finite coproducts and coequalizers has all finite colimits.
-/
theorem hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteCoproducts C]
    [HasCoequalizers C] : HasFiniteColimits C where
  out _ := { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

section

variable [HasColimitsOfShape (Discrete.{w} J) C]
  [HasColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) C] [HasCoequalizers C]

variable (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape (Discrete.{w} J) G]
  [PreservesColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a functor preserves coequalizers and the appropriate coproducts, it preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimit_of_preservesCoequalizers_and_coproduct*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_of_preservesCoequalizers_and_coproduct : PreservesColimit
sOfShape J G where preservesColimit {K}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
If a functor preserves coequalizers and the appropriate coproducts, it preserves
 colimits.
-/
lemma preservesColimit_of_preservesCoequalizers_and_coproduct :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := by
    let P := ∐ K.obj
    let Q := ∐ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    let s : Q ⟶ P := Sigma.desc fun f => K.map f.2 ≫ colimit.ι (Discrete.functor K.obj) ⟨_⟩
    let t : Q ⟶ P := Sigma.desc fun f => colimit.ι (Discrete.functor K.obj) ⟨f.1.1⟩
    let I := coequalizer s t
    let i : P ⟶ I := coequalizer.π s t
    apply preservesColimit_of_preserves_colimit_cocone
        (buildIsColimit s t (by simp [P, s]) (by simp [P, t]) (colimit.isColimit _)
          (colimit.isColimit _) (colimit.isColimit _))
    apply IsColimit.ofIsoColimit (buildIsColimit _ _ _ _ _ _ _) _
    · refine Cofan.mk (G.obj Q) fun j => G.map ?_
      apply Sigma.ι _ j
    -- fun j => G.map (Sigma.ι _ j)
    · exact Cofan.mk _ fun f => G.map (Sigma.ι _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp [P, Q, s, Cofan.mk]
      simp only [← G.map_comp, colimit.ι_desc]
      congr
    · intro f
      dsimp [P, Q, t, Cofan.mk]
      simp only [← G.map_comp, colimit.ι_desc]
      dsimp
    · refine Cofork.ofπ (G.map i) ?_
      rw [← G.map_comp, ← G.map_comp]
      apply congrArg G.map
      apply coequalizer.condition
    · apply isColimitOfHasCoproductOfPreservesColimit
    · apply isColimitOfHasCoproductOfPreservesColimit
    · apply isColimitCoforkMapOfIsColimit
      apply coequalizerIsCoequalizer
    refine Cocone.ext (Iso.refl _) ?_
    dsimp [i]
    simp

end

/-- If G preserves coequalizers and finite coproducts, it preserves finite colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_preservesCoequalizers_and_fin
iteCoproducts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts [Has
Coequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D) [PreservesColimitsOfShape Wa
lkingParallelPair G] [PreservesFiniteCoproducts G] : PreservesFiniteColimits G w
here preservesFiniteColimits
参数：G : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preservesCoequalizers_and_copr
oduct`：preservesColimit_of_preservesCoequalizers_and_coproduct : PreservesColimi
tsOfShape J G where preservesColimit {K}
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…

--- 原说明 ---
If G preserves coequalizers and finite coproducts, it preserves finite colimits.
-/
lemma preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    [HasCoequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D)
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesFiniteCoproducts G] : PreservesFiniteColimits G where
  preservesFiniteColimits := by
    intro J sJ fJ
    apply preservesColimit_of_preservesCoequalizers_and_coproduct

/-- If G preserves coequalizers and coproducts, it preserves all colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_of_preservesCoequalizers_and_coproduct
s** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimits_of_preservesCoequalizers_and_coproducts [HasCoequalizers
 C] [HasCoproducts.{w} C] (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelP
air G] [forall J, PreservesColimitsOfShape (Discrete.{w} J) G] : PreservesColimi
tsOfSize.{w, w} G where preservesColimitsOfShape
参数：G : C ⥤ D；Discrete.{w} J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preservesCoequalizers_and_copr
oduct`：preservesColimit_of_preservesCoequalizers_and_coproduct : PreservesColimi
tsOfShape J G where preservesColimit {K}

--- 原说明 ---
If G preserves coequalizers and coproducts, it preserves all colimits.
-/
lemma preservesColimits_of_preservesCoequalizers_and_coproducts [HasCoequalizers C]
    [HasCoproducts.{w} C] (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesColimitsOfShape (Discrete.{w} J) G] : PreservesColimitsOfSize.{w, w} G where
  preservesColimitsOfShape := preservesColimit_of_preservesCoequalizers_and_coproduct G

section

variable [HasColimitsOfShape (Discrete J) D]
  [HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) D] [HasCoequalizers D]

variable (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesColimitsOfShape WalkingParallelPair G]
  [CreatesColimitsOfShape (Discrete.{w} J) G]
  [CreatesColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

attribute [local instance] preservesColimit_of_preservesCoequalizers_and_coproduct in
/-- If a functor creates coequalizers and the appropriate coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts : CreatesColimits
OfShape J G where CreatesColimit {K}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsO
fShape`：hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤
 D) [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColim…

--- 原说明 ---
If a functor creates coequalizers and the appropriate coproducts, it creates col
imits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating colimits" in the literature, and whether or not the condition can be d
ropped seems to
depend on the specific definition that is used.
-/
noncomputable def createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts :
    CreatesColimitsOfShape J G where
  CreatesColimit {K} :=
    have : HasColimitsOfShape (Discrete J) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasCoequalizers C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimit K := hasColimit_of_coequalizer_and_coproduct K
    createsColimitOfReflectsIsomorphismsOfPreserves

end

/-- If a functor creates coequalizers and finite coproducts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfCreatesCoequalizersAndFiniteCopro
ducts** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts [HasCoequali
zers D] [HasFiniteCoproducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesCol
imitsOfShape WalkingParallelPair G] [CreatesFiniteCoproducts G] : CreatesFiniteC
olimits G where createsFiniteColimits _ _ _
参数：G : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor creates coequalizers and finite coproducts, it creates finite colim
its.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating colimits" in the literature, and whether or not the condition can be d
ropped seems to
depend on the specific definition that is used.
-/
noncomputable def createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts [HasCoequalizers D]
    [HasFiniteCoproducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape WalkingParallelPair G]
    [CreatesFiniteCoproducts G] : CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ := createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

/-- If a functor creates coequalizers and coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts [HasCoequalizers D
] [HasCoproducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesColimitsOfS
hape WalkingParallelPair G] [forall J, CreatesColimitsOfShape (Discrete.{w} J) G
] : CreatesColimitsOfSize.{w, w} G where CreatesColimitsOfShape
参数：G : C ⥤ D；Discrete.{w} J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor creates coequalizers and coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating colimits" in the literature, and whether or not the condition can be d
ropped seems to
depend on the specific definition that is used.
-/
noncomputable def createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts [HasCoequalizers D]
    [HasCoproducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape WalkingParallelPair G]
    [∀ J, CreatesColimitsOfShape (Discrete.{w} J) G] : CreatesColimitsOfSize.{w, w} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G
/-
**CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C
] : HasFiniteColimits C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_co
products`：hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteC
oproducts C] [HasCoequalizers C] : HasFiniteColimits C where out _
· 使用定理 `CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial`：hasFiniteC
oproducts_of_has_binary_and_initial : HasFiniteCoproducts C
· 使用定理 `hasBinaryCoproducts_of_hasInitial_and_pushouts`：hasBinaryCoproducts_of_h
asInitial_and_pushouts [HasInitial C] [HasPushouts C] : HasBinaryCoproducts C
· 使用定理 `CategoryTheory.Limits.hasCoequalizers_of_hasPushouts_and_binary_coproduc
ts`：hasCoequalizers_of_hasPushouts_and_binary_coproducts [HasBinaryCoproducts C]
 [HasPushouts C] : HasCoequalizers C
-/
theorem hasFiniteColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasFiniteColimits C :=
  @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts C _
    (@hasFiniteCoproducts_of_has_binary_and_initial C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)

/-- If G preserves initial objects and pushouts, it preserves all finite colimits. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_preservesInitial_and_pushouts
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_preservesInitial_and_pushouts [HasInitial C] [H
asPushouts C] (G : C ⥤ D) [PreservesColimitsOfShape (Discrete.{0} PEmpty) G] [Pr
eservesColimitsOfShape WalkingSpan G] : PreservesFiniteColimits G
参数：G : C ⥤ D；Discrete.{0} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts`：hasF
initeColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] : HasFin
iteColimits C
· 使用引理 `preservesBinaryCoproducts_of_preservesInitial_and_pushouts`：preservesBin
aryCoproducts_of_preservesInitial_and_pushouts [HasInitial C] [HasPushouts C] [P
reservesColimitsOfShape (Discrete.{0} PEmpty) F]…
· 使用引理 `CategoryTheory.Limits.preservesCoequalizers_of_preservesPushouts_and_bin
aryCoproducts`：preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts [
HasBinaryCoproducts C] [HasPushouts C] [PreservesColimitsOfShape (Discrete …
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_preservesCoequalizers_a
nd_finiteCoproducts`：preservesFiniteColimits_of_preservesCoequalizers_and_finite
Coproducts [HasCoequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D) [PreservesCol
i…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.PreservesFiniteCoproducts.of_preserves_binary_and_initial
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1
 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…

--- 原说明 ---
If G preserves initial objects and pushouts, it preserves all finite colimits.
-/
lemma preservesFiniteColimits_of_preservesInitial_and_pushouts [HasInitial C]
    [HasPushouts C] (G : C ⥤ D) [PreservesColimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesFiniteColimits G := by
  have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  have : PreservesColimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts G
  have : PreservesColimitsOfShape (WalkingParallelPair) G :=
      (preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts G)
  refine
    @preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _ _ _ _ _ _ G _ ?_
  refine ⟨fun _ ↦ ?_⟩
  apply PreservesFiniteCoproducts.of_preserves_binary_and_initial G

attribute [local instance] preservesFiniteColimits_of_preservesInitial_and_pushouts in
/-- If a functor creates initial objects and pushouts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfCreatesInitialAndPushouts** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfCreatesInitialAndPushouts [HasInitial D] [HasPushou
ts D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesColimitsOfShape (Discrete.{0}
 PEmpty) G] [CreatesColimitsOfShape WalkingSpan G] : CreatesFiniteColimits G whe
re createsFiniteColimits _ _ _
参数：G : C ⥤ D；Discrete.{0} PEmpty。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts`：hasF
initeColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] : HasFin
iteColimits C

--- 原说明 ---
If a functor creates initial objects and pushouts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects is
omorphisms. It is
unclear whether the statement remains true without this condition. There are var
ious definitions of
"creating colimits" in the literature, and whether or not the condition can be d
ropped seems to
depend on the specific definition that is used.
-/
noncomputable def createsFiniteColimitsOfCreatesInitialAndPushouts [HasInitial D]
    [HasPushouts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape (Discrete.{0} PEmpty) G] [CreatesColimitsOfShape WalkingSpan G] :
    CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ :=
    { CreatesColimit :=
        have : HasInitial C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasPushouts C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
        createsColimitOfReflectsIsomorphismsOfPreserves }

end CategoryTheory.Limits

