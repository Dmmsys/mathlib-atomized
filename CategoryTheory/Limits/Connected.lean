/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We show that constant functors from a connected category have a limit
and a colimit. From this we deduce that a cocone `c` over a connected diagram
is a colimit cocone if and only if `colimMap c.ι` is an isomorphism (where
`c.ι : F ⟶ const c.pt` is the natural transformation that defines the
cocone).

We give examples of connected categories, and prove
that the functor given by `(X × -)` preserves any connected limit.
That is, any limit of shape `J` where `J` is a connected category is
preserved by the functor `(X × -)`.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Const

namespace Limits

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C] (X : C)

section

variable (J)

/-- The obvious cone of a constant functor. -/
@[simps]
/-
**CategoryTheory.Limits.constCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：constCone : Cone ((Functor.const J).obj X) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious cone of a constant functor.
-/
def constCone : Cone ((Functor.const J).obj X) where
  pt := X
  π := 𝟙 _

/-- The obvious cocone of a constant functor. -/
@[simps]
/-
**CategoryTheory.Limits.constCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：constCocone : Cocone ((Functor.const J).obj X) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious cocone of a constant functor.
-/
def constCocone : Cocone ((Functor.const J).obj X) where
  pt := X
  ι := 𝟙 _

variable [IsConnected J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When `J` is a connected category, the limit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`. -/
/-
**CategoryTheory.Limits.isLimitConstCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isLimitConstCone : IsLimit (constCone J X) where lift s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J

--- 原说明 ---
When `J` is a connected category, the limit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`.
-/
def isLimitConstCone : IsLimit (constCone J X) where
  lift s := s.π.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [comp_id]
    exact constant_of_preserves_morphisms _
      (fun _ _ f ↦ by simpa using s.w f) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When `J` is a connected category, the colimit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`. -/
/-
**CategoryTheory.Limits.isColimitConstCocone** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isColimitConstCocone : IsColimit (constCocone J X) where desc s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J

--- 原说明 ---
When `J` is a connected category, the colimit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`.
-/
def isColimitConstCocone : IsColimit (constCocone J X) where
  desc s := s.ι.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [id_comp]
    exact constant_of_preserves_morphisms _
      (fun _ _ f ↦ by simpa using (s.w f).symm) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)
/-
**CategoryTheory.Limits.hasLimit_const_of_isConnected** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_const_of_isConnected : HasLimit ((Functor.const J).obj X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimit_const_of_isConnected : HasLimit ((Functor.const J).obj X) :=
  ⟨_, isLimitConstCone J X⟩
/-
**CategoryTheory.Limits.hasColimit_const_of_isConnected** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_const_of_isConnected : HasColimit ((Functor.const J).obj X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasColimit_const_of_isConnected : HasColimit ((Functor.const J).obj X) :=
  ⟨_, isColimitConstCocone J X⟩

end

section

variable [IsConnected J]

set_option backward.isDefEq.respectTransparency false in
/-- If `J` is connected, `F : J ⥤ C` and `c` is a cone on `F`, then to check that `c` is a
limit it is sufficient to check that `limMap c.π` is an isomorphism. The converse is also
true, see `Cone.isLimit_iff_isIso_limMap_π`. -/
/-
**CategoryTheory.Limits.Cone.isLimitOfIsIsoLimMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is connected, `F : J ⥤ C` and `c` is a cone on `F`, then to check that `c
` is a
limit it is sufficient to check that `limMap c.π` is an isomorphism. The convers
e is also
true, see `Cone.isLimit_iff_isIso_limMap_π`.
-/
def Cone.isLimitOfIsIsoLimMapπ {F : J ⥤ C} [HasLimit F] (c : Cone F)
    [IsIso (limMap c.π)] : IsLimit c := by
  refine IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ((asIso (limMap c.π)).symm ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt)) ?_)
  intro j
  simp only [limit.cone_x, limit.cone_π, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, assoc, IsIso.eq_inv_comp, limMap_π]
  congr 1
  simp [← Iso.inv_comp_eq_id]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.IsLimit.isIso_limMap_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLimit.isIso_limMap_π {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c) :
    IsIso (limMap c.π) := by
  suffices limMap c.π = ((limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt) ≪≫
      hc.conePointUniqueUpToIso (limit.isLimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [limMap_π, limit.cone_x, Iso.trans_hom, assoc,
    limit.conePointUniqueUpToIso_hom_comp]
  congr 1
  simp [← Iso.inv_comp_eq_id]
/-
**CategoryTheory.Limits.Cone.isLimit_iff_isIso_limMap_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cone.isLimit_iff_isIso_limMap_π {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    Nonempty (IsLimit c) ↔ IsIso (limMap c.π) :=
  ⟨fun ⟨h⟩ => IsLimit.isIso_limMap_π h, fun _ => ⟨c.isLimitOfIsIsoLimMapπ⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `J` is connected, `F : J ⥤ C` and `C` is a cocone on `F`, then to check that `c` is a
colimit it is sufficient to check that `colimMap c.ι` is an isomorphism. The converse is also
true, see `Cocone.isColimit_iff_isIso_colimMap_ι`. -/
/-
**CategoryTheory.Limits.Cocone.isColimitOfIsIsoColimMap** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is connected, `F : J ⥤ C` and `C` is a cocone on `F`, then to check that 
`c` is a
colimit it is sufficient to check that `colimMap c.ι` is an isomorphism. The con
verse is also
true, see `Cocone.isColimit_iff_isIso_colimMap_ι`.
-/
def Cocone.isColimitOfIsIsoColimMapι {F : J ⥤ C} [HasColimit F] (c : Cocone F)
    [IsIso (colimMap c.ι)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (asIso (colimMap c.ι) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J c.pt)) (by simp))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.IsColimit.isIso_colimMap_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsColimit.isIso_colimMap_ι {F : J ⥤ C} [HasColimit F] {c : Cocone F} (hc : IsColimit c) :
    IsIso (colimMap c.ι) := by
  suffices colimMap c.ι = ((colimit.isColimit _).coconePointUniqueUpToIso hc ≪≫
      (isColimitConstCocone J c.pt).coconePointUniqueUpToIso (colimit.isColimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [ι_colimMap, colimit.cocone_x, Iso.trans_hom,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  congr 1
  simp [← Iso.comp_inv_eq_id]
/-
**CategoryTheory.Limits.Cocone.isColimit_iff_isIso_colimMap_** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cocone.isColimit_iff_isIso_colimMap_ι {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    Nonempty (IsColimit c) ↔ IsIso (colimMap c.ι) :=
  ⟨fun ⟨h⟩ => IsColimit.isIso_colimMap_ι h, fun _ => ⟨c.isColimitOfIsIsoColimMapι⟩⟩

end

end Limits

end Const

section Examples

/-
**CategoryTheory.widePullbackShape_connected** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory`。
形式化陈述：widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape
 J)
参数：J : Type v₁。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.of_induct`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {j₀ : J},   (∀ (p : Set J), j₀ ∈ p → (∀ {j₁ j₂ : J} (x
 : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [t (WidePullbackShape.Hom.term _)]
/-
**CategoryTheory.widePushoutShape_connected** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory`。
形式化陈述：widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J
)
参数：J : Type v₁。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.of_induct`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {j₀ : J},   (∀ (p : Set J), j₀ ∈ p → (∀ {j₁ j₂ : J} (x
 : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [← t (WidePushoutShape.Hom.init _)]
/-
**CategoryTheory.parallelPairInhabited** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：parallelPairInhabited : Inhabited WalkingParallelPair
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩
/-
**CategoryTheory.parallel_pair_connected** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：parallel_pair_connected : IsConnected WalkingParallelPair
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.of_induct`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {j₀ : J},   (∀ (p : Set J), j₀ ∈ p → (∀ {j₁ j₂ : J} (x
 : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance parallel_pair_connected : IsConnected WalkingParallelPair := by
  apply IsConnected.of_induct
  · introv _ t
    cases j
    · rwa [t WalkingParallelPairHom.left]
    · assumption

end Examples

variable {C : Type u₂} [Category.{v₂} C]
variable [HasBinaryProducts C]
variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

set_option backward.defeqAttrib.useBackward true in
/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
/-
**CategoryTheory.ProdPreservesConnectedLimits.** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ProdPreservesConnectedLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl). The obvious natural transformation from (X × K -) to K.
-/
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app _ := Limits.prod.snd

set_option backward.defeqAttrib.useBackward true in
/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
/-
**CategoryTheory.ProdPreservesConnectedLimits.** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ProdPreservesConnectedLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl). The obvious natural transformation from (X × K -) to X
-/
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X where
  app _ := Limits.prod.fst

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
/-
**CategoryTheory.ProdPreservesConnectedLimits.forgetCone** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ProdPreservesConnectedLimits`。
形式化陈述：forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone 
K where pt
参数：s : Cone (K ⋙ prod.functor.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformatio
n `γ₂`
-/
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K where
  pt := s.pt
  π := s.π ≫ γ₂ X

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

set_option backward.isDefEq.respectTransparency false in
/-- The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, e.g. `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic
to `X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
/-
**CategoryTheory.prod_preservesConnectedLimits** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：prod_preservesConnectedLimits [IsConnected J] (X : C) : PreservesLimitsOfS
hape J (prod.functor.obj X) where preservesLimit {K}
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.nat_trans_from_is_connected`：nat_trans_from_is_connected 
[IsPreconnected J] {X Y : C} (α : (Functor.const J).obj X ⟶ (Functor.const J).ob
j Y) : forall j j' : J, α.app j …
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.functor_obj_map`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryProducts C
] (X : C)   {x x_1 : C} (g : x ⟶…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.ProdPreservesConnectedLimits.forgetCone_π`：∀ {C : Type u₂
} [inst : CategoryTheory.Category.{v₂, u₂} C] [inst_1 : CategoryTheory.Limits.Ha
sBinaryProducts C]   {J : Type v₂} [inst_2 : C…
· 使用定理 `CategoryTheory.ProdPreservesConnectedLimits.γ₂_app`：∀ {C : Type u₂} [ins
t : CategoryTheory.Category.{v₂, u₂} C] [inst_1 : CategoryTheory.Limits.HasBinar
yProducts C]   {J : Type v₂} [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…

--- 原说明 ---
The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limit
s - that is,
`(X × -)` does not preserve products or terminal object, e.g. `(X ⨯ A) ⨯ (X ⨯ B)
` is not isomorphic
to `X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
lemma prod_preservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J (prod.functor.obj X) where
  preservesLimit {K} :=
    { preserves := fun {c} l => ⟨{
          lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply Limits.prod.hom_ext
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp
          uniq := fun s m L => by
            apply Limits.prod.hom_ext
            · simp [← L]
            · rw [limit.lift_π]
              apply l.uniq (forgetCone s)
              intro j
              simp [← L j] }⟩ }

end CategoryTheory

