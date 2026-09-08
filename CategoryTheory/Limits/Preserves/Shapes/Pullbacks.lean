/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullbackComparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (G : C ⥤ D)

/-- The image of a pullback cone by a functor. -/
/-
**CategoryTheory.Limits.PullbackCone.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits.PullbackCone`。
形式化陈述：map : PullbackCone (G.map f) (G.map g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a pullback cone by a functor.
-/
abbrev map : PullbackCone (G.map f) (G.map g) :=
  PullbackCone.mk (G.map c.fst) (G.map c.snd)
    (by simpa using G.congr_map c.condition)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map (as a cone) of a pullback cone is limit iff
the map (as a pullback cone) is limit. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitMapConeEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitMapConeEquiv : IsLimit (mapCone G c) ≃ IsLimit (c.map G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map (as a cone) of a pullback cone is limit iff
the map (as a pullback cone) is limit.
-/
def isLimitMapConeEquiv :
    IsLimit (mapCone G c) ≃ IsLimit (c.map G) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans <|
    IsLimit.equivIsoLimit <| by
      refine PullbackCone.ext (Iso.refl _) ?_ ?_
      · dsimp only [fst]
        simp
      · dsimp only [snd]
        simp

end PullbackCone

variable (G : C ⥤ D)
variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/-- The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a
limit. This essentially lets us commute `PullbackCone.mk` with `Functor.mapCone`. -/
/-
**CategoryTheory.Limits.isLimitMapConePullbackConeEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：isLimitMapConePullbackConeEquiv : IsLimit (mapCone G (PullbackCone.mk h k 
comm)) ≃ IsLimit (PullbackCone.mk (G.map h) (G.map k) (by simp only [← G.map_com
p, comm]) : PullbackCone (G.map f) (G.map g))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of a pullback cone is a limit iff the fork consisting of the mapped morp
hisms is a
limit. This essentially lets us commute `PullbackCone.mk` with `Functor.mapCone`
.
-/
def isLimitMapConePullbackConeEquiv :
    IsLimit (mapCone G (PullbackCone.mk h k comm)) ≃
      IsLimit
        (PullbackCone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PullbackCone (G.map f) (G.map g)) :=
  (PullbackCone.mk _ _ comm).isLimitMapConeEquiv G

/-- The property of preserving pullbacks expressed in terms of binary fans. -/
/-
**CategoryTheory.Limits.isLimitPullbackConeMapOfIsLimit** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：isLimitPullbackConeMapOfIsLimit [PreservesLimit (cospan f g) G] (l : IsLim
it (PullbackCone.mk h k comm)) : have : G.map h ≫ G.map f = G.map k ≫ G.map g
参数：cospan f g；l : IsLimit (PullbackCone.mk h k comm)。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving pullbacks expressed in terms of binary fans.
-/
def isLimitPullbackConeMapOfIsLimit [PreservesLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk h k comm)) :
    have : G.map h ≫ G.map f = G.map k ≫ G.map g := by rw [← G.map_comp, ← G.map_comp, comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  (PullbackCone.isLimitMapConeEquiv _ G).1 (isLimitOfPreserves G l)

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
/-
**CategoryTheory.Limits.isLimitOfIsLimitPullbackConeMap** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G] (l : IsLimi
t (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G.map f = G.map k ≫ G.map
 g by simp only [← G.map_comp, comm]))) : IsLimit (PullbackCone.mk h k comm)
参数：cospan f g；l : IsLimit (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G
.map f = G.map k ≫ G.map g by simp only [← G.map_comp, comm]))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of reflecting pullbacks expressed in terms of binary fans.
-/
def isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G.map f = G.map k ≫ G.map g
    by simp only [← G.map_comp, comm]))) : IsLimit (PullbackCone.mk h k comm) :=
  isLimitOfReflects G
    ((PullbackCone.isLimitMapConeEquiv (PullbackCone.mk _ _ comm) G).2 l)

variable (f g) [PreservesLimit (cospan f g) G]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
/-
**CategoryTheory.Limits.isLimitOfHasPullbackOfPreservesLimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] : have : G.map (pul
lback.fst f g) ≫ G.map f = G.map (pullback.snd f g) ≫ G.map g
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
If `G` preserves pullbacks and `C` has them, then the pullback cone constructed 
of the mapped
morphisms of the pullback cone is a limit.
-/
def isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] :
    have : G.map (pullback.fst f g) ≫ G.map f = G.map (pullback.snd f g) ≫ G.map g := by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

/-- If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f`. -/
/-
**CategoryTheory.Limits.preservesPullback_symmetry** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesPullback_symmetry : PreservesLimit (cospan g f) G where preserves
 {c} hc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f
`.
-/
lemma preservesPullback_symmetry : PreservesLimit (cospan g f) G where
  preserves {c} hc := ⟨by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @isLimitOfPreserves _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply PullbackCone.isLimitOfFlip
        apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
        exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
      · dsimp
        infer_instance
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl :)⟩
/-
**CategoryTheory.Limits.hasPullback_of_preservesPullback** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasPullback_of_preservesPullback [HasPullback f g] : HasPullback (G.map f)
 (G.map g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem hasPullback_of_preservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g) :=
  ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism. -/
/-
**CategoryTheory.Limits.PreservesPullback.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.PreservesPullback`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           {X Y Z : C} →             (f : X ⟶ Z) →    
           (g : Y ⟶ Z) →                 [CategoryTheory.Limits.PreservesLimit (
CategoryTheory.Limits.cospan f g) G] →                   [inst_3 : CategoryTheor
y.Limits.HasPullback f g] →                     [inst_4 : CategoryTheory.Limits.
HasPullback (G.map f) (G.map g)] →                       G.obj (CategoryTheory.L
imits.pullback f g) ≅ CategoryTheory.Limits.pullback (G.map f) (G.map g)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cosp
an f g；G.map f；G.map g；CategoryTheory.Limits.pullback f g；G.map f；G.map g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `
G` at `(f,g)` is
an isomorphism.
-/
def PreservesPullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesPullback.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.PreservesPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_2 : CategoryTheory.Limits.Preserves
Limit (CategoryTheory.Limits.cospan f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPullback f g] [inst_4 : CategoryTheory.Limits.HasPullback (G.map f) (G.map g)],
   (CategoryTheory.Limits.PreservesPullback.iso G f g).hom = CategoryTheory.Limi
ts.pullbackComparison G f g
参数：G : CategoryTheory.Functor C D；f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cosp
an f g；G.map f；G.map g；CategoryTheory.Limits.PreservesPullback.iso G f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesPullback.iso_hom : (PreservesPullback.iso G f g).hom = pullbackComparison G f g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.PreservesPullback.iso_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PreservesPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_2 : CategoryTheory.Limits.Preserves
Limit (CategoryTheory.Limits.cospan f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPullback f g] [inst_4 : CategoryTheory.Limits.HasPullback (G.map f) (G.map g)],
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.PreservesPullback.i
so G f g).hom       (CategoryTheory.Limits.pullback.fst (G.map f) (G.map g)) =  
   G.map (CategoryTheory.Limits.pullback.fst f g)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cosp
an f g；G.map f；G.map g；CategoryTheory.Limits.PreservesPullback.iso G f g；Categor
yTheory.Limits.pullback.fst (G.map f) (G.map g)；CategoryTheory.Limits.pullback.f
st f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPullback.iso_hom_fst :
    (PreservesPullback.iso G f g).hom ≫ pullback.fst _ _ = G.map (pullback.fst f g) := by
  simp [PreservesPullback.iso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.PreservesPullback.iso_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PreservesPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_2 : CategoryTheory.Limits.Preserves
Limit (CategoryTheory.Limits.cospan f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPullback f g] [inst_4 : CategoryTheory.Limits.HasPullback (G.map f) (G.map g)],
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.PreservesPullback.i
so G f g).hom       (CategoryTheory.Limits.pullback.snd (G.map f) (G.map g)) =  
   G.map (CategoryTheory.Limits.pullback.snd f g)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cosp
an f g；G.map f；G.map g；CategoryTheory.Limits.PreservesPullback.iso G f g；Categor
yTheory.Limits.pullback.snd (G.map f) (G.map g)；CategoryTheory.Limits.pullback.s
nd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPullback.iso_hom_snd :
    (PreservesPullback.iso G f g).hom ≫ pullback.snd _ _ = G.map (pullback.snd f g) := by
  simp [PreservesPullback.iso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PreservesPullback.iso_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PreservesPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_2 : CategoryTheory.Limits.Preserves
Limit (CategoryTheory.Limits.cospan f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPullback f g] [inst_4 : CategoryTheory.Limits.HasPullback (G.map f) (G.map g)],
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.PreservesPullback.i
so G f g).inv       (G.map (CategoryTheory.Limits.pullback.fst f g)) =     Categ
oryTheory.Limits.pullback.fst (G.map f) (G.map g)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cosp
an f g；G.map f；G.map g；CategoryTheory.Limits.PreservesPullback.iso G f g；G.map (
CategoryTheory.Limits.pullback.fst f g)；G.map f；G.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPullback.iso_inv_fst :
    (PreservesPullback.iso G f g).inv ≫ G.map (pullback.fst f g) = pullback.fst _ _ := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PreservesPullback.iso_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PreservesPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_2 : CategoryTheory.Limits.Preserves
Limit (CategoryTheory.Limits.cospan f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPullback f g] [inst_4 : CategoryTheory.Limits.HasPullback (G.map f) (G.map g)],
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.PreservesPullback.i
so G f g).inv       (G.map (CategoryTheory.Limits.pullback.snd f g)) =     Categ
oryTheory.Limits.pullback.snd (G.map f) (G.map g)
参数：G : CategoryTheory.Functor C D；f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cosp
an f g；G.map f；G.map g；CategoryTheory.Limits.PreservesPullback.iso G f g；G.map (
CategoryTheory.Limits.pullback.snd f g)；G.map f；G.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPullback.iso_inv_snd :
    (PreservesPullback.iso G f g).inv ≫ G.map (pullback.snd f g) = pullback.snd _ _ := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

/-- A pullback cone in `C` is a limit iff it is so after the application
of `coyoneda.obj X` for all `X : Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitCoyonedaEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) →           (c : CategoryTheory.
Limits.PullbackCone f g) →             CategoryTheory.Limits.IsLimit c ≃        
       ((X_1 : Cᵒᵖ) → CategoryTheory.Limits.IsLimit (c.map (CategoryTheory.coyon
eda.obj X_1)))
参数：f : X ⟶ Z；g : Y ⟶ Z；c : CategoryTheory.Limits.PullbackCone f g；(X_1 : Cᵒᵖ) → 
CategoryTheory.Limits.IsLimit (c.map (CategoryTheory.coyoneda.obj X_1))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A pullback cone in `C` is a limit iff it is so after the application
of `coyoneda.obj X` for all `X : Cᵒᵖ`.
-/
def PullbackCone.isLimitCoyonedaEquiv (c : PullbackCone f g) :
    IsLimit c ≃ ∀ (X : Cᵒᵖ), IsLimit (c.map (coyoneda.obj X)) :=
  (Cone.isLimitCoyonedaEquiv c).trans
    (Equiv.piCongrRight (fun X ↦ c.isLimitMapConeEquiv (coyoneda.obj X)))

end Pullback

section Pushout

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PushoutCocone

variable {W X Y : C} {f : W ⟶ X} {g : W ⟶ Y} (c : PushoutCocone f g) (G : C ⥤ D)

/-- The image of a pullback cone by a functor. -/
/-
**CategoryTheory.Limits.PushoutCocone.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.PushoutCocone`。
形式化陈述：map : PushoutCocone (G.map f) (G.map g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a pullback cone by a functor.
-/
abbrev map : PushoutCocone (G.map f) (G.map g) :=
  PushoutCocone.mk (G.map c.inl) (G.map c.inr) (by simpa using G.congr_map c.condition)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map (as a cocone) of a pushout cocone is colimit iff
the map (as a pushout cocone) is limit. -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitMapCoconeEquiv** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitMapCoconeEquiv : IsColimit (mapCocone G c) ≃ IsColimit (c.map G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map (as a cocone) of a pushout cocone is colimit iff
the map (as a pushout cocone) is limit.
-/
def isColimitMapCoconeEquiv :
    IsColimit (mapCocone G c) ≃ IsColimit (c.map G) :=
  (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans <|
    IsColimit.equivIsoColimit <| by
      refine PushoutCocone.ext (Iso.refl _) ?_ ?_
      · dsimp only [inl]
        simp
      · dsimp only [inr]
        simp

end PushoutCocone

variable (G : C ⥤ D)
variable {W X Y Z : C} {h : X ⟶ Z} {k : Y ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (comm : f ≫ h = g ≫ k)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map of a pushout cocone is a colimit iff the cofork consisting of the mapped morphisms is a
colimit. This essentially lets us commute `PushoutCocone.mk` with `Functor.mapCocone`. -/
/-
**CategoryTheory.Limits.isColimitMapCoconePushoutCoconeEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitMapCoconePushoutCoconeEquiv : IsColimit (mapCocone G (PushoutCoco
ne.mk h k comm)) ≃ IsColimit (PushoutCocone.mk (G.map h) (G.map k) (by simp only
 [← G.map_comp, comm]) : PushoutCocone (G.map f) (G.map g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a pushout cocone is a colimit iff the cofork consisting of the mapped
 morphisms is a
colimit. This essentially lets us commute `PushoutCocone.mk` with `Functor.mapCo
cone`.
-/
def isColimitMapCoconePushoutCoconeEquiv :
    IsColimit (mapCocone G (PushoutCocone.mk h k comm)) ≃
      IsColimit
        (PushoutCocone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PushoutCocone (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans <|
    IsColimit.equivIsoColimit <|
      Cocone.ext (Iso.refl _) <| by
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [Category.comp_id, Category.id_comp, ← G.map_comp]

/-- The property of preserving pushouts expressed in terms of binary cofans. -/
/-
**CategoryTheory.Limits.isColimitPushoutCoconeMapOfIsColimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitPushoutCoconeMapOfIsColimit [PreservesColimit (span f g) G] (l : 
IsColimit (PushoutCocone.mk h k comm)) : IsColimit (PushoutCocone.mk (G.map h) (
G.map k) (show G.map f ≫ G.map h = G.map g ≫ G.map k by simp only [← G.map_comp,
 comm]))
参数：span f g；l : IsColimit (PushoutCocone.mk h k comm)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving pushouts expressed in terms of binary cofans.
-/
def isColimitPushoutCoconeMapOfIsColimit [PreservesColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk h k comm)) :
    IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h = G.map g ≫ G.map k
      by simp only [← G.map_comp, comm])) :=
  isColimitMapCoconePushoutCoconeEquiv G comm (isColimitOfPreserves G l)

/-- The property of reflecting pushouts expressed in terms of binary cofans. -/
/-
**CategoryTheory.Limits.isColimitOfIsColimitPushoutCoconeMap** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfIsColimitPushoutCoconeMap [ReflectsColimit (span f g) G] (l : I
sColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h = G.map g
 ≫ G.map k by simp only [← G.map_comp, comm]))) : IsColimit (PushoutCocone.mk h 
k comm)
参数：span f g；l : IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ 
G.map h = G.map g ≫ G.map k by simp only [← G.map_comp, comm]))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting pushouts expressed in terms of binary cofans.
-/
def isColimitOfIsColimitPushoutCoconeMap [ReflectsColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h =
      G.map g ≫ G.map k by simp only [← G.map_comp, comm]))) :
    IsColimit (PushoutCocone.mk h k comm) :=
  isColimitOfReflects G ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)

variable (f g) [PreservesColimit (span f g) G]

/-- If `G` preserves pushouts and `C` has them, then the pushout cocone constructed of the mapped
morphisms of the pushout cocone is a colimit. -/
/-
**CategoryTheory.Limits.isColimitOfHasPushoutOfPreservesColimit** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfHasPushoutOfPreservesColimit [i : HasPushout f g] : IsColimit (
PushoutCocone.mk (G.map (pushout.inl _ _)) (G.map (@pushout.inr _ _ _ _ _ f g i)
) (show G.map f ≫ G.map (pushout.inl _ _) = G.map g ≫ G.map (pushout.inr _ _) by
 simp only [← G.map_comp, pushout.condition]))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …

--- 原说明 ---
If `G` preserves pushouts and `C` has them, then the pushout cocone constructed 
of the mapped
morphisms of the pushout cocone is a colimit.
-/
def isColimitOfHasPushoutOfPreservesColimit [i : HasPushout f g] :
    IsColimit (PushoutCocone.mk (G.map (pushout.inl _ _)) (G.map (@pushout.inr _ _ _ _ _ f g i))
    (show G.map f ≫ G.map (pushout.inl _ _) = G.map g ≫ G.map (pushout.inr _ _) by
      simp only [← G.map_comp, pushout.condition])) :=
  isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)

set_option backward.isDefEq.respectTransparency false in
/-- If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`. -/
/-
**CategoryTheory.Limits.preservesPushout_symmetry** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesPushout_symmetry : PreservesColimit (span g f) G where preserves 
{c} hc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`.
-/
lemma preservesPushout_symmetry : PreservesColimit (span g f) G where
  preserves {c} hc := ⟨by
    apply (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply IsColimit.ofIsoColimit _ (PushoutCocone.isoMk _).symm
    apply PushoutCocone.isColimitOfFlip
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
    · -- Need to unfold these to allow the `PreservesColimit` instance to be found.
      dsimp only [span_map_fst, span_map_snd]
      exact isColimitOfPreserves _ (PushoutCocone.flipIsColimit hc)⟩
/-
**CategoryTheory.Limits.hasPushout_of_preservesPushout** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasPushout_of_preservesPushout [HasPushout f g] : HasPushout (G.map f) (G.
map g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
theorem hasPushout_of_preservesPushout [HasPushout f g] : HasPushout (G.map f) (G.map g) :=
  ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G` at `(f,g)` is
an isomorphism. -/
/-
**CategoryTheory.Limits.PreservesPushout.iso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.PreservesPushout`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           {W X Y : C} →             (f : W ⟶ X) →    
           (g : W ⟶ Y) →                 [CategoryTheory.Limits.PreservesColimit
 (CategoryTheory.Limits.span f g) G] →                   [inst_3 : CategoryTheor
y.Limits.HasPushout f g] →                     [inst_4 : CategoryTheory.Limits.H
asPushout (G.map f) (G.map g)] →                       CategoryTheory.Limits.pus
hout (G.map f) (G.map g) ≅ G.obj (CategoryTheory.Limits.pushout f g)
参数：G : CategoryTheory.Functor C D；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.span
 f g；G.map f；G.map g；G.map f；G.map g；CategoryTheory.Limits.pushout f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G`
 at `(f,g)` is
an isomorphism.
-/
def PreservesPushout.iso : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)

@[simp]
/-
**CategoryTheory.Limits.PreservesPushout.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.PreservesPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)   [inst_2 : CategoryTheory.Limits.Preserves
Colimit (CategoryTheory.Limits.span f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPushout f g] [inst_4 : CategoryTheory.Limits.HasPushout (G.map f) (G.map g)],  
 (CategoryTheory.Limits.PreservesPushout.iso G f g).hom = CategoryTheory.Limits.
pushoutComparison G f g
参数：G : CategoryTheory.Functor C D；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.span
 f g；G.map f；G.map g；CategoryTheory.Limits.PreservesPushout.iso G f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesPushout.iso_hom : (PreservesPushout.iso G f g).hom = pushoutComparison G f g :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.PreservesPushout.inl_iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PreservesPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)   [inst_2 : CategoryTheory.Limits.Preserves
Colimit (CategoryTheory.Limits.span f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPushout f g] [inst_4 : CategoryTheory.Limits.HasPushout (G.map f) (G.map g)],  
 CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pushout.inl (G.map f)
 (G.map g))       (CategoryTheory.Limits.PreservesPushout.iso G f g).hom =     G
.map (CategoryTheory.Limits.pushout.inl f g)
参数：G : CategoryTheory.Functor C D；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.span
 f g；G.map f；G.map g；CategoryTheory.Limits.pushout.inl (G.map f) (G.map g)；Categ
oryTheory.Limits.PreservesPushout.iso G f g；CategoryTheory.Limits.pushout.inl f 
g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutComparison`：inl_comp_pushoutCompar
ison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
 pushout.inl _ _ ≫ pushoutComparison G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPushout.inl_iso_hom :
    pushout.inl _ _ ≫ (PreservesPushout.iso G f g).hom = G.map (pushout.inl _ _) := by
  simp

@[reassoc]
/-
**CategoryTheory.Limits.PreservesPushout.inr_iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PreservesPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)   [inst_2 : CategoryTheory.Limits.Preserves
Colimit (CategoryTheory.Limits.span f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPushout f g] [inst_4 : CategoryTheory.Limits.HasPushout (G.map f) (G.map g)],  
 CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pushout.inr (G.map f)
 (G.map g))       (CategoryTheory.Limits.PreservesPushout.iso G f g).hom =     G
.map (CategoryTheory.Limits.pushout.inr f g)
参数：G : CategoryTheory.Functor C D；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.span
 f g；G.map f；G.map g；CategoryTheory.Limits.pushout.inr (G.map f) (G.map g)；Categ
oryTheory.Limits.PreservesPushout.iso G f g；CategoryTheory.Limits.pushout.inr f 
g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutComparison`：inr_comp_pushoutCompar
ison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
 pushout.inr _ _ ≫ pushoutComparison G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPushout.inr_iso_hom :
    pushout.inr _ _ ≫ (PreservesPushout.iso G f g).hom = G.map (pushout.inr _ _) := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PreservesPushout.inl_iso_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PreservesPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)   [inst_2 : CategoryTheory.Limits.Preserves
Colimit (CategoryTheory.Limits.span f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPushout f g] [inst_4 : CategoryTheory.Limits.HasPushout (G.map f) (G.map g)],  
 CategoryTheory.CategoryStruct.comp (G.map (CategoryTheory.Limits.pushout.inl f 
g))       (CategoryTheory.Limits.PreservesPushout.iso G f g).inv =     CategoryT
heory.Limits.pushout.inl (G.map f) (G.map g)
参数：G : CategoryTheory.Functor C D；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.span
 f g；G.map f；G.map g；G.map (CategoryTheory.Limits.pushout.inl f g)；CategoryTheor
y.Limits.PreservesPushout.iso G f g；G.map f；G.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPushout.inl_iso_inv :
    G.map (pushout.inl _ _) ≫ (PreservesPushout.iso G f g).inv = pushout.inl _ _ := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PreservesPushout.inr_iso_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PreservesPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)   [inst_2 : CategoryTheory.Limits.Preserves
Colimit (CategoryTheory.Limits.span f g) G]   [inst_3 : CategoryTheory.Limits.Ha
sPushout f g] [inst_4 : CategoryTheory.Limits.HasPushout (G.map f) (G.map g)],  
 CategoryTheory.CategoryStruct.comp (G.map (CategoryTheory.Limits.pushout.inr f 
g))       (CategoryTheory.Limits.PreservesPushout.iso G f g).inv =     CategoryT
heory.Limits.pushout.inr (G.map f) (G.map g)
参数：G : CategoryTheory.Functor C D；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.span
 f g；G.map f；G.map g；G.map (CategoryTheory.Limits.pushout.inr f g)；CategoryTheor
y.Limits.PreservesPushout.iso G f g；G.map f；G.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesPushout.inr_iso_inv :
    G.map (pushout.inr _ _) ≫ (PreservesPushout.iso G f g).inv = pushout.inr _ _ := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

end Pushout

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

section Pullback

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`. -/
/-
**CategoryTheory.Limits.PreservesPullback.of_iso_comparison** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.PreservesPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [inst_2 : CategoryTheory.Limits.HasPullback
 f g]   [inst_3 : CategoryTheory.Limits.HasPullback (G.map f) (G.map g)]   [i : 
CategoryTheory.IsIso (CategoryTheory.Limits.pullbackComparison G f g)],   Catego
ryTheory.Limits.PreservesLimit (CategoryTheory.Limits.cospan f g) G
参数：G : CategoryTheory.Functor C D；G.map f；G.map g；CategoryTheory.Limits.pullback
Comparison G f g；CategoryTheory.Limits.cospan f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` pr
eserves the
pullback of `(f,g)`.
-/
lemma PreservesPullback.of_iso_comparison [i : IsIso (pullbackComparison G f g)] :
    PreservesLimit (cospan f g) G := by
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (cospan (G.map f) (G.map g))) i

variable [PreservesLimit (cospan f g) G]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (pullbackComparison G f g) := by
  rw [← PreservesPullback.iso_hom]
  infer_instance

end Pullback

section Pushout

variable {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If the pushout comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pushout of `(f,g)`. -/
/-
**CategoryTheory.Limits.PreservesPushout.of_iso_comparison** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PreservesPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [inst_2 : CategoryTheory.Limits.HasPushout 
f g]   [inst_3 : CategoryTheory.Limits.HasPushout (G.map f) (G.map g)]   [i : Ca
tegoryTheory.IsIso (CategoryTheory.Limits.pushoutComparison G f g)],   CategoryT
heory.Limits.PreservesColimit (CategoryTheory.Limits.span f g) G
参数：G : CategoryTheory.Functor C D；G.map f；G.map g；CategoryTheory.Limits.pushoutC
omparison G f g；CategoryTheory.Limits.span f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the pushout comparison map for `G` at `(f,g)` is an isomorphism, then `G` pre
serves the
pushout of `(f,g)`.
-/
lemma PreservesPushout.of_iso_comparison [i : IsIso (pushoutComparison G f g)] :
    PreservesColimit (span f g) G := by
  apply preservesColimit_of_preserves_colimit_cocone (pushoutIsPushout f g)
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).symm _
  exact IsColimit.ofPointIso _ (i := i)

variable [PreservesColimit (span f g) G]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (pushoutComparison G f g) := by
  rw [← PreservesPushout.iso_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- A pushout cocone in `C` is colimit iff it becomes limit
after the application of `yoneda.obj X` for all `X : C`. -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitYonedaEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           (c : CategoryTheory.
Limits.PushoutCocone f g) →             CategoryTheory.Limits.IsColimit c ≃     
          ((X_1 : C) → CategoryTheory.Limits.IsLimit (c.op.map (CategoryTheory.y
oneda.obj X_1)))
参数：c : CategoryTheory.Limits.PushoutCocone f g；(X_1 : C) → CategoryTheory.Limits
.IsLimit (c.op.map (CategoryTheory.yoneda.obj X_1))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A pushout cocone in `C` is colimit iff it becomes limit
after the application of `yoneda.obj X` for all `X : C`.
-/
def PushoutCocone.isColimitYonedaEquiv (c : PushoutCocone f g) :
    IsColimit c ≃ ∀ (X : C), IsLimit (c.op.map (yoneda.obj X)) :=
  (Limits.Cocone.isColimitYonedaEquiv c).trans
    (Equiv.piCongrRight (fun X ↦
      (IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (cospanOp f g).symm (yoneda.obj X)) _).symm.trans
            (Equiv.trans (IsLimit.equivIsoLimit
              (by exact Cone.ext (Iso.refl _) (by rintro (_ | _ | _) <;> cat_disch)))
                (c.op.isLimitMapConeEquiv (yoneda.obj X))))))

end Pushout

end

end CategoryTheory.Limits

