/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The lattice of subobjects

We provide the `SemilatticeInf` with `OrderTop (Subobject X)` instance when `[HasPullback C]`,
and the `SemilatticeSup (Subobject X)` instance when `[HasImages C] [HasBinaryCoproducts C]`.
-/

@[expose] public section


universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

section Top

/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Top (MonoOver X) where top := mk (𝟙 _)
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Inhabited (MonoOver X) :=
  ⟨⊤⟩

/-- The morphism to the top object in `MonoOver X`. -/
/-
**CategoryTheory.MonoOver.leTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：leTop (f : MonoOver X) : f ⟶ ⊤
参数：f : MonoOver X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism to the top object in `MonoOver X`.
-/
def leTop (f : MonoOver X) : f ⟶ ⊤ :=
  homMk f.arrow (comp_id _)

@[simp]
/-
**CategoryTheory.MonoOver.top_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：top_left (X : C) : ((⊤ : MonoOver X) : C) = X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_left (X : C) : ((⊤ : MonoOver X) : C) = X :=
  rfl

@[simp]
/-
**CategoryTheory.MonoOver.top_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mo
noOver`。
形式化陈述：top_arrow (X : C) : (⊤ : MonoOver X).arrow = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_arrow (X : C) : (⊤ : MonoOver X).arrow = 𝟙 X :=
  rfl

/-- `map f` sends `⊤ : MonoOver X` to `⟨X, f⟩ : MonoOver Y`. -/
/-
**CategoryTheory.MonoOver.mapTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoO
ver`。
形式化陈述：mapTop (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ ≅ mk f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map f` sends `⊤ : MonoOver X` to `⟨X, f⟩ : MonoOver Y`.
-/
def mapTop (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ ≅ mk f :=
  iso_of_both_ways (homMk (𝟙 _) rfl) (homMk (𝟙 _) (by simp [id_comp f]))

section

variable [HasPullbacks C]

/-- The pullback of the top object in `MonoOver Y`
is (isomorphic to) the top object in `MonoOver X`. -/
/-
**CategoryTheory.MonoOver.pullbackTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MonoOver`。
形式化陈述：pullbackTop (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of the top object in `MonoOver Y`
is (isomorphic to) the top object in `MonoOver X`.
-/
def pullbackTop (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
  iso_of_both_ways (leTop _)
    (homMk (pullback.lift f (𝟙 _) (by simp)) (pullback.lift_snd _ _ _))

/-- There is a morphism from `⊤ : MonoOver A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
/-
**CategoryTheory.MonoOver.topLEPullbackSelf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoOver`。
形式化陈述：topLEPullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (⊤ : MonoOver A) ⟶ (pul
lback f).obj (mk f)
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a morphism from `⊤ : MonoOver A` to the pullback of a monomorphism alon
g itself;
as the category is thin this is an isomorphism.
-/
def topLEPullbackSelf {A B : C} (f : A ⟶ B) [Mono f] :
    (⊤ : MonoOver A) ⟶ (pullback f).obj (mk f) :=
  homMk _ (pullback.lift_snd _ _ rfl)

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
/-
**CategoryTheory.MonoOver.pullbackSelf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MonoOver`。
形式化陈述：pullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) ≅ ⊤
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a monomorphism along itself is isomorphic to the top object.
-/
def pullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) ≅ ⊤ :=
  iso_of_both_ways (leTop _) (topLEPullbackSelf _)

end

end Top

section Bot

variable [HasInitial C] [InitialMonoClass C]

/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Bot (MonoOver X) where bot := mk (initial.to X)

@[simp]
/-
**CategoryTheory.MonoOver.bot_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：bot_left (X : C) : ((⊥ : MonoOver X) : C) = ⊥_ C
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_left (X : C) : ((⊥ : MonoOver X) : C) = ⊥_ C :=
  rfl

@[simp]
/-
**CategoryTheory.MonoOver.bot_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mo
noOver`。
形式化陈述：bot_arrow {X : C} : (⊥ : MonoOver X).arrow = initial.to X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_arrow {X : C} : (⊥ : MonoOver X).arrow = initial.to X :=
  rfl

/-- The (unique) morphism from `⊥ : MonoOver X` to any other `f : MonoOver X`. -/
/-
**CategoryTheory.MonoOver.botLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：botLE {X : C} (f : MonoOver X) : ⊥ ⟶ f
参数：f : MonoOver X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) morphism from `⊥ : MonoOver X` to any other `f : MonoOver X`.
-/
def botLE {X : C} (f : MonoOver X) : ⊥ ⟶ f :=
  homMk (initial.to _)

/-- `map f` sends `⊥ : MonoOver X` to `⊥ : MonoOver Y`. -/
/-
**CategoryTheory.MonoOver.mapBot** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoO
ver`。
形式化陈述：mapBot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ ≅ ⊥
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map f` sends `⊥ : MonoOver X` to `⊥ : MonoOver Y`.
-/
def mapBot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ ≅ ⊥ :=
  iso_of_both_ways (homMk (initial.to _)) (homMk (𝟙 _))

end Bot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object. -/
/-
**CategoryTheory.MonoOver.botCoeIsoZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MonoOver`。
形式化陈述：botCoeIsoZero {B : C} : ((⊥ : MonoOver B) : C) ≅ 0
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C

--- 原说明 ---
The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object.
-/
def botCoeIsoZero {B : C} : ((⊥ : MonoOver B) : C) ≅ 0 :=
  initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial
/-
**CategoryTheory.MonoOver.bot_arrow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonoOver`。
形式化陈述：bot_arrow_eq_zero [HasZeroMorphisms C] {B : C} : (⊥ : MonoOver B).arrow = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_source_iso_zero`：zero_of_source_iso_zero {
X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
-/
theorem bot_arrow_eq_zero [HasZeroMorphisms C] {B : C} : (⊥ : MonoOver B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

set_option backward.isDefEq.respectTransparency false in
/-- `simp`-normal form of `bot_arrow_eq_zero`. -/
@[simp]
/-
**CategoryTheory.MonoOver.initialTo_b_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoOver`。
形式化陈述：initialTo_b_eq_zero [HasZeroMorphisms C] {B : C} : initial.to B = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoOver.bot_arrow`：bot_arrow {X : C} : (⊥ : MonoOver X).
arrow = initial.to X
· 使用定理 `CategoryTheory.MonoOver.bot_arrow_eq_zero`：bot_arrow_eq_zero [HasZeroMor
phisms C] {B : C} : (⊥ : MonoOver B).arrow = 0

--- 原说明 ---
`simp`-normal form of `bot_arrow_eq_zero`.
-/
theorem initialTo_b_eq_zero [HasZeroMorphisms C] {B : C} : initial.to B = 0 := by
  rw [← bot_arrow, bot_arrow_eq_zero]

end ZeroOrderBot

section Inf

variable [HasPullbacks C]

set_option backward.defeqAttrib.useBackward true in
/-- When `[HasPullbacks C]`, `MonoOver A` has "intersections", functorial in both arguments.

As `MonoOver A` is only a preorder, this doesn't satisfy the axioms of `SemilatticeInf`,
but we reuse all the names from `SemilatticeInf` because they will be used to construct
`SemilatticeInf (Subobject A)` shortly.
-/
@[simps]
/-
**CategoryTheory.MonoOver.inf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOver
`。
形式化陈述：inf {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `[HasPullbacks C]`, `MonoOver A` has "intersections", functorial in both ar
guments.

As `MonoOver A` is only a preorder, this doesn't satisfy the axioms of `Semilatt
iceInf`,
but we reuse all the names from `SemilatticeInf` because they will be used to co
nstruct
`SemilatticeInf (Subobject A)` shortly.
-/
def inf {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A where
  obj f := pullback f.arrow ⋙ map f.arrow
  map k :=
    { app := fun g => by
        apply homMk _ _
        · apply pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k.hom.left) _
          rw [pullback.condition, assoc, w k]
        dsimp
        rw [pullback.lift_snd_assoc, assoc, w k] }

/-- A morphism from the "infimum" of two objects in `MonoOver A` to the first object. -/
/-
**CategoryTheory.MonoOver.infLELeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mo
noOver`。
形式化陈述：infLELeft {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ f
参数：f g : MonoOver A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism from the "infimum" of two objects in `MonoOver A` to the first object
.
-/
def infLELeft {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ f :=
  homMk _ rfl

/-- A morphism from the "infimum" of two objects in `MonoOver A` to the second object. -/
/-
**CategoryTheory.MonoOver.infLERight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onoOver`。
形式化陈述：infLERight {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ g
参数：f g : MonoOver A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism from the "infimum" of two objects in `MonoOver A` to the second objec
t.
-/
def infLERight {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ g :=
  homMk _ pullback.condition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism version of the `le_inf` axiom. -/
/-
**CategoryTheory.MonoOver.leInf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：leInf {A : C} (f g h : MonoOver A) : (h ⟶ f) -> (h ⟶ g) -> (h ⟶ (inf.obj f
).obj g)
参数：f g h : MonoOver A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism version of the `le_inf` axiom.
-/
def leInf {A : C} (f g h : MonoOver A) : (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) :=
  fun k₁ k₂ ↦ homMk (pullback.lift k₂.hom.left k₁.hom.left (by simp))

end Inf

section Sup

variable [HasImages C] [HasBinaryCoproducts C]

/-- When `[HasImages C] [HasBinaryCoproducts C]`, `MonoOver A` has a `sup` construction,
which is functorial in both arguments,
and which on `Subobject A` will induce a `SemilatticeSup`. -/
/-
**CategoryTheory.MonoOver.sup** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOver
`。
形式化陈述：sup {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `[HasImages C] [HasBinaryCoproducts C]`, `MonoOver A` has a `sup` construct
ion,
which is functorial in both arguments,
and which on `Subobject A` will induce a `SemilatticeSup`.
-/
def sup {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A :=
  Functor.curryObj ((forget A).prod (forget A) ⋙ Functor.uncurry.obj Over.coprod ⋙ image)

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism version of `le_sup_left`. -/
/-
**CategoryTheory.MonoOver.leSupLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mo
noOver`。
形式化陈述：leSupLeft {A : C} (f g : MonoOver A) : f ⟶ (sup.obj f).obj g
参数：f g : MonoOver A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism version of `le_sup_left`.
-/
def leSupLeft {A : C} (f g : MonoOver A) : f ⟶ (sup.obj f).obj g := by
  refine homMk (coprod.inl ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inl_desc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism version of `le_sup_right`. -/
/-
**CategoryTheory.MonoOver.leSupRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onoOver`。
形式化陈述：leSupRight {A : C} (f g : MonoOver A) : g ⟶ (sup.obj f).obj g
参数：f g : MonoOver A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism version of `le_sup_right`.
-/
def leSupRight {A : C} (f g : MonoOver A) : g ⟶ (sup.obj f).obj g := by
  refine homMk (coprod.inr ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inr_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism version of `sup_le`. -/
/-
**CategoryTheory.MonoOver.supLe** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：supLe {A : C} (f g h : MonoOver A) : (f ⟶ h) -> (g ⟶ h) -> ((sup.obj f).ob
j g ⟶ h)
参数：f g h : MonoOver A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism version of `sup_le`.
-/
def supLe {A : C} (f g h : MonoOver A) : (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) := by
  intro k₁ k₂
  refine homMk ?_ ?_
  · apply image.lift ⟨_, h.arrow, coprod.desc k₁.hom.left k₂.hom.left, _⟩
    ext
    · simp [w k₁]
    · simp [w k₂]
  · apply image.lift_fac

end Sup

end MonoOver

namespace Subobject

section OrderTop

/-
**CategoryTheory.Subobject.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：orderTop {X : C} : OrderTop (Subobject X) where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance orderTop {X : C} : OrderTop (Subobject X) where
  top := Quotient.mk'' ⊤
  le_top := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.leTop f⟩
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Inhabited (Subobject X) :=
  ⟨⊤⟩
/-
**CategoryTheory.Subobject.top_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：top_eq_id (B : C) : (⊤ : Subobject B) = Subobject.mk (𝟙 B)
参数：B : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_eq_id (B : C) : (⊤ : Subobject B) = Subobject.mk (𝟙 B) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subobject.underlyingIso_top_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subobject`。
形式化陈述：underlyingIso_top_hom {B : C} : (underlyingIso (𝟙 B)).hom = (⊤ : Subobject
 B).arrow
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
-/
theorem underlyingIso_top_hom {B : C} : (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow := by
  convert! underlyingIso_hom_comp_eq_mk (𝟙 B)
  simp only [comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subobject.top_arrow_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：top_arrow_isIso {B : C} : IsIso (⊤ : Subobject B).arrow
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.underlyingIso_top_hom`：underlyingIso_top_hom {B
 : C} : (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance top_arrow_isIso {B : C} : IsIso (⊤ : Subobject B).arrow := by
  rw [← underlyingIso_top_hom]
  infer_instance

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.underlyingIso_inv_top_arrow** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Subobject`。
形式化陈述：underlyingIso_inv_top_arrow {B : C} : (underlyingIso _).inv ≫ (⊤ : Subobje
ct B).arrow = 𝟙 B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
-/
theorem underlyingIso_inv_top_arrow {B : C} :
    (underlyingIso _).inv ≫ (⊤ : Subobject B).arrow = 𝟙 B :=
  underlyingIso_arrow _

@[simp]
/-
**CategoryTheory.Subobject.map_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：map_top (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ = Subobject.mk f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem map_top (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ = Subobject.mk f :=
  Quotient.sound' ⟨MonoOver.mapTop f⟩
/-
**CategoryTheory.Subobject.top_factors** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：top_factors {A B : C} (f : A ⟶ B) : (⊤ : Subobject B).Factors f
参数：f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem top_factors {A B : C} (f : A ⟶ B) : (⊤ : Subobject B).Factors f :=
  ⟨f, comp_id _⟩
/-
**CategoryTheory.Subobject.isIso_iff_mk_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subobject`。
形式化陈述：isIso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem isIso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤ :=
  ⟨fun _ => mk_eq_mk_of_comm _ _ (asIso f) (Category.comp_id _), fun h => by
    rw [← ofMkLEMk_comp h.le, Category.comp_id]
    exact (isoOfMkEqMk _ _ h).isIso_hom⟩
/-
**CategoryTheory.Subobject.isIso_arrow_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Subobject`。
形式化陈述：isIso_arrow_iff_eq_top {Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤
参数：P : Subobject Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.isIso_iff_mk_eq_top`：isIso_iff_mk_eq_top {X Y :
 C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
· 使用定理 `CategoryTheory.Subobject.mk_arrow`：mk_arrow (P : Subobject X) : mk P.arr
ow = P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIso_arrow_iff_eq_top {Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤ := by
  rw [isIso_iff_mk_eq_top, mk_arrow]
/-
**CategoryTheory.Subobject.isIso_top_arrow** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：isIso_top_arrow {Y : C} : IsIso (⊤ : Subobject Y).arrow
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.isIso_arrow_iff_eq_top`：isIso_arrow_iff_eq_top 
{Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤
-/
instance isIso_top_arrow {Y : C} : IsIso (⊤ : Subobject Y).arrow := by rw [isIso_arrow_iff_eq_top]
/-
**CategoryTheory.Subobject.mk_eq_top_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：mk_eq_top_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : mk f = ⊤
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Subobject.isIso_iff_mk_eq_top`：isIso_iff_mk_eq_top {X Y :
 C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
-/
theorem mk_eq_top_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : mk f = ⊤ :=
  (isIso_iff_mk_eq_top f).mp inferInstance
/-
**CategoryTheory.Subobject.eq_top_of_isIso_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subobject`。
形式化陈述：eq_top_of_isIso_arrow {Y : C} (P : Subobject Y) [IsIso P.arrow] : P = ⊤
参数：P : Subobject Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Subobject.isIso_arrow_iff_eq_top`：isIso_arrow_iff_eq_top 
{Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤
-/
theorem eq_top_of_isIso_arrow {Y : C} (P : Subobject Y) [IsIso P.arrow] : P = ⊤ :=
  (isIso_arrow_iff_eq_top P).mp inferInstance
/-
**CategoryTheory.Subobject.epi_iff_mk_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：epi_iff_mk_eq_top [Balanced C] (f : X ⟶ Y) [Mono f] : Epi f ↔ Subobject.mk
 f = ⊤
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.isIso_iff_mk_eq_top`：isIso_iff_mk_eq_top {X Y :
 C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
lemma epi_iff_mk_eq_top [Balanced C] (f : X ⟶ Y) [Mono f] :
    Epi f ↔ Subobject.mk f = ⊤ := by
  rw [← isIso_iff_mk_eq_top]
  exact ⟨fun _ ↦ isIso_of_mono_of_epi f, fun _ ↦ inferInstance⟩

section

variable [HasPullbacks C]

/-
**CategoryTheory.Subobject.pullback_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackTop f⟩
/-
**CategoryTheory.Subobject.pullback_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：pullback_self {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) = ⊤
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem pullback_self {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackSelf f⟩

end

end OrderTop

section OrderBot

variable [HasInitial C] [InitialMonoClass C]

/-
**CategoryTheory.Subobject.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：orderBot {X : C} : OrderBot (Subobject X) where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance orderBot {X : C} : OrderBot (Subobject X) where
  bot := Quotient.mk'' ⊥
  bot_le := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.botLE f⟩
/-
**CategoryTheory.Subobject.bot_eq_initial_to** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：bot_eq_initial_to {B : C} : (⊥ : Subobject B) = Subobject.mk (initial.to B
)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_initial_to {B : C} : (⊥ : Subobject B) = Subobject.mk (initial.to B) :=
  rfl

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the initial object. -/
/-
**CategoryTheory.Subobject.botCoeIsoInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：botCoeIsoInitial {B : C} : ((⊥ : Subobject B) : C) ≅ ⊥_ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object underlying `⊥ : Subobject B` is (up to isomorphism) the initial objec
t.
-/
def botCoeIsoInitial {B : C} : ((⊥ : Subobject B) : C) ≅ ⊥_ C :=
  underlyingIso _
/-
**CategoryTheory.Subobject.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：map_bot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ = ⊥
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem map_bot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ = ⊥ :=
  Quotient.sound' ⟨MonoOver.mapBot f⟩

end OrderBot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object. -/
/-
**CategoryTheory.Subobject.botCoeIsoZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：botCoeIsoZero {B : C} : ((⊥ : Subobject B) : C) ≅ 0
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C

--- 原说明 ---
The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object.
-/
def botCoeIsoZero {B : C} : ((⊥ : Subobject B) : C) ≅ 0 :=
  botCoeIsoInitial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

variable [HasZeroMorphisms C]
/-
**CategoryTheory.Subobject.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：bot_eq_zero {B : C} : (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instMono`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
{X : C}   (f : 0 ⟶ X), CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsInitial.uniqueUpToIso_hom`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {I I' : C} (hI : CategoryTheory.Limits.Is
Initial I)   (hI' : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.MonoOver.initialTo_b_eq_zero`：initialTo_b_eq_zero [HasZer
oMorphisms C] {B : C} : initial.to B = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bot_eq_zero {B : C} : (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B) :=
  mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
    (by simp)

@[simp]
/-
**CategoryTheory.Subobject.bot_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：bot_arrow {B : C} : (⊥ : Subobject B).arrow = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_source_iso_zero`：zero_of_source_iso_zero {
X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
-/
theorem bot_arrow {B : C} : (⊥ : Subobject B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.bot_factors_iff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subobject`。
形式化陈述：bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : Subobject B).Factors f ↔
 f = 0
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoOver.bot_arrow_eq_zero`：bot_arrow_eq_zero [HasZeroMor
phisms C] {B : C} : (⊥ : MonoOver B).arrow = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoOver.initialTo_b_eq_zero`：initialTo_b_eq_zero [HasZer
oMorphisms C] {B : C} : initial.to B = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : Subobject B).Factors f ↔ f = 0 :=
  ⟨by
    rintro ⟨h, rfl⟩
    simp only [MonoOver.bot_arrow_eq_zero, MonoOver.bot_left, comp_zero],
   by
    rintro rfl
    exact ⟨0, by simp⟩⟩
/-
**CategoryTheory.Subobject.mk_eq_bot_iff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：mk_eq_bot_iff_zero {f : X ⟶ Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_factors_self`：mk_factors_self (f : X ⟶ Y) [M
ono f] : (mk f).Factors f
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.isoZeroOfMonoEqZero.congr_simp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroOb
ject C]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_hom`：zeroIsoInitial_h
om [HasInitial C] : zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.MonoOver.initialTo_b_eq_zero`：initialTo_b_eq_zero [HasZer
oMorphisms C] {B : C} : initial.to B = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_bot_iff_zero {f : X ⟶ Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0 :=
  ⟨fun h => by simpa [h, bot_factors_iff_zero] using mk_factors_self f, fun h =>
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial) (by simp [h])⟩

end ZeroOrderBot

section Functor

variable (C)

/-- Sending `X : C` to `Subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
/-
**CategoryTheory.Subobject.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：functor [HasPullbacks C] : Cᵒᵖ ⥤ Type max u₁ v₁ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sending `X : C` to `Subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`.
-/
def functor [HasPullbacks C] : Cᵒᵖ ⥤ Type max u₁ v₁ where
  obj X := Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

end Functor

section SemilatticeInfTop

variable [HasPullbacks C]

/-- The functorial infimum on `MonoOver A` descends to an infimum on `Subobject A`. -/
/-
**CategoryTheory.Subobject.inf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobje
ct`。
形式化陈述：inf {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial infimum on `MonoOver A` descends to an infimum on `Subobject A`.
-/
def inf {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.inf
/-
**CategoryTheory.Subobject.inf_le_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：inf_le_left {A : C} (f g : Subobject A) : (inf.obj f).obj g <= f
参数：f g : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
-/
theorem inf_le_left {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ f :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLELeft _ _⟩
/-
**CategoryTheory.Subobject.inf_le_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：inf_le_right {A : C} (f g : Subobject A) : (inf.obj f).obj g <= g
参数：f g : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
-/
theorem inf_le_right {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ g :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLERight _ _⟩
/-
**CategoryTheory.Subobject.le_inf** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Subo
bject`。
形式化陈述：le_inf {A : C} (h f g : Subobject A) : h <= f -> h <= g -> h <= (inf.obj f
).obj g
参数：h f g : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {
s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}   {p : Quotient s₁ → Quotient s₂ 
→ Quotient s…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem le_inf {A : C} (h f g : Subobject A) : h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
  Quotient.inductionOn₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨MonoOver.leInf _ _ _ k l⟩)
/-
**CategoryTheory.Subobject.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：semilatticeInf {B : C} : SemilatticeInf (Subobject B) where inf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.inf_le_left`：inf_le_left {A : C} (f g : Subobje
ct A) : (inf.obj f).obj g <= f
· 使用定理 `CategoryTheory.Subobject.inf_le_right`：inf_le_right {A : C} (f g : Subob
ject A) : (inf.obj f).obj g <= g
· 使用定理 `CategoryTheory.Subobject.le_inf`：le_inf {A : C} (h f g : Subobject A) : 
h <= f -> h <= g -> h <= (inf.obj f).obj g
-/
instance semilatticeInf {B : C} : SemilatticeInf (Subobject B) where
  inf := fun m n => (inf.obj m).obj n
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

@[reassoc]
/-
**CategoryTheory.Subobject.inf_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：inf_comp_left {A : C} (f g : Subobject A) : (ofLE (f ⊓ g) f (by simp)) ≫ f
.arrow = (f ⊓ g).arrow
参数：f g : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Subobject.inf_le_left`：inf_le_left {A : C} (f g : Subobje
ct A) : (inf.obj f).obj g <= f
-/
lemma inf_comp_left {A : C} (f g : Subobject A) :
   (ofLE (f ⊓ g) f (by simp)) ≫ f.arrow = (f ⊓ g).arrow :=
  ofLE_arrow (inf_le_left f g)

@[reassoc]
/-
**CategoryTheory.Subobject.inf_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：inf_comp_right {A : C} (f g : Subobject A) : (ofLE (f ⊓ g) g (by simp)) ≫ 
g.arrow = (f ⊓ g).arrow
参数：f g : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Subobject.inf_le_right`：inf_le_right {A : C} (f g : Subob
ject A) : (inf.obj f).obj g <= g
-/
lemma inf_comp_right {A : C} (f g : Subobject A) :
   (ofLE (f ⊓ g) g (by simp)) ≫ g.arrow = (f ⊓ g).arrow :=
  ofLE_arrow (inf_le_right f g)
/-
**CategoryTheory.Subobject.factors_left_of_inf_factors** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Subobject`。
形式化陈述：factors_left_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B} (h :
 (X ⊓ Y).Factors f) : X.Factors f
参数：h : (X ⊓ Y).Factors f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.factors_of_le`：factors_of_le {Y Z : C} {P Q : S
ubobject Y} (f : Z ⟶ Y) (h : P <= Q) : P.Factors f -> Q.Factors f
· 使用定理 `CategoryTheory.Subobject.inf_le_left`：inf_le_left {A : C} (f g : Subobje
ct A) : (inf.obj f).obj g <= f
-/
theorem factors_left_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : X.Factors f :=
  factors_of_le _ (inf_le_left _ _) h
/-
**CategoryTheory.Subobject.factors_right_of_inf_factors** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Subobject`。
形式化陈述：factors_right_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B} (h 
: (X ⊓ Y).Factors f) : Y.Factors f
参数：h : (X ⊓ Y).Factors f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.factors_of_le`：factors_of_le {Y Z : C} {P Q : S
ubobject Y} (f : Z ⟶ Y) (h : P <= Q) : P.Factors f -> Q.Factors f
· 使用定理 `CategoryTheory.Subobject.inf_le_right`：inf_le_right {A : C} (f g : Subob
ject A) : (inf.obj f).obj g <= g
-/
theorem factors_right_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : Y.Factors f :=
  factors_of_le _ (inf_le_right _ _) h

@[simp]
/-
**CategoryTheory.Subobject.inf_factors** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：inf_factors {A B : C} {X Y : Subobject B} (f : A ⟶ B) : (X ⊓ Y).Factors f 
↔ X.Factors f ∧ Y.Factors f
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.factors_left_of_inf_factors`：factors_left_of_in
f_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B} (h : (X ⊓ Y).Factors f) : X.
Factors f
· 使用定理 `CategoryTheory.Subobject.factors_right_of_inf_factors`：factors_right_of_
inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B} (h : (X ⊓ Y).Factors f) : 
Y.Factors f
· 使用定理 `Quotient.ind₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ : Se
toid β} {p : Quotient s₁ → Quotient s₂ → Prop},   (∀ (a₁ : α) (a₂ : β), p (Quoti
ent.…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
-/
theorem inf_factors {A B : C} {X Y : Subobject B} (f : A ⟶ B) :
    (X ⊓ Y).Factors f ↔ X.Factors f ∧ Y.Factors f :=
  ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    apply Quotient.ind₂'
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩
/-
**CategoryTheory.Subobject.inf_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：inf_isPullback {A : C} (f g : Subobject A) : IsPullback (ofLE (f ⊓ g) f (b
y simp)) (ofLE (f ⊓ g) g (by simp)) f.arrow g.arrow
参数：f g : Subobject A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.Subobject.factors_comp_arrow`：factors_comp_arrow {X Y : C
} {P : Subobject Y} (f : X ⟶ P) : P.Factors (f ≫ P.arrow)
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Subobject.factorThru.congr_simp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (P : CategoryTheory.Subobject Y) (
f f_1 : X ⟶ Y)   (e_f : f = f_1) (h …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.factorThru_comp_arrow`：factorThru_comp_arrow {X
 Y : C} {P : Subobject Y} (f : X ⟶ P) (h) : P.factorThru (f ≫ P.arrow) h = f
-/
theorem inf_isPullback {A : C} (f g : Subobject A) :
    IsPullback (ofLE (f ⊓ g) f (by simp)) (ofLE (f ⊓ g) g (by simp)) f.arrow g.arrow := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ (f ⊓ g).factorThru (s.fst ≫ f.arrow) ?_)
    ?_ (fun s ↦ ?_) fun _ _ h _ ↦ ?_⟩⟩
  · simpa using ⟨factors_comp_arrow s.fst, by simpa [s.condition] using factors_comp_arrow s.snd⟩
  · cat_disch
  · ext
    simp [s.condition]
  · ext
    simp [← h]
/-
**CategoryTheory.Subobject.inf_arrow_factors_left** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Subobject`。
形式化陈述：inf_arrow_factors_left {B : C} (X Y : Subobject B) : X.Factors (X ⊓ Y).arr
ow
参数：X Y : Subobject B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `CategoryTheory.Subobject.inf_le_left`：inf_le_left {A : C} (f g : Subobje
ct A) : (inf.obj f).obj g <= f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inf_arrow_factors_left {B : C} (X Y : Subobject B) : X.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) X (inf_le_left X Y), by simp⟩
/-
**CategoryTheory.Subobject.inf_arrow_factors_right** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Subobject`。
形式化陈述：inf_arrow_factors_right {B : C} (X Y : Subobject B) : Y.Factors (X ⊓ Y).ar
row
参数：X Y : Subobject B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `CategoryTheory.Subobject.inf_le_right`：inf_le_right {A : C} (f g : Subob
ject A) : (inf.obj f).obj g <= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inf_arrow_factors_right {B : C} (X Y : Subobject B) : Y.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) Y (inf_le_right X Y), by simp⟩

@[simp]
/-
**CategoryTheory.Subobject.finset_inf_factors** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：finset_inf_factors {I : Type*} {A B : C} {s : Finset I} {P : I -> Subobjec
t B} (f : A ⟶ B) : (s.inf P).Factors f ↔ forall i in s, (P i).Factors f
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inf_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {f : β → α}, ∅.inf f = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
-/
theorem finset_inf_factors {I : Type*} {A B : C} {s : Finset I} {P : I → Subobject B} (f : A ⟶ B) :
    (s.inf P).Factors f ↔ ∀ i ∈ s, (P i).Factors f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [top_factors]
  | insert _ _ _ ih => simp [ih]

-- `i` is explicit here because often we'd like to defer a proof of `m`
/-
**CategoryTheory.Subobject.finset_inf_arrow_factors** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Subobject`。
形式化陈述：finset_inf_arrow_factors {I : Type*} {B : C} (s : Finset I) (P : I -> Subo
bject B) (i : I) (m : i in s) : (P i).Factors (s.inf P).arrow
参数：s : Finset I；P : I -> Subobject B；i : I；m : i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `CategoryTheory.Subobject.inf_arrow_factors_left`：inf_arrow_factors_left 
{B : C} (X Y : Subobject B) : X.Factors (X ⊓ Y).arrow
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Subobject.factors_comp_arrow`：factors_comp_arrow {X Y : C
} {P : Subobject Y} (f : X ⟶ P) : P.Factors (f ≫ P.arrow)
· 使用定理 `CategoryTheory.Subobject.inf_arrow_factors_right`：inf_arrow_factors_righ
t {B : C} (X Y : Subobject B) : Y.Factors (X ⊓ Y).arrow
· 使用定理 `CategoryTheory.Subobject.factors_of_factors_right`：factors_of_factors_ri
ght {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z} (h : P.Factors g) : P.
Factors (f ≫ g)
-/
theorem finset_inf_arrow_factors {I : Type*} {B : C} (s : Finset I) (P : I → Subobject B) (i : I)
    (m : i ∈ s) : (P i).Factors (s.inf P).arrow := by
  classical
  revert i m
  induction s using Finset.induction_on with
  | empty => rintro _ ⟨⟩
  | insert _ _ _ ih =>
    intro _ m
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m
/-
**CategoryTheory.Subobject.inf_eq_map_pullback'** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subobject`。
形式化陈述：inf_eq_map_pullback' {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) : (Subob
ject.inf.obj (Quotient.mk'' f₁)).obj f₂ = (Subobject.map f₁.arrow).obj ((Subobje
ct.pullback f₁.arrow).obj f₂)
参数：f₁ : MonoOver A；f₂ : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem inf_eq_map_pullback' {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Subobject.inf.obj (Quotient.mk'' f₁)).obj f₂ =
      (Subobject.map f₁.arrow).obj ((Subobject.pullback f₁.arrow).obj f₂) := by
  induction f₂ using Quotient.inductionOn'
  rfl
/-
**CategoryTheory.Subobject.inf_eq_map_pullback** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subobject`。
形式化陈述：inf_eq_map_pullback {A : C} (f₁ : Subobject A) (f₂ : Subobject A) : (f₁ ⊓ 
f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂)
参数：f₁ : Subobject A；f₂ : Subobject A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subobject.thinSkeleton_mk_representative_eq_self`：thinSke
leton_mk_representative_eq_self {X : C} (A : Subobject X) : ThinSkeleton.mk (rep
resentative.obj A) = A
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Subobject.inf_eq_map_pullback'`：inf_eq_map_pullback' {A :
 C} (f₁ : MonoOver A) (f₂ : Subobject A) : (Subobject.inf.obj (Quotient.mk'' f₁)
).obj f₂ = (Subobject.map f₁.arrow)…
-/
theorem inf_eq_map_pullback {A : C} (f₁ : Subobject A) (f₂ : Subobject A) :
    (f₁ ⊓ f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) := by
  convert! inf_eq_map_pullback' (representative.obj f₁) f₂
  ext1
  nth_rw 1 [← thinSkeleton_mk_representative_eq_self f₁]
  congr
/-
**CategoryTheory.Subobject.prod_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：prod_eq_inf {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂] : (f₁ ⨯
 f₂) = f₁ ⊓ f₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Subobject.le_inf`：le_inf {A : C} (h f g : Subobject A) : 
h <= f -> h <= g -> h <= (inf.obj f).obj g
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `CategoryTheory.Subobject.inf_le_left`：inf_le_left {A : C} (f g : Subobje
ct A) : (inf.obj f).obj g <= f
· 使用定理 `CategoryTheory.Subobject.inf_le_right`：inf_le_right {A : C} (f g : Subob
ject A) : (inf.obj f).obj g <= g
-/
theorem prod_eq_inf {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂] :
    (f₁ ⨯ f₂) = f₁ ⊓ f₂ := by
  apply le_antisymm
  · refine le_inf _ _ _ (Limits.prod.fst.le) (Limits.prod.snd.le)
  · apply leOfHom
    exact prod.lift (inf_le_left _ _).hom (inf_le_right _ _).hom
/-
**CategoryTheory.Subobject.inf_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：inf_def {B : C} (m m' : Subobject B) : m ⊓ m' = (inf.obj m).obj m'
参数：m m' : Subobject B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_def {B : C} (m m' : Subobject B) : m ⊓ m' = (inf.obj m).obj m' :=
  rfl

/-- `⊓` commutes with pullback. -/
/-
**CategoryTheory.Subobject.inf_pullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) : (pullback g).obj (f₁ ⊓ f₂) = 
(pullback g).obj f₁ ⊓ (pullback g).obj f₂
参数：g : X ⟶ Y；f₁ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.inf_def`：inf_def {B : C} (m m' : Subobject B) :
 m ⊓ m' = (inf.obj m).obj m'
· 使用定理 `CategoryTheory.Subobject.inf_eq_map_pullback'`：inf_eq_map_pullback' {A :
 C} (f₁ : MonoOver A) (f₂ : Subobject A) : (Subobject.inf.obj (Quotient.mk'' f₁)
).obj f₂ = (Subobject.map f₁.arrow)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.pullback_comp`：pullback_comp (f : X ⟶ Y) (g : Y
 ⟶ Z) (x : Subobject Z) : (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback
 g).obj x)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Subobject.map_pullback`：map_pullback [HasPullbacks C] {X 
Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [Mono h] [Mono g] (co
mm : f ≫ h = g ≫ k) (t : Is…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
`⊓` commutes with pullback.
-/
theorem inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
    (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pullback g).obj f₂ := by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullbackIsPullback f₁.arrow g), ← pullback_comp,
    pullback.condition]
  rfl

/-- `⊓` commutes with map. -/
/-
**CategoryTheory.Subobject.inf_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：inf_map {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂) : (map g).obj (f₁ ⊓ f₂) = (
map g).obj f₁ ⊓ (map g).obj f₂
参数：g : Y ⟶ X；f₁ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.inf_def`：inf_def {B : C} (m m' : Subobject B) :
 m ⊓ m' = (inf.obj m).obj m'
· 使用定理 `CategoryTheory.Subobject.inf_eq_map_pullback'`：inf_eq_map_pullback' {A :
 C} (f₁ : MonoOver A) (f₂ : Subobject A) : (Subobject.inf.obj (Quotient.mk'' f₁)
).obj f₂ = (Subobject.map f₁.arrow)…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.map_comp`：map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mon
o f] [Mono g] (x : Subobject X) : (map (f ≫ g)).obj x = (map g).obj ((map f).obj
 x)
· 使用定理 `CategoryTheory.Subobject.pullback_comp`：pullback_comp (f : X ⟶ Y) (g : Y
 ⟶ Z) (x : Subobject Z) : (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback
 g).obj x)
· 使用定理 `CategoryTheory.Subobject.pullback_map_self`：pullback_map_self [HasPullba
cks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) : (pullback f).obj ((map f).obj g)
 = g

--- 原说明 ---
`⊓` commutes with map.
-/
theorem inf_map {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂) :
    (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂ := by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  dsimp
  rw [pullback_comp, pullback_map_self]

end SemilatticeInfTop

section SemilatticeSup

variable [HasImages C] [HasBinaryCoproducts C]

/-- The functorial supremum on `MonoOver A` descends to a supremum on `Subobject A`. -/
/-
**CategoryTheory.Subobject.sup** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobje
ct`。
形式化陈述：sup {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial supremum on `MonoOver A` descends to a supremum on `Subobject A`.
-/
def sup {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.sup
/-
**CategoryTheory.Subobject.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：semilatticeSup {B : C} : SemilatticeSup (Subobject B) where sup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup {B : C} : SemilatticeSup (Subobject B) where
  sup := fun m n => (sup.obj m).obj n
  le_sup_left := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupLeft _ _⟩
  le_sup_right := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupRight _ _⟩
  sup_le := fun m n k =>
    Quotient.inductionOn₃' m n k fun _ _ _ ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩
/-
**CategoryTheory.Subobject.sup_factors_of_factors_left** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Subobject`。
形式化陈述：sup_factors_of_factors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P :
 X.Factors f) : (X ⊔ Y).Factors f
参数：P : X.Factors f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.factors_of_le`：factors_of_le {Y Z : C} {P Q : S
ubobject Y} (f : Z ⟶ Y) (h : P <= Q) : P.Factors f -> Q.Factors f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem sup_factors_of_factors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_left P
/-
**CategoryTheory.Subobject.sup_factors_of_factors_right** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Subobject`。
形式化陈述：sup_factors_of_factors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P 
: Y.Factors f) : (X ⊔ Y).Factors f
参数：P : Y.Factors f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.factors_of_le`：factors_of_le {Y Z : C} {P Q : S
ubobject Y} (f : Z ⟶ Y) (h : P <= Q) : P.Factors f -> Q.Factors f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem sup_factors_of_factors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_right P

variable [HasInitial C] [InitialMonoClass C]
/-
**CategoryTheory.Subobject.finset_sup_factors** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：finset_sup_factors {I : Type*} {A B : C} {s : Finset I} {P : I -> Subobjec
t B} {f : A ⟶ B} (h : exists i in s, (P i).Factors f) : (s.sup P).Factors f
参数：h : exists i in s, (P i).Factors f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `CategoryTheory.Subobject.sup_factors_of_factors_left`：sup_factors_of_fac
tors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f) : (X ⊔ Y).
Factors f
· 使用定理 `CategoryTheory.Subobject.sup_factors_of_factors_right`：sup_factors_of_fa
ctors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f) : (X ⊔ Y
).Factors f
-/
theorem finset_sup_factors {I : Type*} {A B : C} {s : Finset I} {P : I → Subobject B} {f : A ⟶ B}
    (h : ∃ i ∈ s, (P i).Factors f) : (s.sup P).Factors f := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => rintro ⟨_, ⟨⟨⟩, _⟩⟩
  | insert _ _ _ ih =>
    rintro ⟨j, ⟨m, h⟩⟩
    simp only [Finset.sup_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)

end SemilatticeSup

section Lattice

/-
**CategoryTheory.Subobject.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：boundedOrder [HasInitial C] [InitialMonoClass C] {B : C} : BoundedOrder (S
ubobject B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance boundedOrder [HasInitial C] [InitialMonoClass C] {B : C} : BoundedOrder (Subobject B) :=
  { Subobject.orderTop, Subobject.orderBot with }

variable [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} : Lattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup with }

end Lattice

section Inf

variable [LocallySmall.{w} C] [WellPowered.{w} C]

/-- The "wide cospan" diagram, with a small indexing type, constructed from a set of subobjects.
(This is just the diagram of all the subobjects pasted together, but using `WellPowered C`
to make the diagram small.)
-/
/-
**CategoryTheory.Subobject.wideCospan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：wideCospan {A : C} (s : Set (Subobject A)) : WidePullbackShape (equivShrin
k _ '' s) ⥤ C
参数：s : Set (Subobject A)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The "wide cospan" diagram, with a small indexing type, constructed from a set of
 subobjects.
(This is just the diagram of all the subobjects pasted together, but using `Well
Powered C`
to make the diagram small.)
-/
def wideCospan {A : C} (s : Set (Subobject A)) : WidePullbackShape (equivShrink _ '' s) ⥤ C :=
  WidePullbackShape.wideCospan A
    (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow

@[simp]
/-
**CategoryTheory.Subobject.wideCospan_map_term** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subobject`。
形式化陈述：wideCospan_map_term {A : C} (s : Set (Subobject A)) (j) : (wideCospan s).m
ap (WidePullbackShape.Hom.term j) = ((equivShrink (Subobject A)).symm j).arrow
参数：s : Set (Subobject A)；j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideCospan_map_term {A : C} (s : Set (Subobject A)) (j) :
    (wideCospan s).map (WidePullbackShape.Hom.term j) =
      ((equivShrink (Subobject A)).symm j).arrow :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary construction of a cone for `le_inf`. -/
/-
**CategoryTheory.Subobject.leInfCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：leInfCone {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g 
in s, f <= g) : Cone (wideCospan s)
参数：s : Set (Subobject A)；f : Subobject A；k : forall g in s, f <= g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Auxiliary construction of a cone for `le_inf`.
-/
def leInfCone {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, f ≤ g) :
    Cone (wideCospan s) :=
  WidePullbackShape.mkCone f.arrow
    (fun j =>
      underlying.map
        (homOfLE
          (k _
            (by
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              simpa using m))))
    (by simp)

@[simp]
/-
**CategoryTheory.Subobject.leInfCone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subobject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leInfCone_π_app_none {A : C} (s : Set (Subobject A)) (f : Subobject A)
    (k : ∀ g ∈ s, f ≤ g) : (leInfCone s f k).π.app none = f.arrow :=
  rfl

variable [HasWidePullbacks.{w} C]

/-- The limit of `wideCospan s`. (This will be the supremum of the set of subobjects.)
-/
/-
**CategoryTheory.Subobject.widePullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：widePullback {A : C} (s : Set (Subobject A)) : C
参数：s : Set (Subobject A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of `wideCospan s`. (This will be the supremum of the set of subobjects
.)
-/
def widePullback {A : C} (s : Set (Subobject A)) : C :=
  Limits.limit (wideCospan s)

/-- The inclusion map from `widePullback s` to `A`
-/
/-
**CategoryTheory.Subobject.widePullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：widePullback {A : C} (s : Set (Subobject A)) : C
参数：s : Set (Subobject A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from `widePullback s` to `A`
-/
def widePullbackι {A : C} (s : Set (Subobject A)) : widePullback s ⟶ A :=
  Limits.limit.π (wideCospan s) none

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.widePullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：widePullback {A : C} (s : Set (Subobject A)) : C
参数：s : Set (Subobject A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance widePullbackι_mono {A : C} (s : Set (Subobject A)) : Mono (widePullbackι s) :=
  ⟨fun u v h =>
    limit.hom_ext fun j => by
      cases j
      · exact h
      · apply (cancel_mono ((equivShrink (Subobject A)).symm _).arrow).1
        rw [assoc, assoc]
        erw [limit.w (wideCospan s) (WidePullbackShape.Hom.term _)]
        exact h⟩

/-- When `[WellPowered C]` and `[HasWidePullbacks C]`, `Subobject A` has arbitrary infimums.
-/
/-
**CategoryTheory.Subobject.sInf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobj
ect`。
形式化陈述：sInf {A : C} (s : Set (Subobject A)) : Subobject A
参数：s : Set (Subobject A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `[WellPowered C]` and `[HasWidePullbacks C]`, `Subobject A` has arbitrary i
nfimums.
-/
def sInf {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (widePullbackι s)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.sInf_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：sInf_le {A : C} (s : Set (Subobject A)) (f) (hf : f in s) : sInf s <= f
参数：s : Set (Subobject A)；f；hf : f in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subobject.arrow_congr`：arrow_congr {A : C} (X Y : Subobje
ct A) (h : X = Y) : eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.a
rrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
-/
theorem sInf_le {A : C} (s : Set (Subobject A)) (f) (hf : f ∈ s) : sInf s ≤ f := by
  fapply le_of_comm
  · exact (underlyingIso _).hom ≫
      Limits.limit.π (wideCospan s)
        (some ⟨equivShrink (Subobject A) f,
          Set.mem_image_of_mem (equivShrink (Subobject A)) hf⟩) ≫
      eqToHom (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _))
  · dsimp [sInf]
    simp only [Category.assoc, ← underlyingIso_hom_comp_eq_mk,
      Iso.cancel_iso_hom_left]
    convert! limit.w (wideCospan s) (WidePullbackShape.Hom.term _)
    simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.le_sInf** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：le_sInf {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in
 s, f <= g) : f <= sInf s
参数：s : Set (Subobject A)；f : Subobject A；k : forall g in s, f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Subobject.widePullbackι.eq_1`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.LocallySmall.{w, v₁, u
₁} C]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Subobject.leInfCone_π_app_none`：leInfCone_π_app_none {A :
 C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, f <= g) : (leI
nfCone s f k).π.app none = f.arrow
-/
theorem le_sInf {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, f ≤ g) :
    f ≤ sInf s := by
  fapply le_of_comm
  · exact Limits.limit.lift _ (leInfCone s f k) ≫ (underlyingIso _).inv
  · dsimp [sInf]
    rw [assoc, underlyingIso_arrow, widePullbackι, limit.lift_π, leInfCone_π_app_none]
/-
**CategoryTheory.Subobject.completeSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Subobject`。
形式化陈述：completeSemilatticeInf {B : C} : CompleteSemilatticeInf (Subobject B) wher
e sInf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance completeSemilatticeInf {B : C} : CompleteSemilatticeInf (Subobject B) where
  sInf := sInf
  isGLB_sInf _ := ⟨sInf_le _, le_sInf _⟩

end Inf

section Sup

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]

/-- The universal morphism out of the coproduct of a set of subobjects,
after using `[WellPowered C]` to reindex by a small type.
-/
/-
**CategoryTheory.Subobject.smallCoproductDesc** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：smallCoproductDesc {A : C} (s : Set (Subobject A))
参数：s : Set (Subobject A)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The universal morphism out of the coproduct of a set of subobjects,
after using `[WellPowered C]` to reindex by a small type.
-/
def smallCoproductDesc {A : C} (s : Set (Subobject A)) :=
  Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow

variable [HasImages C]

/-- When `[WellPowered C] [HasImages C] [HasCoproducts C]`,
`Subobject A` has arbitrary supremums. -/
/-
**CategoryTheory.Subobject.sSup** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobj
ect`。
形式化陈述：sSup {A : C} (s : Set (Subobject A)) : Subobject A
参数：s : Set (Subobject A)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
When `[WellPowered C] [HasImages C] [HasCoproducts C]`,
`Subobject A` has arbitrary supremums.
-/
def sSup {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (image.ι (smallCoproductDesc s))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.le_sSup** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：le_sSup {A : C} (s : Set (Subobject A)) (f) (hf : f in s) : f <= sSup s
参数：s : Set (Subobject A)；f；hf : f in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Subobject.arrow_congr`：arrow_congr {A : C} (X Y : Subobje
ct A) (h : X = Y) : eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.a
rrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_sSup {A : C} (s : Set (Subobject A)) (f) (hf : f ∈ s) : f ≤ sSup s := by
  fapply le_of_comm
  · refine eqToHom ?_ ≫ Sigma.ι _ ⟨equivShrink (Subobject A) f, by simpa [Set.mem_image] using hf⟩
      ≫ factorThruImage _ ≫ (underlyingIso _).inv
    exact (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
  · simp [sSup, smallCoproductDesc]
/-
**CategoryTheory.Subobject.symm_apply_mem_iff_mem_image** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Subobject`。
形式化陈述：symm_apply_mem_iff_mem_image {α β : Type*} (e : α ≃ β) (s : Set α) (x : β)
 : e.symm x in s ↔ x in e '' s
参数：e : α ≃ β；s : Set α；x : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_mem_iff_mem_image {α β : Type*} (e : α ≃ β) (s : Set α) (x : β) :
    e.symm x ∈ s ↔ x ∈ e '' s :=
  ⟨fun h => ⟨e.symm x, h, by simp⟩, by
    rintro ⟨a, m, rfl⟩
    simpa using m⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.sSup_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：sSup_le {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in
 s, g <= f) : sSup s <= f
参数：s : Set (Subobject A)；f : Subobject A；k : forall g in s, g <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Subobject.underlying_arrow`：underlying_arrow {X : C} {Y Z
 : Subobject X} (f : Y ⟶ Z) : underlying.map f ≫ arrow Z = arrow Y
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
-/
theorem sSup_le {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, g ≤ f) :
    sSup s ≤ f := by
  fapply le_of_comm
  · refine (underlyingIso _).hom ≫ image.lift ⟨_, f.arrow, ?_, ?_⟩
    · refine Sigma.desc ?_
      rintro ⟨g, m⟩
      refine underlying.map (homOfLE (k _ ?_))
      simpa using m
    · ext
      dsimp [smallCoproductDesc]
      simp
  · dsimp [sSup]
    rw [assoc, image.lift_fac, underlyingIso_hom_comp_eq_mk]
/-
**CategoryTheory.Subobject.completeSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Subobject`。
形式化陈述：completeSemilatticeSup {B : C} : CompleteSemilatticeSup (Subobject B) wher
e sSup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance completeSemilatticeSup {B : C} : CompleteSemilatticeSup (Subobject B) where
  sSup := sSup
  isLUB_sSup _ := ⟨le_sSup _, sSup_le _⟩

end Sup

section CompleteLattice

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasWidePullbacks.{w} C]
  [HasImages C] [HasCoproducts.{w} C] [InitialMonoClass C]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} : CompleteLattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup, Subobject.boundedOrder,
    Subobject.completeSemilatticeInf, Subobject.completeSemilatticeSup with }

end CompleteLattice

/-
**CategoryTheory.Subobject.subsingleton_of_isInitial** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Subobject`。
形式化陈述：subsingleton_of_isInitial {X : C} (hX : IsInitial X) : Subsingleton (Subob
ject X)
参数：hX : IsInitial X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用引理 `CategoryTheory.Subobject.mk_surjective`：mk_surjective {X : C} (S : Subob
ject X) : exists (A : C) (i : A ⟶ X) (_ : Mono i), S = Subobject.mk i
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma subsingleton_of_isInitial {X : C} (hX : IsInitial X) : Subsingleton (Subobject X) := by
  suffices ∀ (S : Subobject X), S = .mk (𝟙 _) from ⟨by simp [this]⟩
  intro S
  obtain ⟨A, i, _, rfl⟩ := S.mk_surjective
  have fac : hX.to A ≫ i = 𝟙 X := hX.hom_ext _ _
  let e : A ≅ X :=
    { hom := i
      inv := hX.to A
      hom_inv_id := by rw [← cancel_mono i, assoc, fac, id_comp, comp_id]
      inv_hom_id := fac }
  exact mk_eq_mk_of_comm i (𝟙 X) e (by simp [e])
/-
**CategoryTheory.Subobject.subsingleton_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Subobject`。
形式化陈述：subsingleton_of_isZero {X : C} (hX : IsZero X) : Subsingleton (Subobject X
)
参数：hX : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subobject.subsingleton_of_isInitial`：subsingleton_of_isIn
itial {X : C} (hX : IsInitial X) : Subsingleton (Subobject X)
-/
lemma subsingleton_of_isZero {X : C} (hX : IsZero X) : Subsingleton (Subobject X) :=
  subsingleton_of_isInitial hX.isInitial

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

/-- A nonzero object has nontrivial subobject lattice. -/
/-
**CategoryTheory.Subobject.nontrivial_of_not_isZero** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Subobject`。
形式化陈述：nontrivial_of_not_isZero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X
)
参数：h : ¬IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instMono`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
{X : C}   (f : 0 ⟶ X), CategoryThe…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
A nonzero object has nontrivial subobject lattice.
-/
theorem nontrivial_of_not_isZero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X) :=
  ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (isZero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩

end ZeroObject

section SubobjectSubobject

set_option backward.isDefEq.respectTransparency.types false in
/-- The subobject lattice of a subobject `Y` is order isomorphic to the interval `Set.Iic Y`. -/
/-
**CategoryTheory.Subobject.subobjectOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：subobjectOrderIso {X : C} (Y : Subobject X) : Subobject (Y : C) ≃o Set.Iic
 Y where toFun Z
参数：Y : Subobject X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subobject lattice of a subobject `Y` is order isomorphic to the interval `Se
t.Iic Y`.
-/
def subobjectOrderIso {X : C} (Y : Subobject X) : Subobject (Y : C) ≃o Set.Iic Y where
  toFun Z :=
    ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr (le_of_comm ((underlyingIso _).hom ≫ Z.arrow) (by simp))⟩
  invFun Z := Subobject.mk (ofLE _ _ Z.2)
  left_inv Z := mk_eq_of_comm _ (underlyingIso _) (by cat_disch)
  right_inv Z := Subtype.ext (mk_eq_of_comm _ (underlyingIso _) (by simp [← Iso.eq_inv_comp]))
  map_rel_iff' {W Z} := by
    dsimp
    constructor
    · intro h
      exact le_of_comm (((underlyingIso _).inv ≫ ofLE _ _ (Subtype.mk_le_mk.mp h) ≫
        (underlyingIso _).hom)) (by cat_disch)
    · intro h
      exact Subtype.mk_le_mk.mpr (le_of_comm
        ((underlyingIso _).hom ≫ ofLE _ _ h ≫ (underlyingIso _).inv) (by simp))

end SubobjectSubobject

end Subobject

end CategoryTheory

