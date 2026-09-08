/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.FinitaryExtensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive`: The initial object
  in extensive categories is strict.
- `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.finitaryExtensive`: The category of types is extensive.
- `CategoryTheory.FinitaryExtensive_TopCat`:
  The category `Top` is extensive.
- `CategoryTheory.FinitaryExtensive_functor`: The category `C ⥤ D` is extensive if `D`
  has all pullbacks and is extensive.
- `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`: Finite coproducts in a
  finitary extensive category are van Kampen.

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/

@[expose] public section

open CategoryTheory.Limits Topology

namespace CategoryTheory

universe v' u' v u v'' u''

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {D : Type u''} [Category.{v''} D]

section Extensive

variable {X Y : C}

/-- A category has pullback of inclusions if it has all pullbacks along coproduct injections. -/
/-
**CategoryTheory.HasPullbacksOfInclusions** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasBinaryCoproducts C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has pullback of inclusions if it has all pullbacks along coproduct in
jections.
-/
class HasPullbacksOfInclusions (C : Type u) [Category.{v} C] [HasBinaryCoproducts C] : Prop where
  [hasPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]

attribute [instance] HasPullbacksOfInclusions.hasPullbackInl

/--
A functor preserves pullback of inclusions if it preserves all pullbacks along coproduct injections.
-/
/-
**CategoryTheory.PreservesPullbacksOfInclusions** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D → [CategoryTheory.Limits.HasBinaryCoproducts C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor preserves pullback of inclusions if it preserves all pullbacks along c
oproduct injections.
-/
class PreservesPullbacksOfInclusions {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) [HasBinaryCoproducts C] where
  [preservesPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]

attribute [instance] PreservesPullbacksOfInclusions.preservesPullbackInl

/-- A category is (finitary) pre-extensive if it has finite coproducts,
and binary coproducts are universal. -/
/-
**CategoryTheory.FinitaryPreExtensive** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is (finitary) pre-extensive if it has finite coproducts,
and binary coproducts are universal.
-/
class FinitaryPreExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen -/
  universal' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsUniversalColimit c

attribute [instance] FinitaryPreExtensive.hasFiniteCoproducts
attribute [instance] FinitaryPreExtensive.hasPullbacksOfInclusions

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen. -/
/-
**CategoryTheory.FinitaryExtensive** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen.
-/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen -/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c

attribute [instance] FinitaryExtensive.hasFiniteCoproducts
attribute [instance] FinitaryExtensive.hasPullbacksOfInclusions
/-
**CategoryTheory.FinitaryExtensive.vanKampen** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.F
initaryExtensive C]   {F : CategoryTheory.Functor (CategoryTheory.Discrete Categ
oryTheory.Limits.WalkingPair) C}   (c : CategoryTheory.Limits.Cocone F) (hc : Ca
tegoryTheory.Limits.IsColimit c), CategoryTheory.IsVanKampenColimit c
参数：CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair；c : CategoryTheory.
Limits.Cocone F；hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.FinitaryExtensive.van_kampen'`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive C] {X Y 
: C}   (c : CategoryTheory.Limits.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X, Y]
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc

namespace HasPullbacksOfInclusions

/-
**CategoryTheory.HasPullbacksOfInclusions.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.HasPullbacksOfInclusions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasBinaryCoproducts C] [HasPullbacks C] :
    HasPullbacksOfInclusions C := ⟨⟩

variable [HasBinaryCoproducts C] [HasPullbacksOfInclusions C] {X Y Z : C} (f : Z ⟶ X ⨿ Y)
/-
**CategoryTheory.HasPullbacksOfInclusions.preservesPullbackInl'** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.HasPullbacksOfInclusions`。
形式化陈述：preservesPullbackInl' : HasPullback f coprod.inl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.HasPullbacksOfInclusions.hasPullbackInl`：∀ {C : Type u} {
inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasBina
ryCoproducts C}   [self : CategoryTheory.Has…
-/
instance preservesPullbackInl' :
    HasPullback f coprod.inl :=
  hasPullback_symmetry _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.HasPullbacksOfInclusions.hasPullbackInr'** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.HasPullbacksOfInclusions`。
形式化陈述：hasPullbackInr' : HasPullback f coprod.inr
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.coprod.braiding_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts 
C]   (P Q : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprod.desc_inl_inr`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yCoproduct X Y],   CategoryTheo…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
instance hasPullbackInr' :
    HasPullback f coprod.inr := by
  have : IsPullback (𝟙 _) (f ≫ (coprod.braiding X Y).hom) f (coprod.braiding Y X).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := (IsPullback.of_hasPullback (f ≫ (coprod.braiding X Y).hom) coprod.inl).paste_horiz this
  simp only [coprod.braiding_hom, Category.comp_id, colimit.ι_desc,
    BinaryCofan.ι_app_left, BinaryCofan.mk_inl] at this
  exact ⟨⟨⟨_, this.isLimit⟩⟩⟩
/-
**CategoryTheory.HasPullbacksOfInclusions.hasPullbackInr** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.HasPullbacksOfInclusions`。
形式化陈述：hasPullbackInr : HasPullback coprod.inr f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
-/
instance hasPullbackInr :
    HasPullback coprod.inr f :=
  hasPullback_symmetry _ _

end HasPullbacksOfInclusions

namespace PreservesPullbacksOfInclusions

variable {D : Type*} [Category* D] [HasBinaryCoproducts C] (F : C ⥤ D)

noncomputable
/-
**CategoryTheory.PreservesPullbacksOfInclusions.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreservesPullbacksOfInclusions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [PreservesLimitsOfShape WalkingCospan F] :
    PreservesPullbacksOfInclusions F := ⟨⟩

variable [PreservesPullbacksOfInclusions F] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

noncomputable
/-
**CategoryTheory.PreservesPullbacksOfInclusions.preservesPullbackInl'** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.PreservesPullbacksOfInclusions`。
形式化陈述：preservesPullbackInl' : PreservesLimit (cospan f coprod.inl) F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesPullback_symmetry`：preservesPullback_symm
etry : PreservesLimit (cospan g f) G where preserves {c} hc
· 使用定理 `CategoryTheory.PreservesPullbacksOfInclusions.preservesPullbackInl`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {ins
t_1 : CategoryTheory.Category.{v_2, u_2} D} {F : Categor…
-/
instance preservesPullbackInl' :
    PreservesLimit (cospan f coprod.inl) F :=
  preservesPullback_symmetry _ _ _

set_option backward.isDefEq.respectTransparency false in
noncomputable
/-
**CategoryTheory.PreservesPullbacksOfInclusions.preservesPullbackInr'** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.PreservesPullbacksOfInclusions`。
形式化陈述：preservesPullbackInr' : PreservesLimit (cospan f coprod.inr) F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.coprod.braiding_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts 
C]   (P Q : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.coprod.braiding_inv`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts 
C]   (P Q : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprod.desc_inl_inr`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yCoproduct X Y],   CategoryTheo…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance preservesPullbackInr' :
    PreservesLimit (cospan f coprod.inr) F := by
  apply preservesLimit_of_iso_diagram (K₁ := cospan (f ≫ (coprod.braiding X Y).hom) coprod.inl)
  apply cospanExt (Iso.refl _) (Iso.refl _) (coprod.braiding X Y).symm <;> simp

noncomputable
/-
**CategoryTheory.PreservesPullbacksOfInclusions.preservesPullbackInr** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.PreservesPullbacksOfInclusions`。
形式化陈述：preservesPullbackInr : PreservesLimit (cospan coprod.inr f) F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesPullback_symmetry`：preservesPullback_symm
etry : PreservesLimit (cospan g f) G where preserves {c} hc
-/
instance preservesPullbackInr :
    PreservesLimit (cospan coprod.inr f) F :=
  preservesPullback_symmetry _ _ _

end PreservesPullbacksOfInclusions

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) FinitaryExtensive.toFinitaryPreExtensive [FinitaryExtensive C] :
    FinitaryPreExtensive C :=
  ⟨fun c hc ↦ (FinitaryExtensive.van_kampen' c hc).isUniversal⟩
/-
**CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [Catego
ryTheory.FinitaryExtensive C]   {c : CategoryTheory.Limits.BinaryCofan X Y} (hc 
: CategoryTheory.Limits.IsColimit c), CategoryTheory.Mono c.inr
参数：hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.BinaryCofan.mono_inr_of_isVanKampen`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasInitial C] {X Y :
 C}   {c : CategoryTheory.Limits.BinaryC…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.FinitaryExtensive.vanKampen`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C]   {F : Categor
yTheory.Functor (CategoryTheory.…
-/
theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)
/-
**CategoryTheory.FinitaryExtensive.mono_inl_of_isColimit** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [Catego
ryTheory.FinitaryExtensive C]   {c : CategoryTheory.Limits.BinaryCofan X Y} (hc 
: CategoryTheory.Limits.IsColimit c), CategoryTheory.Mono c.inl
参数：hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y : C} [CategoryTheory.FinitaryExten
sive C]   {c : CategoryTheory.Limits.BinaryC…
-/
theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [FinitaryExtensive C] : MonoCoprod C where
  binaryCofan_inl _ _ _ hc := BinaryCofan.mono_inr_of_isVanKampen
    (FinitaryExtensive.vanKampen _ (BinaryCofan.isColimitFlip hc))
/-
**CategoryTheory.FinitaryExtensive.isPullback_initial_to_binaryCofan** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.FinitaryExtensive C]   {c : CategoryTheory.Limits.BinaryCofan 
X Y} (hc : CategoryTheory.Limits.IsColimit c),   CategoryTheory.IsPullback     (
CategoryTheory.Limits.initial.to       ((CategoryTheory.Limits.pair X Y).obj { a
s := CategoryTheory.Limits.WalkingPair.left }))     (CategoryTheory.Limits.initi
al.to       ((CategoryTheory.Limits.pair X Y).obj { as := CategoryTheory.Limits.
WalkingPair.right }))     c.inl c.inr
参数：hc : CategoryTheory.Limits.IsColimit c；CategoryTheory.Limits.initial.to      
 ((CategoryTheory.Limits.pair X Y).obj { as := CategoryTheory.Limits.WalkingPair
.left })；CategoryTheory.Limits.initial.to       ((CategoryTheory.Limits.pair X Y
).obj { as := CategoryTheory.Limits.WalkingPair.right })。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTh
eory.Limits.HasInitial C]   {c : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.FinitaryExtensive.vanKampen`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C]   {F : Categor
yTheory.Functor (CategoryTheory.…
-/
theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasStrictInitialObjects_of_finitaryPreExtensive
    [FinitaryPreExtensive C] : HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryPreExtensive.universal' _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.finitaryExtensive_iff_of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFini
teCoproducts C] [HasPullbacksOfInclusions C] (T : C) (HT : IsTerminal T) (c₀ : B
inaryCofan T T) (hc₀ : IsColimit c₀) : FinitaryExtensive C ↔ IsVanKampenColimit 
c₀
参数：C : Type u；T : C；HT : IsTerminal T；c₀ : BinaryCofan T T；hc₀ : IsColimit c₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.FinitaryExtensive.van_kampen'`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive C] {X Y 
: C}   (c : CategoryTheory.Limits.…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsPullback.paste_vert_iff`：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂
₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ 
⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [HasPullbacksOfInclusions C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine ⟨fun H => H.van_kampen' c₀ hc₀, fun H => ?_⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of% hX, hd, Category.assoc])
      (by rw [← reassoc_of% hY, hd', Category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.types.finitaryExtensive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.types`。
形式化陈述：CategoryTheory.FinitaryExtensive (Type u)
参数：Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.finitaryExtensive_iff_of_isTerminal`：finitaryExtensive_if
f_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C] [HasPullba
cksOfInclusions C] (T : C) (HT : IsTermi…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.HasPullbacksOfInclusions.instOfHasPullbacks`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
BinaryCoproducts C]   [CategoryTheory.Limits.Has…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.BinaryCofan.isVanKampen_mk`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (c : CategoryTheory.Limits.BinaryCofan X Y
)   (cofans : (X Y : C) → Categ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
（共 44 条，此处仅展示前 30 条）
-/
instance types.finitaryExtensive : FinitaryExtensive (Type u) := by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPUnit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intro _ _ _ _ f hαX hαY
    constructor
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        rcases h : s.fst x with val | val
        · simp
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val :).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨↾(l), ?_, Types.isTerminalPUnit.hom_ext _ _, fun {l'} h₁ _ => ?_⟩
      · ext x
        exact (hl x).symm
      · ext x
        exact hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        rcases h : s.fst x with val | val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val :).symm
        · simp
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨↾l, ?_, Types.isTerminalPUnit.hom_ext _ _, fun {l'} h₁ _ => ?_⟩
      · ext x
        exact (hl x).symm
      · ext x
        exact hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm
  · intro Z f
    dsimp [Limits.Types.binaryCoproductCocone]
    have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit := by
      intro x
      rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      exacts [Or.inl rfl, Or.inr rfl]
    let eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, by convert! p.2⟩, fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl,
        fun _ => by ext; rfl⟩
    let eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩,
        fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
    fapply BinaryCofan.isColimitMk
    · exact fun s => ↾fun x => dite _ (fun h => s.inl <| eX.symm ⟨x, h⟩)
        fun h => s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, _⟩
      dsimp
      split_ifs with h <;> tauto
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, hx⟩
      dsimp
      split_ifs with h
      · cases h.symm.trans hx
      · rfl
    · intro s m e₁ e₂
      ext x
      simp only [TypeCat.Fun.toFun_apply, Types.binaryCoproductCocone_pt, pair_obj_left,
        Functor.const_obj_obj, pair_obj_right, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      split_ifs
      · rw [← e₁]
        rfl
      · rw [← e₂]
        rfl

section TopCat

/-- (Implementation) An auxiliary lemma for the proof that `TopCat` is finitary extensive. -/
/-
**CategoryTheory.finitaryExtensiveTopCatAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：finitaryExtensiveTopCatAux (Z : TopCat.{u}) (f : Z ⟶ TopCat.of (PUnit.{u +
 1} oplus PUnit.{u + 1})) : IsColimit (BinaryCofan.mk (TopCat.pullbackFst f (Top
Cat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl) (TopCat.pullbackFst f 
(TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr))
参数：Z : TopCat.{u}；f : Z ⟶ TopCat.of (PUnit.{u + 1} oplus PUnit.{u + 1})。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) An auxiliary lemma for the proof that `TopCat` is finitary exte
nsive.
-/
noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (PUnit.{u + 1} ⊕ PUnit.{u + 1})) :
    IsColimit (BinaryCofan.mk
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) := by
  have h₁ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inl) =
      f ⁻¹' Set.range Sum.inl := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  have h₂ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inr) =
      f ⁻¹' Set.range Sum.inr := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  refine ((TopCat.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩).some
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert! f.hom.2.1 _ isOpen_range_inl
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert! f.hom.2.1 _ isOpen_range_inr
  · convert! Set.isCompl_range_inl_range_inr.preimage f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.finitaryExtensive_TopCat** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：finitaryExtensive_TopCat : FinitaryExtensive TopCat.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.finitaryExtensive_iff_of_isTerminal`：finitaryExtensive_if
f_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C] [HasPullba
cksOfInclusions C] (T : C) (HT : IsTermi…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.HasPullbacksOfInclusions.instOfHasPullbacks`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
BinaryCoproducts C]   [CategoryTheory.Limits.Has…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.BinaryCofan.isVanKampen_mk`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (c : CategoryTheory.Limits.BinaryCofan X Y
)   (cofans : (X Y : C) → Categ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inl
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
（共 31 条，此处仅展示前 30 条）
-/
instance finitaryExtensive_TopCat : FinitaryExtensive TopCat.{u} := by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constructor
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        rcases h : s.fst x with val | val
        · exact ⟨val, rfl, fun y h => Sum.inl_injective h.symm⟩
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val :).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨TopCat.ofHom ⟨l, ?_⟩, TopCat.ext fun a => (hl a).symm,
        TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => TopCat.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (IsEmbedding.inl (X := X') (Y := Y')).isInducing.continuous_iff.mpr
      convert! s.fst.hom.2 using 1
      exact (funext hl).symm
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        rcases h : s.fst x with val | val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val :).symm
        · exact ⟨val, rfl, fun y h => Sum.inr_injective h.symm⟩
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨TopCat.ofHom ⟨l, ?_⟩, TopCat.ext fun a => (hl a).symm,
        TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          TopCat.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (IsEmbedding.inr (X := X') (Y := Y')).isInducing.continuous_iff.mpr
      convert! s.fst.hom.2 using 1
      exact (funext hl).symm
  · intro Z f
    exact finitaryExtensiveTopCatAux Z f

end TopCat

section Functor

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.finitaryExtensive_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：finitaryExtensive_of_reflective [HasFiniteCoproducts D] [HasPullbacksOfInc
lusions D] [FinitaryExtensive C] {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.F
ull] [Gr.Faithful] [forall X Y (f : X ⟶ Gl.obj Y), HasPullback (Gr.map f) (adj.u
nit.app Y)] [forall X Y (f : X ⟶ Gl.obj Y), PreservesLimit (cospan (Gr.map f) (a
dj.unit.app Y)) Gl] [PreservesPullbacksOfInclusions Gl] : FinitaryExtensive D
参数：adj : Gl ⊣ Gr；f : X ⟶ Gl.obj Y；Gr.map f；adj.unit.app Y；f : X ⟶ Gl.obj Y；cospa
n (Gr.map f) (adj.unit.app Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso_iff`：∀ {J : Type v'} 
[inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsVanKampenColimit.map_reflective`：∀ {J : Type v'} [inst 
: CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {D : Type u_2} [inst_…
· 使用定理 `CategoryTheory.FinitaryExtensive.vanKampen`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C]   {F : Categor
yTheory.Functor (CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem finitaryExtensive_of_reflective
    [HasFiniteCoproducts D] [HasPullbacksOfInclusions D] [FinitaryExtensive C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [∀ X Y (f : X ⟶ Gl.obj Y), HasPullback (Gr.map f) (adj.unit.app Y)]
    [∀ X Y (f : X ⟶ Gl.obj Y), PreservesLimit (cospan (Gr.map f) (adj.unit.app Y)) Gl]
    [PreservesPullbacksOfInclusions Gl] :
    FinitaryExtensive D := by
  have : PreservesColimitsOfSize Gl := adj.leftAdjoint_preservesColimits
  constructor
  intro X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : ∀ (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (colimit.cocone (pair X Y ⋙ Gr)).pt),
        PreservesLimit (cospan f ((colimit.cocone (pair X Y ⋙ Gr)).ι.app i)) Gl := by
    have : pair X Y ⋙ Gr = pair (Gr.obj X) (Gr.obj Y) := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    rw [this]
    rintro Z ⟨_ | _⟩ f <;> dsimp <;> infer_instance
  refine ((FinitaryExtensive.vanKampen _ (colimit.isColimit <| pair X Y ⋙ _)).map_reflective
    adj).of_iso (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc
/-
**CategoryTheory.finitaryExtensive_functor** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：finitaryExtensive_functor [HasPullbacks C] [FinitaryExtensive C] : Finitar
yExtensive (D ⥤ C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.HasPullbacksOfInclusions.instOfHasPullbacks`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
BinaryCoproducts C]   [CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.isVanKampenColimit_of_evaluation`：isVanKampenColimit_of_e
valuation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D) (c : Cocone 
F) (hc : forall x : C, IsVanKampenCol…
· 使用定理 `CategoryTheory.FinitaryExtensive.vanKampen`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C]   {F : Categor
yTheory.Functor (CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance finitaryExtensive_functor [HasPullbacks C] [FinitaryExtensive C] :
    FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
    FinitaryExtensive.vanKampen _ <| isColimitOfPreserves _ hc⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C} [Category* C] {D} [Category* D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f] : PreservesLimit (cospan f g) F :=
  have := hasPullback_of_left_iso f g
  preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv _ pullback.condition).symm
      (IsPullback.of_vert_isIso ⟨by simp only [← F.map_comp, pullback.condition]⟩).isLimit)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C} [Category* C] {D} [Category* D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] : PreservesLimit (cospan f g) F :=
  preservesPullback_symmetry _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.finitaryExtensive_of_preserves_and_reflects** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory`。
形式化陈述：finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive
 D] [HasFiniteCoproducts C] [HasPullbacksOfInclusions C] [PreservesPullbacksOfIn
clusions F] [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (D
iscrete WalkingPair) F] [ReflectsColimitsOfShape (Discrete WalkingPair) F] : Fin
itaryExtensive C
参数：F : C ⥤ D；Discrete WalkingPair；Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_mapCocone`：∀ {J : Type v'} [inst : 
CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {D : Type u_2} [inst_…
· 使用定理 `CategoryTheory.instPreservesLimitWalkingCospanCospanOfIsIso_1`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.FinitaryExtensive.vanKampen`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C]   {F : Categor
yTheory.Functor (CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
    [PreservesPullbacksOfInclusions F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C := by
  constructor
  intro X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_ | _⟩ <;> dsimp <;> infer_instance
  refine (FinitaryExtensive.vanKampen _
    (isColimitOfPreserves F (coprodIsCoprod X Y))).of_mapCocone F
/-
**CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [Finit
aryExtensive D] [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape
 WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F] [F.Reflect
sIsomorphisms] : FinitaryExtensive C
参数：F : C ⥤ D；Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms`：r
eflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphis
ms] [HasColimitsOfShape J C] [PreservesColimitsOfShape J G]…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.finitaryExtensive_of_preserves_and_reflects`：finitaryExte
nsive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D] [HasFiniteCopr
oducts C] [HasPullbacksOfInclusions C] [Preserve…
· 使用定理 `CategoryTheory.HasPullbacksOfInclusions.instOfHasPullbacks`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
BinaryCoproducts C]   [CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.PreservesPullbacksOfInclusions.instOfPreservesLimitsOfSha
peWalkingCospan`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : T
ype u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
-/
theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [F.ReflectsIsomorphisms] :
    FinitaryExtensive C := by
  have : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F

end Functor

section FiniteCoproducts

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.F
initaryPreExtensive C] {n : ℕ}   {F : CategoryTheory.Functor (CategoryTheory.Dis
crete (Fin n)) C} {c : CategoryTheory.Limits.Cocone F}   (hc : CategoryTheory.Li
mits.IsColimit c), CategoryTheory.IsUniversalColimit c
参数：CategoryTheory.Discrete (Fin n)；hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsVanKampenColimit.isUniversal`：∀ {J : Type v'} [inst : C
ategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Categor
y.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.isVanKampenColimit_of_isEmpty`：isVanKampenColimit_of_isEm
pty [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C} (c : Cocone F) (hc : IsC
olimit c) : IsVanKampenColimit c
· 使用定理 `CategoryTheory.hasStrictInitialObjects_of_finitaryPreExtensive`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasStrictInitialOb…
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `CategoryTheory.IsUniversalColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.isUniversalColimit_extendCofan`：isUniversalColimit_extend
Cofan {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofan fun i : Fin n => f i.succ} {c
₂ : BinaryCofan (f 0) c₁.pt} (t₁ : …
· 使用定理 `CategoryTheory.FinitaryPreExtensive.universal'`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExtensive C] 
{X Y : C}   (c : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasPullbacksOfInclusions`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPr
eExtensive C],   CategoryTheory.HasPullbacksOfIncl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin [FinitaryPreExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  | succ n IH =>
    refine IsUniversalColimit.of_iso (@isUniversalColimit_extendCofan _ _ _ _ _ _
      (IH _ (coproductIsCoproduct _)) (FinitaryPreExtensive.universal' _ (coprodIsCoprod _ _)) ?_)
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    · dsimp
      infer_instance
/-
**CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.F
initaryPreExtensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTheory.Functor (
CategoryTheory.Discrete ι) C} {c : CategoryTheory.Limits.Cocone F}   (hc : Categ
oryTheory.Limits.IsColimit c), CategoryTheory.IsUniversalColimit c
参数：CategoryTheory.Discrete ι；hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsUniversalColimit.whiskerEquivalence_iff`：∀ {J : Type v'
} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {K : Type u_3} [inst_…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryP
reExtensive C] {n : ℕ}   {F : CategoryTheory.Functor (Cate…
-/
theorem FinitaryPreExtensive.isUniversal_finiteCoproducts [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsUniversalColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts_Fin** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.F
initaryExtensive C] {n : ℕ}   {F : CategoryTheory.Functor (CategoryTheory.Discre
te (Fin n)) C} {c : CategoryTheory.Limits.Cocone F}   (hc : CategoryTheory.Limit
s.IsColimit c), CategoryTheory.IsVanKampenColimit c
参数：CategoryTheory.Discrete (Fin n)；hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.isVanKampenColimit_of_isEmpty`：isVanKampenColimit_of_isEm
pty [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C} (c : Cocone F) (hc : IsC
olimit c) : IsVanKampenColimit c
· 使用定理 `CategoryTheory.hasStrictInitialObjects_of_finitaryPreExtensive`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasStrictInitialOb…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.isVanKampenColimit_extendCofan`：isVanKampenColimit_extend
Cofan {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofan fun i : Fin n => f i.succ} {c
₂ : BinaryCofan (f 0) c₁.pt} (t₁ : …
· 使用定理 `CategoryTheory.FinitaryExtensive.van_kampen'`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive C] {X Y 
: C}   (c : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasPullbacksOfInclusions`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExten
sive C],   CategoryTheory.HasPullbacksOfInclusi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem FinitaryExtensive.isVanKampen_finiteCoproducts_Fin [FinitaryExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact isVanKampenColimit_of_isEmpty _ hc
  | succ n IH =>
    apply IsVanKampenColimit.of_iso _
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    apply @isVanKampenColimit_extendCofan _ _ _ _ _ _ _ _ ?_
    · apply IH
      exact coproductIsCoproduct _
    · apply FinitaryExtensive.van_kampen'
      exact coprodIsCoprod _ _
    · dsimp
      infer_instance
/-
**CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.F
initaryExtensive C] {ι : Type u_1} [Finite ι]   {F : CategoryTheory.Functor (Cat
egoryTheory.Discrete ι) C} {c : CategoryTheory.Limits.Cocone F}   (hc : Category
Theory.Limits.IsColimit c), CategoryTheory.IsVanKampenColimit c
参数：CategoryTheory.Discrete ι；hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.whiskerEquivalence_iff`：∀ {J : Type v'
} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {K : Type u_3} [inst_…
· 使用定理 `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts_Fin`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExte
nsive C] {n : ℕ}   {F : CategoryTheory.Functor (Categor…
-/
theorem FinitaryExtensive.isVanKampen_finiteCoproducts [FinitaryExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.FinitaryPreExtensive.hasPullbacks_of_is_coproduct** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.F
initaryPreExtensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTheory.Functor (
CategoryTheory.Discrete ι) C} {c : CategoryTheory.Limits.Cocone F}   (hc : Categ
oryTheory.Limits.IsColimit c) (i : CategoryTheory.Discrete ι) {X : C}   (g : X ⟶
 ((CategoryTheory.Functor.const (CategoryTheory.Discrete ι)).obj c.pt).obj i),  
 CategoryTheory.Limits.HasPullback g (c.ι.app i)
参数：CategoryTheory.Discrete ι；hc : CategoryTheory.Limits.IsColimit c；i : Category
Theory.Discrete ι；g : X ⟶ ((CategoryTheory.Functor.const (CategoryTheory.Discret
e ι)).obj c.pt).obj i；c.ι.app i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_inv`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
（共 38 条，此处仅展示前 30 条）
-/
lemma FinitaryPreExtensive.hasPullbacks_of_is_coproduct [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) {X : C}
    (g : X ⟶ _) : HasPullback g (c.ι.app i) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
  { hom := Sigma.desc (fun j ↦ if h : j = i then eqToHom (congr_arg f h) ≫ coprod.inl else
      Sigma.ι (fun j : ({i}ᶜ : Set ι) ↦ f j) ⟨j, h⟩ ≫ coprod.inr)
    inv := coprod.desc (Sigma.ι f i) (Sigma.desc fun j ↦ Sigma.ι f j)
    hom_inv_id := by cat_disch
    inv_hom_id := by
      ext j
      · simp
      · simp only [coprod.desc_comp, colimit.ι_desc, Cofan.mk_ι_app,
          eqToHom_refl, Category.id_comp, dite_true, BinaryCofan.ι_app_right,
          BinaryCofan.mk_inr, colimit.ι_desc_assoc, Discrete.functor_obj, Category.comp_id]
        exact dif_neg j.prop }
  let e' : c.pt ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
    hc.coconePointUniqueUpToIso (getColimitCocone _).2 ≪≫ e
  have : coprod.inl ≫ e'.inv = c.ι.app ⟨i⟩ := by
    simp only [e, e', Iso.trans_inv, coprod.desc_comp, colimit.ι_desc,
      BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    exact colimit.comp_coconePointUniqueUpToIso_inv _ _
  clear_value e'
  rw [← this]
  have : IsPullback (𝟙 _) (g ≫ e'.hom) g e'.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨⟨⟨_, ((IsPullback.of_hasPullback (g ≫ e'.hom) coprod.inl).paste_horiz this).isLimit⟩⟩⟩
/-
**CategoryTheory.FinitaryExtensive.mono_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FinitaryExtensive.mono_ι [FinitaryExtensive C] {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) :
    Mono (c.ι.app i) :=
  mono_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FinitaryExtensive C] {ι : Type*} [Finite ι] (X : ι → C) (i : ι) :
    Mono (Sigma.ι X i) :=
  FinitaryExtensive.mono_ι (coproductIsCoproduct _) ⟨i⟩
/-
**CategoryTheory.FinitaryExtensive.isPullback_initial_to** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FinitaryExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.FinitaryExtensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTheory.Fun
ctor (CategoryTheory.Discrete ι) C} {c : CategoryTheory.Limits.Cocone F}   (hc :
 CategoryTheory.Limits.IsColimit c) (i j : CategoryTheory.Discrete ι),   i ≠ j →
     CategoryTheory.IsPullback (CategoryTheory.Limits.initial.to (F.obj i)) (Cat
egoryTheory.Limits.initial.to (F.obj j))       (c.ι.app i) (c.ι.app j)
参数：CategoryTheory.Discrete ι；hc : CategoryTheory.Limits.IsColimit c；i j : Catego
ryTheory.Discrete ι；CategoryTheory.Limits.initial.to (F.obj i)；CategoryTheory.Li
mits.initial.to (F.obj j)；c.ι.app i；c.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isPullback_initial_to_of_cofan_isVanKampen`：isPullback_in
itial_to_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C} {c
 : Cocone F} (hc : IsVanKampenColimit c) (i j :…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensiv
e C] {ι : Type u_1} [Finite ι]   {F : CategoryTheor…
-/
lemma FinitaryExtensive.isPullback_initial_to [FinitaryExtensive C]
    {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i j : Discrete ι) (e : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) :=
  isPullback_initial_to_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) i j e
/-
**CategoryTheory.FinitaryExtensive.isPullback_initial_to_sigma_** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FinitaryExtensive.isPullback_initial_to_sigma_ι [FinitaryExtensive C] {ι : Type*} [Finite ι]
    (X : ι → C) (i j : ι) (e : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (Sigma.ι X i) (Sigma.ι X j) :=
  FinitaryExtensive.isPullback_initial_to (coproductIsCoproduct _) ⟨i⟩ ⟨j⟩
    (ne_of_apply_ne Discrete.as e)

-- TODO: generalize to arbitrary `ι` if `HasCoproductsOfShape ι C`.
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [FinitaryExtensive C] {ι : Type*} [Finite ι] :
    CoproductsOfShapeDisjoint C ι where
  coproductDisjoint X := by
    refine ⟨fun {c} hc i j e s hs ↦ ?_, fun hc i ↦ FinitaryExtensive.mono_ι hc ⟨i⟩⟩
    exact ⟨initialIsInitial.ofIso ((FinitaryExtensive.isPullback_initial_to hc ⟨i⟩ ⟨j⟩
      (by simpa)).isoIsPullback _ _ (IsPullback.of_isLimit hs))⟩
/-
**CategoryTheory.FinitaryPreExtensive.hasPullbacks_of_inclusions** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.FinitaryPreExtensive C] {X Z : C}   {α : Type u_1} (f : X ⟶ Z) {Y : α → 
C} (i : (a : α) → Y a ⟶ Z) [inst_2 : Finite α]   [hi : CategoryTheory.IsIso (Cat
egoryTheory.Limits.Sigma.desc i)] (a : α), CategoryTheory.Limits.HasPullback f (
i a)
参数：f : X ⟶ Z；i : (a : α) → Y a ⟶ Z；CategoryTheory.Limits.Sigma.desc i；a : α；i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasPullbacks_of_is_coproduct`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryPreEx
tensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTh…
-/
instance FinitaryPreExtensive.hasPullbacks_of_inclusions [FinitaryPreExtensive C] {X Z : C}
    {α : Type*} (f : X ⟶ Z) {Y : (a : α) → C} (i : (a : α) → Y a ⟶ Z) [Finite α]
    [hi : IsIso (Sigma.desc i)] (a : α) : HasPullback f (i a) := by
  apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) (i := hi)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.FinitaryPreExtensive C] {α : Type}   [inst_2 : Finite α] {X : C} {Z : α 
→ C} (π : (a : α) → Z a ⟶ X) {Y : C} (f : Y ⟶ X)   (hπ : CategoryTheory.IsIso (C
ategoryTheory.Limits.Sigma.desc π)),   CategoryTheory.IsIso (CategoryTheory.Limi
ts.Sigma.desc fun x => CategoryTheory.Limits.pullback.fst f (π x))
参数：π : (a : α) → Z a ⟶ X；f : Y ⟶ X；hπ : CategoryTheory.IsIso (CategoryTheory.Lim
its.Sigma.desc π)；CategoryTheory.Limits.Sigma.desc fun x => CategoryTheory.Limit
s.pullback.fst f (π x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasPullbacks_of_inclusions`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Finita
ryPreExtensive C] {X Z : C}   {α : Type u_1} (f : X …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`：∀ {β
 : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : β → C}   
[inst_1 : CategoryTheory.Limits.HasCoproduct f] (c : Cat…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryPreEx
tensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTh…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_lef
t`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B 
: C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPullback.id_horiz`：id_horiz (f : X ⟶ Z) : IsPullback (𝟙
 X) f f (𝟙 Z)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
lemma FinitaryPreExtensive.isIso_sigmaDesc_fst [FinitaryPreExtensive C] {α : Type} [Finite α]
    {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X) {Y : C} (f : Y ⟶ X) (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _)) := by
  let c := (Cofan.mk _ ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [c]) (by simp [pullback.condition, c])
  exact pullback.isLimit _ _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over finite
coproducts, i.e., `∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`.
For an `IsPullback` version, see `FinitaryPreExtensive.isPullback_sigmaDesc`. -/
/-
**CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_map** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C]   [inst_2 : CategoryTheory.FinitaryPreExtensive C
] {ι : Type u_1} {ι' : Type u_2} [inst_3 : Finite ι]   [inst_4 : Finite ι'] {S :
 C} {X : ι → C} {Y : ι' → C} (f : (i : ι) → X i ⟶ S) (g : (i : ι') → Y i ⟶ S),  
 CategoryTheory.IsIso     (CategoryTheory.Limits.Sigma.desc fun p =>       Categ
oryTheory.Limits.pullback.map (f p.1) (g p.2) (CategoryTheory.Limits.Sigma.desc 
f)         (CategoryTheory.Limits.Sigma.desc g) (CategoryTheory.Limits.Sigma.ι X
 p.1) (CategoryTheory.Limits.Sigma.ι Y p.2)         (CategoryTheory.CategoryStru
ct.id S) ⋯ ⋯)
参数：f : (i : ι) → X i ⟶ S；g : (i : ι') → Y i ⟶ S；CategoryTheory.Limits.Sigma.desc
 fun p =>       CategoryTheory.Limits.pullback.map (f p.1) (g p.2) (CategoryTheo
ry.Limits.Sigma.desc f)         (CategoryTheory.Limits.Sigma.desc g) (CategoryTh
eory.Limits.Sigma.ι X p.1) (CategoryTheory.Limits.Sigma.ι Y p.2)         (Catego
ryTheory.CategoryStruct.id S) ⋯ ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`：∀ {β
 : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : β → C}   
[inst_1 : CategoryTheory.Limits.HasCoproduct f] (c : Cat…
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCon
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι' :
 Type u_4} {S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cof…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryPreEx
tensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …

--- 原说明 ---
If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over 
finite
coproducts, i.e., `∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`.
For an `IsPullback` version, see `FinitaryPreExtensive.isPullback_sigmaDesc`.
-/
instance FinitaryPreExtensive.isIso_sigmaDesc_map [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsIso (Sigma.desc fun (p : ι × ι') ↦
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)) := by
  let c : Cofan _ := Cofan.mk _ <| fun (p : ι × ι') ↦
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
      (a := Cofan.mk _ <| fun i ↦ Sigma.ι _ i) (b := Cofan.mk _ <| fun i ↦ Sigma.ι _ i)
      ?_ ?_ f g (Sigma.desc f) (Sigma.desc g) (fun i j ↦ (pullback.cone (f i) (g j)))
      (fun i j ↦ pullback.isLimit (f i) (g j)) (pullback.cone _ _) ?_ (Iso.refl _)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  · exact pullback.isLimit (Sigma.desc f) (Sigma.desc g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over finite
coproducts, i.e., `∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`.
For a variant, see `FinitaryPreExtensive.isIso_sigmaDesc_map`. -/
/-
**CategoryTheory.FinitaryPreExtensive.isPullback_sigmaDesc** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.FinitaryPreExtensive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C]   [inst_2 : CategoryTheory.FinitaryPreExtensive C
] {ι : Type u_1} {ι' : Type u_2} [inst_3 : Finite ι]   [inst_4 : Finite ι'] {S :
 C} {X : ι → C} {Y : ι' → C} (f : (i : ι) → X i ⟶ S) (g : (i : ι') → Y i ⟶ S),  
 CategoryTheory.IsPullback     (CategoryTheory.Limits.Sigma.desc fun p =>       
CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (f p.1) (
g p.2))         (CategoryTheory.Limits.Sigma.ι X p.1))     (CategoryTheory.Limit
s.Sigma.desc fun p =>       CategoryTheory.CategoryStruct.comp (CategoryTheory.L
imits.pullback.snd (f p.1) (g p.2))         (CategoryTheory.Limits.Sigma.ι Y p.2
))     (CategoryTheory.Limits.Sigma.desc f) (CategoryTheory.Limits.Sigma.desc g)
参数：f : (i : ι) → X i ⟶ S；g : (i : ι') → Y i ⟶ S；CategoryTheory.Limits.Sigma.desc
 fun p =>       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullba
ck.fst (f p.1) (g p.2))         (CategoryTheory.Limits.Sigma.ι X p.1)；CategoryTh
eory.Limits.Sigma.desc fun p =>       CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Limits.pullback.snd (f p.1) (g p.2))         (CategoryTheory.Limits.Sig
ma.ι Y p.2)；CategoryTheory.Limits.Sigma.desc f；CategoryTheory.Limits.Sigma.desc 
g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsUniversalColimit.isPullback_prod_of_isColimit`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι' : Type u_4} 
{S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cof…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.isUniversal_finiteCoproducts`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryPreEx
tensive C] {ι : Type u_1}   [Finite ι] {F : CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over 
finite
coproducts, i.e., `∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`.
For a variant, see `FinitaryPreExtensive.isIso_sigmaDesc_map`.
-/
lemma FinitaryPreExtensive.isPullback_sigmaDesc [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsPullback
      (Limits.Sigma.desc fun (p : ι × ι') ↦ pullback.fst (f p.1) (g p.2) ≫ Sigma.ι X p.1)
      (Limits.Sigma.desc fun (p : ι × ι') ↦ pullback.snd (f p.1) (g p.2) ≫ Sigma.ι Y p.2)
      (Limits.Sigma.desc f) (Limits.Sigma.desc g) := by
  convert!
    IsUniversalColimit.isPullback_prod_of_isColimit (d :=
      Cofan.mk _ (Sigma.ι fun (p : ι × ι') ↦ pullback (f p.1) (g p.2))) (hd :=
      coproductIsCoproduct (fun (p : ι × ι') ↦ pullback (f p.1) (g p.2))) (a :=
      Cofan.mk _ <| fun i ↦ Sigma.ι _ i) (b := Cofan.mk _ <| fun i ↦ Sigma.ι _ i) ?_ ?_ f g
      (Sigma.desc f) (Sigma.desc g) (fun i j ↦ IsPullback.of_hasPullback (f i) (g j))
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)

end FiniteCoproducts

end Extensive

end CategoryTheory

