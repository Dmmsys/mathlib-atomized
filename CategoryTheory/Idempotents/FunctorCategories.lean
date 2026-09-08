/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and functor categories

In this file we define an instance `functor_category_isIdempotentComplete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)` for all categories
`J` and `C`.

-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

open CategoryTheory.Limits

namespace CategoryTheory

namespace Idempotents

variable {J C : Type*} [Category* J] [Category* C] (P Q : Karoubi (J ⥤ C)) (f : P ⟶ Q) (X : J)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Idempotents.app_idem** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Idempotents`。
形式化陈述：app_idem : P.p.app X ≫ P.p.app X = P.p.app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
-/
theorem app_idem : P.p.app X ≫ P.p.app X = P.p.app X :=
  congr_app P.idem X

variable {P Q}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Idempotents.app_p_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Idempotents`。
形式化陈述：app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comp`：p_comp {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f
-/
theorem app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X :=
  congr_app (p_comp f) X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Idempotents.app_comp_p** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Idempotents`。
形式化陈述：app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Idempotents.Karoubi.comp_p`：comp_p {P Q : Karoubi C} (f :
 Hom P Q) : f.f ≫ Q.p = f.f
-/
theorem app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X :=
  congr_app (comp_p f) X

@[reassoc]
/-
**CategoryTheory.Idempotents.app_p_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Idempotents`。
形式化陈述：app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comm`：p_comm {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p
-/
theorem app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X :=
  congr_app (p_comm f) X

variable (J C)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Idempotents.functor_category_isIdempotentComplete** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：functor_category_isIdempotentComplete [IsIdempotentComplete C] : IsIdempot
entComplete (J ⥤ C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_a
nd_idempotent`：isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent : IsId
empotentComplete C ↔ forall (X : C) (p : X ⟶ X), p ≫ p = p -> HasEqualizer …
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.equalizer.lift.congr_simp`：∀ {C : Type u} {X Y : C
} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTh
eory.Limits.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.equalizer.lift_ι`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
instance functor_category_isIdempotentComplete [IsIdempotentComplete C] :
    IsIdempotentComplete (J ⥤ C) := by
  refine ⟨fun F p hp => ?_⟩
  have hC := (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance
  have : ∀ j : J, HasEqualizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the equalizer of the identity and `p.app j` on each object `(j : J)`. -/
  let Y : J ⥤ C :=
    { obj := fun j => Limits.equalizer (𝟙 _) (p.app j)
      map := fun {j j'} φ =>
        equalizer.lift (Limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
          (by rw [comp_id, assoc, p.naturality φ, ← assoc, ← Limits.equalizer.condition, comp_id]) }
  let i : Y ⟶ F :=
    { app := fun j => equalizer.ι _ _
      naturality := fun _ _ _ => by rw [equalizer.lift_ι] }
  let e : F ⟶ Y :=
    { app := fun j =>
        equalizer.lift (p.app j) (by simpa only [comp_id] using! (congr_app hp j).symm)
      naturality := fun j j' φ => equalizer.hom_ext (by simp [Y]) }
  use Y, i, e
  constructor
  · ext j
    dsimp
    rw [assoc, equalizer.lift_ι, ← equalizer.condition, id_comp, comp_id]
  · ext j
    simp [Y, i, e]
namespace KaroubiFunctorCategoryEmbedding

variable {J C}

set_option backward.isDefEq.respectTransparency.types false in
/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ Karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding`。
形式化陈述：obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where obj j
参数：P : Karoubi (J ⥤ C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ Karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`.
-/
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where
  obj j := ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        have h := congr_app P.idem j
        rw [NatTrans.comp_app] at h
        rw [reassoc_of% h, reassoc_of% h] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Tautological action on maps of the functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.map** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding`。
形式化陈述：map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q where app j
参数：J ⥤ C；f : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tautological action on maps of the functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`.
-/
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  app j := ⟨f.f.app j, congr_app f.comm j⟩

end KaroubiFunctorCategoryEmbedding

/-- The tautological fully faithful functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
/-
**CategoryTheory.Idempotents.karoubiFunctorCategoryEmbedding** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where ob
j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological fully faithful functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`.
-/
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (karoubiFunctorCategoryEmbedding J C).Full where
  map_surjective {P Q} f :=
    ⟨{f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            have h := hom_ext_iff.mp (f.naturality φ)
            dsimp [karoubiFunctorCategoryEmbedding] at h
            simp only [assoc, h.symm, karoubiFunctorCategoryEmbedding_obj,
              KaroubiFunctorCategoryEmbedding.obj_obj_p]
            rw [← P.p.naturality_assoc]
            exact congrArg _ (p_comp (f.app _)).symm }
      comm := by
        ext j
        exact (f.app j).comm }, rfl⟩
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (karoubiFunctorCategoryEmbedding J C).Faithful where
  map_injective h := by
    ext j
    exact hom_ext_iff.mp (congr_app h j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The composition of `(J ⥤ C) ⥤ Karoubi (J ⥤ C)` and `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ Karoubi C)` given by the composition with
`toKaroubi C : C ⥤ Karoubi C`. -/
/-
**CategoryTheory.Idempotents.toKaroubi_comp_karoubiFunctorCategoryEmbedding** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：toKaroubi_comp_karoubiFunctorCategoryEmbedding : toKaroubi _ ⋙ karoubiFunc
torCategoryEmbedding J C = (Functor.whiskeringRight J _ _).obj (toKaroubi C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `CategoryTheory.Idempotents.Karoubi.hom_ext`：hom_ext {P Q : Karoubi C} (f
 g : P ⟶ Q) (h : f.f = g.f) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.eqToHom_f`：eqToHom_f {P Q : Karoubi C
} (h : P = Q) : Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.X h
)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)

--- 原说明 ---
The composition of `(J ⥤ C) ⥤ Karoubi (J ⥤ C)` and `Karoubi (J ⥤ C) ⥤ (J ⥤ Karou
bi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ Karoubi C)` given by the composition with
`toKaroubi C : C ⥤ Karoubi C`.
-/
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C =
      (Functor.whiskeringRight J _ _).obj (toKaroubi C) := by
  apply Functor.ext
  · intro X Y f
    ext j
    simp
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      simp
    · intro j
      rfl

end Idempotents

end CategoryTheory

