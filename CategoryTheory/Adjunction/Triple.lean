/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monad.Adjunction
/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`. We first
prove that `F` is fully faithful iff `H` is, and then prove results about the two special cases
where `G` is fully faithful or `F` and `H` are.

## Main results

All results are about an adjoint triple `F ⊣ G ⊣ H` where `adj₁ : F ⊣ G` and `adj₂ : G ⊣ H`. We
bundle the adjunctions in a structure `Triple F G H`.
* `fullyFaithfulEquiv`: `F` is fully faithful iff `H` is.
* `rightToLeft`: the canonical natural transformation `H ⟶ F` that exists whenever `G` is fully
  faithful. This is defined as the preimage of `adj₂.counit ≫ adj₁.unit` under whiskering with `G`,
  but formulas in terms of the units resp. counits of the adjunctions are also given.
* `whiskerRight_rightToLeft`: whiskering `rightToLeft : H ⟶ F` with `G` yields
  `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G`.
* `epi_rightToLeft_app_iff_epi_map_adj₁_unit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₁.unit.app X` under `H` is.
* `epi_rightToLeft_app_iff_epi_map_adj₂_counit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₂.counit.app X` under `F` is.
* `epi_rightToLeft_app_iff`: when `H` preserves epimorphisms, `rightToLeft : H ⟶ F` is epic at `X`
  iff `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G` is.
* `leftToRight`: the canonical natural transformation `F ⟶ H` that exists whenever `F` and `H` are
  fully faithful. This is defined in terms of the units of the adjunctions, but a formula in terms
  of the counits is also given.
* `whiskerLeft_leftToRight`: whiskering `G` with `leftToRight : F ⟶ H` yields
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H`.
* `mono_leftToRight_app_iff_mono_adj₂_unit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₂.unit` is monic at `F.obj X`.
* `mono_leftToRight_app_iff_mono_adj₁_counit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₁.counit` is monic at `H.obj X`.
* `mono_leftToRight_app_iff`: `leftToRight : F ⟶ H` is componentwise monic iff
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H` is.
-/

@[expose] public section

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]
variable (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D)

/-- Structure containing the two adjunctions of an adjoint triple `F ⊣ G ⊣ H`. -/
/-
**CategoryTheory.Adjunction.Triple** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.A
djunction`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D →           CategoryTheory.Functor D C → CategoryTheory
.Functor C D → Type (max (max (max u_1 u_2) v_1) v_2)
参数：max (max (max u_1 u_2) v_1) v_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the two adjunctions of an adjoint triple `F ⊣ G ⊣ H`.
-/
structure CategoryTheory.Adjunction.Triple where
  /-- Adjunction `F ⊣ G` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₁ : F ⊣ G
  /-- Adjunction `G ⊣ H` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₂ : G ⊣ H

namespace CategoryTheory.Adjunction.Triple

variable {F G H} (t : Triple F G H)

/-
**CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：isIso_unit_iff_isIso_counit : IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isIso_counit_of_iso`：isIso_counit_of_iso (adj 
: L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit
· 使用引理 `CategoryTheory.Adjunction.isIso_unit_of_iso`：isIso_unit_of_iso (adj : L 
⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit
-/
lemma isIso_unit_iff_isIso_counit : IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
    exact t.adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

/--
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if and only if the
right adjoint `H` is fully faithful.
-/
/-
**CategoryTheory.Adjunction.Triple.fullyFaithfulEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction.Triple`。
形式化陈述：fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if a
nd only if the
right adjoint `H` is fully faithful.
-/
noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The adjoint triple `H.op ⊣ G.op ⊣ F.op` dual to an adjoint triple `F ⊣ G ⊣ H`. -/
@[simps]
/-
**CategoryTheory.Adjunction.Triple.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Adjunction.Triple`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {F
 : CategoryTheory.Functor C D} →           {G : CategoryTheory.Functor D C} →   
          {H : CategoryTheory.Functor C D} →               CategoryTheory.Adjunc
tion.Triple F G H → CategoryTheory.Adjunction.Triple H.op G.op F.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint triple `H.op ⊣ G.op ⊣ F.op` dual to an adjoint triple `F ⊣ G ⊣ H`.
-/
protected def op : Triple H.op G.op F.op where
  adj₁ := t.adj₂.op
  adj₂ := t.adj₁.op

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

/-- The natural transformation `H ⟶ F` that exists for every adjoint triple `F ⊣ G ⊣ H` where `G`
is fully faithful, given here as the preimage of `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G`
under whiskering with `G`. -/
/-
**CategoryTheory.Adjunction.Triple.rightToLeft** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Adjunction.Triple`。
形式化陈述：rightToLeft : H ⟶ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `H ⟶ F` that exists for every adjoint triple `F ⊣ G ⊣
 H` where `G`
is fully faithful, given here as the preimage of `adj₂.counit ≫ adj₁.unit : H ⋙ 
G ⟶ F ⋙ G`
under whiskering with `G`.
-/
noncomputable def rightToLeft : H ⟶ F :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimage (t.adj₂.counit ≫ t.adj₁.unit)

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, whiskering the natural
transformation `H ⟶ F` with `G` yields the composition of the counit of the second adjunction with
the unit of the first adjunction. -/
@[simp, reassoc]
/-
**CategoryTheory.Adjunction.Triple.whiskerRight_rightToLeft** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：whiskerRight_rightToLeft : whiskerRight t.rightToLeft G = t.adj₂.counit ≫ 
t.adj₁.unit
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, whiskering the na
tural
transformation `H ⟶ F` with `G` yields the composition of the counit of the seco
nd adjunction with
the unit of the first adjunction.
-/
lemma whiskerRight_rightToLeft : whiskerRight t.rightToLeft G = t.adj₂.counit ≫ t.adj₁.unit :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).map_preimage _

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the images of the components of
the natural transformation `H ⟶ F` under `G` are the components of the composition of counit of the
second adjunction with the unit of the first adjunction. -/
@[simp, reassoc]
/-
**CategoryTheory.Adjunction.Triple.map_rightToLeft_app** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction.Triple`。
形式化陈述：map_rightToLeft_app (X : C) : G.map (t.rightToLeft.app X) = t.adj₂.counit.
app X ≫ t.adj₁.unit.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Adjunction.Triple.whiskerRight_rightToLeft`：whiskerRight_
rightToLeft : whiskerRight t.rightToLeft G = t.adj₂.counit ≫ t.adj₁.unit

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the images of the
 components of
the natural transformation `H ⟶ F` under `G` are the components of the compositi
on of counit of the
second adjunction with the unit of the first adjunction.
-/
lemma map_rightToLeft_app (X : C) :
    G.map (t.rightToLeft.app X) = t.adj₂.counit.app X ≫ t.adj₁.unit.app X :=
  congr_app t.whiskerRight_rightToLeft X

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the whiskered unit `H ⟶ F ⋙ G ⋙ H` of the first adjunction followed by the
inverse of the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second. -/
/-
**CategoryTheory.Adjunction.Triple.rightToLeft_eq_units** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：rightToLeft_eq_units : t.rightToLeft = H.leftUnitor.inv ≫ whiskerRight t.a
dj₁.unit H ≫ (Functor.associator _ _ _).hom ≫ inv (whiskerLeft F t.adj₂.unit) ≫ 
F.rightUnitor.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.inv_whiskerLeft`：inv_whiskerLeft (F : C ⥤ D) {G H
 : D ⥤ E} (α : G ⟶ H) [IsIso α] : inv (whiskerLeft F α) = whiskerLeft F (inv α)
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Adjunction.inv_map_unit`：inv_map_unit {X : C} [IsIso (h.u
nit.app X)] : inv (L.map (h.unit.app X)) = h.counit.app (L.obj X)
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fu
lly faithful
is also equal to the whiskered unit `H ⟶ F ⋙ G ⋙ H` of the first adjunction foll
owed by the
inverse of the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second.
-/
lemma rightToLeft_eq_units :
    t.rightToLeft = H.leftUnitor.inv ≫ whiskerRight t.adj₁.unit H ≫ (Functor.associator _ _ _).hom ≫
    inv (whiskerLeft F t.adj₂.unit) ≫ F.rightUnitor.hom := by
  ext X; apply G.map_injective; simp [rightToLeft]

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first adjunction
followed by the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second. -/
/-
**CategoryTheory.Adjunction.Triple.rightToLeft_eq_counits** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：rightToLeft_eq_counits : t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerL
eft H t.adj₁.counit) ≫ (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.coun
it F ≫ F.leftUnitor.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.inv_whiskerLeft`：inv_whiskerLeft (F : C ⥤ D) {G H
 : D ⥤ E} (α : G ⟶ H) [IsIso α] : inv (whiskerLeft F α) = whiskerLeft F (inv α)
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Adjunction.inv_counit_map`：inv_counit_map {X : D} [IsIso 
(h.counit.app X)] : inv (R.map (h.counit.app X)) = h.unit.app (R.obj X)
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fu
lly faithful
is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the firs
t adjunction
followed by the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second.
-/
lemma rightToLeft_eq_counits :
    t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerLeft H t.adj₁.counit) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.counit F ≫ F.leftUnitor.hom := by
  ext X; apply G.map_injective; simp [rightToLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.Triple.adj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj₁_counit_app_rightToLeft_app (X : C) :
    t.adj₁.counit.app (H.obj X) ≫ t.rightToLeft.app X = F.map (t.adj₂.counit.app X) :=
  G.map_injective (by simp [← cancel_epi (t.adj₁.unit.app _)])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.Triple.rightToLeft_app_adj** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightToLeft_app_adj₂_unit_app (X : C) :
    t.rightToLeft.app X ≫ t.adj₂.unit.app (F.obj X) = H.map (t.adj₁.unit.app X) :=
  G.map_injective (by simp [← cancel_mono (t.adj₂.counit.app _)])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`F.op ⟶ H.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is dual to the natural
transformation `H ⟶ F`. -/
@[simp]
/-
**CategoryTheory.Adjunction.Triple.op_rightToLeft** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction.Triple`。
形式化陈述：op_rightToLeft : t.op.rightToLeft = NatTrans.op t.rightToLeft
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.Triple.rightToLeft_eq_units`：rightToLeft_eq_un
its : t.rightToLeft = H.leftUnitor.inv ≫ whiskerRight t.adj₁.unit H ≫ (Functor.a
ssociator _ _ _).hom ≫ inv (whiskerLeft F t…
· 使用引理 `CategoryTheory.Adjunction.Triple.rightToLeft_eq_counits`：rightToLeft_eq_
counits : t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerLeft H t.adj₁.counit) 
≫ (Functor.associator _ _ _).inv ≫ whiskerRig…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.instIsIsoFunctorOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u_1}   [inst_1 : CategoryTheory.Categor
y.{v_1, u_1} D] {F G : Category…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.inv_whiskerLeft`：inv_whiskerLeft (F : C ⥤ D) {G H
 : D ⥤ E} (α : G ⟶ H) [IsIso α] : inv (whiskerLeft F α) = whiskerLeft F (inv α)
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.op_inv`：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).
op = inv f.op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural trans
formation
`F.op ⟶ H.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is dual
 to the natural
transformation `H ⟶ F`.
-/
lemma op_rightToLeft : t.op.rightToLeft = NatTrans.op t.rightToLeft := by
  ext
  rw [rightToLeft_eq_units, rightToLeft_eq_counits]
  simp

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is epic at `X` iff the image of the unit of the adjunction `F ⊣ G` under `H` is. -/
/-
**CategoryTheory.Adjunction.Triple.epi_rightToLeft_app_iff_epi_map_adj** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural trans
formation
`H ⟶ F` is epic at `X` iff the image of the unit of the adjunction `F ⊣ G` under
 `H` is.
-/
lemma epi_rightToLeft_app_iff_epi_map_adj₁_unit_app {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (H.map (t.adj₁.unit.app X)) := by
  rw [← epi_comp_iff_of_isIso _ (t.adj₂.unit.app (F.obj X)), rightToLeft_app_adj₂_unit_app]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is epic at `X` iff the image of the counit of the adjunction `G ⊣ H` under `F` is. -/
/-
**CategoryTheory.Adjunction.Triple.epi_rightToLeft_app_iff_epi_map_adj** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural trans
formation
`H ⟶ F` is epic at `X` iff the image of the counit of the adjunction `G ⊣ H` und
er `F` is.
-/
lemma epi_rightToLeft_app_iff_epi_map_adj₂_counit_app {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (F.map (t.adj₂.counit.app X)) := by
  rw [← epi_comp_iff_of_epi (t.adj₁.counit.app (H.obj X)), adj₁_counit_app_rightToLeft_app]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and `H` preserves epimorphisms
(which is for example the case if `H` has a further right adjoint), the components of the natural
transformation `H ⟶ F` are epic iff the respective components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are. -/
/-
**CategoryTheory.Adjunction.Triple.epi_rightToLeft_app_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：epi_rightToLeft_app_iff [H.PreservesEpimorphisms] {X : C} : Epi (t.rightTo
Left.app X) ↔ Epi (t.adj₂.counit.app X ≫ t.adj₁.unit.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Adjunction.Triple.map_rightToLeft_app`：map_rightToLeft_ap
p (X : C) : G.map (t.rightToLeft.app X) = t.adj₂.counit.app X ≫ t.adj₁.unit.app 
X
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.Adjunction.Triple.epi_rightToLeft_app_iff_epi_map_adj₁_un
it_app`：epi_rightToLeft_app_iff_epi_map_adj₁_unit_app {X : C} : Epi (t.rightToLe
ft.app X) ↔ Epi (H.map (t.adj₁.unit.app X))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and `H` preserves 
epimorphisms
(which is for example the case if `H` has a further right adjoint), the componen
ts of the natural
transformation `H ⟶ F` are epic iff the respective components of the natural tra
nsformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are.
-/
lemma epi_rightToLeft_app_iff [H.PreservesEpimorphisms] {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) := by
  have _ := t.adj₂.isLeftAdjoint
  refine ⟨fun h ↦ by rw [← map_rightToLeft_app]; exact G.map_epi _, fun h ↦ ?_⟩
  rw [epi_rightToLeft_app_iff_epi_map_adj₁_unit_app]
  simpa using epi_comp (t.adj₂.unit.app (H.obj X)) (H.map (t.adj₂.counit.app X ≫ t.adj₁.unit.app X))

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful] [H.Full] [H.Faithful]

/-- The natural transformation `F ⟶ H` that exists for every adjoint triple `F ⊣ G ⊣ H` where `F`
and `H` are fully faithful, given here as the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second
adjunction followed by the inverse of the whiskered unit `F ⋙ G ⋙ H ⟶ H` of the first. -/
/-
**CategoryTheory.Adjunction.Triple.leftToRight** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Adjunction.Triple`。
形式化陈述：leftToRight : F ⟶ H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `F ⟶ H` that exists for every adjoint triple `F ⊣ G ⊣
 H` where `F`
and `H` are fully faithful, given here as the whiskered unit `F ⟶ F ⋙ G ⋙ H` of 
the second
adjunction followed by the inverse of the whiskered unit `F ⋙ G ⋙ H ⟶ H` of the 
first.
-/
noncomputable def leftToRight : F ⟶ H :=
  F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight t.adj₁.unit H) ≫ H.leftUnitor.hom

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
/-
**CategoryTheory.Adjunction.Triple.leftToRight_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Adjunction.Triple`。
形式化陈述：leftToRight_app {X : C} : t.leftToRight.app X = t.adj₂.unit.app (F.obj X) 
≫ inv (H.map (t.adj₁.unit.app X))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.inv_whiskerRight`：inv_whiskerRight {G H : C ⥤ D} 
(α : G ⟶ H) (F : D ⥤ E) [IsIso α] : inv (whiskerRight α F) = whiskerRight (inv α
) F
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftToRight_app {X : C} :
    t.leftToRight.app X = t.adj₂.unit.app (F.obj X) ≫ inv (H.map (t.adj₁.unit.app X)) := by
  simp [leftToRight]

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `F ⟶ H` for an adjoint triple `F ⊣ G ⊣ H` with `F` and `H`
fully faithful is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second
adjunction followed by the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first. -/
/-
**CategoryTheory.Adjunction.Triple.leftToRight_eq_counits** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：leftToRight_eq_counits : t.leftToRight = F.leftUnitor.inv ≫ inv (whiskerRi
ght t.adj₂.counit F) ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft H t.adj₁.cou
nit ≫ H.rightUnitor.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `CategoryTheory.Functor.whiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.comp_hom_eq_id`：comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The natural transformation `F ⟶ H` for an adjoint triple `F ⊣ G ⊣ H` with `F` an
d `H`
fully faithful is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶
 F` of the second
adjunction followed by the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first.
-/
lemma leftToRight_eq_counits :
    t.leftToRight = F.leftUnitor.inv ≫ inv (whiskerRight t.adj₂.counit F) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft H t.adj₁.counit ≫ H.rightUnitor.hom := by
  ext X; dsimp [leftToRight]; simp only [Category.id_comp, Category.comp_id, NatIso.isIso_inv_app]
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  refine Eq.trans ?_ (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X)
  rw [whiskerRight_app _ H, (asIso (t.adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (t.adj₂.counit_naturality (t.adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| t.adj₂.left_triangle_components (F.obj X)]
  simp

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `F ⟶ H` at `G` are precisely the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions. -/
@[simp, reassoc]
/-
**CategoryTheory.Adjunction.Triple.leftToRight_app_obj** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction.Triple`。
形式化陈述：leftToRight_app_obj {X : D} : dsimp% t.leftToRight.app (G.obj X) = t.adj₁.
counit.app X ≫ t.adj₂.unit.app X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_symm_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_apply`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用引理 `CategoryTheory.Adjunction.Triple.leftToRight_app`：leftToRight_app {X : C
} : t.leftToRight.app X = t.adj₂.unit.app (F.obj X) ≫ inv (H.map (t.adj₁.unit.ap
p X))
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the comp
onents of the
natural transformation `F ⟶ H` at `G` are precisely the components of the natura
l transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions.
-/
lemma leftToRight_app_obj {X : D} :
    dsimp% t.leftToRight.app (G.obj X) = t.adj₁.counit.app X ≫ t.adj₂.unit.app X := by
  refine (((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_).symm
  rw [homEquiv_symm_apply, map_comp, Category.assoc, left_triangle_components,
    homEquiv_apply, leftToRight_app, ← H.map_inv]
  congr
  simpa using IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triangle_components _)

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, whiskering `G` with the
natural transformation `F ⟶ H` yields the composition of the counit of the first adjunction with
the unit of the second adjunction. -/
@[simp, reassoc]
/-
**CategoryTheory.Adjunction.Triple.whiskerLeft_leftToRight** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：whiskerLeft_leftToRight : whiskerLeft G t.leftToRight = t.adj₁.counit ≫ t.
adj₂.unit
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Adjunction.Triple.leftToRight_app_obj`：leftToRight_app_ob
j {X : D} : dsimp% t.leftToRight.app (G.obj X) = t.adj₁.counit.app X ≫ t.adj₂.un
it.app X

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, whiskeri
ng `G` with the
natural transformation `F ⟶ H` yields the composition of the counit of the first
 adjunction with
the unit of the second adjunction.
-/
lemma whiskerLeft_leftToRight : whiskerLeft G t.leftToRight = t.adj₁.counit ≫ t.adj₂.unit := by
  ext X; exact t.leftToRight_app_obj

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
/-
**CategoryTheory.Adjunction.Triple.map_adj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_adj₂_counit_app_leftToRight_app (X : C) :
    F.map (t.adj₂.counit.app X) ≫ t.leftToRight.app X = t.adj₁.counit.app (H.obj X) := by
  simp

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.Triple.leftToRight_app_map_adj** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftToRight_app_map_adj₁_unit_app (X : C) :
    t.leftToRight.app X ≫ H.map (t.adj₁.unit.app X) = t.adj₂.unit.app (F.obj X) := by
  simp [leftToRight_app]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `H.op ⟶ F.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is
dual to the natural transformation `F ⟶ H`. -/
@[simp]
/-
**CategoryTheory.Adjunction.Triple.leftToRight_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction.Triple`。
形式化陈述：leftToRight_op : t.op.leftToRight = NatTrans.op t.leftToRight
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.Triple.leftToRight.eq_1`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] {F : Categor…
· 使用引理 `CategoryTheory.Adjunction.Triple.leftToRight_eq_counits`：leftToRight_eq_
counits : t.leftToRight = F.leftUnitor.inv ≫ inv (whiskerRight t.adj₂.counit F) 
≫ (Functor.associator _ _ _).hom ≫ whiskerLef…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.instIsIsoFunctorOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u_1}   [inst_1 : CategoryTheory.Categor
y.{v_1, u_1} D] {F G : Category…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.inv_whiskerRight`：inv_whiskerRight {G H : C ⥤ D} 
(α : G ⟶ H) (F : D ⥤ E) [IsIso α] : inv (whiskerRight α F) = whiskerRight (inv α
) F
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.unop_inv`：unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (i
nv f).unop = inv f.unop
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.op_inv`：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).
op = inv f.op
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natu
ral
transformation `H.op ⟶ F.op` obtained from the dual adjoint triple `H.op ⊣ G.op 
⊣ F.op` is
dual to the natural transformation `F ⟶ H`.
-/
lemma leftToRight_op : t.op.leftToRight = NatTrans.op t.leftToRight := by
  ext
  rw [leftToRight, leftToRight_eq_counits]
  simp

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is monic at `X` iff the unit of the adjunction `G ⊣ H` is monic
at `F.obj X`. -/
/-
**CategoryTheory.Adjunction.Triple.mono_leftToRight_app_iff_mono_adj** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natu
ral
transformation `F ⟶ H` is monic at `X` iff the unit of the adjunction `G ⊣ H` is
 monic
at `F.obj X`.
-/
lemma mono_leftToRight_app_iff_mono_adj₂_unit_app {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₂.unit.app (F.obj X)) := by
  rw [← leftToRight_app_map_adj₁_unit_app, mono_comp_iff_of_mono]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is monic at `X` iff the counit of the adjunction `F ⊣ G` is monic
at `H.obj X`. -/
/-
**CategoryTheory.Adjunction.Triple.mono_leftToRight_app_iff_mono_adj** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.Triple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natu
ral
transformation `F ⟶ H` is monic at `X` iff the counit of the adjunction `F ⊣ G` 
is monic
at `H.obj X`.
-/
lemma mono_leftToRight_app_iff_mono_adj₁_counit_app {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₁.counit.app (H.obj X)) := by
  rw [← map_adj₂_counit_app_leftToRight_app, mono_comp_iff_of_isIso]

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is componentwise monic iff the natural transformation `G ⋙ F ⟶ G ⋙ H`
obtained from the units and counits of the adjunctions is.
Note that unlike `epi_rightToLeft_app_iff`, this equivalence does not make sense
on a per-object basis because the components of the two natural transformations are indexed by
different categories. -/
/-
**CategoryTheory.Adjunction.Triple.mono_leftToRight_app_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Adjunction.Triple`。
形式化陈述：mono_leftToRight_app_iff : dsimp% (forall X, Mono (t.leftToRight.app X)) ↔
 forall X, Mono (t.adj₁.counit.app X ≫ t.adj₂.unit.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Adjunction.Triple.leftToRight_app_obj`：leftToRight_app_ob
j {X : D} : dsimp% t.leftToRight.app (G.obj X) = t.adj₁.counit.app X ≫ t.adj₂.un
it.app X
· 使用引理 `CategoryTheory.Adjunction.Triple.mono_leftToRight_app_iff_mono_adj₂_unit
_app`：mono_leftToRight_app_iff_mono_adj₂_unit_app {X : C} : Mono (t.leftToRight.
app X) ↔ Mono (t.adj₂.unit.app (F.obj X))
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitObjOfFaithfulOfFull`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…

--- 原说明 ---
For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natu
ral
transformation `F ⟶ H` is componentwise monic iff the natural transformation `G 
⋙ F ⟶ G ⋙ H`
obtained from the units and counits of the adjunctions is.
Note that unlike `epi_rightToLeft_app_iff`, this equivalence does not make sense
on a per-object basis because the components of the two natural transformations 
are indexed by
different categories.
-/
lemma mono_leftToRight_app_iff :
    dsimp% (∀ X, Mono (t.leftToRight.app X)) ↔
      ∀ X, Mono (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) := by
  refine ⟨fun h X ↦ by rw [← leftToRight_app_obj]; exact h _, fun h X ↦ ?_⟩
  rw [mono_leftToRight_app_iff_mono_adj₂_unit_app]
  simpa using h (F.obj X)

end OuterFullyFaithful

end CategoryTheory.Adjunction.Triple

