/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Attaching cells

Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
we introduce a structure `AttachCells g f` which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. It means that
there is a pushout diagram of the form
```
⨿ i, A (π i) -----> X₁
  |                 |f
  v                 v
⨿ i, B (π i) -----> X₂
```
In other words, the morphism `f` is a pushout of coproducts of morphisms
of the form `g a : A a ⟶ B a`, see `nonempty_attachCells_iff`.

See the file `Mathlib/AlgebraicTopology/RelativeCellComplex/Basic.lean` for transfinite compositions
of morphisms `f` with `AttachCells g f` structures.

-/

@[expose] public section

universe w' w t t' v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} (g : ∀ a, A a ⟶ B a)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

/-- Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
this structure contains the data and properties which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. -/
/-
**HomotopicalAlgebra.AttachCells** 是 Mathlib 中的一个结构，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：AttachCells where /-- the index type of the cells -/ ι : Type w /-- for ea
ch `i : ι`, we shall attach a cell given by the morphism `g (π i)`. -/ π : ι -> 
α /-- a colimit cofan which gives the coproduct of the object `A (π i)` -/ cofan
₁ : Cofan (fun i => A (π i)) /-- a colimit cofan which gives the coproduct of th
e object `B (π i)` -/ cofan₂ : Cofan (fun i => B (π i)) /-- `cofan₁` is colimit 
-/ isColimit₁ : IsColimit cofan₁ /-- `cofan₂` is colimit -/ isColimit₂ : IsColim
it cofan₂ /-- the coproduc
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
this structure contains the data and properties which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. -/
-/
structure AttachCells where
  /-- the index type of the cells -/
  ι : Type w
  /-- for each `i : ι`, we shall attach a cell given by the morphism `g (π i)`. -/
  π : ι → α
  /-- a colimit cofan which gives the coproduct of the object `A (π i)` -/
  cofan₁ : Cofan (fun i ↦ A (π i))
  /-- a colimit cofan which gives the coproduct of the object `B (π i)` -/
  cofan₂ : Cofan (fun i ↦ B (π i))
  /-- `cofan₁` is colimit -/
  isColimit₁ : IsColimit cofan₁
  /-- `cofan₂` is colimit -/
  isColimit₂ : IsColimit cofan₂
  /-- the coproduct of the maps `g (π i) : A (π i) ⟶ B (π i)` for all `i : ι`. -/
  m : cofan₁.pt ⟶ cofan₂.pt
  hm (i : ι) : cofan₁.inj i ≫ m = g (π i) ≫ cofan₂.inj i := by cat_disch
  /-- the top morphism of the pushout square -/
  g₁ : cofan₁.pt ⟶ X₁
  /-- the bottom morphism of the pushout square -/
  g₂ : cofan₂.pt ⟶ X₂
  isPushout : IsPushout g₁ m f g₂

namespace AttachCells

open MorphismProperty

attribute [reassoc (attr := simp)] hm

variable {g f} (c : AttachCells.{w} g f)

include c

/-
**HomotopicalAlgebra.AttachCells.pushouts_coproducts** 是 Mathlib 中的一个引理，位于命名空间 `
HomotopicalAlgebra.AttachCells`。
形式化陈述：pushouts_coproducts : (coproducts.{w} (ofHoms g)).pushouts f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `HomotopicalAlgebra.AttachCells.hm`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {α : Type t} {A B : α → C} {g : (a : α) → A a ⟶ B a}   {X₁ X
₂ : C} {f : X₁ ⟶ X₂} (s…
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_iff`：coproducts_iff {X Y : C}
 (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Disc
rete J) f
· 使用定理 `HomotopicalAlgebra.AttachCells.isPushout`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {α : Type t} {A B : α → C} {g : (a : α) → A a ⟶ B a} 
  {X₁ X₂ : C} {f : X₁ ⟶ X₂} (s…
-/
lemma pushouts_coproducts : (coproducts.{w} (ofHoms g)).pushouts f := by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ ↦ by exact g (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ ↦ by rw [IsColimit.fac]; exact c.hm i)
  rw [this, coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, c.isColimit₁, c.isColimit₂, _, fun i ↦ ⟨_⟩⟩⟩

/-- The inclusion of a cell. -/
/-
**HomotopicalAlgebra.AttachCells.cell** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.AttachCells`。
形式化陈述：cell (i : c.ι) : B (c.π i) ⟶ X₂
参数：i : c.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a cell.
-/
def cell (i : c.ι) : B (c.π i) ⟶ X₂ := c.cofan₂.inj i ≫ c.g₂

@[reassoc]
/-
**HomotopicalAlgebra.AttachCells.cell_def** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra.AttachCells`。
形式化陈述：cell_def (i : c.ι) : c.cell i = c.cofan₂.inj i ≫ c.g₂
参数：i : c.ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cell_def (i : c.ι) : c.cell i = c.cofan₂.inj i ≫ c.g₂ := rfl
/-
**HomotopicalAlgebra.AttachCells.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.AttachCells`。
形式化陈述：hom_ext {Z : C} {φ φ' : X₂ ⟶ Z} (h₀ : f ≫ φ = f ≫ φ') (h : forall i, c.cel
l i ≫ φ = c.cell i ≫ φ') : φ = φ'
参数：h₀ : f ≫ φ = f ≫ φ'；h : forall i, c.cell i ≫ φ = c.cell i ≫ φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
· 使用定理 `HomotopicalAlgebra.AttachCells.isPushout`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {α : Type t} {A B : α → C} {g : (a : α) → A a ⟶ B a} 
  {X₁ X₂ : C} {f : X₁ ⟶ X₂} (s…
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma hom_ext {Z : C} {φ φ' : X₂ ⟶ Z}
    (h₀ : f ≫ φ = f ≫ φ') (h : ∀ i, c.cell i ≫ φ = c.cell i ≫ φ') :
    φ = φ' := by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

set_option backward.isDefEq.respectTransparency false in
/-- If `f` and `f'` are isomorphic morphisms and the target of `f`
is obtained by attaching cells to the source of `f`,
then the same holds for `f'`. -/
@[simps]
/-
**HomotopicalAlgebra.AttachCells.ofArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra.AttachCells`。
形式化陈述：ofArrowIso {Y₁ Y₂ : C} {f' : Y₁ ⟶ Y₂} (e : Arrow.mk f ≅ Arrow.mk f') : Att
achCells.{w} g f' where ι
参数：e : Arrow.mk f ≅ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `f'` are isomorphic morphisms and the target of `f`
is obtained by attaching cells to the source of `f`,
then the same holds for `f'`.
-/
def ofArrowIso {Y₁ Y₂ : C} {f' : Y₁ ⟶ Y₂} (e : Arrow.mk f ≅ Arrow.mk f') :
    AttachCells.{w} g f' where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  g₁ := c.g₁ ≫ Arrow.leftFunc.map e.hom
  g₂ := c.g₂ ≫ Arrow.rightFunc.map e.hom
  isPushout :=
    c.isPushout.of_iso (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
      (Arrow.rightFunc.mapIso e) (by simp) (by simp) (by simp) (by simp)

/-- This definition allows the replacement of the `ι` field of
a `AttachCells g f` structure by an equivalent type. -/
@[simps]
/-
**HomotopicalAlgebra.AttachCells.reindex** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalA
lgebra.AttachCells`。
形式化陈述：reindex {ι' : Type w'} (e : ι' ≃ c.ι) : AttachCells.{w'} g f where ι
参数：e : ι' ≃ c.ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.AttachCells.isPushout`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {α : Type t} {A B : α → C} {g : (a : α) → A a ⟶ B a} 
  {X₁ X₂ : C} {f : X₁ ⟶ X₂} (s…

--- 原说明 ---
This definition allows the replacement of the `ι` field of
a `AttachCells g f` structure by an equivalent type.
-/
def reindex {ι' : Type w'} (e : ι' ≃ c.ι) :
    AttachCells.{w'} g f where
  ι := ι'
  π i' := c.π (e i')
  cofan₁ := Cofan.mk c.cofan₁.pt (fun i' ↦ c.cofan₁.inj (e i'))
  cofan₂ := Cofan.mk c.cofan₂.pt (fun i' ↦ c.cofan₂.inj (e i'))
  isColimit₁ := IsColimit.whiskerEquivalence (c.isColimit₁) (Discrete.equivalence e)
  isColimit₂ := IsColimit.whiskerEquivalence (c.isColimit₂) (Discrete.equivalence e)
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  hm i' := c.hm (e i')
  isPushout := c.isPushout

section

variable {α' : Type t'} {A' B' : α' → C} (g' : ∀ i', A' i' ⟶ B' i')
  (a : α → α') (ha : ∀ (i : α), Arrow.mk (g i) ≅ Arrow.mk (g' (a i)))

set_option backward.isDefEq.respectTransparency false in
/-- If a family of maps `g` is contained in another family `g'` (up to isomorphisms),
if `f : X₁ ⟶ X₂` is a morphism, and `X₂` is obtained from `X₁` by attaching cells
of the form `g`, then it is also obtained by attaching cells of the form `g'`. -/
/-
**HomotopicalAlgebra.AttachCells.reindexCellTypes** 是 Mathlib 中的一个定义，位于命名空间 `Hom
otopicalAlgebra.AttachCells`。
形式化陈述：reindexCellTypes : AttachCells g' f where ι
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.AttachCells.isPushout`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {α : Type t} {A B : α → C} {g : (a : α) → A a ⟶ B a} 
  {X₁ X₂ : C} {f : X₁ ⟶ X₂} (s…

--- 原说明 ---
If a family of maps `g` is contained in another family `g'` (up to isomorphisms)
,
if `f : X₁ ⟶ X₂` is a morphism, and `X₂` is obtained from `X₁` by attaching cell
s
of the form `g`, then it is also obtained by attaching cells of the form `g'`.
-/
def reindexCellTypes : AttachCells g' f where
  ι := c.ι
  π := a ∘ c.π
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun i ↦ Arrow.leftFunc.map (ha (c.π i)).inv ≫ c.cofan₁.inj i)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun i ↦ Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cofan₂.inj i)
  isColimit₁ := by
    let e : Discrete.functor (fun i ↦ A (c.π i)) ≅
        Discrete.functor (fun i ↦ A' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ ↦ Arrow.leftFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₁ (Cofan.ext (Iso.refl _) (fun i ↦ ?_)))
    simp [Cocone.precompose, e, Cofan.inj]
  isColimit₂ := by
    let e : Discrete.functor (fun i ↦ B (c.π i)) ≅
        Discrete.functor (fun i ↦ B' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ ↦ Arrow.rightFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₂ (Cofan.ext (Iso.refl _) (fun i ↦ ?_)))
    simp [Cocone.precompose, e, Cofan.inj]
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  isPushout := c.isPushout

end

end AttachCells

set_option backward.isDefEq.respectTransparency false in
open MorphismProperty in
/-
**HomotopicalAlgebra.nonempty_attachCells_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra`。
形式化陈述：nonempty_attachCells_iff : Nonempty (AttachCells.{w} g f) ↔ (coproducts.{w
} (ofHoms g)).pushouts f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.AttachCells.pushouts_coproducts`：pushouts_coproducts 
: (coproducts.{w} (ofHoms g)).pushouts f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_iff`：coproducts_iff {X Y : C}
 (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Disc
rete J) f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Discrete.natIso_hom_app`：∀ {C : Type u₂} [inst : Category
Theory.Category.{v₂, u₂} C] {I : Type u₁}   {F G : CategoryTheory.Functor (Categ
oryTheory.Discrete I) C} (f …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Arrow.leftFunc_map`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C]   {X Y : CategoryTheory.Comma (CategoryTheory.Functor.id C) 
(CategoryTheory.Functor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Arrow.w_mk_right_assoc`：∀ {T : Type u} [inst : CategoryTh
eory.Category.{v, u} T] {f : CategoryTheory.Arrow T} {X Y : T} {g : X ⟶ Y}   (sq
 : f ⟶ CategoryTheory.Arrow…
· 使用定理 `CategoryTheory.Arrow.rightFunc_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C]   {Y X : CategoryTheory.Comma (CategoryTheory.Functor.id C)
 (CategoryTheory.Functor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma nonempty_attachCells_iff :
    Nonempty (AttachCells.{w} g f) ↔ (coproducts.{w} (ofHoms g)).pushouts f := by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    rw [coproducts_iff] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (φ.app ⟨i⟩) ≅ Arrow.mk (g (π i)) :=
      eqToIso (((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose_spec)
    let e₁ (i : ι) : F₁.obj ⟨i⟩ ≅ A (π i) := Arrow.leftFunc.mapIso (e i)
    let e₂ (i : ι) : F₂.obj ⟨i⟩ ≅ B (π i) := Arrow.rightFunc.mapIso (e i)
    exact ⟨{
      ι := ι
      π := π
      cofan₁ := Cofan.mk c₁.pt (fun i ↦ (e₁ i).inv ≫ c₁.ι.app ⟨i⟩)
      cofan₂ := Cofan.mk c₂.pt (fun i ↦ (e₂ i).inv ≫ c₂.ι.app ⟨i⟩)
      isColimit₁ :=
        (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₁ i)) _).1
          (IsColimit.ofIsoColimit h₁ (Cocone.ext (Iso.refl _) (by simp)))
      isColimit₂ :=
        (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ ↦ e₂ i)) _).1
          (IsColimit.ofIsoColimit h₂ (Cocone.ext (Iso.refl _) (by simp)))
      hm i := by simp [e₁, e₂]
      isPushout := sq, .. }⟩

end HomotopicalAlgebra

