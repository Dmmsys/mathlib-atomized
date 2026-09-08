/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Presentation of a colimit of objects equipped with a presentation

## Main definition:
- `CategoryTheory.Limits.ColimitPresentation.bind`: Given a colimit presentation of `X` and
  colimit presentations of the components, this is the colimit presentation over the sigma type.

-/

@[expose] public section

universe s t w v u

namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C]

variable {J : Type*} {I : J → Type*} [Category* J] [∀ j, Category (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

set_option linter.unusedVariables false in
/-- The type underlying the category used in the construction of the composition
of colimit presentations. This is simply `Σ j, I j` but with a different category structure. -/
@[nolint unusedArguments]
/-
**CategoryTheory.Limits.ColimitPresentation.Total** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.ColimitPresentation`。
形式化陈述：Total (P : forall j, ColimitPresentation (I j) (D.obj j)) : Type _
参数：P : forall j, ColimitPresentation (I j) (D.obj j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type underlying the category used in the construction of the composition
of colimit presentations. This is simply `Σ j, I j` but with a different categor
y structure.
-/
def Total (P : ∀ j, ColimitPresentation (I j) (D.obj j)) : Type _ :=
  Σ j, I j

variable (P) in
/-- Constructor for `Total` to guide type checking. -/
/-
**CategoryTheory.Limits.ColimitPresentation.Total.mk** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.ColimitPresentation.Total`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 u_1} →       {I : J → Type u_2} →         [inst_1 : CategoryTheory.Category.{v_
1, u_1} J] →           [inst_2 : (j : J) → CategoryTheory.Category.{u_3, u_2} (I
 j)] →             {D : CategoryTheory.Functor J C} →               (P : (j : J)
 → CategoryTheory.Limits.ColimitPresentation (I j) (D.obj j)) →                 
(i : J) → I i → CategoryTheory.Limits.ColimitPresentation.Total P
参数：j : J；I j；P : (j : J) → CategoryTheory.Limits.ColimitPresentation (I j) (D.ob
j j)；i : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Total` to guide type checking.
-/
abbrev Total.mk (i : J) (k : I i) : Total P := ⟨i, k⟩

/-- Morphisms in the `Total` category. -/
@[ext]
/-
**CategoryTheory.Limits.ColimitPresentation.Total.Hom** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.Limits.ColimitPresentation.Total`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 u_1} →       {I : J → Type u_2} →         [inst_1 : CategoryTheory.Category.{v_
1, u_1} J] →           [inst_2 : (j : J) → CategoryTheory.Category.{u_3, u_2} (I
 j)] →             {D : CategoryTheory.Functor J C} →               {P : (j : J)
 → CategoryTheory.Limits.ColimitPresentation (I j) (D.obj j)} →                 
CategoryTheory.Limits.ColimitPresentation.Total P →                   CategoryTh
eory.Limits.ColimitPresentation.Total P → Type (max v v_1)
参数：j : J；I j；j : J；I j；D.obj j；max v v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in the `Total` category.
-/
structure Total.Hom (k l : Total P) where
  /-- The underlying morphism in the first component. -/
  base : k.1 ⟶ l.1
  /-- A morphism in `C`. -/
  hom : (P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2
  w : (P k.1).ι.app k.2 ≫ D.map base = hom ≫ (P l.1).ι.app l.2 := by cat_disch

set_option backward.isDefEq.respectTransparency false in -- This is needed below
attribute [reassoc] Total.Hom.w

set_option backward.isDefEq.respectTransparency false in
/-- Composition of morphisms in the `Total` category. -/
@[simps]
/-
**CategoryTheory.Limits.ColimitPresentation.Total.Hom.comp** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.ColimitPresentation.Total.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 u_1} →       {I : J → Type u_2} →         [inst_1 : CategoryTheory.Category.{v_
1, u_1} J] →           [inst_2 : (j : J) → CategoryTheory.Category.{u_3, u_2} (I
 j)] →             {D : CategoryTheory.Functor J C} →               {P : (j : J)
 → CategoryTheory.Limits.ColimitPresentation (I j) (D.obj j)} →                 
{k l m : CategoryTheory.Limits.ColimitPresentation.Total P} → k.Hom l → l.Hom m 
→ k.Hom m
参数：j : J；I j；j : J；I j；D.obj j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in the `Total` category.
-/
def Total.Hom.comp {k l m : Total P} (f : k.Hom l) (g : l.Hom m) : k.Hom m where
  base := f.base ≫ g.base
  hom := f.hom ≫ g.hom
  w := by
    simp only [Functor.map_comp, Category.assoc]
    rw [f.w_assoc, g.w]

set_option backward.defeqAttrib.useBackward true in
@[simps! id_base id_hom comp_base comp_hom]
/-
**CategoryTheory.Limits.ColimitPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.ColimitPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Total P) where
  Hom := Total.Hom
  id _ := { base := 𝟙 _, hom := 𝟙 _ }
  comp := Total.Hom.comp
/-
**CategoryTheory.Limits.ColimitPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.ColimitPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] [LocallySmall.{w} J] : LocallySmall.{w} (Total P) where
  hom_small k l :=
    let f (x : k ⟶ l) : (k.1 ⟶ l.1) × ((P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2) :=
      (x.base, x.hom)
    small_of_injective (f := f) (by grind [Function.Injective, Total.Hom.ext])

section Small

variable {J : Type w} {I : J → Type w} [SmallCategory J] [∀ j, SmallCategory (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

/-
**CategoryTheory.Limits.ColimitPresentation.Total.exists_hom_of_hom** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.ColimitPresentation.Total`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} {I :
 J → Type w}   [inst_1 : CategoryTheory.SmallCategory J] [inst_2 : (j : J) → Cat
egoryTheory.SmallCategory (I j)]   {D : CategoryTheory.Functor J C} {P : (j : J)
 → CategoryTheory.Limits.ColimitPresentation (I j) (D.obj j)} {j j' : J}   (i : 
I j) (u : j ⟶ j') [CategoryTheory.IsFiltered (I j')] [CategoryTheory.IsFinitelyP
resentable ((P j).diag.obj i)],   ∃ i' f, f.base = u
参数：j : J；I j；j : J；I j；D.obj j；i : I j；u : j ⟶ j'；I j'；(P j).diag.obj i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTh
eory.SmallCategory J]   [CategoryTheory.IsFiltered…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Total.exists_hom_of_hom {j j' : J} (i : I j) (u : j ⟶ j')
    [IsFiltered (I j')] [IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    ∃ (i' : I j') (f : Total.mk P j i ⟶ Total.mk P j' i'), f.base = u := by
  obtain ⟨i', q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (P j').isColimit
    ((P j).ι.app i ≫ D.map u)
  use i', { base := u, hom := q, w := by simp [← hq] }
/-
**CategoryTheory.Limits.ColimitPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.ColimitPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiltered J] [∀ j, IsFiltered (I j)] : Nonempty (Total P) := by
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨i⟩ : Nonempty (I j) := IsFiltered.nonempty
  exact ⟨⟨j, i⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.ColimitPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.ColimitPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiltered J] [∀ j, IsFiltered (I j)]
    [∀ j i, IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    IsFiltered (Total P) where
  cocone_objs k l := by
    let a := IsFiltered.max k.1 l.1
    obtain ⟨a', f, hf⟩ := Total.exists_hom_of_hom (P := P) k.2 (IsFiltered.leftToMax k.1 l.1)
    obtain ⟨b', g, hg⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.rightToMax k.1 l.1)
    refine ⟨⟨a, IsFiltered.max a' b'⟩, ?_, ?_, trivial⟩
    · exact f ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.leftToMax _ _) }
    · exact g ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.rightToMax _ _) }
  cocone_maps {k l} f g := by
    let a := IsFiltered.coeq f.base g.base
    obtain ⟨a', u, hu⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.coeqHom f.base g.base)
    have : (f.hom ≫ u.hom) ≫ (P _).ι.app _ = (g.hom ≫ u.hom) ≫ (P _).ι.app _ := by
      simp only [Category.assoc, Functor.const_obj_obj, ← u.w, ← f.w_assoc, ← g.w_assoc]
      rw [← Functor.map_comp, hu, IsFiltered.coeq_condition f.base g.base]
      simp
    obtain ⟨j, p, q, hpq⟩ := IsFinitelyPresentable.exists_eq_of_isColimit (P _).isColimit _ _ this
    dsimp at p q
    refine ⟨⟨a, IsFiltered.coeq p q⟩,
      u ≫ { base := 𝟙 _, hom := (P _).diag.map (p ≫ IsFiltered.coeqHom p q) }, ?_⟩
    apply Total.Hom.ext
    · simp [hu, IsFiltered.coeq_condition f.base g.base]
    · rw [Category.assoc] at hpq
      simp only [Functor.map_comp, comp_hom, reassoc_of% hpq]
      simp [← Functor.map_comp, ← IsFiltered.coeq_condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `P` is a colimit presentation over `J` of `X` and for every `j` we are given a colimit
presentation `Qⱼ` over `I j` of the `P.diag.obj j`, this is the refined colimit presentation of `X`
over `Total Q`. -/
@[simps]
/-
**CategoryTheory.Limits.ColimitPresentation.bind** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.ColimitPresentation`。
形式化陈述：bind {X : C} (P : ColimitPresentation J X) (Q : forall j, ColimitPresentat
ion (I j) (P.diag.obj j)) [forall j, IsFiltered (I j)] [forall j i, IsFinitelyPr
esentable.{w} ((Q j).diag.obj i)] : ColimitPresentation (Total Q) X where diag.o
bj k
参数：P : ColimitPresentation J X；Q : forall j, ColimitPresentation (I j) (P.diag.o
bj j)；I j；(Q j).diag.obj i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a colimit presentation over `J` of `X` and for every `j` we are given 
a colimit
presentation `Qⱼ` over `I j` of the `P.diag.obj j`, this is the refined colimit 
presentation of `X`
over `Total Q`.
-/
def bind {X : C} (P : ColimitPresentation J X) (Q : ∀ j, ColimitPresentation (I j) (P.diag.obj j))
    [∀ j, IsFiltered (I j)] [∀ j i, IsFinitelyPresentable.{w} ((Q j).diag.obj i)] :
    ColimitPresentation (Total Q) X where
  diag.obj k := (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  ι.app k := (Q k.1).ι.app k.2 ≫ P.ι.app k.1
  ι.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
          ι.naturality {i i'} u := by
            let v : Total.mk Q j i ⟶ .mk _ j i' := { base := 𝟙 _, hom := (Q _).diag.map u }
            simpa using c.ι.naturality v }
      ι.naturality {j j'} u := by
        refine (Q j).isColimit.hom_ext fun i ↦ ?_
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          (Q j).isColimit.fac]
        obtain ⟨i', hom, rfl⟩ := Total.exists_hom_of_hom (P := Q) i u
        rw [reassoc_of% hom.w, (Q j').isColimit.fac]
        simpa using c.ι.naturality hom }
  isColimit.fac := fun c ⟨j, i⟩ ↦ by simp [P.isColimit.fac, (Q j).isColimit.fac]
  isColimit.uniq c m hm := by
    refine P.isColimit.hom_ext fun j ↦ ?_
    simp only [P.isColimit.fac]
    refine (Q j).isColimit.hom_ext fun i ↦ ?_
    simpa [(Q j).isColimit.fac] using hm (.mk _ j i)

end Small

end CategoryTheory.Limits.ColimitPresentation

