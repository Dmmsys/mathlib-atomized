/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category.

A presheaf on a topological space `X` is a sheaf precisely when it is a sheaf under the
Grothendieck topology on `opens X`, which expands out to say: For each open cover `{ Uᵢ }` of
`U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an `A : X`, there exists a unique
gluing `A ⟶ F(U)` compatible with the restriction.

See the docstring of `TopCat.Presheaf.IsSheaf` for an explanation on the design decisions and a list
of equivalent conditions.

We provide the instance `CategoryTheory.Category (TopCat.Sheaf C X)` as the full subcategory of
presheaves, and the fully faithful functor `Sheaf.forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X`.

-/

@[expose] public section


universe w v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

namespace Presheaf

/-- The sheaf condition has several different equivalent formulations.
The official definition chosen here is in terms of Grothendieck topologies so that the results on
sites could be applied here easily, and this condition does not require additional constraints on
the value category.
The equivalent formulations of the sheaf condition on `presheaf C X` are as follows :

1. `TopCat.Presheaf.IsSheaf`: (the official definition)
  It is a sheaf with respect to the Grothendieck topology on `opens X`, which is to say:
  For each open cover `{ Uᵢ }` of `U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an
  `A : X`, there exists a unique gluing `A ⟶ F(U)` compatible with the restriction.

2. `TopCat.Presheaf.IsSheafEqualizerProducts`: (requires `C` to have all products)
  For each open cover `{ Uᵢ }` of `U`, `F(U) ⟶ ∏ᶜ F(Uᵢ)` is the equalizer of the two morphisms
  `∏ᶜ F(Uᵢ) ⟶ ∏ᶜ F(Uᵢ ∩ Uⱼ)`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`.

3. `TopCat.Presheaf.IsSheafOpensLeCover`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  `F(V₁) ⟶ F(V₂)` for every pair of open sets `V₁ ⊇ V₂` that are contained in some `Uᵢ`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`.

4. `TopCat.Presheaf.IsSheafPairwiseIntersections`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  from `F(Uᵢ)` and `F(Uⱼ)` to `F(Uᵢ ∩ Uⱼ)` for each pair `(i, j)`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`.

The following requires `C` to be concrete and complete, and `forget C` to reflect isomorphisms and
preserve limits. This applies to most "algebraic" categories, e.g. groups, abelian groups and rings.

5. `TopCat.Presheaf.IsSheafUniqueGluing`:
  (requires `C` to be concrete and complete; `forget C` to reflect isomorphisms and preserve limits)
  For each open cover `{ Uᵢ }` of `U`, and a compatible family of elements `x : F(Uᵢ)`, there exists
  a unique gluing `x : F(U)` that restricts to the given elements.
  See `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`.

6. The underlying sheaf of types is a sheaf.
  See `TopCat.Presheaf.isSheaf_iff_isSheaf_comp` and
  `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`.
-/
nonrec def IsSheaf (F : Presheaf.{w, v, u} C X) : Prop :=
  Presheaf.IsSheaf (Opens.grothendieckTopology X) F

/-- The presheaf valued in `Unit` over any topological space is a sheaf.
-/
/-
**TopCat.Presheaf.isSheaf_unit** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：isSheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf
参数：F : Presheaf (CategoryTheory.Discrete Unit) X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Discrete.instSubsingleton`：∀ {α : Type u₁} [Subsingleton 
α], Subsingleton (CategoryTheory.Discrete α)
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}

--- 原说明 ---
The presheaf valued in `Unit` over any topological space is a sheaf.
-/
theorem isSheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf :=
  fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by cat_disch, fun _ => by cat_disch⟩
/-
**TopCat.Presheaf.isSheaf_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：isSheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf
参数：α : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'
-/
theorem isSheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf :=
  Presheaf.isSheaf_of_iso_iff α

/-- Transfer the sheaf condition across an isomorphism of presheaves.
-/
/-
**TopCat.Presheaf.isSheaf_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：isSheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsShea
f
参数：α : F ≅ G；h : F.IsSheaf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.Presheaf.isSheaf_iso_iff`：isSheaf_iso_iff {F G : Presheaf C X} (α
 : F ≅ G) : F.IsSheaf ↔ G.IsSheaf

--- 原说明 ---
Transfer the sheaf condition across an isomorphism of presheaves.
-/
theorem isSheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsSheaf :=
  (isSheaf_iso_iff α).1 h

end Presheaf

variable (C X)

/-- A `TopCat.Sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
nonrec def Sheaf : Type max u v w :=
  Sheaf (Opens.grothendieckTopology X) C
deriving Category

variable {C X}

/-- The underlying presheaf of a sheaf -/
/-
**TopCat.Sheaf.presheaf** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X : TopCat} → 
TopCat.Sheaf C X → TopCat.Presheaf C X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying presheaf of a sheaf
-/
abbrev Sheaf.presheaf (F : X.Sheaf C) : TopCat.Presheaf C X :=
  F.1

variable (C X)

-- Let's construct a trivial example, to keep the inhabited linter happy.
/-
**TopCat.sheafInhabited** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：sheafInhabited : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sheafInhabited : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X) :=
  ⟨⟨Functor.star _, Presheaf.isSheaf_unit _⟩⟩

namespace Sheaf

/-- The forgetful functor from sheaves to presheaves.
-/
/-
**TopCat.Sheaf.forget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from sheaves to presheaves.
-/
def forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X :=
  sheafToPresheaf _ _

-- The following instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
/-
**TopCat.Sheaf.forget_full** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
形式化陈述：forget_full : (forget C X).Full where map_surjective f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_full : (forget C X).Full where
  map_surjective f := ⟨ObjectProperty.homMk f, rfl⟩
/-
**TopCat.Sheaf.forgetFaithful** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
形式化陈述：forgetFaithful : (forget C X).Faithful where map_injective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.hom_ext`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u₂}   [i
nst_1 : CategoryTh…
-/
instance forgetFaithful : (forget C X).Faithful where
  map_injective := Sheaf.hom_ext

-- Note: These can be proved by simp.
/-
**TopCat.Sheaf.id_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：id_app (F : Sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _
参数：F : Sheaf C X；t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_app (F : Sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ :=
  rfl
/-
**TopCat.Sheaf.comp_app** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sheaf`。
形式化陈述：comp_app {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) : (f ≫ g).1.app t
 = f.1.app t ≫ g.1.app t
参数：f : F ⟶ G；g : G ⟶ H；t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_app {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
    (f ≫ g).1.app t = f.1.app t ≫ g.1.app t :=
  rfl

end Sheaf

/-
**TopCat.Presheaf.IsSheaf.section_ext** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf
.IsSheaf`。
形式化陈述：∀ {X : TopCat} {A : Type u_1} [inst : CategoryTheory.Category.{u, u_1} A] 
{FC : A → A → Type u_2} {CC : A → Type u}   [inst_1 : (X Y : A) → FunLike (FC X 
Y) (CC X) (CC Y)] [inst_2 : CategoryTheory.ConcreteCategory A FC]   [CategoryThe
ory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.f
orget A)]   [(CategoryTheory.forget A).ReflectsIsomorphisms] {F : TopCat.Preshea
f A X},   F.IsSheaf →     ∀ {U : (TopologicalSpace.Opens ↑X)ᵒᵖ} {s t : CategoryT
heory.ToType (F.obj U)},       (∀ x ∈ Opposite.unop U,           ∃ V,           
  ∃ (hV : V ≤ Opposite.unop U),               x ∈ V ∧                 (CategoryT
heory.ConcreteCategory.hom (F.map (CategoryTheory.homOfLE hV).op)) s =          
         (CategoryTheory.ConcreteCategory.hom (F.map (CategoryTheory.homOfLE hV)
.op)) t) →         s = t
参数：X Y : A；FC X Y；CC X；CC Y；CategoryTheory.forget A；CategoryTheory.forget A；Topo
logicalSpace.Opens ↑X；F.obj U；∀ x ∈ Opposite.unop U,           ∃ V,             
∃ (hV : V ≤ Opposite.unop U),               x ∈ V ∧                 (CategoryThe
ory.ConcreteCategory.hom (F.map (CategoryTheory.homOfLE hV).op)) s =            
       (CategoryTheory.ConcreteCategory.hom (F.map (CategoryTheory.homOfLE hV).o
p)) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`：isSheaf_iff_isSheaf_
forget (s : A' ⥤ Type (max v₁ u₁)) [HasLimits A'] [PreservesLimits s] [s.Reflect
sIsomorphisms] : IsSheaf J P' ↔ IsSheaf …
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSheafFor`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTopology C}
   {P : CategoryTheory.Functor C…
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Presheaf.IsSheaf.section_ext {X : TopCat.{u}}
    {A : Type*} [Category.{u} A] {FC : A → A → Type*} {CC : A → Type u}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    [HasLimits A] [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]
    {F : TopCat.Presheaf A X} (hF : TopCat.Presheaf.IsSheaf F)
    {U : (Opens X)ᵒᵖ} {s t : ToType (F.obj U)}
    (hst : ∀ x ∈ U.unop, ∃ V, ∃ hV : V ≤ U.unop, x ∈ V ∧
      F.map (homOfLE hV).op s = F.map (homOfLE hV).op t) :
    s = t := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (C := Opens X) (A' := A) _ F (forget _)).mp hF)
  choose V hV hxV H using fun x : U.unop ↦ hst x.1 x.2
  refine (this.isSheafFor (.ofArrows V fun x ↦ homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · exact fun x hx ↦ ⟨V ⟨x, hx⟩, homOfLE (hV _), Sieve.ofArrows_mk _ _ _, hxV _⟩
  · rintro _ _ ⟨x⟩; exact H x

end TopCat

