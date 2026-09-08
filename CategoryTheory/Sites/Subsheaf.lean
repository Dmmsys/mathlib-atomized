/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subfunctor.Sieves

/-!

# Subsheaf of types

We define the subsheaf of a type-valued presheaf.

## Main results

- `CategoryTheory.Subfunctor.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `CategoryTheory.Subfunctor.sheafify_isSheaf` :
  The sheafification is a sheaf
- `CategoryTheory.Subfunctor.sheafifyLift` :
  The descent of a map into a sheaf to the sheafification.
- `CategoryTheory.GrothendieckTopology.imageSheaf` : The image sheaf of a morphism.
- `CategoryTheory.GrothendieckTopology.imageFactorization` : The image sheaf as a
  `Limits.imageFactorization`.
-/

@[expose] public section


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subfunctor F)

/-- Every subpresheaf of a separated presheaf is itself separated. -/
/-
**CategoryTheory.Subfunctor.isSeparated** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)}   (G : CategoryTheory.Subfunctor F) {J : CategoryTheory
.GrothendieckTopology C},   CategoryTheory.Presieve.IsSeparated J F → CategoryTh
eory.Presieve.IsSeparated J G.toFunctor
参数：Type w；G : CategoryTheory.Subfunctor F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.map`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor C
ᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…

--- 原说明 ---
Every subpresheaf of a separated presheaf is itself separated.
-/
theorem Subfunctor.isSeparated {J : GrothendieckTopology C} (h : Presieve.IsSeparated J F) :
    Presieve.IsSeparated J G.toFunctor :=
  fun _ S hS _ _ _ hx₁ hx₂ ↦ Subtype.ext <| h S hS _ _ _ (hx₁.map G.ι) (hx₂.map G.ι)

set_option backward.defeqAttrib.useBackward true in
/-- The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf. -/
/-
**CategoryTheory.Subfunctor.sheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.GrothendieckTopology C →       {F : CategoryTheory.Functor Cᵒᵖ (Type w)} →
 CategoryTheory.Subfunctor F → CategoryTheory.Subfunctor F
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf.
-/
def Subfunctor.sheafify : Subfunctor F where
  obj U := { s | G.sieveOfSection s ∈ J (unop U) }
  map := by
    rintro U V i s hs
    refine J.superset_covering ?_ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp at h ⊢
    rwa [← comp_apply, ← Functor.map_comp]
/-
**CategoryTheory.Subfunctor.le_sheafify** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C)   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : Cate
goryTheory.Subfunctor F),   G ≤ CategoryTheory.Subfunctor.sheafify J G
参数：J : CategoryTheory.GrothendieckTopology C；Type w；G : CategoryTheory.Subfuncto
r F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `CategoryTheory.Subfunctor.map`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (self : CategoryTheory
.Subfunctor F) {U V…
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X
-/
theorem Subfunctor.le_sheafify : G ≤ G.sheafify J := by
  intro U s hs
  change _ ∈ J _
  convert! J.top_mem U.unop
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

variable {J}
/-
**CategoryTheory.Subfunctor.eq_sheafify** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : Cate
goryTheory.Subfunctor F),   CategoryTheory.Presieve.IsSheaf J F →     CategoryTh
eory.Presieve.IsSheaf J G.toFunctor → G = CategoryTheory.Subfunctor.sheafify J G
参数：Type w；G : CategoryTheory.Subfunctor F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `CategoryTheory.Subfunctor.le_sheafify`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C)   {F : Categ
oryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `CategoryTheory.Subfunctor.family_of_elements_compatible`：family_of_eleme
nts_compatible {U : Cᵒᵖ} (s : F.obj U) : (G.familyOfElementsOfSection s).Compati
ble
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Subfunctor.eq_sheafify (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toFunctor) :
    G = G.sheafify J := by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).isSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) :)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Subfunctor.sheafify_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : Cate
goryTheory.Subfunctor F),   CategoryTheory.Presieve.IsSheaf J F →     CategoryTh
eory.Presieve.IsSheaf J (CategoryTheory.Subfunctor.sheafify J G).toFunctor
参数：Type w；G : CategoryTheory.Subfunctor F；CategoryTheory.Subfunctor.sheafify J G
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparated.isSheaf`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `CategoryTheory.Subfunctor.isSeparated`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Type w)}   (G : Categor
yTheory.Subfunctor F) {J : …
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GrothendieckTopology.bind_covering`：bind_covering {S : Si
eve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X) (hR : fo
rall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in …
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Subfunctor.sheafify_isSheaf (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (G.sheafify J).toFunctor := by
  refine (isSeparated _ hF.isSeparated).isSheaf fun U S hS x hx ↦ ?_
  let S' := Sieve.bind S fun Y f hf => G.sieveOfSection (x f hf).1
  have := fun (V) (i : V ⟶ U) (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂ using this
  dsimp [-Sieve.bind_apply] at *
  let x'' : Presieve.FamilyOfElements F S' := fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi))
  have H : ∀ s, x''.IsAmalgamation s.1 → x.IsAmalgamation s := by
    intro s H V i hi
    refine Subtype.ext ?_
    apply (hF _ (x i hi).2).isSeparatedFor.ext
    intro V' i' hi'
    have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
    have := H _ hi''
    rw [op_comp, F.map_comp] at this
    exact this.trans (congr_arg Subtype.val (hx _ _ (hi₂ _ _ hi'') hi (h₂ _ _ hi'')))
  have : x''.Compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← comp_apply, ← Functor.map_comp, ← comp_apply, Functor.map_comp]
    simpa using!
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ _ _ S₁) (g₂ ≫ i₁ _ _ S₂) (hi₂ _ _ S₁) (hi₂ _ _ S₂)
        (by simp only [Category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine ⟨⟨t, _⟩, H ⟨t, ?_⟩ ht⟩
  refine J.superset_covering ?_ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp
  rw [ht _ hi]
  exact h₁ _ _ hi
/-
**CategoryTheory.Subfunctor.eq_sheafify_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : Cate
goryTheory.Subfunctor F),   CategoryTheory.Presieve.IsSheaf J F →     (G = Categ
oryTheory.Subfunctor.sheafify J G ↔ CategoryTheory.Presieve.IsSheaf J G.toFuncto
r)
参数：Type w；G : CategoryTheory.Subfunctor F；G = CategoryTheory.Subfunctor.sheafify
 J G ↔ CategoryTheory.Presieve.IsSheaf J G.toFunctor。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.sheafify_isSheaf`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F : 
CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subfunctor.eq_sheafify`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F : Categ
oryTheory.Functor Cᵒᵖ (Type…
-/
theorem Subfunctor.eq_sheafify_iff (h : Presieve.IsSheaf J F) :
    G = G.sheafify J ↔ Presieve.IsSheaf J G.toFunctor :=
  ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩
/-
**CategoryTheory.Subfunctor.isSheaf_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : Cate
goryTheory.Subfunctor F),   CategoryTheory.Presieve.IsSheaf J F →     (CategoryT
heory.Presieve.IsSheaf J G.toFunctor ↔       ∀ (U : Cᵒᵖ) (s : F.obj U), G.sieveO
fSection s ∈ J (Opposite.unop U) → s ∈ G.obj U)
参数：Type w；G : CategoryTheory.Subfunctor F；CategoryTheory.Presieve.IsSheaf J G.to
Functor ↔       ∀ (U : Cᵒᵖ) (s : F.obj U), G.sieveOfSection s ∈ J (Opposite.unop
 U) → s ∈ G.obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subfunctor.eq_sheafify_iff`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F : C
ategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `CategoryTheory.Subfunctor.le_sheafify`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C)   {F : Categ
oryTheory.Functor Cᵒᵖ (Type…
-/
theorem Subfunctor.isSheaf_iff (h : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J G.toFunctor ↔
      ∀ (U) (s : F.obj U), G.sieveOfSection s ∈ J (unop U) → s ∈ G.obj U := by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J ≤ G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩
/-
**CategoryTheory.Subfunctor.sheafify_sheafify** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : Cate
goryTheory.Subfunctor F),   CategoryTheory.Presieve.IsSheaf J F →     CategoryTh
eory.Subfunctor.sheafify J (CategoryTheory.Subfunctor.sheafify J G) =       Cate
goryTheory.Subfunctor.sheafify J G
参数：Type w；G : CategoryTheory.Subfunctor F；CategoryTheory.Subfunctor.sheafify J G
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subfunctor.eq_sheafify_iff`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F : C
ategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `CategoryTheory.Subfunctor.sheafify_isSheaf`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F : 
CategoryTheory.Functor Cᵒᵖ (Type…
-/
theorem Subfunctor.sheafify_sheafify (h : Presieve.IsSheaf J F) :
    (G.sheafify J).sheafify J = G.sheafify J :=
  ((Subfunctor.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The lift of a presheaf morphism onto the sheafification subpresheaf. -/
/-
**CategoryTheory.Subfunctor.sheafifyLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Subfunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {F F' : CategoryTheory.Functor Cᵒᵖ (T
ype w)} →         (G : CategoryTheory.Subfunctor F) →           (G.toFunctor ⟶ F
') →             CategoryTheory.Presieve.IsSheaf J F' → ((CategoryTheory.Subfunc
tor.sheafify J G).toFunctor ⟶ F')
参数：Type w；G : CategoryTheory.Subfunctor F；G.toFunctor ⟶ F'；(CategoryTheory.Subfu
nctor.sheafify J G).toFunctor ⟶ F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of a presheaf morphism onto the sheafification subpresheaf.
-/
noncomputable def Subfunctor.sheafifyLift (f : G.toFunctor ⟶ F') (h : Presieve.IsSheaf J F') :
    (G.sheafify J).toFunctor ⟶ F' where
  app _ := ↾fun s ↦ (h (G.sieveOfSection s.1) s.prop).amalgamate
    (_) ((G.family_of_elements_compatible s.1).map f)
  naturality := by
    intro U V i
    ext s
    apply (h _ ((Subfunctor.sheafify J G).toFunctor.map i s).prop).isSeparatedFor.ext
    intro W j hj
    refine (Presieve.IsSheafFor.valid_glue (h _ ((G.sheafify J).toFunctor.map i s).2)
      ((G.family_of_elements_compatible _).map _) _ hj).trans ?_
    dsimp
    simp only [← comp_apply, ← Functor.map_comp]
    change _ = F'.map (j ≫ i.unop).op _
    refine Eq.trans ?_ (Presieve.IsSheafFor.valid_glue (h _ s.2)
      ((G.family_of_elements_compatible s.1).map f) (j ≫ i.unop) ?_).symm
    · simp [Presieve.FamilyOfElements.map, Subfunctor.familyOfElementsOfSection]
      rfl
    · dsimp [Presieve.FamilyOfElements.map] at hj ⊢
      rwa [Functor.map_comp, comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subfunctor.to_sheafifyLift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F F' : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : C
ategoryTheory.Subfunctor F) (f : G.toFunctor ⟶ F')   (h : CategoryTheory.Presiev
e.IsSheaf J F'),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Subfunctor
.homOfLe ⋯) (G.sheafifyLift f h) = f
参数：Type w；G : CategoryTheory.Subfunctor F；f : G.toFunctor ⟶ F'；h : CategoryTheor
y.Presieve.IsSheaf J F'；CategoryTheory.Subfunctor.homOfLe ⋯；G.sheafifyLift f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.Subfunctor.le_sheafify`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C)   {F : Categ
oryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Mathlib.Tactic.Elementwise.hom_elementwise`：hom_elementwise {C : Type*} 
[Category* C] {FC : outParam <| C -> C -> Type*} {CC : outParam <| C -> Type*} {
_ : outParam <| forall X Y, FunL…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.map`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor Cᵒᵖ (
Type w)} {X : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Subfunctor.family_of_elements_compatible`：family_of_eleme
nts_compatible {U : Cᵒᵖ} (s : F.obj U) : (G.familyOfElementsOfSection s).Compati
ble
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
-/
theorem Subfunctor.to_sheafifyLift (f : G.toFunctor ⟶ F') (h : Presieve.IsSheaf J F') :
    Subfunctor.homOfLe (G.le_sheafify J) ≫ G.sheafifyLift f h = f := by
  ext U s
  apply (h _ ((Subfunctor.homOfLe (G.le_sheafify J)).app U s).prop).isSeparatedFor.ext
  intro V i hi
  have := elementwise_of% f.naturality
  exact (Presieve.IsSheafFor.valid_glue (h _ ((homOfLe (_ : _ ≤ sheafify _ _)).app _ _).2)
    ((G.family_of_elements_compatible _).map _) _ _).trans (this _ _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Subfunctor.to_sheafify_lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F F' : CategoryTheory.Functor Cᵒᵖ (Type w)} (G : C
ategoryTheory.Subfunctor F),   CategoryTheory.Presieve.IsSheaf J F' →     ∀ (l₁ 
l₂ : (CategoryTheory.Subfunctor.sheafify J G).toFunctor ⟶ F'),       CategoryThe
ory.CategoryStruct.comp (CategoryTheory.Subfunctor.homOfLe ⋯) l₁ =           Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Subfunctor.homOfLe ⋯) l₂ →      
   l₁ = l₂
参数：Type w；G : CategoryTheory.Subfunctor F；l₁ l₂ : (CategoryTheory.Subfunctor.she
afify J G).toFunctor ⟶ F'；CategoryTheory.Subfunctor.homOfLe ⋯；CategoryTheory.Sub
functor.homOfLe ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.le_sheafify`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C)   {F : Categ
oryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
theorem Subfunctor.to_sheafify_lift_unique (h : Presieve.IsSheaf J F')
    (l₁ l₂ : (G.sheafify J).toFunctor ⟶ F')
    (e : Subfunctor.homOfLe (G.le_sheafify J) ≫ l₁ = Subfunctor.homOfLe (G.le_sheafify J) ≫ l₂) :
    l₁ = l₂ := by
  ext U s
  apply (h _ s.prop).isSeparatedFor.ext
  rintro V i hi
  dsimp
  rw [← dsimp% l₁.naturality_apply, ← dsimp% l₂.naturality_apply]
  exact ConcreteCategory.congr_hom (congr_app e <| op V) ⟨_, hi⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subfunctor.sheafify_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {F : CategoryTheory.Functor Cᵒᵖ (Type w)} (G G' : C
ategoryTheory.Subfunctor F),   G ≤ G' →     CategoryTheory.Presieve.IsSheaf J F 
→       CategoryTheory.Presieve.IsSheaf J G'.toFunctor → CategoryTheory.Subfunct
or.sheafify J G ≤ G'
参数：Type w；G G' : CategoryTheory.Subfunctor F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Subfunctor.le_sheafify`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C)   {F : Categ
oryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Subfunctor.to_sheafifyLift`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F F' 
: CategoryTheory.Functor Cᵒᵖ (T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subfunctor.nat_trans_naturality`：nat_trans_naturality (f 
: F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V) (x : F'.obj U) : (f.app V (F'.map i x)
).1 = F.map i (f.app U x).1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Subfunctor.sheafify_le (h : G ≤ G') (hF : Presieve.IsSheaf J F)
    (hG' : Presieve.IsSheaf J G'.toFunctor) : G.sheafify J ≤ G' := by
  intro U x hx
  convert! ((G.sheafifyLift (Subfunctor.homOfLe h) hG').app U ⟨x, hx⟩).2
  apply (hF _ hx).isSeparatedFor.ext
  intro V i hi
  have :=
    congr_arg (fun f : G.toFunctor ⟶ G'.toFunctor => (NatTrans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafifyLift (Subfunctor.homOfLe h) hG')
  convert! this.symm
  rw [← Subfunctor.nat_trans_naturality]
  rfl

section Image

variable (J) in
/-- A morphism factors through the sheafification of the image presheaf. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.Subfunctor.toRangeSheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Subfunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (J : Cate
goryTheory.GrothendieckTopology C) →       {F F' : CategoryTheory.Functor Cᵒᵖ (T
ype w)} →         (f : F' ⟶ F) → F' ⟶ (CategoryTheory.Subfunctor.sheafify J (Cat
egoryTheory.Subfunctor.range f)).toFunctor
参数：J : CategoryTheory.GrothendieckTopology C；Type w；f : F' ⟶ F；CategoryTheory.Su
bfunctor.sheafify J (CategoryTheory.Subfunctor.range f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism factors through the sheafification of the image presheaf.
-/
def Subfunctor.toRangeSheafify (f : F' ⟶ F) : F' ⟶ ((Subfunctor.range f).sheafify J).toFunctor :=
  toRange f ≫ Subfunctor.homOfLe ((range f).le_sheafify J)

/-- The image sheaf of a morphism between sheaves, defined to be the sheafification of
`image_presheaf`. -/
@[simps]
/-
**CategoryTheory.Sheaf.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {F F' : CategoryTheory.Sheaf J (Type 
w)} → (F ⟶ F') → CategoryTheory.Sheaf J (Type w)
参数：Type w；F ⟶ F'；Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image sheaf of a morphism between sheaves, defined to be the sheafification 
of
`image_presheaf`.
-/
def Sheaf.image {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf J (Type w) :=
  ⟨((Subfunctor.range f.1).sheafify J).toFunctor, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F'.2⟩

/-- A morphism factors through the image sheaf. -/
@[simps]
/-
**CategoryTheory.Sheaf.toImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {F F' : CategoryTheory.Sheaf J (Type 
w)} → (f : F ⟶ F') → F ⟶ CategoryTheory.Sheaf.image f
参数：Type w；f : F ⟶ F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism factors through the image sheaf.
-/
def Sheaf.toImage {F F' : Sheaf J (Type w)} (f : F ⟶ F') : F ⟶ Sheaf.image f :=
  ⟨Subfunctor.toRangeSheafify J f.1⟩

/-- The inclusion of the image sheaf to the target. -/
@[simps]
/-
**CategoryTheory.Sheaf.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {F F' : CategoryTheory.Sheaf J (Type 
w)} → (F ⟶ F') → CategoryTheory.Sheaf J (Type w)
参数：Type w；F ⟶ F'；Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the image sheaf to the target.
-/
def Sheaf.imageι {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf.image f ⟶ F' :=
  ⟨Subfunctor.ι _⟩


set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Sheaf.toImage_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sheaf.toImage_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    toImage f ≫ imageι f = f := by
  ext1
  simp [Subfunctor.toRangeSheafify]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Mono (Sheaf.imageι f) :=
  (sheafToPresheaf J _).mono_of_mono_map
    (by
      dsimp
      infer_instance)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Epi (Sheaf.toImage f) := by
  refine ⟨@fun G' g₁ g₂ e => ?_⟩
  ext U ⟨s, hx⟩
  apply ((isSheaf_iff_isSheaf_of_type J _).mp G'.2 _ hx).isSeparatedFor.ext
  rintro V i ⟨y, e'⟩
  change (g₁.hom.app _ ≫ G'.obj.map _) _ = (g₂.hom.app _ ≫ G'.obj.map _) _
  rw [← NatTrans.naturality, ← NatTrans.naturality]
  have E : (Sheaf.toImage f).hom.app (op V) y = (Sheaf.image f).obj.map i.op ⟨s, hx⟩ :=
    Subtype.ext e'
  have := congr_arg (fun f : F ⟶ G' => f.hom.app _ y) e
  simp only [ObjectProperty.FullSubcategory.comp_hom, Sheaf.toImage_hom,
    NatTrans.comp_app, comp_apply, op_unop] at this E ⊢
  convert this <;> exact E.symm

/-- The mono factorization given by `image_sheaf` for a morphism. -/
/-
**CategoryTheory.imageMonoFactorization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：imageMonoFactorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Limits.Mon
oFactorisation f where I
参数：Type w；f : F ⟶ F'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoSheafTypeImageι`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F F' : C
ategoryTheory.Sheaf J (Type …

--- 原说明 ---
The mono factorization given by `image_sheaf` for a morphism.
-/
def imageMonoFactorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    Limits.MonoFactorisation f where
  I := Sheaf.image f
  m := Sheaf.imageι f
  e := Sheaf.toImage f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The mono factorization given by `image_sheaf` for a morphism is an image. -/
/-
**CategoryTheory.imageFactorization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：imageFactorization {F F' : Sheaf J (Type (max v u))} (f : F ⟶ F') : Limits
.ImageFactorisation f where F
参数：Type (max v u)；f : F ⟶ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mono factorization given by `image_sheaf` for a morphism is an image.
-/
noncomputable def imageFactorization {F F' : Sheaf J (Type (max v u))} (f : F ⟶ F') :
    Limits.ImageFactorisation f where
  F := imageMonoFactorization f
  isImage :=
    { lift := fun I => by
        haveI M := (Sheaf.Hom.mono_iff_presheaf_mono J (Type (max v u)) _).mp I.m_mono
        refine ⟨Subfunctor.homOfLe ?_ ≫ inv (Subfunctor.toRange I.m.1)⟩
        apply Subfunctor.sheafify_le
        · conv_lhs => rw [← I.fac]
          apply Subfunctor.range_comp_le
        · rw [← isSheaf_iff_isSheaf_of_type]
          exact F'.2
        · apply Presieve.isSheaf_iso J (asIso <| Subfunctor.toRange I.m.1)
          rw [← isSheaf_iff_isSheaf_of_type]
          exact I.I.2
      lift_fac := fun I => by
        ext1
        dsimp [imageMonoFactorization]
        generalize_proofs h
        rw [← Subfunctor.homOfLe_ι h, Category.assoc]
        congr 1
        rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι] }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasImages (Sheaf J (Type max v u)) :=
  ⟨fun f => ⟨⟨imageFactorization f⟩⟩⟩

end Image

end CategoryTheory

