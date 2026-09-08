/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.
Conversely, if `F : C ⥤ D` is a functor between preadditive categories, where `C` has binary
biproducts, and if `F` preserves binary biproducts, then `F` is additive.

We also define the category of bundled additive functors.

## Implementation details

`Functor.Additive` is a `Prop`-valued class, defined by saying that for every two objects `X` and
`Y`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian groups.

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
@[stacks 00ZY]
/-
**CategoryTheory.Functor.Additive** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [C
ategoryTheory.Preadditive C] → [CategoryTheory.Preadditive D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` is additive provided `F.map` is an additive homomorphism.
-/
class Functor.Additive {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) : Prop where
  /-- the addition of two morphisms is mapped to the sum of their images -/
  map_add : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g := by cat_disch

section Preadditive

namespace Functor

section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]

@[simp]
/-
**CategoryTheory.Functor.map_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Additive.map_add`：∀ {C : Type u_1} {D : Type u_2}
 {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
  Functor.Additive.map_add

/-- `F.mapAddHom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapAddHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：mapAddHom {X Y : C} : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g

--- 原说明 ---
`F.mapAddHom` is an additive homomorphism whose underlying function is `F.map`.
-/
def mapAddHom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun _ _ => F.map_add
/-
**CategoryTheory.Functor.coe_mapAddHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：coe_mapAddHom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) ->+ _) = F.map
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mapAddHom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) →+ _) = F.map :=
  rfl
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesZeroMorphisms_of_additive : PreservesZeroMorphisms F where
  map_zero _ _ := F.mapAddHom.map_zero
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Additive (𝟭 C) where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : Type*} [Category* E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] :
    Additive (F ⋙ G) where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] (j : J) : ((evaluation J C).obj j).Additive where

@[simp]
/-
**CategoryTheory.Functor.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]
/-
**CategoryTheory.Functor.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_sub _ _
/-
**CategoryTheory.Functor.map_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：map_nsmul {X Y : C} {f : X ⟶ Y} {n : Nat} : F.map (n • f) = n • F.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
theorem map_nsmul {X Y : C} {f : X ⟶ Y} {n : ℕ} : F.map (n • f) = n • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

-- You can alternatively just use `Functor.map_smul` here, with an explicit `(r : ℤ)` argument.
/-
**CategoryTheory.Functor.map_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：map_zsmul {X Y : C} {f : X ⟶ Y} {r : Int} : F.map (r • f) = r • F.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
-/
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

@[simp]
nonrec theorem map_sum {X Y : C} {α : Type*} (f : α → (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a ∈ s, f a) = ∑ a ∈ s, F.map (f a) :=
  map_sum F.mapAddHom f s

variable {F}
/-
**CategoryTheory.Functor.additive_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：additive_of_iso {G : C ⥤ D} (e : F ≅ G) : G.Additive
参数：e : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma additive_of_iso {G : C ⥤ D} (e : F ≅ G) : G.Additive := by
  constructor
  intro X Y f g
  simp only [← NatIso.naturality_1 e (f + g), map_add, Preadditive.add_comp,
    NatTrans.naturality, Preadditive.comp_add, Iso.inv_hom_id_app_assoc]

omit [F.Additive] in
/-
**CategoryTheory.Functor.additive_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：additive_iff_of_iso {G : C ⥤ D} (e : F ≅ G) : F.Additive ↔ G.Additive
参数：e : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.additive_of_iso`：additive_of_iso {G : C ⥤ D} (e :
 F ≅ G) : G.Additive
-/
lemma additive_iff_of_iso {G : C ⥤ D} (e : F ≅ G) : F.Additive ↔ G.Additive :=
  ⟨fun _ => additive_of_iso e, fun _ => additive_of_iso e.symm⟩

variable (F)
/-
**CategoryTheory.Functor.additive_of_full_essSurj_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：additive_of_full_essSurj_comp [Full F] [EssSurj F] (G : D ⥤ E) [(F ⋙ G).Ad
ditive] : G.Additive where map_add {X Y f g}
参数：G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
lemma additive_of_full_essSurj_comp [Full F] [EssSurj F] (G : D ⥤ E)
    [(F ⋙ G).Additive] : G.Additive where
  map_add {X Y f g} := by
    obtain ⟨f', hf'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫
      (F.objObjPreimageIso Y).inv)
    obtain ⟨g', hg'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ g ≫
      (F.objObjPreimageIso Y).inv)
    simp only [← cancel_mono (G.map (F.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (F.objObjPreimageIso X).hom),
      Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp]
    erw [← hf', ← hg', ← (F ⋙ G).map_add]
    dsimp
    rw [F.map_add]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.additive_of_comp_faithful** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：additive_of_comp_faithful (F : C ⥤ D) (G : D ⥤ E) [G.Additive] [(F ⋙ G).Ad
ditive] [Faithful G] : F.Additive where map_add {_ _ f₁ f₂}
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
lemma additive_of_comp_faithful
    (F : C ⥤ D) (G : D ⥤ E) [G.Additive] [(F ⋙ G).Additive] [Faithful G] :
    F.Additive where
  map_add {_ _ f₁ f₂} := G.map_injective (by
    rw [← Functor.comp_map, G.map_add, (F ⋙ G).map_add, Functor.comp_map, Functor.comp_map])

open ZeroObject Limits in
include F in
/-
**CategoryTheory.Functor.hasZeroObject_of_additive** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：hasZeroObject_of_additive [HasZeroObject C] : HasZeroObject D where zero
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.id_zero`：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma hasZeroObject_of_additive [HasZeroObject C] :
    HasZeroObject D where
  zero := ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩

open Limits ZeroObject
/-
**CategoryTheory.Functor.Additive.of_isZero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor.Additive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   [inst_3 : CategoryTheory.Preadditive D] {F : CategoryTheory.Func
tor C D}, CategoryTheory.Limits.IsZero F → F.Additive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma Additive.of_isZero {F : C ⥤ D} (hF : IsZero F) :
    F.Additive where
  map_add {_ _ _ _} :=
    IsZero.eq_of_tgt (by
      rw [IsZero.iff_id_eq_zero]
      exact NatTrans.congr_app ((IsZero.iff_id_eq_zero _).1 hF) _) _ _
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject D] : Functor.Additive (0 : C ⥤ D) :=
  .of_isZero (isZero_zero _)

omit [Preadditive C] in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ E) [F.Additive] : ((Functor.whiskeringRight C D E).obj F).Additive where

omit [Preadditive C] [Preadditive D] in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Functor.whiskeringRight C D E).Additive where

omit [Preadditive C] [Preadditive D] in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) : ((Functor.whiskeringLeft C D E).obj F).Additive where

set_option backward.defeqAttrib.useBackward true in
omit [Preadditive D] in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E' : Type*} [Category* E'] [Preadditive E'] (G : C ⥤ D ⥤ E) (F : E ⥤ E')
    [F.Additive] [G.Additive] : ((Functor.postcompose₂.obj F).obj G).Additive := by
  dsimp [Functor.postcompose₂]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
universe w in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCoproducts.{w} C] : (sigmaConst.{w} (C := C)).Additive where

end

section InducedCategory

variable {C : Type*} {D : Type*} [Category* D] [Preadditive D] (F : C → D)

/-
**CategoryTheory.Functor.inducedFunctor_additive** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 D] [inst_1 : CategoryTheory.Preadditive D]   (F : C → D), (CategoryTheory.induc
edFunctor F).Additive
参数：F : C → D；CategoryTheory.inducedFunctor F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inducedFunctor_additive : Functor.Additive (inducedFunctor F) where

end InducedCategory

/-
**CategoryTheory.Functor.fullSubcategoryInclusion_additive** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (Z : CategoryTheory.ObjectProperty C), Z.ι.Additi
ve
参数：Z : CategoryTheory.ObjectProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fullSubcategoryInclusion_additive {C : Type*} [Category* C] [Preadditive C]
    (Z : ObjectProperty C) : Z.ι.Additive where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : D ⥤ C) [F.Additive] (P : ObjectProperty C)
    (hF : ∀ (X : D), P (F.obj X)) :
    (P.lift F hF).Additive where

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D)

open CategoryTheory.Limits

open CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesFiniteBiproductsOfAdditive [Additive F] :
    PreservesFiniteBiproducts F where
  preserves := fun {J} _ =>
    let ⟨_⟩ := nonempty_fintype J
    { preserves :=
      { preserves := fun hb =>
          ⟨isBilimitOfTotal _ (by
            simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
            erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ } }
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesFiniteCoproductsOfAdditive [Additive F] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesCoproductsOfShape_of_preservesBiproductsOfShape F
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesFiniteProductsOfAdditive [Additive F] :
    PreservesFiniteProducts F where
  preserves _ := preservesProductsOfShape_of_preservesBiproductsOfShape F
/-
**CategoryTheory.Functor.hasFiniteProducts_of_additive_of_essSurj** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasFiniteProducts_of_additive_of_essSurj [HasFiniteProducts C] [Additive F
] [EssSurj F] : HasFiniteProducts D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesFiniteProductsOfAdditive`：∀ {C : Type u₁
} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   [inst_2 : Category…
-/
lemma hasFiniteProducts_of_additive_of_essSurj [HasFiniteProducts C] [Additive F]
    [EssSurj F] : HasFiniteProducts D :=
  ⟨fun _ ↦ ⟨fun K ↦ hasLimit_of_iso
    (F := Discrete.functor (fun i ↦ F.objPreimage (K.obj ⟨i⟩)) ⋙ F)
      (Discrete.natIso (fun _ ↦ F.objObjPreimageIso _))⟩⟩
/-
**CategoryTheory.Functor.additive_of_preservesBinaryBiproducts** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：additive_of_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZe
roMorphisms F] [PreservesBinaryBiproducts F] : Additive F where map_add {X Y f g
}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.add_eq_lift_id_desc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y 
: C} (f g : X ⟶ Y)   [inst_2 : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.PreservesBinaryBiproducts.preserves`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryT
heory.Category.{v₂, u₂} D}   {inst_2 : Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biprod.lift_mapBiprod`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.biprod.mapBiprod_hom_desc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem additive_of_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
    [PreservesBinaryBiproducts F] : Additive F where
  map_add {X Y f g} := by
    rw [biprod.add_eq_lift_id_desc, F.map_comp, ← biprod.lift_mapBiprod,
      ← biprod.mapBiprod_hom_desc, Category.assoc, Iso.inv_hom_id_assoc, F.map_id,
      biprod.add_eq_lift_id_desc]
/-
**CategoryTheory.Functor.additive_of_preserves_binary_products** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：additive_of_preserves_binary_products [HasBinaryProducts C] [PreservesLimi
tsOfShape (Discrete WalkingPair) F] [F.PreservesZeroMorphisms] : F.Additive
参数：Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasBinaryProducts …
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProduc
ts`：preservesBinaryBiproducts_of_preservesBinaryProducts [PreservesLimitsOfShape
 (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where p…
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
-/
lemma additive_of_preserves_binary_products
    [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [F.PreservesZeroMorphisms] : F.Additive := by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

end

end

end Functor

namespace Equivalence

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Equivalence.inverse_additive** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：inverse_additive (e : C ≌ D) [e.functor.Additive] : e.inverse.Additive whe
re map_add {f g}
参数：e : C ≌ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance inverse_additive (e : C ≌ D) [e.functor.Additive] : e.inverse.Additive where
  map_add {f g} := e.functor.map_injective (by simp)

end Equivalence

section

variable (C D : Type*) [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- The additivity of a functor, as a property of objects in `C ⥤ D`. -/
/-
**CategoryTheory.additiveFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：additiveFunctor : ObjectProperty (C ⥤ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additivity of a functor, as a property of objects in `C ⥤ D`.
-/
def additiveFunctor : ObjectProperty (C ⥤ D) := fun F ↦ F.Additive

variable {C D} in
/-
**CategoryTheory.additiveFunctor_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：additiveFunctor_iff (F : C ⥤ D) : additiveFunctor C D F ↔ F.Additive
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma additiveFunctor_iff (F : C ⥤ D) :
    additiveFunctor C D F ↔ F.Additive := Iff.rfl

/-- Bundled additive functors. -/
/-
**CategoryTheory.AdditiveFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：AdditiveFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled additive functors.
-/
abbrev AdditiveFunctor := (additiveFunctor C D).FullSubcategory
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : AdditiveFunctor C D) : F.obj.Additive := F.property

/-- the category of additive functors is denoted `C ⥤+ D` -/
infixr:26 " ⥤+ " => AdditiveFunctor

/-- An additive functor is in particular a functor. -/
/-
**CategoryTheory.AdditiveFunctor.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.AdditiveFunctor`。
形式化陈述：(C : Type u_1) →   (D : Type u_2) →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Preadditive C] →           [inst_3 : CategoryTheory.Pread
ditive D] → CategoryTheory.Functor (C ⥤+ D) (CategoryTheory.Functor C D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive functor is in particular a functor.
-/
abbrev AdditiveFunctor.forget : (C ⥤+ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

variable {C D}

/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
@[simps]
/-
**CategoryTheory.AdditiveFunctor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ad
ditiveFunctor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.Preadditive C] →           [inst_3 : CategoryTheory.Pread
ditive D] → (F : CategoryTheory.Functor C D) → [F.Additive] → C ⥤+ D
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an additive functor into an object of the category `AdditiveFunctor C D`.
-/
def AdditiveFunctor.of (F : C ⥤ D) [F.Additive] : C ⥤+ D :=
  ⟨F, by simpa⟩

@[simp]
/-
**CategoryTheory.AdditiveFunctor.of_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.AdditiveFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   [inst_3 : CategoryTheory.Preadditive D] (F : CategoryTheory.Func
tor C D) [inst_4 : F.Additive],   (CategoryTheory.AdditiveFunctor.of F).obj = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.AdditiveFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.of_fst (F : C ⥤ D) [F.Additive] : (AdditiveFunctor.of F).1 = F :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   [inst_3 : CategoryTheory.Preadditive D] (F : C ⥤+ D), (CategoryT
heory.AdditiveFunctor.forget C D).obj F = F.obj
参数：F : C ⥤+ D；CategoryTheory.AdditiveFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
  rfl
/-
**CategoryTheory.AdditiveFunctor.forget_obj_of** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   [inst_3 : CategoryTheory.Preadditive D] (F : CategoryTheory.Func
tor C D) [inst_4 : F.Additive],   (CategoryTheory.AdditiveFunctor.forget C D).ob
j (CategoryTheory.AdditiveFunctor.of F) = F
参数：F : CategoryTheory.Functor C D；CategoryTheory.AdditiveFunctor.forget C D；Cate
goryTheory.AdditiveFunctor.of F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.Additive] :
    (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   [inst_3 : CategoryTheory.Preadditive D] (F G : C ⥤+ D) (α : F ⟶ 
G),   (CategoryTheory.AdditiveFunctor.forget C D).map α = α.hom
参数：F G : C ⥤+ D；α : F ⟶ G；CategoryTheory.AdditiveFunctor.forget C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) :
    (AdditiveFunctor.forget C D).map α = α.hom :=
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Additive (AdditiveFunctor.forget C D) where map_add := rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤+ D) : Functor.Additive F.1 :=
  F.2

end

section Exact

open CategoryTheory.Limits

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
variable [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-
**CategoryTheory.leftExactFunctor_le_additiveFunctor** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：leftExactFunctor_le_additiveFunctor : leftExactFunctor C D <= additiveFunc
tor C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProduc
ts`：preservesBinaryBiproducts_of_preservesBinaryProducts [PreservesLimitsOfShape
 (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where p…
-/
lemma leftExactFunctor_le_additiveFunctor :
    leftExactFunctor C D ≤ additiveFunctor C D :=
  fun F h ↦ by
    simp only [leftExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F
/-
**CategoryTheory.rightExactFunctor_le_additiveFunctor** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：rightExactFunctor_le_additiveFunctor : rightExactFunctor C D <= additiveFu
nctor C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_objec
t`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoprod
ucts`：preservesBinaryBiproducts_of_preservesBinaryCoproducts [PreservesColimitsO
fShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F whe…
-/
lemma rightExactFunctor_le_additiveFunctor :
    rightExactFunctor C D ≤ additiveFunctor C D :=
  fun F h ↦ by
    simp only [rightExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F
/-
**CategoryTheory.exactFunctor_le_additiveFunctor** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：exactFunctor_le_additiveFunctor : exactFunctor C D <= additiveFunctor C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.exactFunctor_le_leftExactFunctor`：exactFunctor_le_leftExa
ctFunctor : exactFunctor C D <= leftExactFunctor C D
· 使用引理 `CategoryTheory.leftExactFunctor_le_additiveFunctor`：leftExactFunctor_le_
additiveFunctor : leftExactFunctor C D <= additiveFunctor C D
-/
lemma exactFunctor_le_additiveFunctor :
    exactFunctor C D ≤ additiveFunctor C D :=
  (exactFunctor_le_leftExactFunctor C D).trans
    (leftExactFunctor_le_additiveFunctor C D)

/-- Turn a left exact functor into an additive functor. -/
/-
**CategoryTheory.AdditiveFunctor.ofLeftExact** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.AdditiveFunctor`。
形式化陈述：(C : Type u₁) →   (D : Type u₂) →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Preadditive C] →           [inst_3 : CategoryTheory.Preadditive
 D] →             [CategoryTheory.Limits.HasZeroObject C] →               [Categ
oryTheory.Limits.HasZeroObject D] →                 [CategoryTheory.Limits.HasBi
naryBiproducts C] → CategoryTheory.Functor (C ⥤ₗ D) (C ⥤+ D)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.leftExactFunctor_le_additiveFunctor`：leftExactFunctor_le_
additiveFunctor : leftExactFunctor C D <= additiveFunctor C D

--- 原说明 ---
Turn a left exact functor into an additive functor.
-/
abbrev AdditiveFunctor.ofLeftExact : (C ⥤ₗ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE (leftExactFunctor_le_additiveFunctor C D)

/-- Turn a right exact functor into an additive functor. -/
/-
**CategoryTheory.AdditiveFunctor.ofRightExact** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.AdditiveFunctor`。
形式化陈述：(C : Type u₁) →   (D : Type u₂) →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Preadditive C] →           [inst_3 : CategoryTheory.Preadditive
 D] →             [CategoryTheory.Limits.HasZeroObject C] →               [Categ
oryTheory.Limits.HasZeroObject D] →                 [CategoryTheory.Limits.HasBi
naryBiproducts C] → CategoryTheory.Functor (C ⥤ᵣ D) (C ⥤+ D)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.rightExactFunctor_le_additiveFunctor`：rightExactFunctor_l
e_additiveFunctor : rightExactFunctor C D <= additiveFunctor C D

--- 原说明 ---
Turn a right exact functor into an additive functor.
-/
abbrev AdditiveFunctor.ofRightExact : (C ⥤ᵣ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE (rightExactFunctor_le_additiveFunctor C D)

/-- Turn an exact functor into an additive functor. -/
/-
**CategoryTheory.AdditiveFunctor.ofExact** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.AdditiveFunctor`。
形式化陈述：(C : Type u₁) →   (D : Type u₂) →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Preadditive C] →           [inst_3 : CategoryTheory.Preadditive
 D] →             [CategoryTheory.Limits.HasZeroObject C] →               [Categ
oryTheory.Limits.HasZeroObject D] →                 [CategoryTheory.Limits.HasBi
naryBiproducts C] → CategoryTheory.Functor (C ⥤ₑ D) (C ⥤+ D)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.exactFunctor_le_additiveFunctor`：exactFunctor_le_additive
Functor : exactFunctor C D <= additiveFunctor C D

--- 原说明 ---
Turn an exact functor into an additive functor.
-/
abbrev AdditiveFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_additiveFunctor C D)

end

variable {C D}

@[simp]
/-
**CategoryTheory.AdditiveFunctor.ofLeftExact_obj_fst** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Preaddi
tive C] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasZeroObject C] [inst_5 : CategoryTheory.Limits.HasZeroObject D]   [inst_6 : 
CategoryTheory.Limits.HasBinaryBiproducts C] (F : C ⥤ₗ D),   ((CategoryTheory.Ad
ditiveFunctor.ofLeftExact C D).obj F).obj = F.obj
参数：F : C ⥤ₗ D；(CategoryTheory.AdditiveFunctor.ofLeftExact C D).obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.ofLeftExact_obj_fst (F : C ⥤ₗ D) :
    ((AdditiveFunctor.ofLeftExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.ofRightExact_obj_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Preaddi
tive C] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasZeroObject C] [inst_5 : CategoryTheory.Limits.HasZeroObject D]   [inst_6 : 
CategoryTheory.Limits.HasBinaryBiproducts C] (F : C ⥤ᵣ D),   ((CategoryTheory.Ad
ditiveFunctor.ofRightExact C D).obj F).obj = F.obj
参数：F : C ⥤ᵣ D；(CategoryTheory.AdditiveFunctor.ofRightExact C D).obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.ofRightExact_obj_fst (F : C ⥤ᵣ D) :
    ((AdditiveFunctor.ofRightExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.ofExact_obj_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Preaddi
tive C] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasZeroObject C] [inst_5 : CategoryTheory.Limits.HasZeroObject D]   [inst_6 : 
CategoryTheory.Limits.HasBinaryBiproducts C] (F : C ⥤ₑ D),   ((CategoryTheory.Ad
ditiveFunctor.ofExact C D).obj F).obj = F.obj
参数：F : C ⥤ₑ D；(CategoryTheory.AdditiveFunctor.ofExact C D).obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.ofExact_obj_fst (F : C ⥤ₑ D) :
    ((AdditiveFunctor.ofExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.ofLeftExact_map_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Preaddi
tive C] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasZeroObject C] [inst_5 : CategoryTheory.Limits.HasZeroObject D]   [inst_6 : 
CategoryTheory.Limits.HasBinaryBiproducts C] {F G : C ⥤ₗ D} (α : F ⟶ G),   ((Cat
egoryTheory.AdditiveFunctor.ofLeftExact C D).map α).hom = α.hom
参数：α : F ⟶ G；(CategoryTheory.AdditiveFunctor.ofLeftExact C D).map α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.ofLeftExact_map_hom {F G : C ⥤ₗ D} (α : F ⟶ G) :
    ((AdditiveFunctor.ofLeftExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.ofRightExact_map_hom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Preaddi
tive C] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasZeroObject C] [inst_5 : CategoryTheory.Limits.HasZeroObject D]   [inst_6 : 
CategoryTheory.Limits.HasBinaryBiproducts C] {F G : C ⥤ᵣ D} (α : F ⟶ G),   ((Cat
egoryTheory.AdditiveFunctor.ofRightExact C D).map α).hom = α.hom
参数：α : F ⟶ G；(CategoryTheory.AdditiveFunctor.ofRightExact C D).map α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.ofRightExact_map_hom {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    ((AdditiveFunctor.ofRightExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.AdditiveFunctor.ofExact_map_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.AdditiveFunctor`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Preaddi
tive C] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasZeroObject C] [inst_5 : CategoryTheory.Limits.HasZeroObject D]   [inst_6 : 
CategoryTheory.Limits.HasBinaryBiproducts C] {F G : C ⥤ₑ D} (α : F ⟶ G),   ((Cat
egoryTheory.AdditiveFunctor.ofExact C D).map α).hom = α.hom
参数：α : F ⟶ G；(CategoryTheory.AdditiveFunctor.ofExact C D).map α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdditiveFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((AdditiveFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

end Exact

end Preadditive

end CategoryTheory

