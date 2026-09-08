/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final

/-!
# Action of an initial functor on sections

Given `F : C ⥤ D` and `P : D ⥤ Type w`, we define a map
`sectionsPrecomp F : P.sections → (F ⋙ P).sections` and
show that it is a bijection when `F` is initial.
As `Functor.sections` identify to limits of functors to types
(at least under suitable universe assumptions), this could
be deduced from general results about limits and
initial functors, but we provide a more down to earth proof.

We also obtain the dual result that if `F` is final,
then `F.colimitTypePrecomp : (F ⋙ P).ColimitType → P.ColimitType`
is a bijection.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- When `F : C ⥤ D` and `P : D ⥤ Type _`, this is the obvious map
`P.sections → (F ⋙ P).sections`. -/
@[simps]
/-
**CategoryTheory.Functor.sectionsPrecomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：sectionsPrecomp (F : C ⥤ D) {P : D ⥤ Type w} (x : P.sections) : (F ⋙ P).se
ctions where val _
参数：F : C ⥤ D；x : P.sections。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F : C ⥤ D` and `P : D ⥤ Type _`, this is the obvious map
`P.sections → (F ⋙ P).sections`.
-/
def sectionsPrecomp (F : C ⥤ D) {P : D ⥤ Type w} (x : P.sections) :
    (F ⋙ P).sections where
  val _ := x.val _
  property _ := x.property _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.bijective_sectionsPrecomp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：bijective_sectionsPrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Initial] : Funct
ion.Bijective (F.sectionsPrecomp (P
参数：F : C ⥤ D；P : D ⥤ Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.Initial.instNonemptyCostructuredArrow`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.constant_of_preserves_morphisms'`：constant_of_preserves_m
orphisms' [IsConnected J] {α : Type u₂} (F : J -> α) (h : forall (j₁ j₂ : J) (_ 
: j₁ ⟶ j₂), F j₁ = F j₂) : exists (a …
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma bijective_sectionsPrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Initial] :
    Function.Bijective (F.sectionsPrecomp (P := P)) := by
  refine ⟨fun s₁ s₂ h ↦ ?_, fun t ↦ ?_⟩
  · ext Y
    let X : CostructuredArrow F Y := Classical.arbitrary _
    have := congr_fun (congr_arg Subtype.val h) X.left
    have h₁ := s₁.property X.hom
    have h₂ := s₂.property X.hom
    dsimp at this h₁ h₂
    rw [← h₁, this, h₂]
  · have h (Y : D) : ∃ (a : P.obj Y),
        ∀ (j : CostructuredArrow F Y), P.map j.hom (t.val j.left) = a := by
      apply constant_of_preserves_morphisms'
      intro Z₁ Z₂ φ
      dsimp
      rw [← t.property φ.left]
      dsimp
      rw [← comp_apply, ← Functor.map_comp, CostructuredArrow.w]
    choose val hval using h
    refine ⟨⟨val, fun {Y₁ Y₂} f ↦ ?_⟩, ?_⟩
    · let X : CostructuredArrow F Y₁ := Classical.arbitrary _
      simp [← hval Y₁ X, ← hval Y₂ ((CostructuredArrow.map f).obj X)]
    · ext X : 2
      simpa using (hval (F.obj X) (CostructuredArrow.mk (𝟙 _))).symm

/-- Given `P : D ⥤ Type w` and `F : C ⥤ D`, this is the obvious map
`(F ⋙ P).ColimitType → P.ColimitType`. -/
/-
**CategoryTheory.Functor.colimitTypePrecomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：colimitTypePrecomp (F : C ⥤ D) (P : D ⥤ Type w) : (F ⋙ P).ColimitType -> P
.ColimitType
参数：F : C ⥤ D；P : D ⥤ Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : D ⥤ Type w` and `F : C ⥤ D`, this is the obvious map
`(F ⋙ P).ColimitType → P.ColimitType`.
-/
def colimitTypePrecomp (F : C ⥤ D) (P : D ⥤ Type w) :
    (F ⋙ P).ColimitType → P.ColimitType :=
  (F ⋙ P).descColimitType (P.coconeTypes.precomp F)

@[simp]
/-
**CategoryTheory.Functor.colimitTypePrecomp_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma colimitTypePrecomp_ιColimitType (F : C ⥤ D) {P : D ⥤ Type w}
    (i : C) (x : P.obj (F.obj i)) :
    colimitTypePrecomp F P ((F ⋙ P).ιColimitType i x) = P.ιColimitType (F.obj i) x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.bijective_colimitTypePrecomp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：bijective_colimitTypePrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Final] : Func
tion.Bijective (F.colimitTypePrecomp (P
参数：F : C ⥤ D；P : D ⥤ Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.constant_of_preserves_morphisms'`：constant_of_preserves_m
orphisms' [IsConnected J] {α : Type u₂} (F : J -> α) (h : forall (j₁ j₂ : J) (_ 
: j₁ ⟶ j₂), F j₁ = F j₂) : exists (a …
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ιColimitType_map`：ιColimitType_map {j j' : J} (f 
: j ⟶ j') (x : F.obj j) : F.ιColimitType j' (F.map f x) = F.ιColimitType j x
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.Final.instNonemptyStructuredArrow`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma bijective_colimitTypePrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Final] :
    Function.Bijective (F.colimitTypePrecomp (P := P)) := by
  refine ⟨?_, fun x ↦ ?_⟩
  · have h (Y : D) : ∃ (a : P.obj Y → (F ⋙ P).ColimitType), ∀ (j : StructuredArrow Y F),
        (F ⋙ P).ιColimitType j.right ∘ P.map j.hom = a := by
      apply constant_of_preserves_morphisms'
      intro Z₁ Z₂ f
      ext x
      dsimp
      rw [← (F ⋙ P).ιColimitType_map f.right, comp_map]
      simp [← comp_apply, ← Functor.map_comp]
    choose φ hφ using h
    let c : P.CoconeTypes :=
      { pt := (F ⋙ P).ColimitType
        ι Y := φ Y
        ι_naturality {Y₁ Y₂} f := by
          ext
          have X : StructuredArrow Y₂ F := Classical.arbitrary _
          rw [← hφ Y₂ X, ← hφ Y₁ ((StructuredArrow.map f).obj X)]
          simp }
    refine Function.RightInverse.injective (g := (P.descColimitType c)) (fun x ↦ ?_)
    obtain ⟨X, x, rfl⟩ := (F ⋙ P).ιColimitType_jointly_surjective x
    simp [c, ← hφ (F.obj X) (StructuredArrow.mk (𝟙 _))]
  · obtain ⟨X, x, rfl⟩ := P.ιColimitType_jointly_surjective x
    let Y : StructuredArrow X F := Classical.arbitrary _
    exact ⟨(F ⋙ P).ιColimitType Y.right (P.map Y.hom x), by simp⟩

end Functor

end CategoryTheory

