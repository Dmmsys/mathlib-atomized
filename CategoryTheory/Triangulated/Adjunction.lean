/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-!
# The adjoint functor is triangulated

If a functor `F : C ⥤ D` between pretriangulated categories is triangulated, and if we
have an adjunction `F ⊣ G`, then `G` is also a triangulated functor. We deduce the
symmetric statement (if `G` is a triangulated functor, then so is `F`) using opposite
categories.

We then introduce a class `IsTriangulated` for adjunctions: an adjunction `F ⊣ G`
is called triangulated if both `F` and `G` are triangulated, and if the adjunction
is compatible with the shifts by `ℤ` on `F` and `G` (in the sense of `Adjunction.CommShift`);
we prove that this is compatible with composition and that the identity adjunction is
triangulated.
Thanks to the results above, an adjunction carrying an `Adjunction.CommShift` instance
is triangulated as soon as one of the adjoint functors is triangulated.

We finally specialize these structures to equivalences of categories, and prove that,
if `E : C ≌ D` is an equivalence of pretriangulated categories, then
`E.functor` is triangulated if and only if `E.inverse` is triangulated.

-/

public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated Adjunction

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ]
  [adj.CommShift ℤ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include adj in
/--
The right adjoint of a triangulated functor is triangulated.
-/
/-
**CategoryTheory.Adjunction.isTriangulated_rightAdjoint** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：isTriangulated_rightAdjoint [F.IsTriangulated] : G.IsTriangulated where ma
p_distinguished T hT
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.right_adjoint_additive`：right_adjoint_additive
 [F.Additive] : G.Additive where map_add {X Y} f g
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instAdditive`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism`
：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Adjunction.shift_counit_app`：shift_counit_app [adj.CommSh
ift A] (a : A) (Y : D) : (adj.counit.app Y)⟦a⟧' = (F.commShiftIso a).inv.app (G.
obj Y) ≫ F.map ((G.commShiftIso …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Preadditive.mono_iff_cancel_zero`：mono_iff_cancel_zero {Q
 R : C} (f : Q ⟶ R) : Mono f ↔ forall (P : C) (g : P ⟶ Q), g ≫ f = 0 -> g = 0
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₃`：coyoneda_exact₃
 {X : C} (f : X ⟶ T.obj₃) (hf : f ≫ T.mor₃ = 0) : exists (g : X ⟶ T.obj₂), f = g
 ≫ T.mor₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The right adjoint of a triangulated functor is triangulated.
-/
lemma isTriangulated_rightAdjoint [F.IsTriangulated] : G.IsTriangulated where
  map_distinguished T hT := by
    have : G.Additive := adj.right_adjoint_additive
    obtain ⟨Z, f, g, mem⟩ := distinguished_cocone_triangle (G.map T.mor₁)
    obtain ⟨h, ⟨h₁, h₂⟩⟩ := complete_distinguished_triangle_morphism _ _
      (F.map_distinguished _ mem) hT (adj.counit.app T.obj₁) (adj.counit.app T.obj₂) (by simp)
    dsimp at h h₁ h₂ ⊢
    have h₁' : f ≫ adj.unit.app Z ≫ G.map h = G.map T.mor₂ := by
      simpa [homEquiv_apply] using DFunLike.congr_arg (adj.homEquiv _ _) h₁
    have h₂' : g ≫ (G.commShiftIso (1 : ℤ)).inv.app T.obj₁ =
        adj.homEquiv _ _ h ≫ G.map T.mor₃ := by
      apply (adj.homEquiv _ _).symm.injective
      simp only [Functor.comp_obj, homEquiv_counit, Functor.id_obj, Functor.map_comp, assoc,
        homEquiv_unit, counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
        ← h₂, adj.shift_counit_app, Iso.hom_inv_id_app_assoc]
    rw [assoc] at h₂
    have : Mono (adj.homEquiv _ _ h) := by
      rw [mono_iff_cancel_zero]
      intro _ φ hφ
      obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ _ mem φ (by
        dsimp
        simp only [homEquiv_unit, Functor.comp_obj] at hφ
        rw [← cancel_mono ((G.commShiftIso (1 : ℤ)).inv.app T.obj₁), assoc, h₂', zero_comp,
          homEquiv_unit, assoc, reassoc_of% hφ, zero_comp])
      dsimp at ψ hφ ⊢
      obtain ⟨α, hα⟩ := T.coyoneda_exact₂ hT ((adj.homEquiv _ _).symm ψ)
        ((adj.homEquiv _ _).injective (by simpa [homEquiv_counit, homEquiv_unit, ← h₁'] using hφ))
      have eq := DFunLike.congr_arg (adj.homEquiv _ _) hα
      simp only [homEquiv_counit, homEquiv_unit, comp_id,
        Functor.map_comp, unit_naturality_assoc, right_triangle_components] at eq
      have eq' := comp_distTriang_mor_zero₁₂ _ mem
      dsimp at eq eq'
      rw [eq, assoc, assoc, eq', comp_zero, comp_zero]
    have := isIso_of_yoneda_map_bijective (adj.homEquiv _ _ h) (fun Y => by
      constructor
      · intro φ₁ φ₂ hφ
        rw [← cancel_mono (adj.homEquiv _ _ h)]
        exact hφ
      · intro φ
        obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₁ _ mem (φ ≫ G.map T.mor₃ ≫
          (G.commShiftIso (1 : ℤ)).hom.app T.obj₁) (by
            dsimp
            rw [assoc, assoc, ← G.commShiftIso_hom_naturality, ← G.map_comp_assoc,
              comp_distTriang_mor_zero₃₁ _ hT, G.map_zero, zero_comp, comp_zero])
        dsimp at ψ hψ
        obtain ⟨α, hα⟩ : ∃ α, α = φ - ψ ≫ adj.homEquiv _ _ h := ⟨_, rfl⟩
        have hα₀ : α ≫ G.map T.mor₃ = 0 := by
          rw [hα, sub_comp, ← cancel_mono ((Functor.commShiftIso G (1 : ℤ)).hom.app T.obj₁),
            assoc, sub_comp, assoc, assoc, hψ, zero_comp, sub_eq_zero,
            ← cancel_mono ((Functor.commShiftIso G (1 : ℤ)).inv.app T.obj₁), assoc,
            assoc, assoc, assoc, h₂', Iso.hom_inv_id_app, comp_id]
        suffices ∃ (β : Y ⟶ Z), β ≫ adj.homEquiv _ _ h = α by
          obtain ⟨β, hβ⟩ := this
          refine ⟨ψ + β, ?_⟩
          dsimp
          rw [add_comp, hβ, hα, add_sub_cancel]
        obtain ⟨β, hβ⟩ := T.coyoneda_exact₃ hT ((adj.homEquiv _ _).symm α)
          ((adj.homEquiv _ _).injective (by simpa [homEquiv_unit, homEquiv_counit] using hα₀))
        refine ⟨adj.homEquiv _ _ β ≫ f, ?_⟩
        simpa [homEquiv_unit, h₁'] using congr_arg (adj.homEquiv _ _).toFun hβ.symm)
    refine isomorphic_distinguished _ mem _ (Iso.symm ?_)
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (adj.homEquiv Z T.obj₃ h)) ?_ ?_ ?_
    · simp
    · apply (adj.homEquiv _ _).symm.injective
      dsimp
      simp only [homEquiv_unit, homEquiv_counit, Functor.map_comp, assoc,
        counit_naturality, left_triangle_components_assoc, h₁, id_comp]
    · dsimp
      rw [Functor.map_id, comp_id, homEquiv_unit, assoc, ← G.map_comp_assoc, ← h₂,
        Functor.map_comp, Functor.map_comp, assoc, unit_naturality_assoc, assoc,
        Functor.commShiftIso_hom_naturality, ← adj.shift_unit_app_assoc,
        ← Functor.map_comp, right_triangle_components, Functor.map_id, comp_id]

include adj in
open Pretriangulated.Opposite in
/--
The left adjoint of a triangulated functor is triangulated.
-/
/-
**CategoryTheory.Adjunction.isTriangulated_leftAdjoint** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：isTriangulated_leftAdjoint [G.IsTriangulated] : F.IsTriangulated
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.Adjunction.isTriangulated_rightAdjoint`：isTriangulated_ri
ghtAdjoint [F.IsTriangulated] : G.IsTriangulated where map_distinguished T hT
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.commShift_adjunction_op_int`：∀ {
C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.functor_isTriangulated_op`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.isTriangulated_of_op`：isTriangulated_of_op [F.op.
IsTriangulated] : F.IsTriangulated where map_distinguished T dT

--- 原说明 ---
The left adjoint of a triangulated functor is triangulated.
-/
lemma isTriangulated_leftAdjoint [G.IsTriangulated] : F.IsTriangulated := by
  have := isTriangulated_rightAdjoint adj.op
  exact F.isTriangulated_of_op

/--
We say that an adjunction `F ⊣ G` is triangulated if it is compatible with the `CommShift`
structures on `F` and `G` (in the sense of `Adjunction.CommShift`) and if both `F` and `G`
are triangulated functors.
-/
/-
**CategoryTheory.Adjunction.IsTriangulated** 是 Mathlib 中的一个类，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：IsTriangulated : Prop where commShift : adj.CommShift Int
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an adjunction `F ⊣ G` is triangulated if it is compatible with the `
CommShift`
structures on `F` and `G` (in the sense of `Adjunction.CommShift`) and if both `
F` and `G`
are triangulated functors.
-/
class IsTriangulated : Prop where
  commShift : adj.CommShift ℤ := by infer_instance
  leftAdjoint_isTriangulated : F.IsTriangulated := by infer_instance
  rightAdjoint_isTriangulated : G.IsTriangulated := by infer_instance

namespace IsTriangulated

attribute [instance] commShift leftAdjoint_isTriangulated rightAdjoint_isTriangulated

/-- Constructor for `Adjunction.IsTriangulated`.
-/
/-
**CategoryTheory.Adjunction.IsTriangulated.mk'** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Adjunction.IsTriangulated`。
形式化陈述：mk' [F.IsTriangulated] : adj.IsTriangulated where rightAdjoint_isTriangula
ted
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isTriangulated_rightAdjoint`：isTriangulated_ri
ghtAdjoint [F.IsTriangulated] : G.IsTriangulated where map_distinguished T hT

--- 原说明 ---
Constructor for `Adjunction.IsTriangulated`.
-/
lemma mk' [F.IsTriangulated] : adj.IsTriangulated where
  rightAdjoint_isTriangulated := adj.isTriangulated_rightAdjoint

/-- Constructor for `Adjunction.IsTriangulated`.
-/
/-
**CategoryTheory.Adjunction.IsTriangulated.mk''** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Adjunction.IsTriangulated`。
形式化陈述：mk'' [G.IsTriangulated] : adj.IsTriangulated where leftAdjoint_isTriangula
ted
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isTriangulated_leftAdjoint`：isTriangulated_lef
tAdjoint [G.IsTriangulated] : F.IsTriangulated

--- 原说明 ---
Constructor for `Adjunction.IsTriangulated`.
-/
lemma mk'' [G.IsTriangulated] : adj.IsTriangulated where
  leftAdjoint_isTriangulated := adj.isTriangulated_leftAdjoint

/-- The identity adjunction is triangulated.
-/
/-
**CategoryTheory.Adjunction.IsTriangulated.id** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Adjunction.IsTriangulated`。
形式化陈述：id : (Adjunction.id (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instId`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasShift C ℤ]   [i
nst_2 : CategoryTheory.Limits.HasZ…

--- 原说明 ---
The identity adjunction is triangulated.
-/
instance id : (Adjunction.id (C := C)).IsTriangulated where

variable {E : Type*} [Category* E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G') [HasZeroObject E]
  [Preadditive E] [HasShift E ℤ] [∀ (n : ℤ), (shiftFunctor E n).Additive] [Pretriangulated E]
  [F'.CommShift ℤ] [G'.CommShift ℤ] [adj'.CommShift ℤ]

/-- A composition of triangulated adjunctions is triangulated.
-/
/-
**CategoryTheory.Adjunction.IsTriangulated.comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Adjunction.IsTriangulated`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroObject C]   [inst_3 : CategoryTheory.Limits.HasZeroObject D] [inst_
4 : CategoryTheory.Preadditive C]   [inst_5 : CategoryTheory.Preadditive D] [ins
t_6 : CategoryTheory.HasShift C ℤ] [inst_7 : CategoryTheory.HasShift D ℤ]   [ins
t_8 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]   [inst_9 : ∀ (n : 
ℤ), (CategoryTheory.shiftFunctor D n).Additive] [inst_10 : CategoryTheory.Pretri
angulated C]   [inst_11 : CategoryTheory.Pretriangulated D] {F : CategoryTheory.
Functor C D} {G : CategoryTheory.Functor D C}   (adj : F ⊣ G) [inst_12 : F.CommS
hift ℤ] [inst_13 : G.CommShift ℤ] [adj.CommShift ℤ] {E : Type u_3}   [inst_15 : 
CategoryTheory.Category.{v_3, u_3} E] {F' : CategoryTheory.Functor D E} {G' : Ca
tegoryTheory.Functor E D}   (adj' : F' ⊣ G') [inst_16 : CategoryTheory.Limits.Ha
sZeroObject E] [inst_17 : CategoryTheory.Preadditive E]   [inst_18 : CategoryThe
ory.HasShift E ℤ] [inst_19 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor E n).Additi
ve]   [inst_20 : CategoryTheory.Pretriangulated E] [inst_21 : F'.CommShift ℤ] [i
nst_22 : G'.CommShift ℤ] [adj'.CommShift ℤ]   [adj.IsTriangulated] [adj'.IsTrian
gulated], (adj.comp adj').IsTriangulated
参数：n : ℤ；CategoryTheory.shiftFunctor C n；n : ℤ；CategoryTheory.shiftFunctor D n；a
dj : F ⊣ G；adj' : F' ⊣ G'；n : ℤ；CategoryTheory.shiftFunctor E n；adj.comp adj'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instComp`：∀ {C : Type u_1} {D : Ty
pe u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Adjunction.IsTriangulated.leftAdjoint_isTriangulated`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Adjunction.IsTriangulated.rightAdjoint_isTriangulated`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…

--- 原说明 ---
A composition of triangulated adjunctions is triangulated.
-/
instance comp [adj.IsTriangulated] [adj'.IsTriangulated] : (adj.comp adj').IsTriangulated where

end IsTriangulated

end Adjunction

namespace Equivalence

variable (E : C ≌ D) [E.functor.CommShift ℤ] [E.inverse.CommShift ℤ] [E.CommShift ℤ]

/--
We say that an equivalence of categories `E` is triangulated if both `E.functor` and
`E.inverse` are triangulated functors.
-/
/-
**CategoryTheory.Equivalence.IsTriangulated** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：IsTriangulated : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an equivalence of categories `E` is triangulated if both `E.functor`
 and
`E.inverse` are triangulated functors.
-/
abbrev IsTriangulated : Prop := E.toAdjunction.IsTriangulated

namespace IsTriangulated

/-
**CategoryTheory.Equivalence.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [E.IsTriangulated] : E.functor.IsTriangulated := inferInstance
/-
**CategoryTheory.Equivalence.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [E.IsTriangulated] : E.inverse.IsTriangulated := inferInstance
/-
**CategoryTheory.Equivalence.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : E.functor.IsTriangulated] : E.symm.inverse.IsTriangulated := h
/-
**CategoryTheory.Equivalence.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : E.inverse.IsTriangulated] : E.symm.functor.IsTriangulated := h


/-- Constructor for `Equivalence.IsTriangulated`. -/
/-
**CategoryTheory.Equivalence.IsTriangulated.mk'** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Equivalence.IsTriangulated`。
形式化陈述：mk' (h : E.functor.IsTriangulated) : E.IsTriangulated where rightAdjoint_i
sTriangulated
参数：h : E.functor.IsTriangulated。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isTriangulated_rightAdjoint`：isTriangulated_ri
ghtAdjoint [F.IsTriangulated] : G.IsTriangulated where map_distinguished T hT

--- 原说明 ---
Constructor for `Equivalence.IsTriangulated`.
-/
lemma mk' (h : E.functor.IsTriangulated) : E.IsTriangulated where
  rightAdjoint_isTriangulated := E.toAdjunction.isTriangulated_rightAdjoint

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for `Equivalence.IsTriangulated`. -/
/-
**CategoryTheory.Equivalence.IsTriangulated.mk''** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Equivalence.IsTriangulated`。
形式化陈述：mk'' (h : E.inverse.IsTriangulated) : E.IsTriangulated where leftAdjoint_i
sTriangulated
参数：h : E.inverse.IsTriangulated。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.IsTriangulated.rightAdjoint_isTriangulated`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用引理 `CategoryTheory.Equivalence.IsTriangulated.mk'`：mk' (h : E.functor.IsTria
ngulated) : E.IsTriangulated where rightAdjoint_isTriangulated
· 使用定理 `CategoryTheory.Equivalence.CommShift.instSymm`：∀ {C : Type u_1} {D : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_2} D] (E : C ≌ D) …

--- 原说明 ---
Constructor for `Equivalence.IsTriangulated`.
-/
lemma mk'' (h : E.inverse.IsTriangulated) : E.IsTriangulated where
  leftAdjoint_isTriangulated := (mk' E.symm h).rightAdjoint_isTriangulated

set_option backward.isDefEq.respectTransparency false in
/--
The identity equivalence is triangulated.
-/
/-
**CategoryTheory.Equivalence.IsTriangulated.refl** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Equivalence.IsTriangulated`。
形式化陈述：refl : (Equivalence.refl (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Equivalence.refl_toAdjunction`：refl_toAdjunction : (refl 
(C

--- 原说明 ---
The identity equivalence is triangulated.
-/
instance refl : (Equivalence.refl (C := C)).IsTriangulated := by
  dsimp [Equivalence.IsTriangulated]
  rw [refl_toAdjunction]
  infer_instance

/-- If the equivalence `E` is triangulated, so is the equivalence `E.symm`.
-/
/-
**CategoryTheory.Equivalence.IsTriangulated.symm** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Equivalence.IsTriangulated`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.L
imits.HasZeroObject C]   [inst_3 : CategoryTheory.Limits.HasZeroObject D] [inst_
4 : CategoryTheory.Preadditive C]   [inst_5 : CategoryTheory.Preadditive D] [ins
t_6 : CategoryTheory.HasShift C ℤ] [inst_7 : CategoryTheory.HasShift D ℤ]   [ins
t_8 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]   [inst_9 : ∀ (n : 
ℤ), (CategoryTheory.shiftFunctor D n).Additive] [inst_10 : CategoryTheory.Pretri
angulated C]   [inst_11 : CategoryTheory.Pretriangulated D] (E : C ≌ D) [inst_12
 : E.functor.CommShift ℤ]   [inst_13 : E.inverse.CommShift ℤ] [E.CommShift ℤ] [E
.IsTriangulated], E.symm.IsTriangulated
参数：n : ℤ；CategoryTheory.shiftFunctor C n；n : ℤ；CategoryTheory.shiftFunctor D n；E
 : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.CommShift.instSymm`：∀ {C : Type u_1} {D : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_2} D] (E : C ≌ D) …
· 使用定理 `CategoryTheory.Equivalence.IsTriangulated.instIsTriangulatedFunctorSymmO
fInverse`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, 
u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Equivalence.IsTriangulated.instIsTriangulatedInverse`：∀ {
C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Equivalence.IsTriangulated.instIsTriangulatedInverseSymmO
fFunctor`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, 
u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Equivalence.IsTriangulated.instIsTriangulatedFunctor`：∀ {
C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If the equivalence `E` is triangulated, so is the equivalence `E.symm`.
-/
instance symm [E.IsTriangulated] : E.symm.IsTriangulated where

variable {D' : Type*} [Category* D'] [HasZeroObject D'] [Preadditive D'] [HasShift D' ℤ]
  [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D'] {E' : D ≌ D'}
  [E'.functor.CommShift ℤ] [E'.inverse.CommShift ℤ] [E'.CommShift ℤ]

set_option backward.isDefEq.respectTransparency false in
/--
If equivalences `E : C ≌ D` and `E' : D ≌ F` are triangulated, so is `E.trans E'`.
-/
/-
**CategoryTheory.Equivalence.IsTriangulated.trans** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Equivalence.IsTriangulated`。
形式化陈述：trans [E.IsTriangulated] [E'.IsTriangulated] : (E.trans E').IsTriangulated
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Equivalence.trans_toAdjunction`：trans_toAdjunction {E : T
ype*} [Category* E] (e' : D ≌ E) : (e.trans e').toAdjunction = e.toAdjunction.co
mp e'.toAdjunction
· 使用定理 `CategoryTheory.Adjunction.IsTriangulated.comp`：∀ {C : Type u_1} {D : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If equivalences `E : C ≌ D` and `E' : D ≌ F` are triangulated, so is `E.trans E'
`.
-/
instance trans [E.IsTriangulated] [E'.IsTriangulated] : (E.trans E').IsTriangulated := by
  dsimp [Equivalence.IsTriangulated]
  rw [trans_toAdjunction]
  infer_instance

end IsTriangulated

end Equivalence

end CategoryTheory

