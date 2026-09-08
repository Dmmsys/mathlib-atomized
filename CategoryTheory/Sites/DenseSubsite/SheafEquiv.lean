/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# The equivalence of categories of sheaves of a dense subsite

If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, and `A` is
a category with suitable limits, then the functor
`G.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is an equivalence
of categories. The equivalence of categories can be obtained as `sheafEquiv J K G A`
which is defined in the file `Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean`.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

public section

universe w v u w'

namespace CategoryTheory.Functor.IsDenseSubsite

open CategoryTheory Opposite

variable {C D : Type*} [Category* C] [Category* D]
variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {A : Type w} [Category.{w'} A] [∀ X, Limits.HasLimitsOfShape (StructuredArrow X G.op) A]
variable [G.IsDenseSubsite J K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include K in
/-
**CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：isIso_ranCounit_app_of_isDenseSubsite (Y : Sheaf J A) (U X) : IsIso ((yone
da.map ((G.op.ranCounit.app Y.obj).app (op U))).app (op X))
参数：Y : Sheaf J A；U X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用引理 `CategoryTheory.StructuredArrow.mk_surjective`：mk_surjective (f : Structu
redArrow S T) : exists (Y : C) (g : S ⟶ T.obj Y), f = mk g
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.equalizer_mem`：equalizer_mem {U V}
 (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) : Sieve.equalizer f₁ f₂ in J _
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation.w`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.Grothen
dieckTopology C}   {S : J.Cover X} {I₁ I₂ : S.Ar…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.StructuredArrow.homMk_surjective`：homMk_surjective {f f' 
: StructuredArrow S T} (φ : f ⟶ f') : exists (ψ : f.right ⟶ f'.right) (hψ : f.ho
m ≫ T.map ψ = f'.hom), φ = Structured…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.amalgamate_map`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} 
{A : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
（共 32 条，此处仅展示前 30 条）
-/
lemma isIso_ranCounit_app_of_isDenseSubsite (Y : Sheaf J A) (U X) :
    IsIso ((yoneda.map ((G.op.ranCounit.app Y.obj).app (op U))).app (op X)) := by
  rw [isIso_iff_bijective]
  constructor
  · intro f₁ f₂ e
    refine (isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).hom_ext (fun g ↦ ?_)
    obtain ⟨⟨W⟩, ⟨g : G.obj W ⟶ G.obj U⟩, rfl⟩ := g.mk_surjective
    refine (Y.2 X _ (IsDenseSubsite.imageSieve_mem J K G g)).isSeparatedFor.ext
      (fun V iVW ⟨iVU, h⟩ ↦ ?_)
    have := congr($e ≫ Y.1.map iVU.op)
    dsimp at this ⊢
    simp only [Category.assoc, ← NatTrans.naturality] at this ⊢
    simpa [h] using! this
  · intro f
    have (X Y Z) (f : X ⟶ Y) (g : G.obj Y ⟶ G.obj Z) (hf : G.imageSieve g f) : Exists _ := hf
    choose l hl using this
    let c : Limits.Cone (StructuredArrow.proj (op (G.obj U)) G.op ⋙ Y.obj) := by
      refine ⟨X, ⟨fun g ↦ ?_, fun g₁ g₂ i ↦ ?_⟩⟩
      · refine Y.2.amalgamate ⟨_, IsDenseSubsite.imageSieve_mem J K G g.hom.unop⟩
          (fun I ↦ f ≫ Y.1.map (l _ _ _ _ _ I.hf).op) fun I₁ I₂ r ↦ ?_
        apply (Y.2 X _ (IsDenseSubsite.equalizer_mem J K G (r.g₁ ≫ l _ _ _ _ _ I₁.hf)
          (r.g₂ ≫ l _ _ _ _ _ I₂.hf) ?_)).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
        · rw [map_comp, hl, map_comp, hl, ← map_comp_assoc, r.w, map_comp_assoc]
        · simp [← map_comp, ← op_comp, hiUV]
      · obtain ⟨⟨W₁⟩, ⟨g₁⟩, rfl⟩ := g₁.mk_surjective
        obtain ⟨⟨W₂⟩, ⟨g₂⟩, rfl⟩ := g₂.mk_surjective
        obtain ⟨⟨i⟩, hi, rfl⟩ := StructuredArrow.homMk_surjective i
        replace hi := Quiver.Hom.op_inj hi
        dsimp at g₁ g₂ i hi ⊢
        subst hi
        rw [Category.id_comp]
        apply Y.2.hom_ext ⟨_, IsDenseSubsite.imageSieve_mem J K G (G.map i ≫ g₁)⟩
        intro I
        simp only [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← Functor.map_comp]
        let I' : GrothendieckTopology.Cover.Arrow ⟨_, IsDenseSubsite.imageSieve_mem J K G g₁⟩ :=
          ⟨_, I.f ≫ i, ⟨l _ _ _ _ _ I.hf, by simp [hl]⟩⟩
        refine Eq.trans ?_ (Y.2.amalgamate_map _ _ _ I').symm
        apply (Y.2 X _ (IsDenseSubsite.equalizer_mem J K G (l _ _ _ _ _ I.hf)
          (l _ _ _ _ _ I'.hf) (by simp [I', hl]))).isSeparatedFor.ext
            fun V iUV (hiUV : _ = _) ↦ ?_
        simp [I', ← Functor.map_comp, ← op_comp, hiUV]
    refine ⟨(isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).lift c, ?_⟩
    · have := (isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).fac c (.mk (𝟙 _))
      simp only [id_obj, comp_obj, StructuredArrow.proj_obj, StructuredArrow.mk_right,
        RightExtension.coneAt_pt, RightExtension.mk_left, RightExtension.coneAt_π_app,
        const_obj_obj, op_obj, StructuredArrow.mk_hom_eq_self, map_id, whiskeringLeft_obj_obj,
        RightExtension.mk_hom, Category.id_comp] at this
      simp only [c, id_obj, yoneda_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, this]
      apply Y.2.hom_ext ⟨_, IsDenseSubsite.imageSieve_mem J K G (𝟙 (G.obj U))⟩ _ _ fun I ↦ ?_
      apply (Y.2 X _ (IsDenseSubsite.equalizer_mem J K G (l _ _ _ _ _ I.hf)
        I.f (by simp [hl]))).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
      simp [← Functor.map_comp, ← op_comp, hiUV]
/-
**CategoryTheory.Functor.IsDenseSubsite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsDenseSubsite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : Sheaf J A) : IsIso ((G.sheafAdjunctionCocontinuous A J K).counit.app Y) := by
  apply +allowSynthFailures ReflectsIsomorphisms.reflects (sheafToPresheaf J A)
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨U⟩
  apply +allowSynthFailures ReflectsIsomorphisms.reflects yoneda
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨X⟩
  simpa [sheafAdjunctionCocontinuous_counit_app_hom]
    using! isIso_ranCounit_app_of_isDenseSubsite G J K Y U X
/-
**CategoryTheory.Functor.IsDenseSubsite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsDenseSubsite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (G.sheafPushforwardContinuous A J K).IsEquivalence :=
  (G.sheafAdjunctionCocontinuous A J K).toEquivalence.isEquivalence_functor

end IsDenseSubsite

end CategoryTheory.Functor

