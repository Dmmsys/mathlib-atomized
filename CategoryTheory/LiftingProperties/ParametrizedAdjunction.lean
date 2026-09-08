/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Lifting properties and parametrized adjunctions

If we have a parametrized adjunction `adj₂ : F ⊣₂ G`,
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
we show that `sq₁₂.ι` has the left lifting property with respect to
`f₃` if and only if `f₂` has the left lifting property with respect
to `sq₁₃.π`: this is the lemma `ParametrizedAdjunction.hasLiftingProperty_iff`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace ParametrizedAdjunction

variable {F G} (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
  {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
  (sq₁₂ : F.PushoutObjObj f₁ f₂) (sq₁₃ : G.PullbackObjObj f₁ f₃)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a parametrized adjunction `F ⊣₂ G` between bifunctors, and structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`, there are
as many commutative squares with left map `sq₁₂.ι` and right map `f₃`
as commutative squares with left map `f₂` and right map `sq₁₃.π`. -/
@[simps! apply_left symm_apply_right]
/-
**CategoryTheory.ParametrizedAdjunction.arrowHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ParametrizedAdjunction`。
形式化陈述：arrowHomEquiv : (Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) ≃ (Arrow.mk f₂ ⟶ Arrow.mk 
sq₁₃.π) where toFun α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PullbackObjObj.isPullback`：∀ {C₁ : Type u₁} {C₂ :
 Type u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 
: CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `CategoryTheory.Functor.PushoutObjObj.isPushout`：∀ {C₁ : Type u₁} {C₂ : T
ype u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : 
CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a parametrized adjunction `F ⊣₂ G` between bifunctors, and structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`, there are
as many commutative squares with left map `sq₁₂.ι` and right map `f₃`
as commutative squares with left map `f₂` and right map `sq₁₃.π`.
-/
noncomputable def arrowHomEquiv :
    (Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) ≃
      (Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) where
  toFun α :=
    Arrow.homMk (adj₂.homEquiv (sq₁₂.inl ≫ α.left))
      (sq₁₃.isPullback.lift
        (adj₂.homEquiv (sq₁₂.inr ≫ α.left)) (adj₂.homEquiv α.right)
          (by simp [← adj₂.homEquiv_naturality_one,
              ← adj₂.homEquiv_naturality_three])) (by
            apply sq₁₃.isPullback.hom_ext
            · simp [← adj₂.homEquiv_naturality_two,
                ← adj₂.homEquiv_naturality_one,
                sq₁₂.isPushout.w_assoc]
            · simp [← adj₂.homEquiv_naturality_two,
                ← adj₂.homEquiv_naturality_three])
  invFun β :=
    Arrow.homMk
      (sq₁₂.isPushout.desc
        (adj₂.homEquiv.symm β.left)
        (adj₂.homEquiv.symm (β.right ≫ sq₁₃.fst)) (by
          have := Arrow.w β =≫ sq₁₃.fst
          dsimp at this
          simp only [Category.assoc, sq₁₃.π_fst] at this
          simp only [← adj₂.homEquiv_symm_naturality_one,
            ← adj₂.homEquiv_symm_naturality_two,
            Arrow.mk_left, Arrow.mk_right, this]))
      (adj₂.homEquiv.symm (β.right ≫ sq₁₃.snd)) (by
        apply sq₁₂.isPushout.hom_ext
        · have := Arrow.w β =≫ sq₁₃.snd
          dsimp at this
          simp only [Category.assoc, sq₁₃.π_snd] at this
          simp [← adj₂.homEquiv_symm_naturality_two,
            ← adj₂.homEquiv_symm_naturality_three, this]
        · simp [← adj₂.homEquiv_symm_naturality_one,
            ← adj₂.homEquiv_symm_naturality_three, sq₁₃.isPullback.w])
  left_inv α := by
    ext
    · apply sq₁₂.isPushout.hom_ext <;> simp
    · simp
  right_inv β := by
    ext
    · simp
    · apply sq₁₃.isPullback.hom_ext <;> simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.ParametrizedAdjunction.arrowHomEquiv_apply_right_fst** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：arrowHomEquiv_apply_right_fst (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) : ((adj₂
.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.fst = adj₂.homEquiv (sq₁₂.inr ≫ α.left
)
参数：α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用定理 `CategoryTheory.Functor.PullbackObjObj.isPullback`：∀ {C₁ : Type u₁} {C₂ :
 Type u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 
: CategoryTheory.Category.{v₂, u₂} C₂]…
-/
lemma arrowHomEquiv_apply_right_fst (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    ((adj₂.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.fst = adj₂.homEquiv (sq₁₂.inr ≫ α.left) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ParametrizedAdjunction.arrowHomEquiv_apply_right_snd** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：arrowHomEquiv_apply_right_snd (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) : ((adj₂
.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.snd = adj₂.homEquiv α.right
参数：α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
· 使用定理 `CategoryTheory.Functor.PullbackObjObj.isPullback`：∀ {C₁ : Type u₁} {C₂ :
 Type u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 
: CategoryTheory.Category.{v₂, u₂} C₂]…
-/
lemma arrowHomEquiv_apply_right_snd (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    ((adj₂.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.snd = adj₂.homEquiv α.right :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ParametrizedAdjunction.inl_arrowHomEquiv_symm_apply_left** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：inl_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) : sq
₁₂.inl ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left = adj₂.homEquiv.symm β.lef
t
参数：β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `CategoryTheory.Functor.PushoutObjObj.isPushout`：∀ {C₁ : Type u₁} {C₂ : T
ype u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : 
CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma inl_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) :
    sq₁₂.inl ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left = adj₂.homEquiv.symm β.left :=
  IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ParametrizedAdjunction.inr_arrowHomEquiv_symm_apply_left** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：inr_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) : sq
₁₂.inr ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left = adj₂.homEquiv.symm (β.ri
ght ≫ sq₁₃.fst)
参数：β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
· 使用定理 `CategoryTheory.Functor.PushoutObjObj.isPushout`：∀ {C₁ : Type u₁} {C₂ : T
ype u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : 
CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma inr_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) :
    sq₁₂.inr ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left =
    adj₂.homEquiv.symm (β.right ≫ sq₁₃.fst) :=
  IsPushout.inr_desc _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a parametrized adjunction `F ⊣₂ G` between bifunctors, structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
there are as many liftings for the commutative square given by a
map `α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃` as there are liftings
for the square given by the corresponding map `Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π`. -/
/-
**CategoryTheory.ParametrizedAdjunction.liftStructEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：liftStructEquiv (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) : Arrow.LiftStruct α ≃
 Arrow.LiftStruct (adj₂.arrowHomEquiv sq₁₂ sq₁₃ α) where toFun l
参数：α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a parametrized adjunction `F ⊣₂ G` between bifunctors, structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
there are as many liftings for the commutative square given by a
map `α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃` as there are liftings
for the square given by the corresponding map `Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π`.
-/
noncomputable def liftStructEquiv (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    Arrow.LiftStruct α ≃ Arrow.LiftStruct (adj₂.arrowHomEquiv sq₁₂ sq₁₃ α) where
  toFun l :=
    { l := adj₂.homEquiv l.l
      fac_left := by
        have := l.fac_left
        dsimp at this ⊢
        simp only [← adj₂.homEquiv_naturality_two, ← this,
          sq₁₂.inl_ι_assoc]
      fac_right := by
        apply sq₁₃.isPullback.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_fst, ← adj₂.homEquiv_naturality_one,
            arrowHomEquiv_apply_right_fst, Arrow.mk_left, ← this, sq₁₂.inr_ι_assoc]
        · have := l.fac_right
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_snd, ← this, adj₂.homEquiv_naturality_three,
            arrowHomEquiv_apply_right_snd, Arrow.mk_right] }
  invFun l :=
    { l := adj₂.homEquiv.symm l.l
      fac_left := by
        apply sq₁₂.isPushout.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
          simp only [sq₁₂.inl_ι_assoc, ← adj₂.homEquiv_symm_naturality_two,
            this, Equiv.symm_apply_apply]
        · have := l.fac_right =≫ sq₁₃.fst
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_fst] at this
          simp only [sq₁₂.inr_ι_assoc, ← adj₂.homEquiv_symm_naturality_one,
            this, Equiv.symm_apply_apply, arrowHomEquiv_apply_right_fst, Arrow.mk_left]
      fac_right := by
        have := l.fac_right =≫ sq₁₃.snd
        dsimp at this ⊢
        simp only [Category.assoc, sq₁₃.π_snd, arrowHomEquiv_apply_right_snd,
          Arrow.mk_right] at this
        rw [← adj₂.homEquiv_symm_naturality_three, this,
          Equiv.symm_apply_apply] }
  left_inv _ := by aesop
  right_inv _ := by aesop

include adj₂ in
/-
**CategoryTheory.ParametrizedAdjunction.hasLiftingProperty_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：hasLiftingProperty_iff : HasLiftingProperty sq₁₂.ι f₃ ↔ HasLiftingProperty
 f₂ sq₁₃.π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma hasLiftingProperty_iff :
    HasLiftingProperty sq₁₂.ι f₃ ↔ HasLiftingProperty f₂ sq₁₃.π := by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h β
    obtain ⟨α, rfl⟩ := (adj₂.arrowHomEquiv sq₁₂ sq₁₃).surjective β
    exact ⟨adj₂.liftStructEquiv sq₁₂ sq₁₃ α (h α).some⟩
  · intro h α
    exact ⟨(adj₂.liftStructEquiv sq₁₂ sq₁₃ α).symm (h _).some⟩

end ParametrizedAdjunction

end CategoryTheory

