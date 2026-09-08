/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy

/-!
# The fundamental lemma of homotopical algebra

Let `C` be a model category. Let `L : C ⥤ H` be a localization functor
with respect to weak equivalences in `C`. We obtain the fundamental
lemma of homotopical algebra: if `X` is cofibrant and `Y` fibrant,
the map `(X ⟶ Y) → (L.obj X ⟶ L.obj Y)` identifies `L.obj X ⟶ L.obj Y`
to the quotient of `X ⟶ Y` by the homotopy relation (in this case,
the left and right homotopy relations coincide).

## References
* [Daniel G. Quillen, Homotopical algebra, I.1][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C] {H : Type*} [Category* H]
  (L : C ⥤ H) [L.IsLocalization (weakEquivalences _)]
  {X Y : C}

/-- The map `LeftHomotopyClass X Y → (L.obj X ⟶ L.obj Y)` when `L` is
a localization functor with respect to `weakEquivalences C`. -/
/-
**HomotopicalAlgebra.leftHomotopyClassToHom** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra`。
形式化陈述：leftHomotopyClassToHom : LeftHomotopyClass X Y -> (L.obj X ⟶ L.obj Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `LeftHomotopyClass X Y → (L.obj X ⟶ L.obj Y)` when `L` is
a localization functor with respect to `weakEquivalences C`.
-/
def leftHomotopyClassToHom : LeftHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ h.factorsThroughLocalization.map_eq _)

@[simp]
/-
**HomotopicalAlgebra.leftHomotopyClassToHom_mk** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：leftHomotopyClassToHom_mk (f : X ⟶ Y) : leftHomotopyClassToHom L (.mk f) =
 L.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftHomotopyClassToHom_mk (f : X ⟶ Y) :
    leftHomotopyClassToHom L (.mk f) = L.map f := rfl

/-- The map `RightHomotopyClass X Y → (L.obj X ⟶ L.obj Y)` when `L` is
a localization functor with respect to `weakEquivalences C`. -/
/-
**HomotopicalAlgebra.rightHomotopyClassToHom** 是 Mathlib 中的一个定义，位于命名空间 `Homotopi
calAlgebra`。
形式化陈述：rightHomotopyClassToHom : RightHomotopyClass X Y -> (L.obj X ⟶ L.obj Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `RightHomotopyClass X Y → (L.obj X ⟶ L.obj Y)` when `L` is
a localization functor with respect to `weakEquivalences C`.
-/
def rightHomotopyClassToHom : RightHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ h.factorsThroughLocalization.map_eq _)

@[simp]
/-
**HomotopicalAlgebra.rightHomotopyClassToHom_mk** 是 Mathlib 中的一个引理，位于命名空间 `Homot
opicalAlgebra`。
形式化陈述：rightHomotopyClassToHom_mk (f : X ⟶ Y) : rightHomotopyClassToHom L (.mk f)
 = L.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightHomotopyClassToHom_mk (f : X ⟶ Y) :
    rightHomotopyClassToHom L (.mk f) = L.map f := rfl

variable (X Y)
/-
**HomotopicalAlgebra.bijective_leftHomotopyClassToHom_iff_bijective_rightHomotop
yClassToHom** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom [Is
Cofibrant X] [IsFibrant Y] : Function.Bijective (leftHomotopyClassToHom L : Left
HomotopyClass X Y -> _) ↔ Function.Bijective (rightHomotopyClassToHom L : RightH
omotopyClass X Y -> _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomotopicalAlgebra.LeftHomotopyClass.mk_surjective`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C],   Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom
    [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) ↔
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y → _) := by
  have : (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) =
      rightHomotopyClassToHom L ∘ leftHomotopyClassEquivRightHomotopyClass := by
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  simp [this]

section

variable [IsCofibrant X] [IsFibrant Y]

/-
**HomotopicalAlgebra.bijective_rightHomotopyClassToHom** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopicalAlgebra`。
形式化陈述：bijective_rightHomotopyClassToHom : Function.Bijective (rightHomotopyClass
ToHom L : RightHomotopyClass X Y -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsLocalizationHoCatToHoCatWeakEqu
ivalences`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Ho
motopicalAlgebra.ModelCategory C],   HomotopicalAlgebra.BifibrantObject…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsLocalizationCompιWeakEquivalenc
es`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotopic
alAlgebra.ModelCategory C] {D : Type u_1}   [inst_2 : CategoryTh…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomotopicalAlgebra.RightHomotopyClass.mk_surjective`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.C
ategoryWithWeakEquivalences C],   Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `HomotopicalAlgebra.FibrantObject.instCofibrationIResolutionObj`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] (X : C),   HomotopicalAlgebra.C…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instWeakEquivalenceIResolutionObj`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopical
Algebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsFibrantResolutionObj`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra
.ModelCategory C] (X : C),   HomotopicalAlgebra.I…
· 使用引理 `HomotopicalAlgebra.isCofibrant_of_cofibration`：isCofibrant_of_cofibratio
n [(cofibrations C).IsStableUnderComposition] {X Y : C} (i : X ⟶ Y) [Cofibration
 i] [hX : IsCofibrant X] : IsCofibr…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeCofibrations`：∀ (C : Type u) [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithW
eakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemCofibratio
nsTrivialFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.cofibrations 
C…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_cofibration_o
f_weakEquivalence`：precomp_bijective_of_cofibration_of_weakEquivalence [IsFibran
t Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] : Function.Bijective (fun …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 43 条，此处仅展示前 30 条）
-/
lemma bijective_rightHomotopyClassToHom :
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y → _) := by
  wlog _ : IsCofibrant Y generalizing Y
  · obtain ⟨Y', _, p, _, _⟩ := CofibrantObject.HoCat.exists_resolution Y
    have _ : IsFibrant Y' := isFibrant_of_fibration p
    have hY' := this Y' inferInstance
    simp only [← bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom] at hY' ⊢
    have := Localization.inverts L (weakEquivalences _) p
      (by rwa [← weakEquivalence_iff])
    rw [← Function.Bijective.of_comp_iff _
      (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence _ p)]
    convert! (Iso.homCongr (Iso.refl (L.obj X)) (asIso (L.map p))).bijective.comp hY'
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  wlog _ : IsFibrant X generalizing X
  · obtain ⟨X', i, _, _, _⟩ : ∃ (X' : C) (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i ∧
        IsFibrant X' :=
      ⟨_, FibrantObject.HoCat.iResolutionObj X, inferInstance, inferInstance, inferInstance⟩
    have _ := isCofibrant_of_cofibration i
    have hX' := this X' inferInstance
    have := Localization.inverts L (weakEquivalences _) i
      (by rwa [← weakEquivalence_iff])
    rw [← Function.Bijective.of_comp_iff _
      (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence Y i)]
    convert! (Iso.homCongr (asIso (L.map i)) (Iso.refl (L.obj Y))).symm.bijective.comp hX'
    ext f
    obtain ⟨f, rfl⟩ := f.mk_surjective
    simp
  let E := Localization.uniq BifibrantObject.toHoCat (BifibrantObject.ι ⋙ L) (weakEquivalences _)
  let e : BifibrantObject.toHoCat ⋙ E.functor ≅ BifibrantObject.ι ⋙ L :=
    Localization.compUniqFunctor BifibrantObject.toHoCat (BifibrantObject.ι ⋙ L)
      (weakEquivalences _)
  have : rightHomotopyClassToHom L =
      (BifibrantObject.HoCat.homEquivRight.trans (E.fullyFaithfulFunctor.homEquiv.trans
        (Iso.homCongr (e.app (.mk X)) (e.app (.mk Y))))) := by
    ext f
    obtain ⟨f, rfl⟩ := RightHomotopyClass.mk_surjective f
    exact (NatIso.naturality_1 e (BifibrantObject.homMk f)).symm
  rw [this]
  exact Equiv.bijective _
/-
**HomotopicalAlgebra.bijective_leftHomotopyClassToHom** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra`。
形式化陈述：bijective_leftHomotopyClassToHom : Function.Bijective (leftHomotopyClassTo
Hom L : LeftHomotopyClass X Y -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.bijective_leftHomotopyClassToHom_iff_bijective_rightH
omotopyClassToHom`：bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyC
lassToHom [IsCofibrant X] [IsFibrant Y] : Function.Bijective (leftHomotopyClass…
· 使用引理 `HomotopicalAlgebra.bijective_rightHomotopyClassToHom`：bijective_rightHom
otopyClassToHom : Function.Bijective (rightHomotopyClassToHom L : RightHomotopyC
lass X Y -> _)
-/
lemma bijective_leftHomotopyClassToHom :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) := by
  rw [bijective_leftHomotopyClassToHom_iff_bijective_rightHomotopyClassToHom]
  exact bijective_rightHomotopyClassToHom L X Y
/-
**HomotopicalAlgebra.map_surjective_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra`。
形式化陈述：map_surjective_of_isLocalization : Function.Surjective (L.map : (X ⟶ Y) ->
 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `HomotopicalAlgebra.bijective_leftHomotopyClassToHom`：bijective_leftHomot
opyClassToHom : Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass
 X Y -> _)
-/
lemma map_surjective_of_isLocalization :
    Function.Surjective (L.map : (X ⟶ Y) → _) := by
  intro f
  obtain ⟨⟨f⟩, rfl⟩ := (bijective_leftHomotopyClassToHom L X Y).2 f
  exact ⟨f, rfl⟩
/-
**HomotopicalAlgebra.RightHomotopyRel.iff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homo
topicalAlgebra.RightHomotopyRel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C]   {H : Type u_2} [inst_2 : CategoryTheory.Cat
egory.{v_2, u_2} H] (L : CategoryTheory.Functor C H)   [L.IsLocalization (Homoto
picalAlgebra.weakEquivalences C)] (X Y : C) [HomotopicalAlgebra.IsCofibrant X]  
 [HomotopicalAlgebra.IsFibrant Y] {f g : X ⟶ Y}, HomotopicalAlgebra.RightHomotop
yRel f g ↔ L.map f = L.map g
参数：L : CategoryTheory.Functor C H；HomotopicalAlgebra.weakEquivalences C；X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `CategoryTheory.AreEqualizedByLocalization.map_eq`：map_eq (h : AreEqualiz
edByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] : L.map f = L.map g
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.factorsThroughLocalization`：factorsT
hroughLocalization [CategoryWithWeakEquivalences C] : RightHomotopyRel.FactorsTh
roughLocalization (weakEquivalences C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelC
ategory C] [IsFibrant Y] (f g : X ⟶ Y) : mk f = mk g ↔ RightHomotopyRel f g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `HomotopicalAlgebra.bijective_rightHomotopyClassToHom`：bijective_rightHom
otopyClassToHom : Function.Bijective (rightHomotopyClassToHom L : RightHomotopyC
lass X Y -> _)
-/
lemma RightHomotopyRel.iff_map_eq {f g : X ⟶ Y} :
    RightHomotopyRel f g ↔ L.map f = L.map g := by
  refine ⟨fun h ↦ (RightHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h ↦ ?_⟩
  rw [← RightHomotopyClass.mk_eq_mk_iff]
  exact (bijective_rightHomotopyClassToHom L X Y).1 (by simpa)
/-
**HomotopicalAlgebra.LeftHomotopyRel.iff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homot
opicalAlgebra.LeftHomotopyRel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C]   {H : Type u_2} [inst_2 : CategoryTheory.Cat
egory.{v_2, u_2} H] (L : CategoryTheory.Functor C H)   [L.IsLocalization (Homoto
picalAlgebra.weakEquivalences C)] (X Y : C) [HomotopicalAlgebra.IsCofibrant X]  
 [HomotopicalAlgebra.IsFibrant Y] {f g : X ⟶ Y}, HomotopicalAlgebra.LeftHomotopy
Rel f g ↔ L.map f = L.map g
参数：L : CategoryTheory.Functor C H；HomotopicalAlgebra.weakEquivalences C；X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `CategoryTheory.AreEqualizedByLocalization.map_eq`：map_eq (h : AreEqualiz
edByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] : L.map f = L.map g
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.factorsThroughLocalization`：factorsTh
roughLocalization [CategoryWithWeakEquivalences C] : LeftHomotopyRel.FactorsThro
ughLocalization (weakEquivalences C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.LeftHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelCa
tegory C] [IsCofibrant X] (f g : X ⟶ Y) : mk f = mk g ↔ LeftHomotopyRel f g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `HomotopicalAlgebra.bijective_leftHomotopyClassToHom`：bijective_leftHomot
opyClassToHom : Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass
 X Y -> _)
-/
lemma LeftHomotopyRel.iff_map_eq {f g : X ⟶ Y} :
    LeftHomotopyRel f g ↔ L.map f = L.map g := by
  refine ⟨fun h ↦ (LeftHomotopyRel.factorsThroughLocalization C h).map_eq L,
    fun h ↦ ?_⟩
  rw [← LeftHomotopyClass.mk_eq_mk_iff]
  exact (bijective_leftHomotopyClassToHom L X Y).1 (by simpa)

end

end HomotopicalAlgebra

