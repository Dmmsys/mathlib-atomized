/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Long exact sequences of `Ext`-groups

In this file, we obtain the covariant long exact sequence of `Ext` when `n₀ + 1 = n₁`:
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`
when `S` is a short exact short complex in an abelian category `C`, `n₀ + 1 = n₁` and `X : C`.
Similarly, if `Y : C`, there is a contravariant long exact sequence :
`Ext S.X₃ Y n₀ → Ext S.X₂ Y n₀ → Ext S.X₁ Y n₀ → Ext S.X₃ Y n₁ → Ext S.X₂ Y n₁ → Ext S.X₁ Y n₁`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Opposite DerivedCategory Pretriangulated Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Abelian

namespace Ext

section CovariantSequence

/-
**CategoryTheory.Abelian.Ext.hom_comp_singleFunctor_map_shift** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：hom_comp_singleFunctor_map_shift [HasDerivedCategory.{w'} C] {X Y Z : C} {
n : Nat} (x : Ext X Y n) (f : Y ⟶ Z) : x.hom ≫ ((DerivedCategory.singleFunctor C
 0).map f)⟦(n : Int)⟧' = (x.comp (mk₀ f) (add_zero n)).hom
参数：x : Ext X Y n；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀`：comp_mk₀ {a : M} (f : ShiftedHom X Y
 a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) : f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zer
o_add]) = f ≫ g⟦a⟧'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_comp_singleFunctor_map_shift [HasDerivedCategory.{w'} C]
    {X Y Z : C} {n : ℕ} (x : Ext X Y n) (f : Y ⟶ Z) :
    x.hom ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦(n : ℤ)⟧' =
      (x.comp (mk₀ f) (add_zero n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Abelian.Ext.preadditiveCoyoneda_homologySequence** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {X : C} {n₀ : ℕ} (x : Ext X S.X₃ n₀)
    {n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequenceδ
      hS.singleTriangle n₀ n₁ (by lia) x.hom =
        (x.comp hS.extClass h).hom := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

variable (X)

set_option backward.defeqAttrib.useBackward true in
include hS in
/-- Alternative formulation of `covariant_sequence_exact₂` -/
/-
**CategoryTheory.Abelian.Ext.covariant_sequence_exact** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative formulation of `covariant_sequence_exact₂`
-/
lemma covariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n)))
      (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ShortComplex.zero, mk₀_zero,
          comp_zero])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext x; apply hom_comp_singleFunctor_map_shift (C := C)

section

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

set_option backward.defeqAttrib.useBackward true in
/-- Alternative formulation of `covariant_sequence_exact₃` -/
/-
**CategoryTheory.Abelian.Ext.covariant_sequence_exact** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative formulation of `covariant_sequence_exact₃`
-/
lemma covariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h)) (by
        ext x
        dsimp
        simp only [comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
          comp_zero])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₃ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h

set_option backward.defeqAttrib.useBackward true in
/-- Alternative formulation of `covariant_sequence_exact₁` -/
/-
**CategoryTheory.Abelian.Ext.covariant_sequence_exact** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative formulation of `covariant_sequence_exact₁`
-/
lemma covariant_sequence_exact₁' :
    (ShortComplex.mk
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
      (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp,
          comp_zero])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)

open ComposableArrows

/-- Given a short exact short complex `S` in an abelian category `C` and an object `X : C`,
this is the long exact sequence
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`
when `n₀ + 1 = n₁` -/
/-
**CategoryTheory.Abelian.Ext.covariantSequence** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Abelian.Ext`。
形式化陈述：covariantSequence : ComposableArrows AddCommGrpCat.{w} 5
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short exact short complex `S` in an abelian category `C` and an object `
X : C`,
this is the long exact sequence
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ →
 Ext X S.X₃ n₁`
when `n₀ + 1 = n₁`
-/
noncomputable def covariantSequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
    (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₁)))
/-
**CategoryTheory.Abelian.Ext.covariantSequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Abelian.Ext`。
形式化陈述：covariantSequence_exact : (covariantSequence X hS n₀ n₁ h).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.exact_of_δ₀`：exact_of_δ₀ {S : Composable
Arrows C (n + 2)} (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) 
: S.Exact
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂'`：covariant_sequenc
e_exact₂' (n : Nat) : (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp 
X (add_zero n))) (AddCommGrpCat.ofHom ((mk₀…
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'`：covariant_sequenc
e_exact₃' : (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zer
o n₀))) (AddCommGrpCat.ofHom (hS.extClass.p…
· 使用引理 `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'`：covariant_sequenc
e_exact₁' : (ShortComplex.mk (AddCommGrpCat.ofHom (hS.extClass.postcomp X h)) (A
ddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (a…
-/
lemma covariantSequence_exact :
    (covariantSequence X hS n₀ n₁ h).Exact :=
  exact_of_δ₀ (covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

end

/-
**CategoryTheory.Abelian.Ext.covariant_sequence_exact** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma covariant_sequence_exact₁ {n₁ : ℕ} (x₁ : Ext X S.X₁ n₁)
    (hx₁ : x₁.comp (mk₀ S.f) (add_zero n₁) = 0) {n₀ : ℕ} (hn₀ : n₀ + 1 = n₁) :
    ∃ (x₃ : Ext X S.X₃ n₀), x₃.comp hS.extClass hn₀ = x₁ := by
  have := covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in
/-
**CategoryTheory.Abelian.Ext.covariant_sequence_exact** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma covariant_sequence_exact₂ {n : ℕ} (x₂ : Ext X S.X₂ n)
    (hx₂ : x₂.comp (mk₀ S.g) (add_zero n) = 0) :
    ∃ (x₁ : Ext X S.X₁ n), x₁.comp (mk₀ S.f) (add_zero n) = x₂ := by
  have := covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂
/-
**CategoryTheory.Abelian.Ext.covariant_sequence_exact** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma covariant_sequence_exact₃ {n₀ : ℕ} (x₃ : Ext X S.X₃ n₀) {n₁ : ℕ} (hn₁ : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.extClass hn₁ = 0) :
    ∃ (x₂ : Ext X S.X₂ n₀), x₂.comp (mk₀ S.g) (add_zero n₀) = x₃ := by
  have := covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃
/-
**CategoryTheory.Abelian.Ext.postcomp_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma postcomp_mk₀_injective_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Function.Injective ((Ext.mk₀ f).postcomp L (add_zero 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_mono f] using hx
/-
**CategoryTheory.Abelian.Ext.mono_postcomp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_postcomp_mk₀_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Mono (AddCommGrpCat.ofHom <| (Ext.mk₀ f).postcomp L (add_zero 0)) :=
  (AddCommGrpCat.mono_iff_injective _).mpr (postcomp_mk₀_injective_of_mono L f)

end CovariantSequence

section ContravariantSequence

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

/-
**CategoryTheory.Abelian.Ext.singleFunctor_map_comp_hom** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Abelian.Ext`。
形式化陈述：singleFunctor_map_comp_hom [HasDerivedCategory.{w'} C] {X Y Z : C} (f : X 
⟶ Y) {n : Nat} (x : Ext Y Z n) : (DerivedCategory.singleFunctor C 0).map f ≫ x.h
om = ((mk₀ f).comp x (zero_add n)).hom
参数：f : X ⟶ Y；x : Ext Y Z n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma singleFunctor_map_comp_hom [HasDerivedCategory.{w'} C]
    {X Y Z : C} (f : X ⟶ Y) {n : ℕ} (x : Ext Y Z n) :
    (DerivedCategory.singleFunctor C 0).map f ≫ x.hom =
      ((mk₀ f).comp x (zero_add n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Abelian.Ext.preadditiveYoneda_homologySequence** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preadditiveYoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {Y : C} {n₀ : ℕ} (x : Ext S.X₁ Y n₀)
    {n₁ : ℕ} (h : 1 + n₀ = n₁) :
    (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op hS.singleTriangle)) n₀ n₁ (by lia) x.hom =
      (hS.extClass.comp x h).hom := by
  rw [preadditiveYoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
include hS in
/-- Alternative formulation of `contravariant_sequence_exact₂` -/
/-
**CategoryTheory.Abelian.Ext.contravariant_sequence_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative formulation of `contravariant_sequence_exact₂`
-/
lemma contravariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n)))
      (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n))) (by
        ext
        dsimp
        simp only [mk₀_comp_mk₀_assoc, ShortComplex.zero, mk₀_zero, zero_comp])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₂ _
    (op_distinguished _ hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext; apply singleFunctor_map_comp_hom (C := C)

section

variable (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)

set_option backward.defeqAttrib.useBackward true in
/-- Alternative formulation of `contravariant_sequence_exact₁` -/
/-
**CategoryTheory.Abelian.Ext.contravariant_sequence_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative formulation of `contravariant_sequence_exact₁`
-/
lemma contravariant_sequence_exact₁' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (((mk₀ S.f).precomp Y (zero_add n₀))))
      (AddCommGrpCat.ofHom (hS.extClass.precomp Y h)) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.extClass_comp_assoc])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₃ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; apply singleFunctor_map_comp_hom (C := C)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply

set_option backward.defeqAttrib.useBackward true in
/-- Alternative formulation of `contravariant_sequence_exact₃` -/
/-
**CategoryTheory.Abelian.Ext.contravariant_sequence_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative formulation of `contravariant_sequence_exact₃`
-/
lemma contravariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
      (AddCommGrpCat.ofHom (((mk₀ S.g).precomp Y (zero_add n₁)))) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.comp_extClass_assoc])).Exact := by
  let := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₁ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  · ext; apply singleFunctor_map_comp_hom (C := C)

open ComposableArrows

/-- Given a short exact short complex `S` in an abelian category `C` and an object `Y : C`,
this is the long exact sequence
`Ext S.X₃ Y n₀ → Ext S.X₂ Y n₀ → Ext S.X₁ Y n₀ → Ext S.X₃ Y n₁ → Ext S.X₂ Y n₁ → Ext S.X₁ Y n₁`
when `1 + n₀ = n₁`. -/
/-
**CategoryTheory.Abelian.Ext.contravariantSequence** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.Ext`。
形式化陈述：contravariantSequence : ComposableArrows AddCommGrpCat.{w} 5
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short exact short complex `S` in an abelian category `C` and an object `
Y : C`,
this is the long exact sequence
`Ext S.X₃ Y n₀ → Ext S.X₂ Y n₀ → Ext S.X₁ Y n₀ → Ext S.X₃ Y n₁ → Ext S.X₂ Y n₁ →
 Ext S.X₁ Y n₁`
when `1 + n₀ = n₁`.
-/
noncomputable def contravariantSequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
    (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₁)))
/-
**CategoryTheory.Abelian.Ext.contravariantSequence_exact** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：contravariantSequence_exact : (contravariantSequence hS Y n₀ n₁ h).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.exact_of_δ₀`：exact_of_δ₀ {S : Composable
Arrows C (n + 2)} (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) 
: S.Exact
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'`：contravariant
_sequence_exact₂' (n : Nat) : (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).p
recomp Y (zero_add n))) (AddCommGrpCat.ofHom ((…
· 使用引理 `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'`：contravariant
_sequence_exact₁' : (ShortComplex.mk (AddCommGrpCat.ofHom (((mk₀ S.f).precomp Y 
(zero_add n₀)))) (AddCommGrpCat.ofHom (hS.extCl…
· 使用引理 `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃'`：contravariant
_sequence_exact₃' : (ShortComplex.mk (AddCommGrpCat.ofHom (hS.extClass.precomp Y
 h)) (AddCommGrpCat.ofHom (((mk₀ S.g).precomp Y…
-/
lemma contravariantSequence_exact :
    (contravariantSequence hS Y n₀ n₁ h).Exact :=
  exact_of_δ₀ (contravariant_sequence_exact₂' hS Y n₀).exact_toComposableArrows
    (exact_of_δ₀ (contravariant_sequence_exact₁' hS Y n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (contravariant_sequence_exact₃' hS Y n₀ n₁ h).exact_toComposableArrows
        (contravariant_sequence_exact₂' hS Y n₁).exact_toComposableArrows))

end

/-
**CategoryTheory.Abelian.Ext.contravariant_sequence_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma contravariant_sequence_exact₁ {n₀ : ℕ} (x₁ : Ext S.X₁ Y n₀) {n₁ : ℕ} (hn₁ : 1 + n₀ = n₁)
    (hx₁ : hS.extClass.comp x₁ hn₁ = 0) :
    ∃ (x₂ : Ext S.X₂ Y n₀), (mk₀ S.f).comp x₂ (zero_add n₀) = x₁ := by
  have := contravariant_sequence_exact₁' hS Y n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in
/-
**CategoryTheory.Abelian.Ext.contravariant_sequence_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma contravariant_sequence_exact₂ {n : ℕ} (x₂ : Ext S.X₂ Y n)
    (hx₂ : (mk₀ S.f).comp x₂ (zero_add n) = 0) :
    ∃ (x₁ : Ext S.X₃ Y n), (mk₀ S.g).comp x₁ (zero_add n) = x₂ := by
  have := contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂
/-
**CategoryTheory.Abelian.Ext.contravariant_sequence_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma contravariant_sequence_exact₃ {n₁ : ℕ} (x₃ : Ext S.X₃ Y n₁)
    (hx₃ : (mk₀ S.g).comp x₃ (zero_add n₁) = 0) {n₀ : ℕ} (hn₀ : 1 + n₀ = n₁) :
    ∃ (x₁ : Ext S.X₁ Y n₀), hS.extClass.comp x₁ hn₀ = x₃ := by
  have := contravariant_sequence_exact₃' hS Y n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃
/-
**CategoryTheory.Abelian.Ext.precomp_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma precomp_mk₀_injective_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Function.Injective ((Ext.mk₀ g).precomp L (zero_add 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_epi g] using hx
/-
**CategoryTheory.Abelian.Ext.mono_precomp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_precomp_mk₀_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Mono (AddCommGrpCat.ofHom <| (Ext.mk₀ g).precomp L (zero_add 0)) :=
  (AddCommGrpCat.mono_iff_injective _).mpr (precomp_mk₀_injective_of_epi L g)

end ContravariantSequence

end Ext

end Abelian

end CategoryTheory

