/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.EquivalenceAdditive
public import Mathlib.AlgebraicTopology.DoldKan.Compatibility
public import Mathlib.CategoryTheory.Idempotents.SimplicialObject
public import Mathlib.Tactic.SuppressCompilation

/-!

# The Dold-Kan correspondence for pseudoabelian categories

In this file, for any idempotent complete additive category `C`,
the Dold-Kan equivalence
`Idempotents.DoldKan.Equivalence C : SimplicialObject C ≌ ChainComplex C ℕ`
is obtained. It is deduced from the equivalence
`Preadditive.DoldKan.Equivalence` between the respective idempotent
completions of these categories using the fact that when `C` is idempotent complete,
then both `SimplicialObject C` and `ChainComplex C ℕ` are idempotent complete.

The construction of `Idempotents.DoldKan.Equivalence` uses the tools
introduced in the file `Compatibility.lean`. Doing so, the functor
`Idempotents.DoldKan.N` of the equivalence is
the composition of `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)`
(defined in `FunctorN.lean`) and the inverse of the equivalence
`ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`. The functor
`Idempotents.DoldKan.Γ` of the equivalence is by definition the functor
`Γ₀` introduced in `FunctorGamma.lean`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


suppress_compilation
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents

variable {C : Type*} [Category* C] [Preadditive C]

namespace CategoryTheory

namespace Idempotents

namespace DoldKan

open AlgebraicTopology.DoldKan

/-- The functor `N` for the equivalence is obtained by composing
`N' : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` and the inverse
of the equivalence `ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`. -/
@[simps!, nolint unusedArguments]
/-
**CategoryTheory.Idempotents.DoldKan.N** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Idempotents.DoldKan`。
形式化陈述：N [IsIdempotentComplete C] [HasFiniteCoproducts C] : SimplicialObject C ⥤ 
ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `N` for the equivalence is obtained by composing
`N' : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` and the inverse
of the equivalence `ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`.
-/
def N [IsIdempotentComplete C] [HasFiniteCoproducts C] : SimplicialObject C ⥤ ChainComplex C ℕ :=
  N₁ ⋙ (toKaroubiEquivalence _).inverse

/-- The functor `Γ` for the equivalence is `Γ₀`. -/
@[simps!, nolint unusedArguments]
/-
**CategoryTheory.Idempotents.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Γ` for the equivalence is `Γ₀`.
-/
def Γ [IsIdempotentComplete C] [HasFiniteCoproducts C] : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀

variable [IsIdempotentComplete C] [HasFiniteCoproducts C]

/-- A reformulation of the isomorphism `toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁` -/
/-
**CategoryTheory.Idempotents.DoldKan.isoN** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reformulation of the isomorphism `toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁`
-/
def isoN₁ :
    (toKaroubiEquivalence (SimplicialObject C)).functor ⋙
      Preadditive.DoldKan.equivalence.functor ≅ N₁ := toKaroubiCompN₂IsoN₁

@[simp]
/-
**CategoryTheory.Idempotents.DoldKan.isoN** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoN₁_hom_app_f (X : SimplicialObject C) :
    (isoN₁.hom.app X).f = PInfty := rfl

/-- A reformulation of the canonical isomorphism
`toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ≅ Γ ⋙ toKaroubi (SimplicialObject C)`. -/
/-
**CategoryTheory.Idempotents.DoldKan.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reformulation of the canonical isomorphism
`toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ≅ Γ ⋙ toKaroubi (SimplicialObject C)`.
-/
def isoΓ₀ :
    (toKaroubiEquivalence (ChainComplex C ℕ)).functor ⋙ Preadditive.DoldKan.equivalence.inverse ≅
      Γ ⋙ (toKaroubiEquivalence _).functor :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀

@[simp]
/-
**CategoryTheory.Idempotents.DoldKan.N** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Idempotents.DoldKan`。
形式化陈述：N [IsIdempotentComplete C] [HasFiniteCoproducts C] : SimplicialObject C ⥤ 
ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma N₂_map_isoΓ₀_hom_app_f (X : ChainComplex C ℕ) :
    (N₂.map (isoΓ₀.hom.app X)).f = PInfty := by
  ext
  apply comp_id

/-- The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`Compatibility.lean` to the equivalence `Preadditive.DoldKan.Equivalence`. -/
/-
**CategoryTheory.Idempotents.DoldKan.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Idempotents.DoldKan`。
形式化陈述：equivalence : SimplicialObject C ≌ ChainComplex C Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.instIsIdempotentCompleteSimplicialObject`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.IsId
empotentComplete C],   CategoryTheory.IsIdempotentComplet…

--- 原说明 ---
The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`Compatibility.lean` to the equivalence `Preadditive.DoldKan.Equivalence`.
-/
def equivalence : SimplicialObject C ≌ ChainComplex C ℕ :=
  Compatibility.equivalence isoN₁ isoΓ₀
/-
**CategoryTheory.Idempotents.DoldKan.equivalence_functor** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Idempotents.DoldKan`。
形式化陈述：equivalence_functor : (equivalence : SimplicialObject C ≌ _).functor = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem equivalence_functor : (equivalence : SimplicialObject C ≌ _).functor = N :=
  rfl
/-
**CategoryTheory.Idempotents.DoldKan.equivalence_inverse** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Idempotents.DoldKan`。
形式化陈述：equivalence_inverse : (equivalence : SimplicialObject C ≌ _).inverse = Γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem equivalence_inverse : (equivalence : SimplicialObject C ≌ _).inverse = Γ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `NΓ'` satisfies the compatibility that is needed
for the construction of our counit isomorphism `η`. -/
/-
**CategoryTheory.Idempotents.DoldKan.h** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `NΓ'` satisfies the compatibility that is needed
for the construction of our counit isomorphism `η`.
-/
theorem hη :
    Compatibility.τ₀ =
      Compatibility.τ₁ isoN₁ isoΓ₀
        (N₁Γ₀ : Γ ⋙ N₁ ≅ (toKaroubiEquivalence (ChainComplex C ℕ)).functor) := by
  ext K : 3
  simp only [Compatibility.τ₀_hom_app, Compatibility.τ₁_hom_app]
  exact (N₂Γ₂_compatible_with_N₁Γ₀ K).trans (by simp)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit isomorphism induced by `N₁Γ₀` -/
@[simps!]
/-
**CategoryTheory.Idempotents.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism induced by `N₁Γ₀`
-/
def η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ) :=
  Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C ℕ ⥤ _) ⋙ N₁ ≅ (toKaroubiEquivalence _).functor)
/-
**CategoryTheory.Idempotents.DoldKan.equivalence_counitIso** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Idempotents.DoldKan`。
形式化陈述：equivalence_counitIso : DoldKan.equivalence.counitIso = (η : Γ ⋙ N ≅ 𝟭 (Ch
ainComplex C Nat))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.Compatibility.equivalenceCounitIso_eq`：equival
enceCounitIso_eq (hη : τ₀ = τ₁ hF hG η) : (equivalence hF hG).counitIso = equiva
lenceCounitIso η
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Idempotents.instIsIdempotentCompleteSimplicialObject`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.IsId
empotentComplete C],   CategoryTheory.IsIdempotentComplet…
· 使用定理 `CategoryTheory.Idempotents.DoldKan.hη`：hη : Compatibility.τ₀ = Compatibi
lity.τ₁ isoN₁ isoΓ₀ (N₁Γ₀ : Γ ⋙ N₁ ≅ (toKaroubiEquivalence (ChainComplex C Nat))
.functor)
-/
theorem equivalence_counitIso :
    DoldKan.equivalence.counitIso = (η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ)) :=
  Compatibility.equivalenceCounitIso_eq hη

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Idempotents.DoldKan.h** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hε :
    Compatibility.υ (isoN₁) =
      (Γ₂N₁ : (toKaroubiEquivalence _).functor ≅
          (N₁ : SimplicialObject C ⥤ _) ⋙ Preadditive.DoldKan.equivalence.inverse) := by
  dsimp only [isoN₁]
  ext1
  rw [← cancel_epi Γ₂N₁.inv, Iso.inv_hom_id]
  ext X : 2
  rw [NatTrans.comp_app, Γ₂N₁_inv, compatibility_Γ₂N₁_Γ₂N₂_natTrans X, Compatibility.υ_hom_app,
    Preadditive.DoldKan.equivalence_unitIso, Iso.app_inv, assoc]
  dsimp only [Functor.comp_obj, Preadditive.DoldKan.equivalence_inverse, Preadditive.DoldKan.Γ.eq_1,
    toKaroubiEquivalence, Functor.asEquivalence_functor, Preadditive.DoldKan.N.eq_1,
    NatTrans.id_app]
  rw [← NatTrans.comp_app_assoc, ← Γ₂N₂_inv, Iso.inv_hom_id, NatTrans.id_app, id_comp,
    Γ₂N₂ToKaroubiIso_inv_app, ← Γ₂.map_comp, Iso.inv_hom_id_app, Γ₂.map_id]

/-- The unit isomorphism induced by `Γ₂N₁`. -/
/-
**CategoryTheory.Idempotents.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Idempotents.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism induced by `Γ₂N₁`.
-/
def ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ :=
  Compatibility.equivalenceUnitIso isoΓ₀ Γ₂N₁
/-
**CategoryTheory.Idempotents.DoldKan.equivalence_unitIso** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Idempotents.DoldKan`。
形式化陈述：equivalence_unitIso : DoldKan.equivalence.unitIso = (ε : 𝟭 (SimplicialObje
ct C) ≅ N ⋙ Γ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.Compatibility.equivalenceUnitIso_eq`：equivalen
ceUnitIso_eq (hε : υ hF = ε) : (equivalence hF hG).unitIso = equivalenceUnitIso 
hG ε
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Idempotents.instIsIdempotentCompleteSimplicialObject`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.IsId
empotentComplete C],   CategoryTheory.IsIdempotentComplet…
· 使用定理 `CategoryTheory.Idempotents.DoldKan.hε`：hε : Compatibility.υ (isoN₁) = (Γ
₂N₁ : (toKaroubiEquivalence _).functor ≅ (N₁ : SimplicialObject C ⥤ _) ⋙ Preaddi
tive.DoldKan.equivalence.in…
-/
theorem equivalence_unitIso :
    DoldKan.equivalence.unitIso = (ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ) :=
  Compatibility.equivalenceUnitIso_eq hε

end DoldKan

end Idempotents

end CategoryTheory

