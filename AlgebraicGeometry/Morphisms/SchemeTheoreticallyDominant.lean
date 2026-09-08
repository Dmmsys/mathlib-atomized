/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Scheme-theoretically dominant morphisms

In this file, we define scheme-theoretically dominant morphisms as morphisms with trivial kernel.

## Main results
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant`:
  The class of scheme-theoretically dominant morphisms.
- `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant`:
  If the target is reduced and the map is quasi-compact, then scheme-theoretically dominant
  is equivalent to dominant.
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`:
  quasicompact + scheme-theoretically dominant is stable under flat base change.

-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- A morphism is scheme-theoretically dominant if its kernel is trivial. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsSchemeTheoreticallyDominant** 是 Mathlib 中的一个类，位于命名空间 `Alge
braicGeometry`。
形式化陈述：IsSchemeTheoreticallyDominant (f : X ⟶ Y) : Prop where ker_eq_bot (f) : f.
ker = ⊥  alias Scheme.Hom.ker_eq_bot
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is scheme-theoretically dominant if its kernel is trivial.
-/
class IsSchemeTheoreticallyDominant (f : X ⟶ Y) : Prop where
  ker_eq_bot (f) : f.ker = ⊥

alias Scheme.Hom.ker_eq_bot := IsSchemeTheoreticallyDominant.ker_eq_bot
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsIso f] : IsSchemeTheoreticallyDominant f :=
  ⟨by simp⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
    IsDominant f := by
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq, ← Scheme.Hom.support_ker,
    f.ker_eq_bot, Scheme.IdealSheafData.support_bot, TopologicalSpace.Closeds.coe_top]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsSchemeTheoreticallyDominant f]
    [IsSchemeTheoreticallyDominant g] :
    IsSchemeTheoreticallyDominant (f ≫ g) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.Hom.ker_comp, f.ker_eq_bot,
    Scheme.IdealSheafData.map_bot, g.ker_eq_bot]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMultiplicative @IsSchemeTheoreticallyDominant where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance
/-
**AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.IsSchemeTheoreticallyDominant`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsDomina
nt f] [AlgebraicGeometry.IsReduced Y],   AlgebraicGeometry.IsSchemeTheoretically
Dominant f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsSchemeTheoreticallyDominant f
 ↔ AlgebraicGeometry.Scheme.Hom.ker f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`：∀ {X : Algeb
raicGeometry.Scheme} [AlgebraicGeometry.IsReduced X] {I : X.IdealSheafData}, I.s
upport = ⊤ ↔ I = ⊥
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `TopologicalSpace.Closeds.coe_top`：coe_top : (↑(⊤ : Closeds α) : Set α) =
 univ
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `AlgebraicGeometry.Scheme.Hom.denseRange`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f], DenseRange ⇑f
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `TopologicalSpace.Closeds.isClosed`：isClosed (s : Closeds α) : IsClosed (
s : Set α)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_subset_ker_support`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y), Set.range ⇑f ⊆ ↑(AlgebraicGeometry.Scheme.Hom.ker
 f).support
-/
lemma IsSchemeTheoreticallyDominant.of_isDominant (f : X ⟶ Y) [IsDominant f] [IsReduced Y] :
    IsSchemeTheoreticallyDominant f := by
  rw [isSchemeTheoreticallyDominant_iff, ← Scheme.IdealSheafData.support_eq_top_iff,
    ← SetLike.coe_injective.eq_iff, TopologicalSpace.Closeds.coe_top, ← Set.univ_subset_iff,
    ← f.denseRange.closure_eq, f.ker.support.isClosed.closure_subset_iff]
  exact f.range_subset_ker_support

/-- If the target is reduced and the map is quasi-compact, then scheme-theoretically dominant
is equivalent to dominant. -/
/-
**AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isSchemeTheoreticallyDominant_iff_isDominant (f : X ⟶ Y) [QuasiCompact f] 
[IsReduced Y] : IsSchemeTheoreticallyDominant f ↔ IsDominant f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsDominantOfIsSchemeTheoreticallyDominantOfQuasiCo
mpact`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.IsSchem
eTheoreticallyDominant f]   [AlgebraicGeometry.QuasiCompact f], Alg…
· 使用定理 `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant`：∀ {X Y : 
AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f] [Algebrai
cGeometry.IsReduced Y],   AlgebraicGeometry.IsSchem…

--- 原说明 ---
If the target is reduced and the map is quasi-compact, then scheme-theoretically
 dominant
is equivalent to dominant.
-/
lemma isSchemeTheoreticallyDominant_iff_isDominant (f : X ⟶ Y) [QuasiCompact f] [IsReduced Y] :
    IsSchemeTheoreticallyDominant f ↔ IsDominant f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_isDominant _⟩
/-
**AlgebraicGeometry.Scheme.Hom.app_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsScheme
TheoreticallyDominant f]   [AlgebraicGeometry.QuasiCompact f] (U : Y.Opens),   F
unction.Injective ⇑(CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.Schem
e.Hom.app f U))
参数：f : X ⟶ Y；U : Y.Opens；CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.
Scheme.Hom.app f U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_eq_bot`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [self : AlgebraicGeometry.IsSchemeTheoreticallyDominant f],   Al
gebraicGeometry.Scheme.Hom.ke…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `TopCat.Presheaf.IsSheaf.section_ext`：∀ {X : TopCat} {A : Type u_1} [inst
 : CategoryTheory.Category.{u, u_1} A] {FC : A → A → Type u_2} {CC : A → Type u}
   [inst_1 : (X Y : A) → …
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsSheaf`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] (self : AlgebraicGeometry.SheafedSpace C),   self.presh
eaf.IsSheaf
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.naturality`：naturality (i : op U' ⟶ op U) :
 Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map 
i.unop).op
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma Scheme.Hom.app_injective (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (U : Y.Opens) :
    Function.Injective (f.app U) := by
  wlog hU : IsAffineOpen U generalizing U; swap
  · rw [RingHom.injective_iff_ker_eq_bot, ← f.ker_apply ⟨U, hU⟩, f.ker_eq_bot]
    simp
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Y.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨V, hVU, hxV, this V hV ?_⟩
  rw [← ConcreteCategory.comp_apply, f.naturality]
  simp [hs]
/-
**AlgebraicGeometry.IsSchemeTheoreticallyDominant.isReduced** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.IsSchemeTheoreticallyDominant`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsScheme
TheoreticallyDominant f]   [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry
.IsReduced X], AlgebraicGeometry.IsReduced Y
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.app_injective`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.IsSchemeTheoreticallyDominant f]   [Algebr
aicGeometry.QuasiCompact f] (U :…
· 使用定理 `AlgebraicGeometry.IsReduced.component_reduced`：∀ {X : AlgebraicGeometry.
Scheme} [self : AlgebraicGeometry.IsReduced X] (U : X.Opens),   IsReduced ↑(X.pr
esheaf.obj (Opposite.op U))
-/
lemma IsSchemeTheoreticallyDominant.isReduced (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f]
    [QuasiCompact f] [IsReduced X] : IsReduced Y :=
  ⟨fun _ ↦ isReduced_of_injective _ (f.app_injective _)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackSnd** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsSchemeTheoreticallyDominant`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeo
metry.IsSchemeTheoreticallyDominant f]   [AlgebraicGeometry.QuasiCompact f] [Alg
ebraicGeometry.Flat g],   AlgebraicGeometry.IsSchemeTheoreticallyDominant (Categ
oryTheory.Limits.pullback.snd f g)
参数：f : X ⟶ S；g : Y ⟶ S；CategoryTheory.Limits.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.IsSchemeTheoreticallyDominant f
 ↔ AlgebraicGeometry.Scheme.Hom.ker f = ⊥
· 使用定理 `TopologicalSpace.Opens.IsBasis.isOpenCover_mem_and_le`：∀ {ι : Type u_1} 
{X : Type u_3} [inst : TopologicalSpace X] {S : Set (TopologicalSpace.Opens X)},
   TopologicalSpace.Opens.IsBasis S →     ∀…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用引理 `TopologicalSpace.IsOpenCover.comap`：comap (hv : IsOpenCover v) (f : C(X,
 Y)) : IsOpenCover fun k => (v k).comap f
· 使用定理 `TopologicalSpace.Opens.IsBasis.isOpenCover`：∀ {X : Type u_3} [inst : Top
ologicalSpace X] {S : Set (TopologicalSpace.Opens X)},   TopologicalSpace.Opens.
IsBasis S → TopologicalSpace.IsO…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top`：ext_of_iSup_
eq_top {I J : X.IdealSheafData} {ι : Type*} (U : ι -> X.affineOpens) (hU : ⨆ i, 
(U i).1 = ⊤) (H : forall i, I.ideal (U i) = J.id…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `AlgebraicGeometry.instQuasiCompactSndScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.QuasiCompact f],   Algebrai
cGeometry.QuasiCompact (CategoryT…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.comp_preimage`：comp_preimage {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `right_eq_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b = a 
⊓ b ↔ b ≤ a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_right`：mono_p
ushoutSection_of_isCompact_of_flat_right [Flat f] (hUS : IsAffineOpen US) (hUT :
 IsAffineOpen UT) (hUX : IsCompact (X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isCompact_preimage`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] {U : Y.Opens},   IsCo
mpact ↑U → IsCompact ↑((TopologicalSp…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
（共 44 条，此处仅展示前 30 条）
-/
instance IsSchemeTheoreticallyDominant.pullbackSnd (f : X ⟶ S) (g : Y ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant (pullback.snd f g) := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap g.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U ↦ ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨V, ⟨U, hU⟩⟩, hV, hVU : V ≤ g ⁻¹ᵁ U⟩
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro x hx
  have := mono_pushoutSection_of_isCompact_of_flat_right
    (.of_hasPullback f g) (UY := pullback.snd f g ⁻¹ᵁ V) hVU le_rfl (by
      grw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, right_eq_inf,
        hVU]) hU hV (f.isCompact_preimage hU.isCompact)
  rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at this
  refine CommRingCat.inr_injective_of_flat (f.appLE U (f ⁻¹ᵁ U) le_rfl) (g.appLE U V hVU)
    (by simpa [Scheme.Hom.appLE] using f.app_injective U) (g.flat_appLE hU hV hVU) ?_
  apply this
  simpa [← CommRingCat.comp_apply, ← Scheme.Hom.app_eq_appLE] using hx
/-
**AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.IsSchemeTheoreticallyDominant`。
形式化陈述：∀ {X Y Z S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} {pX : Z ⟶ X
} {pY : Z ⟶ Y},   CategoryTheory.IsPullback pX pY f g →     ∀ [AlgebraicGeometry
.IsSchemeTheoreticallyDominant f] [AlgebraicGeometry.QuasiCompact f] [AlgebraicG
eometry.Flat g],       AlgebraicGeometry.IsSchemeTheoreticallyDominant pY
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
· 使用定理 `AlgebraicGeometry.instIsSchemeTheoreticallyDominantCompScheme`：∀ {X Y Z 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsSchemeT
heoreticallyDominant f]   [AlgebraicGeometry.IsSche…
· 使用定理 `AlgebraicGeometry.instIsSchemeTheoreticallyDominantOfIsIsoScheme`：∀ {X S
 : AlgebraicGeometry.Scheme} (f : X ⟶ S) [CategoryTheory.IsIso f],   AlgebraicGe
ometry.IsSchemeTheoreticallyDominant f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackSnd`：∀ {X Y S : 
AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsSchemeThe
oreticallyDominant f]   [AlgebraicGeometry.QuasiC…
-/
lemma IsSchemeTheoreticallyDominant.of_isPullback {f : X ⟶ S} {g : Y ⟶ S}
    {pX : Z ⟶ X} {pY : Z ⟶ Y} (H : IsPullback pX pY f g)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant pY := by
  rw [← H.isoPullback_hom_snd]
  infer_instance
/-
**AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsSchemeTheoreticallyDominant`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeo
metry.IsSchemeTheoreticallyDominant g]   [AlgebraicGeometry.QuasiCompact g] [Alg
ebraicGeometry.Flat f],   AlgebraicGeometry.IsSchemeTheoreticallyDominant (Categ
oryTheory.Limits.pullback.fst f g)
参数：f : X ⟶ S；g : Y ⟶ S；CategoryTheory.Limits.pullback.fst f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`：∀ {X Y Z 
S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} {pX : Z ⟶ X} {pY : Z ⟶ Y},
   CategoryTheory.IsPullback pX pY f g →     ∀ [Alg…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
instance IsSchemeTheoreticallyDominant.pullbackFst (f : X ⟶ S) (g : Y ⟶ S)
    [IsSchemeTheoreticallyDominant g] [QuasiCompact g] [Flat f] :
    IsSchemeTheoreticallyDominant (pullback.fst f g) :=
  .of_isPullback (.flip <| .of_hasPullback _ _)

end AlgebraicGeometry

