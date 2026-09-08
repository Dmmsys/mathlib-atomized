/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Category.CompHausLike.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `TopCat`.
The fully faithful functor `CompHaus ⥤ TopCat` is denoted `compHausToTop`.

**Note:** The file `Mathlib/Topology/Category/Compactum.lean` provides the equivalence between
`Compactum`, which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`CompactumToCompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `CompactumToCompHaus.isEquivalence`.
See `Mathlib/Topology/Category/Compactum.lean` for a more detailed discussion where these
definitions are introduced.

## Implementation

The category `CompHaus` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

@[expose] public section


universe v u

open CategoryTheory CompHausLike

/-- The category of compact Hausdorff spaces. -/
/-
**CompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CompHaus
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of compact Hausdorff spaces.
-/
abbrev CompHaus := CompHausLike (fun _ ↦ True)

namespace CompHaus

/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CompHaus :=
  ⟨{ toTop := TopCat.of PEmpty, prop := trivial}⟩
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort CompHaus Type* :=
  ⟨fun X => X.toTop⟩
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : CompHaus} : CompactSpace X :=
  X.is_compact
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasProp (fun _ ↦ True) X := ⟨trivial⟩

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
/-
**CompHaus.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHaus`。
形式化陈述：of : CompHaus
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X

--- 原说明 ---
A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference.
-/
abbrev of : CompHaus := CompHausLike.of _ X

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `TopCat`. -/
/-
**compHausToTop** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：compHausToTop : CompHaus.{u} ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful embedding of `CompHaus` in `TopCat`.
-/
abbrev compHausToTop : CompHaus.{u} ⥤ TopCat.{u} :=
  CompHausLike.compHausLikeToTop _

/-- (Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps!]
/-
**stoneCechObj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stoneCechObj (X : TopCat) : CompHaus
参数：X : TopCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) The object part of the compactification functor from topologica
l spaces to
compact Hausdorff spaces.
-/
def stoneCechObj (X : TopCat) : CompHaus :=
  CompHaus.of (StoneCech X)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
/-
**stoneCechEquivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stoneCechEquivalence (X : TopCat.{u}) (Y : CompHaus.{u}) : (stoneCechObj X
 ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y) where toFun f
参数：X : TopCat.{u}；Y : CompHaus.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop

--- 原说明 ---
(Implementation) The bijection of homsets to establish the reflective adjunction
 of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : TopCat.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y) where
  toFun f := TopCat.ofHom
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.hom.hom.2.comp (@continuous_stoneCechUnit X _) }
  invFun f := CompHausLike.ofHom _
    { toFun := stoneCechExtend f.hom.2
      continuous_toFun := continuous_stoneCechExtend f.hom.2 }
  left_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext x
    refine congr_fun ?_ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    · rintro _ ⟨y, rfl⟩
      apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
      apply continuous_stoneCechUnit
  right_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext
    exact congr_fun (stoneCechExtend_extends hf) _

/-- The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
/-
**topToCompHaus** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topToCompHaus : TopCat.{u} ⥤ CompHaus.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Stone-Cech compactification functor from topological spaces to compact Hausd
orff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : TopCat.{u} ⥤ CompHaus.{u} :=
  Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl
/-
**topToCompHaus_obj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topToCompHaus_obj (X : TopCat) : ↥(topToCompHaus.obj X) = StoneCech X
参数：X : TopCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem topToCompHaus_obj (X : TopCat) : ↥(topToCompHaus.obj X) = StoneCech X :=
  rfl

/-- The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
/-
**compHausToTop.reflective** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：compHausToTop.reflective : Reflective compHausToTop where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of compact Hausdorff spaces is reflective in the category of topolo
gical spaces.
-/
noncomputable instance compHausToTop.reflective : Reflective compHausToTop where
  L := topToCompHaus
  adj := Adjunction.adjunctionOfEquivLeft _ _
/-
**compHausToTop.createsLimits** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：compHausToTop.createsLimits : CreatesLimits compHausToTop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance compHausToTop.createsLimits : CreatesLimits compHausToTop :=
  monadicCreatesLimits _
/-
**CompHaus.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompHaus.hasLimits : Limits.HasLimits CompHaus
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimits_of_hasLimits_createsLimits`：hasLimits_of_hasLim
its_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D] [CreatesLimitsOfSize.{
w, w'} F] : HasLimitsOfSize.{w, w'} C
-/
instance CompHaus.hasLimits : Limits.HasLimits CompHaus :=
  hasLimits_of_hasLimits_createsLimits compHausToTop
/-
**CompHaus.hasColimits** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompHaus.hasColimits : Limits.HasColimits CompHaus
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimits_of_reflective`：hasColimits_of_reflective (R :
 D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] : HasColimitsOfSize.{v, u} D
-/
instance CompHaus.hasColimits : Limits.HasColimits CompHaus :=
  hasColimits_of_reflective compHausToTop

namespace CompHaus

/-- An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`TopCat.limitCone`. -/
/-
**CompHaus.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
形式化陈述：limitCone {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Li
mits.Cone F
参数：F : J ⥤ CompHaus.{max v u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`TopCat.limitCone`.
-/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Limits.Cone F :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { pt := {
      toTop := (TopCat.limitCone FF).pt
      is_compact := by
        change CompactSpace { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        have :
          { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } := by
          ext1
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        rw [this]
        apply isClosed_iInter
        intro i
        apply isClosed_iInter
        intro j
        apply isClosed_iInter
        intro f
        apply isClosed_eq
        · exact ((F.map f).hom.hom.continuous).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance
      prop := trivial }
    π := {
      app := fun j => InducedCategory.homMk ((TopCat.limitCone FF).π.app j)
      naturality := by
        intro _ _ f
        ext ⟨x, hx⟩
        simp only [Functor.const_obj_map]
        exact (hx f).symm } }

/-- The limit cone `CompHaus.limitCone F` is indeed a limit cone. -/
/-
**CompHaus.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
形式化陈述：limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u
}) : Limits.IsLimit.{v} (limitCone.{v, u} F)
参数：F : J ⥤ CompHaus.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone `CompHaus.limitCone F` is indeed a limit cone.
-/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) :
    Limits.IsLimit.{v} (limitCone.{v, u} F) :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { lift := fun S => InducedCategory.homMk
      ((TopCat.limitConeIsLimit FF).lift (compHausToTop.mapCone S))
    uniq := fun S m hm => InducedCategory.hom_ext
      ((TopCat.limitConeIsLimit FF).uniq (compHausToTop.mapCone S) _ (fun j ↦ by
        simp [← hm]
        rfl)) }
/-
**CompHaus.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CompHaus`。
形式化陈述：epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Sur
jective f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `Homeomorph.compactSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   Comp
actSpace Y
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Homeomorph.t2Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
（共 60 条，此处仅展示前 30 条）
-/
theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let D := ({y} : Set Y)
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
    have : CompactSpace (ULift.{u} <| Set.Icc (0 : ℝ) 1) := Homeomorph.ulift.symm.compactSpace
    have : T2Space (ULift.{u} <| Set.Icc (0 : ℝ) 1) := Homeomorph.ulift.symm.t2Space
    let Z := of (ULift.{u} <| Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z := ofHom _
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uliftUp.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ofHom _
      ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x : 4
      simp [g, h, Z, hφ0 (Set.mem_range_self x)]
    apply_fun fun e => (e y).down.1 at H
    dsimp [g, h, Z] at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map

end CompHaus

/-- Every `CompHausLike` admits a functor to `CompHaus`. -/
/-
**compHausLikeToCompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：compHausLikeToCompHaus (P : TopCat -> Prop) : CompHausLike P ⥤ CompHaus
参数：P : TopCat -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `CompHausLike` admits a functor to `CompHaus`.
-/
abbrev compHausLikeToCompHaus (P : TopCat → Prop) : CompHausLike P ⥤ CompHaus :=
  CompHausLike.toCompHausLike (by simp only [implies_true])
