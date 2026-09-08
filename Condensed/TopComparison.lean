/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.Condensed.Basic
public import Mathlib.Topology.Category.TopCat.Yoneda

/-!

# The functor from topological spaces to condensed sets

This file builds on the API from the file `TopCat.Yoneda`. If the forgetful functor to `TopCat` has
nice properties, like preserving pullbacks and finite coproducts, then this Yoneda presheaf
satisfies the sheaf condition for the regular and extensive topologies respectively.

We apply this API to `CompHaus` and define the functor
`topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u}`.

-/

@[expose] public section

universe w w' v u

open CategoryTheory Opposite Limits regularTopology ContinuousMap Topology

variable {C : Type u} [Category.{v} C] (G : C ⥤ TopCat.{w})
  (X : Type w') [TopologicalSpace X]

/--
An auxiliary lemma to that allows us to use `IsQuotientMap.lift` in the proof of
`equalizerCondition_yonedaPresheaf`.
-/
/-
**factorsThrough_of_pullbackCondition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：factorsThrough_of_pullbackCondition {Z B : C} {π : Z ⟶ B} [HasPullback π π
] [PreservesLimit (cospan π π) G] {a : C(G.obj Z, X)} (ha : a ∘ (G.map (pullback
.fst _ _)) = a ∘ (G.map (pullback.snd π π))) : Function.FactorsThrough a (G.map 
π)
参数：cospan π π；G.obj Z, X；ha : a ∘ (G.map (pullback.fst _ _)) = a ∘ (G.map (pullb
ack.snd π π))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd_apply`：pullbackIsoProdSubtype_inv_
snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.snd f g ((pullbackIsoProdSubtyp…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst_apply`：pullbackIsoProdSubtype_inv_
fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.fst f g ((pullbackIsoProdSubtyp…

--- 原说明 ---
An auxiliary lemma to that allows us to use `IsQuotientMap.lift` in the proof of
`equalizerCondition_yonedaPresheaf`.
-/
theorem factorsThrough_of_pullbackCondition {Z B : C} {π : Z ⟶ B} [HasPullback π π]
    [PreservesLimit (cospan π π) G]
    {a : C(G.obj Z, X)}
    (ha : a ∘ (G.map (pullback.fst _ _)) = a ∘ (G.map (pullback.snd π π))) :
    Function.FactorsThrough a (G.map π) := by
  intro x y hxy
  let xy : G.obj (pullback π π) := (PreservesPullback.iso G π π).inv <|
    (TopCat.pullbackIsoProdSubtype (G.map π) (G.map π)).inv ⟨(x, y), hxy⟩
  have ha' := congr_fun ha xy
  dsimp at ha'
  have h₁ : ∀ y, G.map (pullback.fst _ _) ((PreservesPullback.iso G π π).inv y) =
      pullback.fst (G.map π) (G.map π) y := by
    simp only [← PreservesPullback.iso_inv_fst]; intro y; rfl
  have h₂ : ∀ y, G.map (pullback.snd _ _) ((PreservesPullback.iso G π π).inv y) =
      pullback.snd (G.map π) (G.map π) y := by
    simp only [← PreservesPullback.iso_inv_snd]; intro y; rfl
  rw [h₁, h₂, TopCat.pullbackIsoProdSubtype_inv_fst_apply,
    TopCat.pullbackIsoProdSubtype_inv_snd_apply] at ha'
  simpa using ha'

set_option backward.isDefEq.respectTransparency false in
/--
If `G` preserves the relevant pullbacks and every effective epi in `C` is a quotient map (which is
the case when `C` is `CompHaus` or `Profinite`), then `yonedaPresheaf` satisfies the equalizer
condition which is required to be a sheaf for the regular topology.
-/
/-
**equalizerCondition_yonedaPresheaf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equalizerCondition_yonedaPresheaf [forall (Z B : C) (π : Z ⟶ B) [Effective
Epi π], PreservesLimit (cospan π π) G] (hq : forall (Z B : C) (π : Z ⟶ B) [Effec
tiveEpi π], IsQuotientMap (G.map π)) : EqualizerCondition (yonedaPresheaf G X)
参数：Z B : C；π : Z ⟶ B；cospan π π；hq : forall (Z B : C) (π : Z ⟶ B) [EffectiveEpi 
π], IsQuotientMap (G.map π)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.regularTopology.EqualizerCondition.mk`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Functor Cᵒᵖ (Ty
pe u_4)),   (∀ (X B : C) (π : X ⟶ B) [Cate…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `ContinuousMap.mk.injEq`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (toFun : X → Y)   (continuous_toFun : 
autoParam (C…
· 使用定理 `factorsThrough_of_pullbackCondition`：factorsThrough_of_pullbackCondition
 {Z B : C} {π : Z ⟶ B} [HasPullback π π] [PreservesLimit (cospan π π) G] {a : C(
G.obj Z, X)} (ha : a ∘ (G…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Topology.IsQuotientMap.lift_comp`：lift_comp : (hf.lift g h).comp f = g

--- 原说明 ---
If `G` preserves the relevant pullbacks and every effective epi in `C` is a quot
ient map (which is
the case when `C` is `CompHaus` or `Profinite`), then `yonedaPresheaf` satisfies
 the equalizer
condition which is required to be a sheaf for the regular topology.
-/
theorem equalizerCondition_yonedaPresheaf
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) G]
    (hq : ∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], IsQuotientMap (G.map π)) :
      EqualizerCondition (yonedaPresheaf G X) := by
  apply EqualizerCondition.mk
  intro Z B π _ _
  refine ⟨fun a b h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, TypeCat.Fun.coe_mk,
      Set.coe_ofPred, mapToEqualizer, Set.mem_ofPred_eq, ConcreteCategory.hom_ofHom,
      Subtype.mk.injEq, mk.injEq] at h
    simp only [yonedaPresheaf, unop_op]
    ext x
    obtain ⟨y, hy⟩ := (hq Z B π).surjective x
    rw [← hy]
    exact congr_fun h y
  · simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, mk.injEq, Set.mem_ofPred_eq] at ha
    simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, TypeCat.Fun.coe_mk,
      Set.coe_ofPred, mapToEqualizer, Set.mem_ofPred_eq, ConcreteCategory.hom_ofHom,
      Subtype.mk.injEq]
    simp only [yonedaPresheaf, unop_op] at a
    refine ⟨(hq Z B π).lift a (factorsThrough_of_pullbackCondition G X ha), ?_⟩
    congr 1
    exact DFunLike.ext'_iff.mp ((hq Z B π).lift_comp a (factorsThrough_of_pullbackCondition G X ha))

/--
If `G` preserves finite coproducts (which is the case when `C` is `CompHaus`, `Profinite` or
`Stonean`), then `yonedaPresheaf` preserves finite products, which is required to be a sheaf for
the extensive topology.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves finite coproducts (which is the case when `C` is `CompHaus`, `P
rofinite` or
`Stonean`), then `yonedaPresheaf` preserves finite products, which is required t
o be a sheaf for
the extensive topology.
-/
noncomputable instance [PreservesFiniteCoproducts G] :
    PreservesFiniteProducts (yonedaPresheaf G X) :=
  have := preservesFiniteProducts_op G
  ⟨fun _ ↦ comp_preservesLimitsOfShape G.op (yonedaPresheaf' X)⟩

section

variable (P : TopCat.{u} → Prop) (X : TopCat.{max u w})
    [CompHausLike.HasExplicitFiniteCoproducts.{0} P] [CompHausLike.HasExplicitPullbacks.{u} P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/--
The sheaf on `CompHausLike P` of continuous maps to a topological space.
-/
@[simps! obj_obj obj_map]
/-
**TopCat.toSheafCompHausLike** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopCat.toSheafCompHausLike : have
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf on `CompHausLike P` of continuous maps to a topological space.
-/
def TopCat.toSheafCompHausLike :
    have := CompHausLike.preregular hs
    Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj := yonedaPresheaf.{u, max u w} (CompHausLike.compHausLikeToTop.{u} P) X
  property := by
    have := CompHausLike.preregular hs
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    refine ⟨inferInstance, ?_⟩
    apply +allowSynthFailures equalizerCondition_yonedaPresheaf
      (CompHausLike.compHausLikeToTop.{u} P) X
    intro Z B π he
    exact .of_surjective_continuous (hs _ he) π.hom.hom.continuous

/--
`TopCat.toSheafCompHausLike` yields a functor from `TopCat.{max u w}` to
`Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))`.
-/
@[simps]
/-
**topCatToSheafCompHausLike** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topCatToSheafCompHausLike : have
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TopCat.toSheafCompHausLike` yields a functor from `TopCat.{max u w}` to
`Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))`.
-/
noncomputable def topCatToSheafCompHausLike :
    have := CompHausLike.preregular hs
    TopCat.{max u w} ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := X.toSheafCompHausLike P hs
  map f := ⟨⟨fun _ ↦ ↾fun g ↦ f.hom.comp g,  by aesop⟩⟩

end

/--
Associate to a `(u + 1)`-small topological space the corresponding condensed set, given by
`yonedaPresheaf`.
-/
/-
**TopCat.toCondensedSet** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopCat.toCondensedSet (X : TopCat.{u + 1}) : CondensedSet.{u}
参数：X : TopCat.{u + 1}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True

--- 原说明 ---
Associate to a `(u + 1)`-small topological space the corresponding condensed set
, given by
`yonedaPresheaf`.
-/
noncomputable abbrev TopCat.toCondensedSet (X : TopCat.{u + 1}) : CondensedSet.{u} :=
  toSheafCompHausLike.{u + 1} _ X (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
`TopCat.toCondensedSet` yields a functor from `TopCat.{u + 1}` to `CondensedSet.{u}`.
-/
/-
**topCatToCondensedSet** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True

--- 原说明 ---
`TopCat.toCondensedSet` yields a functor from `TopCat.{u + 1}` to `CondensedSet.
{u}`.
-/
noncomputable abbrev topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u} :=
  topCatToSheafCompHausLike.{u + 1} _ (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)
