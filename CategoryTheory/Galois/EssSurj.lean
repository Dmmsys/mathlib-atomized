/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Full
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Essential surjectivity of fiber functors

Let `F : C ⥤ FintypeCat` be a fiber functor of a Galois category `C` and denote by
`H` the induced functor `C ⥤ Action FintypeCat (Aut F)`.

In this file we show that the essential image of `H` consists of the finite `Aut F`-sets where
the `Aut F` action is continuous.

## Main results

- `exists_lift_of_quotient_openSubgroup`: If `U` is an open subgroup of `Aut F`, then
  there exists an object `X` such that `F.obj X` is isomorphic to `Aut F ⧸ U` as
  `Aut F`-sets.
- `exists_lift_of_continuous`: If `X` is a finite, discrete `Aut F`-set, then
  there exists an object `A` such that `F.obj A` is isomorphic to `X` as
  `Aut F`-sets.

## Strategy

We first show that every finite, discrete `Aut F`-set `Y` has a decomposition into connected
components and each connected component is of the form `Aut F ⧸ U` for an open subgroup `U`.
Since `H` preserves finite coproducts, it hence suffices to treat the case `Y = Aut F ⧸ U`.
For the case `Y = Aut F ⧸ U` we closely follow the second part of Stacks Project Tag 0BN4.

-/

@[expose] public section

noncomputable section

universe u₁ u₂

namespace CategoryTheory

namespace PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {F : C ⥤ FintypeCat.{u₁}}

open Limits CategoryTheory.Functor

variable [GaloisCategory C] [FiberFunctor F]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

private local instance fintypeQuotient (H : OpenSubgroup (G)) :
    Fintype (G ⧸ (H : Subgroup (G))) :=
  have : Finite (G ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  Fintype.ofFinite _

set_option backward.privateInPublic true in
private local instance fintypeQuotientStabilizer {X : Type*} [MulAction G X]
    [TopologicalSpace X] [ContinuousSMul G X] [DiscreteTopology X] (x : X) :
    Fintype (G ⧸ (MulAction.stabilizer (G) x)) :=
  fintypeQuotient ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩

/-- If `X` is a finite discrete `G`-set, it can be written as the finite disjoint union
of quotients of the form `G ⧸ Uᵢ` for open subgroups `(Uᵢ)`. Note that this
is simply the decomposition into orbits. -/
/-
**CategoryTheory.PreGaloisCategory.has_decomp_quotients** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：has_decomp_quotients (X : Action FintypeCat G) [TopologicalSpace X.V] [Dis
creteTopology X.V] [ContinuousSMul G X.V] : exists (ι : Type) (_ : Finite ι) (f 
: ι -> OpenSubgroup (G)), Nonempty ((∐ fun i => G ⧸ₐ (f i).toSubgroup) ≅ X)
参数：X : Action FintypeCat G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasFiniteCoproducts`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCatego
ry C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.FintypeCat.instGaloisCategoryActionFintypeCat`：∀ (G : Typ
e u) [inst : Group G], CategoryTheory.GaloisCategory (Action FintypeCat G)
· 使用定理 `Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace`：∀ {G
 : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [SeparatelyContinuou
sMul G] [CompactSpace G]   (U : OpenSubgroup G), Finite …
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Action.instHasFiniteCoproducts`：∀ {V : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G]   [CategoryTheory.Limi
ts.HasFiniteCoproduc…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.PreGaloisCategory.has_decomp_connected_components'`：has_d
ecomp_connected_components' (X : C) : exists (ι : Type) (_ : Finite ι) (f : ι ->
 C) (_ : ∐ f ≅ X), forall i, IsConnected (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Action.Hom.comm`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (self : M.Hom N)
 (g :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback`
：mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y) [PreservesLimitsO
fShape WalkingCospan (forget C)] : Mono f ↔ Function.Injectiv…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.FintypeCat.instPreservesFiniteLimitsActionFintypeCatForge
tHomSubtypeFunObjFiniteV`：∀ (G : Type u) [inst : Group G],   CategoryTheory.Limi
ts.PreservesFiniteLimits (CategoryTheory.forget (Action FintypeCat G))
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.PreGaloisCategory.instMonoCoprod`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.GaloisCategory C],   Catego
ryTheory.Limits.MonoCoprod C
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` is a finite discrete `G`-set, it can be written as the finite disjoint un
ion
of quotients of the form `G ⧸ Uᵢ` for open subgroups `(Uᵢ)`. Note that this
is simply the decomposition into orbits.
-/
lemma has_decomp_quotients (X : Action FintypeCat G)
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul G X.V] :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → OpenSubgroup (G)),
      Nonempty ((∐ fun i ↦ G ⧸ₐ (f i).toSubgroup) ≅ X) := by
  obtain ⟨ι, hf, f, u, hc⟩ := has_decomp_connected_components' X
  let (i : ι) : TopologicalSpace (f i).V := ⊥
  have (i : ι) : DiscreteTopology (f i).V := ⟨rfl⟩
  have (i : ι) : ContinuousSMul G (f i).V := ContinuousSMul.mk <| by
    let r : f i ⟶ X := Sigma.ι f i ≫ u.hom
    let r'' (p : G × (f i).V) : G × X.V := (p.1, r.hom p.2)
    let q (p : G × X.V) : X.V := (X.ρ p.1).hom p.2
    let q' (p : G × (f i).V) : (f i).V := ((f i).ρ p.1).hom p.2
    have heq : q ∘ r'' = r.hom ∘ q' := by
      ext (p : G × (f i).V)
      exact (ConcreteCategory.congr_hom (r.comm p.1) p.2).symm
    have hrinj : Function.Injective r.hom :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback r).mp <| mono_comp _ _
    let t₁ : TopologicalSpace (G × (f i).V) := inferInstance
    change @Continuous _ _ _ ⊥ q'
    have : TopologicalSpace.induced r.hom inferInstance = ⊥ := by
      rw [← le_bot_iff]
      exact fun s _ ↦ ⟨r.hom '' s, ⟨isOpen_discrete (r.hom '' s), Set.preimage_image_eq s hrinj⟩⟩
    rw [← this, continuous_induced_rng, ← heq]
    exact Continuous.comp continuous_smul (by fun_prop)
  have (i : ι) : ∃ (U : OpenSubgroup (G)), (Nonempty ((f i) ≅ G ⧸ₐ U.toSubgroup)) := by
    obtain ⟨(x : (f i).V)⟩ := nonempty_fiber_of_isConnected (forget₂ _ _) (f i)
    let U : OpenSubgroup (G) := ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩
    exact ⟨U, ⟨FintypeCat.isoQuotientStabilizerOfIsConnected (f i) x⟩⟩
  choose g ui using this
  exact ⟨ι, hf, g, ⟨(Sigma.mapIso (fun i ↦ (ui i).some)).symm ≪≫ u⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `X` is connected and `x` is in the fiber of `X`, `F.obj X` is isomorphic
to the quotient of `Aut F` by the stabilizer of `x` as `Aut F`-sets. -/
/-
**CategoryTheory.PreGaloisCategory.fiberIsoQuotientStabilizer** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberIsoQuotientStabilizer (X : C) [IsConnected X] (x : F.obj X) : (functo
rToAction F).obj X ≅ Aut F ⧸ₐ MulAction.stabilizer (Aut F) x
参数：X : C；x : F.obj X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.instIsTopologicalGroupAutFunctorFintype
Cat`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTh
eory.Functor C FintypeCat),   IsTopologicalGroup (CategoryTheory.…
· 使用定理 `CategoryTheory.PreGaloisCategory.instCompactSpaceAutFunctorFintypeCat`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.F
unctor C FintypeCat),   CompactSpace (CategoryTheory.Aut F)
· 使用引理 `CategoryTheory.PreGaloisCategory.obj_discreteTopology`：obj_discreteTopol
ogy (X : C) : DiscreteTopology (F.obj X)

--- 原说明 ---
If `X` is connected and `x` is in the fiber of `X`, `F.obj X` is isomorphic
to the quotient of `Aut F` by the stabilizer of `x` as `Aut F`-sets.
-/
def fiberIsoQuotientStabilizer (X : C) [IsConnected X] (x : F.obj X) :
    (functorToAction F).obj X ≅ Aut F ⧸ₐ MulAction.stabilizer (Aut F) x :=
  haveI : IsConnected ((functorToAction F).obj X) := PreservesIsConnected.preserves
  letI : Fintype (Aut F ⧸ MulAction.stabilizer (Aut F) x) := fintypeQuotientStabilizer x
  FintypeCat.isoQuotientStabilizerOfIsConnected ((functorToAction F).obj X) x

section

open Action.FintypeCat

variable (V : OpenSubgroup (Aut F)) {U : OpenSubgroup (Aut F)}
  (h : Subgroup.Normal U.toSubgroup) {A : C} (u : (functorToAction F).obj A ≅ Aut F ⧸ₐ U.toSubgroup)

/-

### Strategy outline

Let `A` be an object of `C` with fiber `Aut F`-isomorphic to `Aut F ⧸ U` for an open normal
subgroup `U`. Then for any open subgroup `V` of `Aut F`, `V ⧸ (U ⊓ V)` acts on `A`. This
induces the diagram `quotientDiag`. Now assume `U ≤ V`. Then we can also postcompose
the diagram `quotientDiag` with `F`. The goal of this section is to compute that the colimit
of this composed diagram is `Aut F ⧸ V`. Finally, we obtain `F.obj (A ⧸ V) ≅ Aut F ⧸ V` as
`Aut F`-sets.
-/

/-
**CategoryTheory.PreGaloisCategory.quotientToEndObjectHom** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Strategy outline

Let `A` be an object of `C` with fiber `Aut F`-isomorphic to `Aut F ⧸ U` for an 
open normal
subgroup `U`. Then for any open subgroup `V` of `Aut F`, `V ⧸ (U ⊓ V)` acts on `
A`. This
induces the diagram `quotientDiag`. Now assume `U ≤ V`. Then we can also postcom
pose
the diagram `quotientDiag` with `F`. The goal of this section is to compute that
 the colimit
of this composed diagram is `Aut F ⧸ V`. Finally, we obtain `F.obj (A ⧸ V) ≅ Aut
 F ⧸ V` as
`Aut F`-sets.
-/
private def quotientToEndObjectHom :
    V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End A :=
  let ff : (functorToAction F).FullyFaithful := FullyFaithful.ofFullyFaithful (functorToAction F)
  let e : End A ≃* End (Aut F ⧸ₐ U.toSubgroup) := (ff.mulEquivEnd A).trans (Iso.conj u)
  e.symm.toMonoidHom.comp (quotientToEndHom V.toSubgroup U.toSubgroup)
/-
**CategoryTheory.PreGaloisCategory.functorToAction_map_quotientToEndObjectHom** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma functorToAction_map_quotientToEndObjectHom
    (m : SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⟶
      SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup)) :
    (functorToAction F).map (quotientToEndObjectHom V h u m) =
      u.hom ≫ quotientToEndHom V.toSubgroup U.toSubgroup m ≫ u.inv := by
  simp [← cancel_epi u.inv, ← cancel_mono u.hom, ← Iso.conj_apply, quotientToEndObjectHom]

@[simps!]
/-
**CategoryTheory.PreGaloisCategory.quotientDiag** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def quotientDiag : SingleObj (V.toSubgroup ⧸ Subgroup.subgroupOf U V) ⥤ C :=
  SingleObj.functor (quotientToEndObjectHom V h u)

variable {V} (hUinV : U ≤ V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
/-
**CategoryTheory.PreGaloisCategory.coconeQuotientDiag** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def coconeQuotientDiag :
    Cocone (quotientDiag V h u ⋙ functorToAction F) where
  pt := Aut F ⧸ₐ V.toSubgroup
  ι := SingleObj.natTrans (u.hom ≫ quotientToQuotientOfLE V.toSubgroup U.toSubgroup hUinV) <| by
    intro (m : V ⧸ Subgroup.subgroupOf U V)
    simp only [const_obj_obj, Functor.comp_map, const_obj_map, Category.comp_id]
    rw [← cancel_epi (u.inv), Iso.inv_hom_id_assoc]
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction m, x using Quotient.inductionOn₂ with | _ σ μ
    suffices h : ⟦μ * σ⁻¹⟧ = ⟦μ⟧ by
      simp only [quotientToQuotientOfLE_hom_mk, quotientDiag_map,
        functorToAction_map_quotientToEndObjectHom V _ u]
      simpa
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
/-
**CategoryTheory.PreGaloisCategory.coconeQuotientDiagDesc** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def coconeQuotientDiagDesc
    (s : Cocone (quotientDiag V h u ⋙ functorToAction F)) :
      (coconeQuotientDiag h u hUinV).pt ⟶ s.pt where
  hom := FintypeCat.homMk
    (Quotient.lift (fun σ ↦ (u.inv ≫ s.ι.app (SingleObj.star _)).hom ⟦σ⟧) <| fun σ τ hst ↦ by
      let J' := quotientDiag V h u ⋙ functorToAction F
      let m : End (SingleObj.star (V.toSubgroup ⧸ Subgroup.subgroupOf U V)) :=
        ⟦⟨σ⁻¹ * τ, (QuotientGroup.leftRel_apply).mp hst⟩⟧
      have h1 : J'.map m ≫ s.ι.app (SingleObj.star _) = s.ι.app (SingleObj.star _) :=
        s.ι.naturality m
      conv_rhs => rw [← h1]
      have h2 : (J'.map m).hom (u.inv.hom ⟦τ⟧) = u.inv.hom ⟦σ⟧ := by
        simp [J', functorToAction_map_quotientToEndObjectHom V h u m, ← comp_apply, m]
      simp [← h2, J'])
  comm g := by
    ext (x : Aut F ⧸ V.toSubgroup)
    induction x using Quotient.inductionOn with | _ σ
    simp only [const_obj_obj]
    change (((Aut F ⧸ₐ U.toSubgroup).ρ g ≫ u.inv.hom) ≫ (s.ι.app (SingleObj.star _)).hom) ⟦σ⟧ =
      ((s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g) (u.inv.hom ⟦σ⟧)
    have : ((functorToAction F).obj A).ρ g ≫ (s.ι.app (SingleObj.star _)).hom =
        (s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g :=
      (s.ι.app (SingleObj.star _)).comm g
    rw [← this, u.inv.comm g]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed cocone `coconeQuotientDiag` on the diagram `quotientDiag` is colimiting. -/
/-
**CategoryTheory.PreGaloisCategory.coconeQuotientDiagIsColimit** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed cocone `coconeQuotientDiag` on the diagram `quotientDiag` is col
imiting.
-/
private def coconeQuotientDiagIsColimit :
    IsColimit (coconeQuotientDiag h u hUinV) where
  desc := coconeQuotientDiagDesc h u hUinV
  fac s j := by
    apply (cancel_epi u.inv).mp
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction x using Quotient.inductionOn
    simp
    rfl
  uniq s f hf := by
    apply Action.hom_ext
    ext (x : Aut F ⧸ V.toSubgroup)
    induction x using Quotient.inductionOn with | _ σ
    simp [← hf (SingleObj.star _), ← ConcreteCategory.comp_apply]

end

set_option backward.isDefEq.respectTransparency false in
/-- For every open subgroup `V` of `Aut F`, there exists an `X : C` such that
`F.obj X ≅ Aut F ⧸ V` as `Aut F`-sets. -/
/-
**CategoryTheory.PreGaloisCategory.exists_lift_of_quotient_openSubgroup** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_lift_of_quotient_openSubgroup (V : OpenSubgroup (Aut F)) : exists (
X : C), Nonempty ((functorToAction F).obj X ≅ Aut F ⧸ₐ V.toSubgroup)
参数：V : OpenSubgroup (Aut F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace`：∀ {G
 : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [SeparatelyContinuou
sMul G] [CompactSpace G]   (U : OpenSubgroup G), Finite …
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `CategoryTheory.PreGaloisCategory.instContinuousMulAutFunctorFintypeCat`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.
Functor C FintypeCat),   ContinuousMul (CategoryTheory.Aut F…
· 使用定理 `CategoryTheory.PreGaloisCategory.instCompactSpaceAutFunctorFintypeCat`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.F
unctor C FintypeCat),   CompactSpace (CategoryTheory.Aut F)
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_set_ker_evaluation_subset_of_isO
pen`：exists_set_ker_evaluation_subset_of_isOpen {H : Set (Aut F)} (h1 : 1 in H) 
(h : IsOpen H) : exists (I : Set C) (_ : Fintype I), (forall X in…
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `OpenSubgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G] [inst_
1 : TopologicalSpace G], SubgroupClass (OpenSubgroup G) G
· 使用定理 `OpenSubgroup.isOpen'`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolo
gicalSpace G] (self : OpenSubgroup G), IsOpen (↑self).carrier
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasFiniteLimits`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasFiniteLimits C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber_nonempt
y`：exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) : e
xists (A : C) (_ : A ⟶ X), IsGalois A
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用引理 `CategoryTheory.PreGaloisCategory.obj_discreteTopology`：obj_discreteTopol
ogy (X : C) : DiscreteTopology (F.obj X)
· 使用定理 `CategoryTheory.PreGaloisCategory.instIsTopologicalGroupAutFunctorFintype
Cat`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTh
eory.Functor C FintypeCat),   IsTopologicalGroup (CategoryTheory.…
· 使用引理 `CategoryTheory.PreGaloisCategory.stabilizer_normal_of_isGalois`：stabiliz
er_normal_of_isGalois (X : C) [IsGalois X] (x : F.obj X) : Subgroup.Normal (MulA
ction.stabilizer (Aut F) x) where conj_mem n ninstab…
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
For every open subgroup `V` of `Aut F`, there exists an `X : C` such that
`F.obj X ≅ Aut F ⧸ V` as `Aut F`-sets.
-/
lemma exists_lift_of_quotient_openSubgroup (V : OpenSubgroup (Aut F)) :
    ∃ (X : C), Nonempty ((functorToAction F).obj X ≅ Aut F ⧸ₐ V.toSubgroup) := by
  obtain ⟨I, hf, hc, hi⟩ := exists_set_ker_evaluation_subset_of_isOpen F (one_mem V) V.isOpen'
  have (X : I) : IsConnected X.val := hc X X.property
  have (X : I) : Nonempty (F.obj X.val) := nonempty_fiber_of_isConnected F X
  have hn : Nonempty (F.obj <| (∏ᶜ fun X : I => X)) := nonempty_fiber_pi_of_nonempty_of_finite F _
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_fiber_nonempty F (∏ᶜ fun X : I => X) hn
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  let U : OpenSubgroup (Aut F) := ⟨MulAction.stabilizer (Aut F) a, stabilizer_isOpen (Aut F) a⟩
  let u := fiberIsoQuotientStabilizer A a
  have hUnormal : U.toSubgroup.Normal := stabilizer_normal_of_isGalois F A a
  have h1 (σ : Aut F) (σinU : σ ∈ U) : σ.hom.app A = 𝟙 (F.obj A) := by
    have hi : (Aut F ⧸ₐ MulAction.stabilizer (Aut F) a).ρ σ = 𝟙 _ := by
      refine FintypeCat.hom_ext _ _ (fun x ↦ ?_)
      induction x using Quotient.inductionOn with | _ τ
      change ⟦σ * τ⟧ = ⟦τ⟧
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp only [mul_inv_rev]
      exact Subgroup.Normal.conj_mem hUnormal _ (Subgroup.inv_mem U.toSubgroup σinU) _
    simp [← cancel_mono u.hom.hom, show σ.hom.app A ≫ u.hom.hom = _ from u.hom.comm σ, hi]
  have h2 (σ : Aut F) (σinU : σ ∈ U) : ∀ X : I, σ.hom.app X = 𝟙 (F.obj X) := by
    intro ⟨X, hX⟩
    ext (x : F.obj X)
    let p : A ⟶ X := f ≫ Pi.π (fun Z : I => (Z : C)) ⟨X, hX⟩
    have : IsConnected X := hc X hX
    obtain ⟨a, rfl⟩ := surjective_of_nonempty_fiber_of_isConnected F p x
    simp only [FintypeCat.id_apply, NatTrans.naturality_apply, h1 σ σinU]
  have hUinV : (U : Set (Aut F)) ≤ V := fun u uinU ↦ hi u (h2 u uinU)
  have := V.quotient_finite_of_isOpen' (U.subgroupOf V) V.isOpen (V.subgroupOf_isOpen U U.isOpen)
  exact ⟨colimit (quotientDiag V hUnormal u),
    ⟨preservesColimitIso (functorToAction F) (quotientDiag V hUnormal u) ≪≫
    colimit.isoColimitCocone ⟨coconeQuotientDiag hUnormal u hUinV,
    coconeQuotientDiagIsColimit hUnormal u hUinV⟩⟩⟩

/--
If `X` is a finite, discrete `Aut F`-set with continuous `Aut F`-action, then
there exists `A : C` such that `F.obj A ≅ X` as `Aut F`-sets.
-/
@[stacks 0BN4 "Essential surjectivity part"]
/-
**CategoryTheory.PreGaloisCategory.exists_lift_of_continuous** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_lift_of_continuous (X : Action FintypeCat (Aut F)) [TopologicalSpac
e X.V] [DiscreteTopology X.V] [ContinuousSMul (Aut F) X.V] : exists A, Nonempty 
((functorToAction F).obj A ≅ X)
参数：X : Action FintypeCat (Aut F)；Aut F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace`：∀ {G
 : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [SeparatelyContinuou
sMul G] [CompactSpace G]   (U : OpenSubgroup G), Finite …
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `CategoryTheory.PreGaloisCategory.instIsTopologicalGroupAutFunctorFintype
Cat`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTh
eory.Functor C FintypeCat),   IsTopologicalGroup (CategoryTheory.…
· 使用定理 `CategoryTheory.PreGaloisCategory.instCompactSpaceAutFunctorFintypeCat`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.F
unctor C FintypeCat),   CompactSpace (CategoryTheory.Aut F)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Action.instHasFiniteCoproducts`：∀ {V : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G]   [CategoryTheory.Limi
ts.HasFiniteCoproduc…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用引理 `CategoryTheory.PreGaloisCategory.has_decomp_quotients`：has_decomp_quotie
nts (X : Action FintypeCat G) [TopologicalSpace X.V] [DiscreteTopology X.V] [Con
tinuousSMul G X.V] : exists (ι : Type) (_ :…
· 使用定理 `CategoryTheory.PreGaloisCategory.instContinuousMulAutFunctorFintypeCat`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.
Functor C FintypeCat),   ContinuousMul (CategoryTheory.Aut F…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasFiniteCoproducts`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCatego
ry C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `CategoryTheory.PreGaloisCategory.instPreservesFiniteCoproductsActionFint
ypeCatAutFunctorFunctorToAction`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] (F : CategoryTheory.Functor C FintypeCat)   [inst_1 : CategoryTh
eory.GaloisCa…
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_lift_of_quotient_openSubgroup`：e
xists_lift_of_quotient_openSubgroup (V : OpenSubgroup (Aut F)) : exists (X : C),
 Nonempty ((functorToAction F).obj X ≅ Aut F ⧸ₐ V.toSubgrou…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `X` is a finite, discrete `Aut F`-set with continuous `Aut F`-action, then
there exists `A : C` such that `F.obj A ≅ X` as `Aut F`-sets.
-/
theorem exists_lift_of_continuous (X : Action FintypeCat (Aut F))
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul (Aut F) X.V] :
    ∃ A, Nonempty ((functorToAction F).obj A ≅ X) := by
  obtain ⟨ι, hfin, f, ⟨u⟩⟩ := has_decomp_quotients X
  choose g gu using (fun i ↦ exists_lift_of_quotient_openSubgroup (f i))
  exact ⟨∐ g, ⟨PreservesCoproduct.iso (functorToAction F) g ≪≫
    Sigma.mapIso (fun i ↦ (gu i).some) ≪≫ u⟩⟩

end PreGaloisCategory

end CategoryTheory

