/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Smooth manifolds as locally ringed spaces

This file equips a smooth manifold with the structure of a locally ringed space.

## Main results

* `smoothSheafCommRing.isUnit_stalk_iff`: The units of the stalk at `x` of the sheaf of smooth
  functions from a smooth manifold `M` to its scalar field `𝕜`, considered as a sheaf of commutative
  rings, are the functions whose values at `x` are nonzero.

## Main definitions

* `ChartedSpace.locallyRingedSpace`: A smooth manifold can be considered as a locally ringed space.
* `ChartedSpace.locallyRingedSpaceMap`: A smooth map between smooth manifolds induces a morphism
  of locally ringed spaces.

## TODO

- Show that every morphism of locally ringed spaces between two smooth manifolds is induced
  by a smooth map via `ChartedSpace.locallyRingedSpaceMap`.

-/

@[expose] public section

noncomputable section
universe u

open scoped ContDiff

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] (IN : ModelWithCorners 𝕜 EN HN)
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  {P : Type u} [TopologicalSpace P] [ChartedSpace HP P]

open AlgebraicGeometry Manifold TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency.types false in
/-- The units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, considered as a
sheaf of commutative rings, are the functions whose values at `x` are nonzero. -/
/-
**smoothSheafCommRing.isUnit_stalk_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.isUnit_stalk_iff {x : M} (f : (smoothSheafCommRing IM 
𝓘(𝕜) M 𝕜).presheaf.stalk x) : IsUnit f ↔ f ∉ RingHom.ker (smoothSheafCommRing.ev
al IM 𝓘(𝕜) M 𝕜 x)
参数：f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smoothSheafCommRing.eval_germ`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [inst_2 : NormedSp
ace 𝕜 EM] {HM : Typ…
· 使用定理 `ContinuousAt.eventually_ne`：ContinuousAt.eventually_ne [TopologicalSpace
 Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y} (hg1 : ContinuousAt g x) (hg2 : g x
 != y) : forallᶠ…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, 
considered as a
sheaf of commutative rings, are the functions whose values at `x` are nonzero.
-/
theorem smoothSheafCommRing.isUnit_stalk_iff {x : M}
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) :
    IsUnit f ↔ f ∉ RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x f = 0)
    simpa [h'] using congr_arg (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) hf
  · let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    -- Suppose that `f`, in the stalk at `x`, is nonzero at `x`
    rintro (hf : _ ≠ 0)
    -- Represent `f` as the germ of some function (also called `f`) on an open neighbourhood `U` of
    -- `x`, which is nonzero at `x`
    obtain ⟨U : Opens M, hxU, f : C^∞⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.exists_germ_eq f
    have hf' : f ⟨x, hxU⟩ ≠ 0 := by
      convert! hf
      exact (smoothSheafCommRing.eval_germ U x hxU f).symm
    -- In fact, by continuity, `f` is nonzero on a neighbourhood `V` of `x`
    have H : ∀ᶠ (z : U) in 𝓝 ⟨x, hxU⟩, f z ≠ 0 := f.2.continuous.continuousAt.eventually_ne hf'
    rw [eventually_nhds_iff] at H
    obtain ⟨V₀, hV₀f, hV₀, hxV₀⟩ := H
    let V : Opens M := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀⟩
    have hUV : V ≤ U := Subtype.coe_image_subset (U : Set M) V₀
    have hV : V₀ = Set.range (Set.inclusion hUV) := by
      convert! (Set.range_inclusion hUV).symm
      ext y
      change _ ↔ y ∈ Subtype.val ⁻¹' Subtype.val '' V₀
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV
    have hxV : x ∈ (V : Set M) := by
      obtain ⟨x₀, hxx₀⟩ := hxV₀
      convert! x₀.2
      exact congr_arg Subtype.val hxx₀.symm
    have hVf : ∀ y : V, f (Set.inclusion hUV y) ≠ 0 :=
      fun y ↦ hV₀f (Set.inclusion hUV y) (Set.mem_range_self y)
    -- Let `g` be the pointwise inverse of `f` on `V`, which is smooth since `f` is nonzero there
    let g : C^∞⟮IM, V; 𝓘(𝕜), 𝕜⟯ := ⟨(f ∘ Set.inclusion hUV)⁻¹, ?_⟩
    -- The germ of `g` is inverse to the germ of `f`, so `f` is a unit
    · refine ⟨⟨S.germ _ x (hxV) (ContMDiffMap.restrictRingHom IM 𝓘(𝕜) 𝕜 hUV f), S.germ _ x hxV g,
        ?_, ?_⟩, S.germ_res_apply hUV.hom x hxV f⟩
      · rw [← map_mul]
        -- Qualified the name to avoid Lean not finding a `OneHomClass` https://github.com/leanprover-community/mathlib4/pull/8386
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply mul_inv_cancel₀
        exact hVf y
      · rw [← map_mul]
        -- Qualified the name to avoid Lean not finding a `OneHomClass` https://github.com/leanprover-community/mathlib4/pull/8386
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply inv_mul_cancel₀
        exact hVf y
    · intro y
      exact (((contDiffAt_inv _ (hVf y)).contMDiffAt).comp y
        (f.contMDiff.comp (contMDiff_inclusion hUV)).contMDiffAt :)

/-- The non-units of the stalk at `x` of the sheaf of smooth functions from `M` to `𝕜`, considered
as a sheaf of commutative rings, are the functions whose values at `x` are zero. -/
/-
**smoothSheafCommRing.nonunits_stalk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.nonunits_stalk (x : M) : nonunits ((smoothSheafCommRin
g IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) = RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜)
 M 𝕜 x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `smoothSheafCommRing.isUnit_stalk_iff`：smoothSheafCommRing.isUnit_stalk_i
ff {x : M} (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) : IsUnit f ↔
 f ∉ RingHom.ker (smoothSh…

--- 原说明 ---
The non-units of the stalk at `x` of the sheaf of smooth functions from `M` to `
𝕜`, considered
as a sheaf of commutative rings, are the functions whose values at `x` are zero.
-/
theorem smoothSheafCommRing.nonunits_stalk (x : M) :
    nonunits ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x)
    = RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  ext1 f
  rw [mem_nonunits_iff, not_iff_comm, Iff.comm]
  apply smoothSheafCommRing.isUnit_stalk_iff

/-- The stalks of the structure sheaf of a smooth manifold are local rings. -/
/-
**smoothSheafCommRing.instLocalRing_stalk** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.instLocalRing_stalk (x : M) : IsLocalRing ((smoothShea
fCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x)
参数：x : M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_nonunits_add`：of_nonunits_add [Nontrivial R] (h : forall 
a b : R, a in nonunits R -> b in nonunits R -> a + b in nonunits R) : IsLocalRin
g R where isUnit_…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `instNontrivialCarrierStalkCommRingCatPresheafSmoothSheafCommRing`：∀ {𝕜 :
 Type u_1} [inst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_1 : NormedAd
dCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Typ…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smoothSheafCommRing.nonunits_stalk`：smoothSheafCommRing.nonunits_stalk (
x : M) : nonunits ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) = RingHom
.ker (smoothSheafCommRin…
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I

--- 原说明 ---
The stalks of the structure sheaf of a smooth manifold are local rings.
-/
instance smoothSheafCommRing.instLocalRing_stalk (x : M) :
    IsLocalRing ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [smoothSheafCommRing.nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

variable (M)

/-- A smooth manifold can be considered as a locally ringed space. -/
@[implicit_reducible]
/-
**ChartedSpace.locallyRingedSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyRingedSpace : LocallyRingedSpace where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth manifold can be considered as a locally ringed space.
-/
def ChartedSpace.locallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of M
  presheaf := smoothPresheafCommRing IM 𝓘(𝕜) M 𝕜
  IsSheaf := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).property
  isLocalRing x := smoothSheafCommRing.instLocalRing_stalk IM x

@[deprecated (since := "2026-04-01")]
alias IsManifold.locallyRingedSpace := ChartedSpace.locallyRingedSpace

open CategoryTheory Limits

variable {M IM IN}

/-- (Implementation): Use `ChartedSpace.locallyRingedSpaceMap`. -/
/-
**ChartedSpace.locallyRingedSpaceMapAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyRingedSpaceMapAux (f : M -> N) (hf : ContMDiff IM IN ∞
 f) : (locallyRingedSpace IM M).toPresheafedSpace ⟶ (locallyRingedSpace IN N).to
PresheafedSpace where base
参数：f : M -> N；hf : ContMDiff IM IN ∞ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Use `ChartedSpace.locallyRingedSpaceMap`.
-/
def ChartedSpace.locallyRingedSpaceMapAux (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace where
  base := TopCat.ofHom ⟨f, hf.continuous⟩
  c := (hf.smoothSheafCommRingHom _ _ f).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- (Implementation): Use `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom`. -/
/-
**ChartedSpace.stalkMap_locallyRingedSpaceMapAux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChartedSpace.stalkMap_locallyRingedSpaceMapAux (f : M -> N) (hf : ContMDif
f IM IN ∞ f) (x : M) : (locallyRingedSpaceMapAux f hf).stalkMap x ≫ smoothSheafC
ommRing.evalHom IM 𝓘(𝕜) M 𝕜 x = smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x)
参数：f : M -> N；hf : ContMDiff IM IN ∞ f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColim
its C]   {X Y : AlgebraicGeometry.Presheafe…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smoothSheafCommRing.evalHom_germ`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [inst_2 : Norme
dSpace 𝕜 EM] {HM : Typ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
(Implementation): Use `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom`.
-/
lemma ChartedSpace.stalkMap_locallyRingedSpaceMapAux (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (x : M) :
    (locallyRingedSpaceMapAux f hf).stalkMap x ≫
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext a
  refine Eq.trans ?_ (smoothSheafCommRing.evalHom_germ _ _ _ _ _ _ _ a).symm
  apply smoothSheafCommRing.evalHom_germ

set_option backward.isDefEq.respectTransparency false in
/-- A smooth function of manifolds `f : M → N` induces a morphism of locally ringed spaces. -/
@[simps! base]
/-
**ChartedSpace.locallyRingedSpaceMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyRingedSpaceMap (f : M -> N) (hf : ContMDiff IM IN ∞ f)
 : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N where __
参数：f : M -> N；hf : ContMDiff IM IN ∞ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth function of manifolds `f : M → N` induces a morphism of locally ringed 
spaces.
-/
def ChartedSpace.locallyRingedSpaceMap (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    locallyRingedSpace IM M ⟶ locallyRingedSpace IN N where
  __ := locallyRingedSpaceMapAux f hf
  prop x := by
    refine ⟨fun a ha ↦ ?_⟩
    rw [smoothSheafCommRing.isUnit_stalk_iff, RingHom.mem_ker] at ha ⊢
    convert! ha
    exact (congr($(stalkMap_locallyRingedSpaceMapAux f hf x) a)).symm

@[reassoc (attr := simp)]
/-
**ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom (f : M -> N) (hf : Con
tMDiff IM IN ∞ f) (x : M) : (locallyRingedSpaceMap f hf).stalkMap x ≫ smoothShea
fCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x = smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x)
参数：f : M -> N；hf : ContMDiff IM IN ∞ f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ChartedSpace.stalkMap_locallyRingedSpaceMapAux`：ChartedSpace.stalkMap_lo
callyRingedSpaceMapAux (f : M -> N) (hf : ContMDiff IM IN ∞ f) (x : M) : (locall
yRingedSpaceMapAux f hf).stalkMap x …
-/
lemma ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (x : M) :
    (locallyRingedSpaceMap f hf).stalkMap x ≫
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x) :=
  stalkMap_locallyRingedSpaceMapAux f hf x

variable (IM M) in
/-
**ChartedSpace.locallyRingedSpace_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyRingedSpace_id : locallyRingedSpaceMap (IM
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
-/
lemma ChartedSpace.locallyRingedSpace_id :
    locallyRingedSpaceMap (IM := IM) (IN := IM) (M := M) id contMDiff_id = 𝟙 _ :=
  rfl
/-
**ChartedSpace.locallyRingedSpace_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChartedSpace.locallyRingedSpace_comp {f : M -> N} (hf : ContMDiff IM IN ∞ 
f) {g : N -> P} (hg : ContMDiff IN IP ∞ g) : locallyRingedSpaceMap (g ∘ f) (hg.c
omp hf) = locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg
参数：hf : ContMDiff IM IN ∞ f；hg : ContMDiff IN IP ∞ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
-/
lemma ChartedSpace.locallyRingedSpace_comp {f : M → N} (hf : ContMDiff IM IN ∞ f)
    {g : N → P} (hg : ContMDiff IN IP ∞ g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg :=
  rfl

-- TODO: This holds more generally if `U` is replaced by an open embedding that
-- is also a smooth immersion.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (ChartedSpace.locallyRingedSpaceMap _ (contMDiff_subtype_val (I := IM) (U := U))) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ Subtype.ext ?_, fun ⟨g, hg⟩ ↦ ?_⟩
    · ext ⟨x, y, hy, rfl⟩
      exact congr($(hab).1 ⟨y, ⟨y, hy, rfl⟩⟩)
    · let a : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
      let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
      let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      refine ⟨⟨g ∘ b.symm, ContMDiff.comp hg ?_⟩, Subtype.ext <| funext fun _ ↦ ?_⟩
      · refine (ContMDiff.subtypeVal_comp_iff V' _).mp ?_
        rw [← ContMDiff.subtypeVal_comp_iff]
        convert! contMDiff_subtype_val
        ext x
        exact congr($(b.apply_symm_apply x).1)
      · change g _ = _
        congr
        apply b.symm_apply_apply

/-- Viewing a manifold as a locally ringed space commutes with restriction to open subsets. -/
@[simps]
/-
**ChartedSpace.restrictLocallyRingedSpaceIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ChartedSpace.restrictLocallyRingedSpaceIso (U : Opens M) : (locallyRingedS
pace IM M).restrict U.isOpenEmbedding ≅ locallyRingedSpace IM U where hom
参数：U : Opens M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsOpenImmersionLocallyRingedSpaceMapSubtypeMemOpensVal`：∀ {𝕜 : Type 
u} [inst : NontriviallyNormedField 𝕜] {EM : Type u_1} [inst_1 : NormedAddCommGro
up EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Type …

--- 原说明 ---
Viewing a manifold as a locally ringed space commutes with restriction to open s
ubsets.
-/
def ChartedSpace.restrictLocallyRingedSpaceIso (U : Opens M) :
    (locallyRingedSpace IM M).restrict U.isOpenEmbedding ≅
      locallyRingedSpace IM U where
  hom := LocallyRingedSpace.IsOpenImmersion.lift
    (locallyRingedSpaceMap _ contMDiff_subtype_val)
    (LocallyRingedSpace.ofRestrict _ _) (by rfl)
  inv := LocallyRingedSpace.IsOpenImmersion.lift
    ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)
    (locallyRingedSpaceMap _ contMDiff_subtype_val) (by rfl)
  hom_inv_id := by
    simp [← cancel_mono ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)]
  inv_hom_id := by
    simp [← cancel_mono (locallyRingedSpaceMap _ contMDiff_subtype_val)]
