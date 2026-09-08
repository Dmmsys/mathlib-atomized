/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically Irreducible Schemes

## Main results
- `AlgebraicGeometry.GeometricallyIrreducible`:
  We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is irreducible.
  We also provide the fact that this is stable under base change (by `infer_instance`)
- `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber`:
  A scheme is geometrically irreducible over `S` iff the fibers of all
  `s : S` are geometrically irreducible.
- `AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace`:
  If `X` is geometrically irreducible and universally open (e.g. when flat + finite presentation),
  over an irreducible scheme, then `X` is also irreducible.
  In particular, the base change of a geometrically irreducible and universally open scheme to an
  irreducible scheme is irreducible (by `infer_instance`).
-/

universe u

@[expose] public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is irreducible. -/
@[mk_iff]
/-
**AlgebraicGeometry.GeometricallyIrreducible** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K
 ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is irreducible.
-/
class GeometricallyIrreducible (f : X ⟶ Y) : Prop where
  geometrically_irreducibleSpace : geometrically (IrreducibleSpace ·) f
/-
**AlgebraicGeometry.GeometricallyIrreducible.eq_geometrically** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.GeometricallyIrreducible`。
形式化陈述：@AlgebraicGeometry.GeometricallyIrreducible = AlgebraicGeometry.geometrica
lly fun x => IrreducibleSpace ↥x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.geometricallyIrreducible_iff`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.GeometricallyIrreducible f ↔ Algebra
icGeometry.geometrically (fun x => I…
-/
lemma GeometricallyIrreducible.eq_geometrically :
    @GeometricallyIrreducible = geometrically (IrreducibleSpace ·) := by
  ext; exact geometricallyIrreducible_iff _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @GeometricallyIrreducible :=
  GeometricallyIrreducible.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyIrreducible g] : GeometricallyIrreducible (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyIrreducible f] : GeometricallyIrreducible (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : S.Opens) [GeometricallyIrreducible f] : GeometricallyIrreducible (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyIrreducible f] :
    GeometricallyIrreducible (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyIrreducible f] : IrreducibleSpace (f.fiber s) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [GeometricallyIrreducible f] : Surjective f :=
  ⟨fun x ↦ ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩
/-
**AlgebraicGeometry.Scheme.Hom.isIrreducible_preimage** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyIrreducible f],   IsOpenMap ⇑f → ∀ {s : Set ↥S}, IsIrreducible s → IsIrredu
cible (⇑f ⁻¹' s)
参数：f : X ⟶ S；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_fiberι`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) (y : ↥Y),   Set.range ⇑(AlgebraicGeometry.Scheme.Hom.fiberι f 
y) = ⇑f ⁻¹' {y}
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsIrreducible.image`：IsIrreducible.image (H : IsIrreducible s) (f : X ->
 Y) (hf : ContinuousOn f s) : IsIrreducible (f '' s)
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatFiberOfGe
ometricallyIrreducible`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (s : ↥S) 
[AlgebraicGeometry.GeometricallyIrreducible f],   IrreducibleSpace ↥(AlgebraicGe
omet…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用引理 `IsIrreducible.preimage_of_isPreirreducible_fiber`：IsIrreducible.preimage
_of_isPreirreducible_fiber (ht : IsIrreducible t) (f : Y -> X) (hf₂ : IsOpenMap 
f) (hf₃ : forall x, IsPreirreducible (…
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
· 使用定理 `isIrreducible_singleton`：isIrreducible_singleton {x} : IsIrreducible ({x
} : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `AlgebraicGeometry.instSurjectiveOfGeometricallyIrreducible`：∀ {X S : Alg
ebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIrreducible f
],   AlgebraicGeometry.Surjective f
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
-/
lemma Scheme.Hom.isIrreducible_preimage
    [GeometricallyIrreducible f] (hf : IsOpenMap f)
    {s : Set S} (hs : IsIrreducible s) : IsIrreducible (f ⁻¹' s) := by
  wlog H : ∃ x, s = {x} generalizing s
  · refine hs.preimage_of_isPreirreducible_fiber _ hf
      (fun x ↦ (this isIrreducible_singleton ⟨_, rfl⟩).isPreirreducible) ?_
    rw [Set.range_eq_univ.mpr f.surjective, Set.inter_univ]
    exact hs.nonempty
  obtain ⟨s, rfl⟩ := H
  rw [← f.range_fiberι, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.fiberι _).continuous.continuousOn

/-- If `f : X ⟶ S` is geometrically irreducible and open,
then `f` induces an equivalence between the irreducible components of `X` and `S`. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：{X S : AlgebraicGeometry.Scheme} →   (f : X ⟶ S) →     [AlgebraicGeometry.
GeometricallyIrreducible f] →       IsOpenMap ⇑f → ↑(irreducibleComponents ↥X) ≃
 ↑(irreducibleComponents ↥S)
参数：f : X ⟶ S；irreducibleComponents ↥X；irreducibleComponents ↥S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f

--- 原说明 ---
If `f : X ⟶ S` is geometrically irreducible and open,
then `f` induces an equivalence between the irreducible components of `X` and `S
`.
-/
def Scheme.Hom.irreducibleComponentsEquiv [GeometricallyIrreducible f] (hf : IsOpenMap f) :
    irreducibleComponents X ≃ irreducibleComponents S :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous hf
    (fun _ ↦ (f.isIrreducible_preimage hf isIrreducible_singleton).isPreirreducible)
    f.surjective).symm.toEquiv
/-
**AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.GeometricallyIrreducible`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyIrreducible f] [IrreducibleSpace ↥S],   IsOpenMap ⇑f → IrreducibleSpace ↥X
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isIrreducible_preimage`：∀ {X S : AlgebraicG
eometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIrreducible f],   Is
OpenMap ⇑f → ∀ {s : Set ↥S}, IsIrreducibl…
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)
-/
lemma GeometricallyIrreducible.irreducibleSpace
    [GeometricallyIrreducible f] [IrreducibleSpace S] (hf : IsOpenMap f) : IrreducibleSpace X := by
  simpa [irreducibleSpace_def] using
    f.isIrreducible_preimage hf (IrreducibleSpace.isIrreducible_univ _)

/-- If `X` is geometrically irreducible over a point, then it is irreducible. -/
/-
**AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace_of_subsingleton** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIrreducible`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyIrreducible f] [Subsingleton ↥S]   [Nonempty ↥S], IrreducibleSpace ↥X
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace`：∀ {X S : Al
gebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIrreducible 
f] [IrreducibleSpace ↥S],   IsOpenMap ⇑f → Irredu…
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α

--- 原说明 ---
If `X` is geometrically irreducible over a point, then it is irreducible.
-/
lemma GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    [GeometricallyIrreducible f] [Subsingleton S] [Nonempty S] : IrreducibleSpace X :=
  have : IrreducibleSpace S := ⟨‹_›⟩
  GeometricallyIrreducible.irreducibleSpace (f := f) fun _ _ ↦ isOpen_discrete _

/-- If `X` is geometrically irreducible and universally open over `S` and `Y` is irreducible,
then `X ×ₛ Y` is irreducible.

The universally open assumption in particular holds when it is flat and locally of finite
presentation, or when `S` is a field. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is geometrically irreducible and universally open over `S` and `Y` is irr
educible,
then `X ×ₛ Y` is irreducible.

The universally open assumption in particular holds when it is flat and locally 
of finite
presentation, or when `S` is a field.
-/
instance [GeometricallyIrreducible f] [UniversallyOpen f] [IrreducibleSpace Y] :
    IrreducibleSpace ↥(pullback f g) :=
  GeometricallyIrreducible.irreducibleSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyIrreducible g] [UniversallyOpen g] [IrreducibleSpace X] :
    IrreducibleSpace ↥(pullback f g) :=
  GeometricallyIrreducible.irreducibleSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap
/-
**AlgebraicGeometry.GeometricallyIrreducible.iff_geometricallyIrreducible_fiber*
* 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIrreducible`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S),   AlgebraicGeometry.Geomet
ricallyIrreducible f ↔     ∀ (s : ↥S), AlgebraicGeometry.GeometricallyIrreducibl
e (AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField f s)
参数：f : X ⟶ S；s : ↥S；AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgebraicGeometry.GeometricallyIrreducible.eq_geometrically`：@AlgebraicG
eometry.GeometricallyIrreducible = AlgebraicGeometry.geometrically fun x => Irre
ducibleSpace ↥x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma GeometricallyIrreducible.iff_geometricallyIrreducible_fiber :
    GeometricallyIrreducible f ↔ ∀ s, GeometricallyIrreducible (f.fiberToSpecResidueField s) := by
  simp only [GeometricallyIrreducible.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]
/-
**AlgebraicGeometry.GeometricallyIrreducible.comp** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.GeometricallyIrreducible`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeo
metry.GeometricallyIrreducible f]   [AlgebraicGeometry.GeometricallyIrreducible 
g] [AlgebraicGeometry.UniversallyOpen f]   [AlgebraicGeometry.UniversallyOpen g]
,   AlgebraicGeometry.GeometricallyIrreducible (CategoryTheory.CategoryStruct.co
mp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms`：geomet
rically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] : geometr
ically P f ↔ forall (K : Type u) [Field K] (y : Spec (…
· 使用定理 `AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeIrreducibleSpaceCar
rierCarrierCommRingCat`：CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms 
fun x => IrreducibleSpace ↥x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Homeomorph.irreducibleSpace_iff`：Homeomorph.irreducibleSpace_iff (e : X 
≃ₜ Y) : IrreducibleSpace X ↔ IrreducibleSpace Y
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatPullbackS
chemeOfGeometricallyIrreducibleOfUniversallyOpen`：∀ {X Y S : AlgebraicGeometry.S
cheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.GeometricallyIrreducible f]   
[AlgebraicGeometry.Universally…
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsD
omainCarrier`：∀ {R : CommRingCat} [IsDomain ↑R], IrreducibleSpace ↥(AlgebraicGeo
metry.Spec R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma GeometricallyIrreducible.comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIrreducible f] [GeometricallyIrreducible g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyIrreducible (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If an open subscheme `U` of `X` surjects onto `S` and `X` is geometrically irreducible over `S`,
then also `U` is geometrically irreducible over `S`. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an open subscheme `U` of `X` surjects onto `S` and `X` is geometrically irred
ucible over `S`,
then also `U` is geometrically irreducible over `S`.
-/
instance {U : Scheme.{u}} {f : U ⟶ X} {g : X ⟶ S} [IsOpenImmersion f] [GeometricallyIrreducible g]
    [Surjective (f ≫ g)] :
    GeometricallyIrreducible (f ≫ g) := by
  rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber]
  intro s
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  let i : pullback ((f ≫ g).fiberToSpecResidueField s) x ⟶
      pullback (g.fiberToSpecResidueField s) x :=
    pullback.map _ _ _ _ (pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)) (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fiberToSpecResidueField]) (by simp)
  have : Nonempty ((f ≫ g).fiber s) := by
    rw [((f ≫ g).fiberHomeo s).nonempty_congr, Set.nonempty_coe_sort]
    exact (Set.singleton_nonempty s).preimage (f ≫ g).surjective
  exact i.isOpenEmbedding.irreducibleSpace

end AlgebraicGeometry

