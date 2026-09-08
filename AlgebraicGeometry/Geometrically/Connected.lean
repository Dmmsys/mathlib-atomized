/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten,
  Yannis Monbru, Alireza Shavali, Chenyi Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically connected schemes

In this file we define geometrically connected morphisms of schemes. A morphism `f : X ⟶ Y` is
geometrically connected if for all `Spec K ⟶ Y` with `K` a field, `X ×[Y] Spec K` is connected.
In the case where `Y = Spec K` for some field `K` this recovers the standard definition
of a geometrically connected scheme over a field.

## Main results

- `AlgebraicGeometry.GeometricallyConnected`: A morphism `f : X ⟶ Y` is geometrically connected if
  for all `Spec K ⟶ Y` with `K` a field, `X ×[Y] Spec K` is connected.
- `GeometricallyConnected.iff_geometricallyConnected_fiber`: A scheme is geometrically connected
  over `S` iff the fibers of all `s : S` are geometrically connected.

-/

@[expose] public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that a morphism `f : X ⟶ Y` is geometrically connected if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is connected. -/
@[mk_iff]
/-
**AlgebraicGeometry.GeometricallyConnected** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a morphism `f : X ⟶ Y` is geometrically connected if for all `Spec K
 ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is connected.
-/
class GeometricallyConnected (f : X ⟶ Y) : Prop where
  geometrically_connectedSpace : geometrically (ConnectedSpace ·) f
/-
**AlgebraicGeometry.GeometricallyConnected.eq_geometrically** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.GeometricallyConnected`。
形式化陈述：@AlgebraicGeometry.GeometricallyConnected = AlgebraicGeometry.geometricall
y fun x => ConnectedSpace ↥x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.geometricallyConnected_iff`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.GeometricallyConnected f ↔ AlgebraicGe
ometry.geometrically (fun x => Con…
-/
lemma GeometricallyConnected.eq_geometrically :
    @GeometricallyConnected = geometrically (ConnectedSpace ·) := by
  ext; exact geometricallyConnected_iff _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyConnected g] : GeometricallyConnected (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyConnected f] : GeometricallyConnected (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : S.Opens) [GeometricallyConnected f] : GeometricallyConnected (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyConnected f] :
    GeometricallyConnected (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyConnected f] : ConnectedSpace (f.fiber s) :=
  GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [GeometricallyConnected f] : Surjective f :=
  ⟨fun x ↦ ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩
/-
**AlgebraicGeometry.Scheme.Hom.isConnected_preimage_singleton** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyConnected f] (x : ↥S),   IsConnected (⇑f ⁻¹' {x})
参数：f : X ⟶ S；x : ↥S；⇑f ⁻¹' {x}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_fiberι`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) (y : ↥Y),   Set.range ⇑(AlgebraicGeometry.Scheme.Hom.fiberι f 
y) = ⇑f ⁻¹' {y}
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)
· 使用定理 `AlgebraicGeometry.instConnectedSpaceCarrierCarrierCommRingCatFiberOfGeom
etricallyConnected`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (s : ↥S) [Alg
ebraicGeometry.GeometricallyConnected f],   ConnectedSpace ↥(AlgebraicGeometry.S
…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
lemma Scheme.Hom.isConnected_preimage_singleton [GeometricallyConnected f] (x : S) :
    _root_.IsConnected (f ⁻¹' {x}) := by
  rw [← f.range_fiberι, ← Set.image_univ]
  exact isConnected_univ.image _ (f.fiberι _).continuous.continuousOn
/-
**AlgebraicGeometry.Scheme.Hom.isConnected_preimage** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyConnected f],   IsOpenMap ⇑f → ∀ {s : Set ↥S}, IsConnected s → IsClosed s →
 IsConnected (⇑f ⁻¹' s)
参数：f : X ⟶ S；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.isConnected_preimage_of_isClosed`：Topology.IsCoind
ucing.isConnected_preimage_of_isClosed (connected_fibers : forall t : β, IsConne
cted (f ⁻¹' {t})) (hcl : IsCoinducing f) {t …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isConnected_preimage_singleton`：∀ {X S : Al
gebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyConnected f]
 (x : ↥S),   IsConnected (⇑f ⁻¹' {x})
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `AlgebraicGeometry.instSurjectiveOfGeometricallyConnected`：∀ {X S : Algeb
raicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyConnected f],  
 AlgebraicGeometry.Surjective f
-/
lemma Scheme.Hom.isConnected_preimage [GeometricallyConnected f] (hf : IsOpenMap f)
    {s : Set S} (hs : _root_.IsConnected s) (hs' : IsClosed s) : _root_.IsConnected (f ⁻¹' s) := by
  refine Topology.IsCoinducing.isConnected_preimage_of_isClosed f.isConnected_preimage_singleton
    ?_ hs' hs
  exact (hf.isQuotientMap f.continuous f.surjective).isCoinducing

/-- If `f : X ⟶ S` is geometrically connected and open,
then `f` induces a homeomorphism between the connected components of `X` and `S`. -/
@[simps! apply]
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.connectedComponentsHomeomorph** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：{X S : AlgebraicGeometry.Scheme} →   (f : X ⟶ S) →     [AlgebraicGeometry.
GeometricallyConnected f] → IsOpenMap ⇑f → ConnectedComponents ↥X ≃ₜ ConnectedCo
mponents ↥S
参数：f : X ⟶ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isConnected_preimage_singleton`：∀ {X S : Al
gebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyConnected f]
 (x : ↥S),   IsConnected (⇑f ⁻¹' {x})
-/
def Scheme.Hom.connectedComponentsHomeomorph [GeometricallyConnected f] (hf : IsOpenMap f) :
    ConnectedComponents X ≃ₜ ConnectedComponents S :=
  (hf.isQuotientMap f.continuous f.surjective).isCoinducing.connectedComponentsHomeomorph
    f.isConnected_preimage_singleton
/-
**AlgebraicGeometry.GeometricallyConnected.connectedSpace** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.GeometricallyConnected`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyConnected f] [ConnectedSpace ↥S],   IsOpenMap ⇑f → ConnectedSpace ↥X
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isConnected_preimage`：∀ {X S : AlgebraicGeo
metry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyConnected f],   IsOpen
Map ⇑f → ∀ {s : Set ↥S}, IsConnected s …
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)
-/
lemma GeometricallyConnected.connectedSpace [GeometricallyConnected f] [ConnectedSpace S]
    (hf : IsOpenMap f) :
    ConnectedSpace X := by
  simpa [connectedSpace_iff_univ] using f.isConnected_preimage hf isConnected_univ

/-- If `X` is geometrically connected over a point, then it is connected. -/
/-
**AlgebraicGeometry.GeometricallyConnected.connectedSpace_of_subsingleton** 是 Ma
thlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyConnected`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyConnected f] [Subsingleton ↥S]   [Nonempty ↥S], ConnectedSpace ↥X
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreirreducibleSpace.preconnectedSpace`：∀ (α : Type u) [inst : Topologica
lSpace α] [PreirreducibleSpace α], PreconnectedSpace α
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `AlgebraicGeometry.GeometricallyConnected.connectedSpace`：∀ {X S : Algebr
aicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyConnected f] [Co
nnectedSpace ↥S],   IsOpenMap ⇑f → ConnectedS…
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α

--- 原说明 ---
If `X` is geometrically connected over a point, then it is connected.
-/
lemma GeometricallyConnected.connectedSpace_of_subsingleton
    [GeometricallyConnected f] [Subsingleton S] [Nonempty S] : ConnectedSpace X :=
  have : ConnectedSpace S := ⟨‹_›⟩
  GeometricallyConnected.connectedSpace (f := f) fun _ _ ↦ isOpen_discrete _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) :=
  GeometricallyConnected.connectedSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyConnected g] [UniversallyOpen g] [ConnectedSpace X] :
    ConnectedSpace ↥(pullback f g) :=
  GeometricallyConnected.connectedSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap
/-
**AlgebraicGeometry.GeometricallyConnected.iff_geometricallyConnected_fiber** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyConnected`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S),   AlgebraicGeometry.Geomet
ricallyConnected f ↔     ∀ (s : ↥S), AlgebraicGeometry.GeometricallyConnected (A
lgebraicGeometry.Scheme.Hom.fiberToSpecResidueField f s)
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
· 使用定理 `AlgebraicGeometry.GeometricallyConnected.eq_geometrically`：@AlgebraicGeo
metry.GeometricallyConnected = AlgebraicGeometry.geometrically fun x => Connecte
dSpace ↥x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma GeometricallyConnected.iff_geometricallyConnected_fiber :
    GeometricallyConnected f ↔ ∀ s, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  simp only [eq_geometrically, ← geometrically_iff_forall_fiberToSpecResidueField]
/-
**AlgebraicGeometry.GeometricallyConnected.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.GeometricallyConnected`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeo
metry.GeometricallyConnected f]   [AlgebraicGeometry.GeometricallyConnected g] [
AlgebraicGeometry.UniversallyOpen f]   [AlgebraicGeometry.UniversallyOpen g],   
AlgebraicGeometry.GeometricallyConnected (CategoryTheory.CategoryStruct.comp f g
)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms`：geomet
rically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] : geometr
ically P f ↔ forall (K : Type u) [Field K] (y : Spec (…
· 使用定理 `AlgebraicGeometry.instIsClosedUnderIsomorphismsSchemeConnectedSpaceCarri
erCarrierCommRingCat`：CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms fu
n x => ConnectedSpace ↥x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Homeomorph.connectedSpace_iff`：Homeomorph.connectedSpace_iff [Topologica
lSpace β] (e : α ≃ₜ β) : ConnectedSpace α ↔ ConnectedSpace β
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instConnectedSpaceCarrierCarrierCommRingCatPullbackSch
emeOfGeometricallyConnectedOfUniversallyOpen`：∀ {X Y S : AlgebraicGeometry.Schem
e} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.GeometricallyConnected f]   [Algeb
raicGeometry.UniversallyOp…
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsD
omainCarrier`：∀ {R : CommRingCat} [IsDomain ↑R], IrreducibleSpace ↥(AlgebraicGeo
metry.Spec R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma GeometricallyConnected.comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected f] [GeometricallyConnected g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  infer_instance

end AlgebraicGeometry

