/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Geometrically Integral Schemes

## Main results
- `AlgebraicGeometry.GeometricallyIntegral`:
  We say that morphism `f : X ⟶ Y` is geometrically integral if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is integral.
  We also provide the fact that this is stable under base change (`by infer_instance`)
- `GeometricallyIntegral.iff_geometricallyIntegral_fiber`:
  A scheme is geometrically integral over `S` iff the fibers of all
  `s : S` are geometrically integral.
- `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`:
  If `X` is geometrically integral, flat, and universally open (e.g. when over a field),
  over an integral locally noetherian scheme, then `X` is also integral.
- `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_subsingleton`:
  If `X` is geometrically integral over a field, then it is integral.
-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically integral if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is integral. -/
@[mk_iff]
/-
**AlgebraicGeometry.GeometricallyIntegral** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebraic
Geometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that morphism `f : X ⟶ Y` is geometrically integral if for all `Spec K ⟶ 
Y` with `K`
a field, `X ×[Y] Spec K` is integral.
-/
class GeometricallyIntegral (f : X ⟶ Y) : Prop where
  geometrically_isIntegral : geometrically IsIntegral f
/-
**AlgebraicGeometry.GeometricallyIntegral.eq_geometrically** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.GeometricallyIntegral`。
形式化陈述：@AlgebraicGeometry.GeometricallyIntegral = AlgebraicGeometry.geometrically
 AlgebraicGeometry.IsIntegral
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.geometricallyIntegral_iff`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   AlgebraicGeometry.GeometricallyIntegral f ↔ AlgebraicGeom
etry.geometrically AlgebraicGeome…
-/
lemma GeometricallyIntegral.eq_geometrically :
    @GeometricallyIntegral = geometrically IsIntegral := by
  ext; exact geometricallyIntegral_iff _
/-
**AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geometrica
llyIrreducible** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIntegra
l`。
形式化陈述：@AlgebraicGeometry.GeometricallyIntegral =   @AlgebraicGeometry.Geometrica
llyReduced ⊓ @AlgebraicGeometry.GeometricallyIrreducible
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.GeometricallyIntegral.eq_geometrically`：@AlgebraicGeom
etry.GeometricallyIntegral = AlgebraicGeometry.geometrically AlgebraicGeometry.I
sIntegral
· 使用定理 `AlgebraicGeometry.GeometricallyReduced.eq_geometrically`：@AlgebraicGeome
try.GeometricallyReduced = AlgebraicGeometry.geometrically AlgebraicGeometry.IsR
educed
· 使用定理 `AlgebraicGeometry.GeometricallyIrreducible.eq_geometrically`：@AlgebraicG
eometry.GeometricallyIrreducible = AlgebraicGeometry.geometrically fun x => Irre
ducibleSpace ↥x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.geometrically_inf`：geometrically_inf (P Q : ObjectProp
erty Scheme.{u}) : geometrically (P ⊓ Q) = geometrically P ⊓ geometrically Q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible :
    @GeometricallyIntegral =
      (@GeometricallyReduced ⊓ @GeometricallyIrreducible : MorphismProperty Scheme) := by
  rw [eq_geometrically, GeometricallyReduced.eq_geometrically,
    GeometricallyIrreducible.eq_geometrically, ← geometrically_inf]
  eta_expand
  simp [isIntegral_iff_irreducibleSpace_and_isReduced, and_comm]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [GeometricallyIntegral f] : GeometricallyReduced f :=
  (GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.le _ _ _ ‹_›).1
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [GeometricallyIntegral f] : GeometricallyIrreducible f :=
  (GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.le _ _ _ ‹_›).2
/-
**AlgebraicGeometry.GeometricallyIntegral.of_geometricallyReduced_of_geometrical
lyIrreducible** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIntegral
`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyReduced f]   [AlgebraicGeometry.GeometricallyIrreducible f], AlgebraicGeome
try.GeometricallyIntegral f
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geom
etricallyIrreducible`：@AlgebraicGeometry.GeometricallyIntegral =   @AlgebraicGeo
metry.GeometricallyReduced ⊓ @AlgebraicGeometry.GeometricallyIrreducible
-/
lemma GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
    [GeometricallyReduced f] [GeometricallyIrreducible f] :
    GeometricallyIntegral f :=
  GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.ge _ _ _ ⟨‹_›, ‹_›⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @GeometricallyIntegral :=
  GeometricallyIntegral.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyIntegral g] : GeometricallyIntegral (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyIntegral f] : GeometricallyIntegral (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : S.Opens) [GeometricallyIntegral f] : GeometricallyIntegral (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyIntegral f] :
    GeometricallyIntegral (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : S) [GeometricallyIntegral f] : IsIntegral (f.fiber s) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [GeometricallyIntegral f] : Surjective f :=
  ⟨fun x ↦ ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩
/-
**AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIntegral`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyIntegral f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.UniversallyOpen
 f] [AlgebraicGeometry.IsIntegral S] [AlgebraicGeometry.IsLocallyNoetherian S], 
  AlgebraicGeometry.IsIntegral X
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`：isInteg
ral_iff_irreducibleSpace_and_isReduced : IsIntegral X ↔ IrreducibleSpace X ∧ IsR
educed X
· 使用定理 `AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace`：∀ {X S : Al
gebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIrreducible 
f] [IrreducibleSpace ↥S],   IsOpenMap ⇑f → Irredu…
· 使用定理 `AlgebraicGeometry.instGeometricallyIrreducibleOfGeometricallyIntegral`：∀
 {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIn
tegral f],   AlgebraicGeometry.GeometricallyIrreducible f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenMap`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyOpen f], IsOpenMap ⇑f
· 使用定理 `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoe
therian`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Geome
tricallyReduced f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.Is…
· 使用定理 `AlgebraicGeometry.instGeometricallyReducedOfGeometricallyIntegral`：∀ {X 
S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIntegr
al f],   AlgebraicGeometry.GeometricallyReduced f
· 使用定理 `AlgebraicGeometry.isReduced_of_isIntegral`：∀ (X : AlgebraicGeometry.Sche
me) [AlgebraicGeometry.IsIntegral X], AlgebraicGeometry.IsReduced X
-/
lemma GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] [IsLocallyNoetherian S] : IsIntegral X := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

/-- If `X` is geometrically integral over a field, then it is integral. -/
/-
**AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_subsingleton** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIntegral`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometri
callyIntegral f] [Subsingleton ↥S]   [AlgebraicGeometry.IsIntegral S], Algebraic
Geometry.IsIntegral X
参数：f : X ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`：isInteg
ral_iff_irreducibleSpace_and_isReduced : IsIntegral X ↔ IrreducibleSpace X ∧ IsR
educed X
· 使用定理 `AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace_of_subsingle
ton`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.Geometric
allyIrreducible f] [Subsingleton ↥S]   [Nonempty ↥S], Irreducible…
· 使用定理 `AlgebraicGeometry.instGeometricallyIrreducibleOfGeometricallyIntegral`：∀
 {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIn
tegral f],   AlgebraicGeometry.GeometricallyIrreducible f
· 使用定理 `AlgebraicGeometry.IsIntegral.nonempty`：∀ {X : AlgebraicGeometry.Scheme} 
[self : AlgebraicGeometry.IsIntegral X], Nonempty ↥X
· 使用定理 `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoe
therian`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Geome
tricallyReduced f] [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.Is…
· 使用定理 `AlgebraicGeometry.instGeometricallyReducedOfGeometricallyIntegral`：∀ {X 
S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.GeometricallyIntegr
al f],   AlgebraicGeometry.GeometricallyReduced f
· 使用定理 `AlgebraicGeometry.Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIn
tegral`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [Subsingleton ↥Y] [Algebr
aicGeometry.IsIntegral Y],   AlgebraicGeometry.Flat f
· 使用定理 `AlgebraicGeometry.isReduced_of_isIntegral`：∀ (X : AlgebraicGeometry.Sche
me) [AlgebraicGeometry.IsIntegral X], AlgebraicGeometry.IsReduced X
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isLocallyNoetherian`：∀ {X : Algebrai
cGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian X], AlgebraicGeometry
.IsLocallyNoetherian X
· 使用定理 `AlgebraicGeometry.IsArtinianScheme.toIsLocallyArtinian`：∀ {X : Algebraic
Geometry.Scheme} [self : AlgebraicGeometry.IsArtinianScheme X], AlgebraicGeometr
y.IsLocallyArtinian X
· 使用定理 `AlgebraicGeometry.instIsArtinianSchemeOfSubsingletonCarrierCarrierCommRi
ngCatOfIsReduced`：∀ {X : AlgebraicGeometry.Scheme} [Subsingleton ↥X] [AlgebraicG
eometry.IsReduced X], AlgebraicGeometry.IsArtinianScheme X

--- 原说明 ---
If `X` is geometrically integral over a field, then it is integral.
-/
lemma GeometricallyIntegral.isIntegral_of_subsingleton
    [GeometricallyIntegral f] [Subsingleton S] [IsIntegral S] : IsIntegral X := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨GeometricallyIrreducible.irreducibleSpace_of_subsingleton f,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

/-- If `X` is geometrically integral and flat and universally open over `S` and `Y` is integral
and locally noetherian, then `X ×ₛ Y` is integral. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is geometrically integral and flat and universally open over `S` and `Y` 
is integral
and locally noetherian, then `X ×ₛ Y` is integral.
-/
instance [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [IsIntegral Y]
    [IsLocallyNoetherian Y] : IsIntegral (pullback f g) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (pullback f g) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst _ _)
/-
**AlgebraicGeometry.GeometricallyIntegral.iff_geometricallyIntegral_fiber** 是 Ma
thlib 中的一个定理，位于命名空间 `AlgebraicGeometry.GeometricallyIntegral`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S),   AlgebraicGeometry.Geomet
ricallyIntegral f ↔     ∀ (s : ↥S), AlgebraicGeometry.GeometricallyIntegral (Alg
ebraicGeometry.Scheme.Hom.fiberToSpecResidueField f s)
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
· 使用定理 `AlgebraicGeometry.GeometricallyIntegral.eq_geometrically`：@AlgebraicGeom
etry.GeometricallyIntegral = AlgebraicGeometry.geometrically AlgebraicGeometry.I
sIntegral
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma GeometricallyIntegral.iff_geometricallyIntegral_fiber :
    GeometricallyIntegral f ↔ ∀ s, GeometricallyIntegral (f.fiberToSpecResidueField s) := by
  simp only [GeometricallyIntegral.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

end AlgebraicGeometry

