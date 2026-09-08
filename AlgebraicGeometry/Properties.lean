/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Ideal.Height

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `AlgebraicGeometry.IsIntegral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `AlgebraicGeometry.IsReduced`: A scheme is reduced if all the components of the structure sheaf
  are reduced.
-/

public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat Topology

namespace AlgebraicGeometry

variable (X : Scheme)

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T0Space X :=
  T0Space.of_open_cover fun x => ⟨_, X.affineCover.covers x,
    (X.affineCover.f _).opensRange.2, IsEmbedding.t0Space (Y := PrimeSpectrum _)
    (isAffineOpen_opensRange (X.affineCover.f _)).isoSpec.schemeIsoToHomeo.isEmbedding⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiSober X := by
  apply +allowSynthFailures
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.f x))
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.f i).isOpenEmbedding.isOpen_range
  · rintro ⟨_, i, rfl⟩
    exact @IsOpenEmbedding.quasiSober _ _ _ _ _
      (X.affineCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph.symm.isOpenEmbedding
        PrimeSpectrum.quasiSober
  · rw [Set.top_eq_univ, Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x; exact ⟨_, ⟨_, rfl⟩, X.affineCover.covers x⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} : PrespectralSpace X :=
  have (Y : Scheme.{u}) (_ : IsAffine Y) : PrespectralSpace Y :=
    .of_isClosedEmbedding (Y := PrimeSpectrum _) _
      Y.isoSpec.hom.homeomorph.isClosedEmbedding
  have (i : _) : PrespectralSpace (X.affineCover.f i).opensRange.1 :=
    this (X.affineCover.f i).opensRange (isAffineOpen_opensRange (X.affineCover.f i))
  .of_isOpenCover X.affineCover.isOpenCover_opensRange
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IrreducibleSpace ·) :=
  ⟨fun e ↦ e.hom.homeomorph.irreducibleSpace_iff.mp⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (ConnectedSpace ·) :=
  ⟨fun e ↦ e.hom.homeomorph.connectedSpace_iff.mp⟩

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
/-
**AlgebraicGeometry.IsReduced** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsReduced : Prop where component_reduced : forall U, _root_.IsReduced Γ(X,
 U)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced.
-/
class IsReduced : Prop where
  component_reduced : ∀ U, _root_.IsReduced Γ(X, U) := by infer_instance

attribute [instance] IsReduced.component_reduced
/-
**AlgebraicGeometry.isReduced_of_isReduced_stalk** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isReduced_of_isReduced_stalk [forall x : X, _root_.IsReduced (X.presheaf.s
talk x)] : IsReduced X
参数：X.presheaf.stalk x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.section_ext`：section_ext (F : Sheaf C X) (U : Opens X) (
s t : ToType (F.1.obj (op U))) (h : forall (x : X) (hx : x in U), F.presheaf.ger
m U x hx s = F.pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
-/
theorem isReduced_of_isReduced_stalk [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero
/-
**AlgebraicGeometry.isReduced_stalk_of_isReduced** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isReduced_stalk_of_isReduced [IsReduced X] (x : X) : _root_.IsReduced (X.p
resheaf.stalk x)
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `AlgebraicGeometry.IsReduced.component_reduced`：∀ {X : AlgebraicGeometry.
Scheme} [self : AlgebraicGeometry.IsReduced X] (U : X.Opens),   IsReduced ↑(X.pr
esheaf.obj (Opposite.op U))
· 使用定理 `IsNilpotent.mk`：IsNilpotent.mk [Zero R] [Pow R Nat] (x : R) (n : Nat) (e
 : x ^ n = 0) : IsNilpotent x
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
-/
instance isReduced_stalk_of_isReduced [IsReduced X] (x : X) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, (rfl : (X.presheaf.germ U x hxU) s = g)⟩ := X.presheaf.exists_germ_eq g
  rw [← map_pow, ← map_zero (X.presheaf.germ _ x hxU).hom] at e
  obtain ⟨V, hxV, iU, iV, (e' : (X.presheaf.map iU.op) (s ^ n) = (X.presheaf.map iV.op) 0)⟩ :=
    X.presheaf.germ_eq x hxU hxU _ 0 e
  rw [map_pow, map_zero] at e'
  replace e' := (IsNilpotent.mk _ _ e').eq_zero (R := Γ(X, V))
  rw [← X.presheaf.germ_res iU x hxV, CommRingCat.comp_apply, e', map_zero]
/-
**AlgebraicGeometry.isReduced_of_isOpenImmersion** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f
] [IsReduced Y] : IsReduced X
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatAppObjOpensOpensFunctor
`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenIm
mersion f] (U : X.Opens),   CategoryTheory.IsIso (AlgebraicGeo…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `AlgebraicGeometry.IsReduced.component_reduced`：∀ {X : AlgebraicGeometry.
Scheme} [self : AlgebraicGeometry.IsReduced X] (U : X.Opens),   IsReduced ↑(X.pr
esheaf.obj (Opposite.op U))
-/
theorem isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  intro U
  rw [← f.preimage_image_eq U]
  exact isReduced_of_injective (inv <| f.app (f ''ᵁ U)).hom
    (asIso <| f.app (f ''ᵁ U) : Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme} {U : X.Opens} [IsReduced X] : IsReduced U :=
    isReduced_of_isOpenImmersion U.ι
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝒰 : X.OpenCover} [IsReduced X] (i : 𝒰.I₀) : IsReduced (𝒰.X i) :=
  isReduced_of_isOpenImmersion (𝒰.f i)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsReduced ·) :=
  ⟨fun e _ ↦ isReduced_of_isOpenImmersion e.inv⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat.{u}} [H : _root_.IsReduced R] : IsReduced (Spec R) := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  have : _root_.IsReduced (CommRingCat.of <| Localization.AtPrime (PrimeSpectrum.asIdeal x)) := by
    dsimp; infer_instance
  exact isReduced_of_injective (Spec.stalkIso R x).hom.hom
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv.injective
/-
**AlgebraicGeometry.affine_isReduced_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：affine_isReduced_iff (R : CommRingCat) : IsReduced (Spec R) ↔ _root_.IsRed
uced R
参数：R : CommRingCat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `AlgebraicGeometry.IsReduced.component_reduced`：∀ {X : AlgebraicGeometry.
Scheme} [self : AlgebraicGeometry.IsReduced X] (U : X.Opens),   IsReduced ↑(X.pr
esheaf.obj (Opposite.op U))
· 使用定理 `AlgebraicGeometry.instIsReducedSpecOfIsReducedCarrier`：∀ {R : CommRingCa
t} [H : IsReduced ↑R], AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec R)
-/
theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (Spec R) ↔ _root_.IsReduced R := by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective
/-
**AlgebraicGeometry.isReduced_of_isAffine_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：isReduced_of_isAffine_isReduced [IsAffine X] [_root_.IsReduced Γ(X, ⊤)] : 
IsReduced X
参数：X, ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isReduced_of_isOpenImmersion`：isReduced_of_isOpenImmer
sion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsReduced Y] : IsReduced X
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instIsReducedSpecOfIsReducedCarrier`：∀ {R : CommRingCa
t} [H : IsReduced ↑R], AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec R)
-/
theorem isReduced_of_isAffine_isReduced [IsAffine X] [_root_.IsReduced Γ(X, ⊤)] :
    IsReduced X :=
  isReduced_of_isOpenImmersion X.isoSpec.hom
/-
**AlgebraicGeometry.IsReduced.of_openCover** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.IsReduced`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (𝒰 : X.OpenCover) [∀ (i : 𝒰.I₀), Algebrai
cGeometry.IsReduced (𝒰.X i)],   AlgebraicGeometry.IsReduced X
参数：X : AlgebraicGeometry.Scheme；𝒰 : X.OpenCover；i : 𝒰.I₀；𝒰.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `AlgebraicGeometry.isReduced_of_isReduced_stalk`：isReduced_of_isReduced_s
talk [forall x : X, _root_.IsReduced (X.presheaf.stalk x)] : IsReduced X
-/
theorem IsReduced.of_openCover (𝒰 : X.OpenCover) [∀ i, IsReduced (𝒰.X i)] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    exact isReduced_of_injective _
      (asIso <| (𝒰.f i).stalkMap x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _
/-
**AlgebraicGeometry.IsReduced.iff_of_openCover** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.IsReduced`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (𝒰 : X.OpenCover),   AlgebraicGeometry.Is
Reduced X ↔ ∀ (i : 𝒰.I₀), AlgebraicGeometry.IsReduced (𝒰.X i)
参数：X : AlgebraicGeometry.Scheme；𝒰 : X.OpenCover；i : 𝒰.I₀；𝒰.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsReducedXScheme`：∀ (X : AlgebraicGeometry.Scheme)
 {𝒰 : X.OpenCover} [AlgebraicGeometry.IsReduced X] (i : 𝒰.I₀),   AlgebraicGeomet
ry.IsReduced (𝒰.X i)
· 使用定理 `AlgebraicGeometry.IsReduced.of_openCover`：∀ (X : AlgebraicGeometry.Schem
e) (𝒰 : X.OpenCover) [∀ (i : 𝒰.I₀), AlgebraicGeometry.IsReduced (𝒰.X i)],   Alge
braicGeometry.IsReduced X
-/
theorem IsReduced.iff_of_openCover (𝒰 : X.OpenCover) : IsReduced X ↔ ∀ i, IsReduced (𝒰.X i) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ of_openCover X 𝒰⟩

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immersion `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
@[elab_as_elim]
/-
**AlgebraicGeometry.reduce_to_affine_global** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：reduce_to_affine_global (P : forall {X : Scheme} (_ : X.Opens), Prop) {X :
 Scheme} (U : X.Opens) (h₁ : forall (X : Scheme) (U : X.Opens), (forall x : U, e
xists (V : _) (_ : x.1 in V) (_ : V ⟶ U), P V) -> P U) (h₂ : forall (X Y) (f : X
 ⟶ Y) [IsOpenImmersion f], exists (U : X.Opens) (V : Y.Opens), U = ⊤ ∧ V = f.ope
nsRange ∧ (P U -> P V)) (h₃ : forall R : CommRingCat, P (X
参数：P : forall {X : Scheme} (_ : X.Opens), Prop；U : X.Opens；h₁ : forall (X : Sche
me) (U : X.Opens), (forall x : U, exists (V : _) (_ : x.1 in V) (_ : V ⟶ U), P V
) -> P U；h₂ : forall (X Y) (f : X ⟶ Y) [IsOpenImmersion f], exists (U : X.Opens)
 (V : Y.Opens), U = ⊤ ∧ V = f.opensRange ∧ (P U -> P V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.affineBasisCover_is_basis`：affineBasisCover_is_
basis (X : Scheme.{u}) : TopologicalSpace.IsTopologicalBasis {x : Set X | exists
 a : X.affineBasisCover.I₀, x = Set.rang…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
To show that a statement `P` holds for all open subsets of all schemes, it suffi
ces to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for 
`U`.
2. For an open immersion `f : X ⟶ Y`, if `P` holds for the entire space of `X`, 
then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
theorem reduce_to_affine_global (P : ∀ {X : Scheme} (_ : X.Opens), Prop)
    {X : Scheme} (U : X.Opens)
    (h₁ : ∀ (X : Scheme) (U : X.Opens),
      (∀ x : U, ∃ (V : _) (_ : x.1 ∈ V) (_ : V ⟶ U), P V) → P U)
    (h₂ : ∀ (X Y) (f : X ⟶ Y) [IsOpenImmersion f],
      ∃ (U : X.Opens) (V : Y.Opens), U = ⊤ ∧ V = f.opensRange ∧ (P U → P V))
    (h₃ : ∀ R : CommRingCat, P (X := Spec R) ⊤) : P U := by
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.f j).isOpenEmbedding.isOpen_range⟩
  let i' : U' ⟶ U := homOfLE i
  refine ⟨U', hx, i', ?_⟩
  obtain ⟨_, _, rfl, rfl, h₂'⟩ := h₂ _ _ (X.affineBasisCover.f j)
  apply h₂'
  apply h₃
/-
**AlgebraicGeometry.reduce_to_affine_nbhd** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：reduce_to_affine_nbhd (P : forall (X : Scheme) (_ : X), Prop) (h₁ : forall
 R x, P (Spec R) x) (h₂ : forall {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X), 
P X x -> P Y (f x)) : forall (X : Scheme) (x : X), P X x
参数：P : forall (X : Scheme) (_ : X), Prop；h₁ : forall R x, P (Spec R) x；h₂ : fora
ll {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X), P X x -> P Y (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
-/
theorem reduce_to_affine_nbhd (P : ∀ (X : Scheme) (_ : X), Prop)
    (h₁ : ∀ R x, P (Spec R) x)
    (h₂ : ∀ {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X), P X x → P Y (f x)) :
    ∀ (X : Scheme) (x : X), P X x := by
  intro X x
  obtain ⟨y, e⟩ := X.affineCover.covers x
  convert! h₂ (X.affineCover.f (X.affineCover.idx x)) y _
  · rw [e]
  apply h₁

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：eq_zero_of_basicOpen_eq_bot {X : Scheme} [hX : IsReduced X] {U : X.Opens} 
(s : Γ(X, U)) (hs : X.basicOpen s = ⊥) : s = 0
参数：s : Γ(X, U)；hs : X.basicOpen s = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.section_ext`：section_ext (F : Sheaf C X) (U : Opens X) (
s t : ToType (F.1.obj (op U))) (h : forall (x : X) (hx : x in U), F.presheaf.ger
m U x hx s = F.pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.reduce_to_affine_global`：reduce_to_affine_global (P : 
forall {X : Scheme} (_ : X.Opens), Prop) {X : Scheme} (U : X.Opens) (h₁ : forall
 (X : Scheme) (U : X.Opens), (f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_opensRange`：preimage_opensRange {X
 Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : f ⁻¹ᵁ f.opensRange = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.isReduced_of_isOpenImmersion`：isReduced_of_isOpenImmer
sion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsReduced Y] : IsReduced X
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
· 使用定理 `SupBotHomClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Max α] [inst_2 : Max β] [inst_3 : Bot α]  
 [inst_4 : Bot β] …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `FrameHomClass.tosSupHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLat
tice β] [FrameHomC…
· 使用定理 `FrameHom.instFrameHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Comp
leteLattice α] [inst_1 : CompleteLattice β],   FrameHomClass (FrameHom α β) α β
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`：germ_stalkMap_apply (U
 : Y.Opens) (x : X) (hx : f x in U) (y) : f.stalkMap x (Y.presheaf.germ _ (f x) 
hx y) = X.presheaf.germ (f ⁻¹ᵁ U) x hx…
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
（共 36 条，此处仅展示前 30 条）
-/
theorem eq_zero_of_basicOpen_eq_bot {X : Scheme} [hX : IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) (hs : X.basicOpen s = ⊥) : s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  induction U using reduce_to_affine_global generalizing hX with
  | h₁ X U H =>
    obtain ⟨V, hx, i, H⟩ := H ⟨x, hx⟩
    specialize H (X.presheaf.map i.op s)
    rw [Scheme.basicOpen_res, hs] at H
    specialize H (inf_bot_eq _) x hx
    rw [← X.sheaf.presheaf.germ_res_apply i x hx s]
    exact H
  | h₂ X Y f =>
    refine ⟨f ⁻¹ᵁ f.opensRange, f.opensRange, by simp, rfl, ?_⟩
    rintro H hX s hs _ ⟨x, rfl⟩
    have := isReduced_of_isOpenImmersion f
    specialize H (f.app _ s) _ x ⟨x, rfl⟩
    · rw [← Scheme.preimage_basicOpen, hs]; ext1; simp [Opens.map]
    · have H : (X.presheaf.germ _ x _).hom _ = 0 := H
      rw [← Scheme.Hom.germ_stalkMap_apply f ⟨_, _⟩ x] at H
      apply_fun inv <| f.stalkMap x at H
      rw [← CommRingCat.comp_apply, CategoryTheory.IsIso.hom_inv_id, map_zero] at H
      exact H
  | h₃ R =>
    rw [basicOpen_eq_of_affine', PrimeSpectrum.basicOpen_eq_bot_iff] at hs
    replace hs := (hs.map (Scheme.ΓSpecIso R).inv.hom).eq_zero
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hs
    rw [hs, map_zero]

@[simp]
/-
**AlgebraicGeometry.basicOpen_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : X.Opens} (s : Γ(X, U)
) : X.basicOpen s = ⊥ ↔ s = 0
参数：s : Γ(X, U)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot`：eq_zero_of_basicOpen_eq_b
ot {X : Scheme} [hX : IsReduced X] {U : X.Opens} (s : Γ(X, U)) (hs : X.basicOpen
 s = ⊥) : s = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_zero`：basicOpen_zero (U : X.Opens) : 
X.basicOpen (0 : Γ(X, U)) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) : X.basicOpen s = ⊥ ↔ s = 0 := by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X` is reduced and has finitely many irreducible components, then the stalks at the generic
points of the irreducible components are fields. -/
/-
**AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isField_stalk_of_closure_mem_irreducibleComponents (x : X) (hx : closure {
x} in irreducibleComponents X) [IsReduced X] : IsField (X.presheaf.stalk x)
参数：x : X；hx : closure {x} in irreducibleComponents X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.vanishingIdeal_singleton`：vanishingIdeal_singleton (x : Pr
imeSpectrum R) : vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal
· 使用引理 `PrimeSpectrum.vanishingIdeal_mem_minimalPrimes`：vanishingIdeal_mem_minim
alPrimes {s : Set (PrimeSpectrum R)} : vanishingIdeal s in minimalPrimes R ↔ clo
sure s in irreducibleComponents (Pri…
· 使用引理 `PrimeSpectrum.subsingleton_iff_isField_of_isReduced`：PrimeSpectrum.subsi
ngleton_iff_isField_of_isReduced {R : Type*} [CommRing R] [IsReduced R] [Nontriv
ial R] : Subsingleton (PrimeSpectrum R) ↔…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用引理 `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`：IsLocali
zation.subsingleton_primeSpectrum_of_mem_minimalPrimes {R : Type*} [CommSemiring
 R] (p : Ideal R) (hp : p in minimalPrimes R) (S : T…
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.isReduced_of_isOpenImmersion`：isReduced_of_isOpenImmer
sion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsReduced Y] : IsReduced X
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `Topology.IsEmbedding.closure_eq_preimage_closure_image`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsEmbedding f → ∀ (s : Set…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `preimage_mem_irreducibleComponents`：preimage_mem_irreducibleComponents (
ht : t in irreducibleComponents X) {f : Y -> X} (hf : IsOpenEmbedding f) (h : (t
 inter Set.range f).None…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…

--- 原说明 ---
If `X` is reduced and has finitely many irreducible components, then the stalks 
at the generic
points of the irreducible components are fields.
-/
lemma isField_stalk_of_closure_mem_irreducibleComponents
    (x : X) (hx : closure {x} ∈ irreducibleComponents X) [IsReduced X] :
    IsField (X.presheaf.stalk x) := by
  wlog hX : ∃ R, X = Spec R
  · obtain ⟨i, x, rfl⟩ := X.affineCover.exists_eq x
    have inst : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
    refine (asIso <| (X.affineCover.f i).stalkMap x).commRingCatIsoToRingEquiv.isField
      (this _ x ?_ ⟨_, rfl⟩)
    rw [(X.affineCover.f i).isOpenEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hx (X.affineCover.f i).isOpenEmbedding
      ⟨X.affineCover.f i x, subset_closure rfl, _, rfl⟩
  obtain ⟨R, rfl⟩ := hX
  replace hx : x.asIdeal ∈ minimalPrimes R := by
    rwa [← PrimeSpectrum.vanishingIdeal_singleton, PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  rw [← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
  exact IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes _ hx
    ((Spec.structureSheaf R).presheaf.stalk x)

/-- A scheme `X` is integral if its is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
/-
**AlgebraicGeometry.IsIntegral** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsIntegral : Prop where nonempty : Nonempty X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is integral if its is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`.
-/
class IsIntegral : Prop where
  nonempty : Nonempty X := by infer_instance
  component_integral : ∀ (U : X.Opens) [Nonempty U], IsDomain Γ(X, U) := by infer_instance

attribute [instance] IsIntegral.component_integral IsIntegral.nonempty
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegral X] : IsDomain Γ(X, ⊤) :=
  @IsIntegral.component_integral _ _ _ ⟨Nonempty.some inferInstance, trivial⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) isReduced_of_isIntegral [IsIntegral X] : IsReduced X := by
  constructor
  intro U
  rcases U.1.eq_empty_or_nonempty with h | h
  · have : U = ⊥ := SetLike.ext' h
    have : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty this)
    infer_instance
  · have : Nonempty U := by simpa
    infer_instance
/-
**AlgebraicGeometry.Scheme.component_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (U : X.Opens) [Nonempty ↥↑U], Nontrivial 
↑(X.presheaf.obj (Opposite.op U))
参数：X : AlgebraicGeometry.Scheme；U : X.Opens；X.presheaf.obj (Opposite.op U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Scheme.component_nontrivial (X : Scheme.{u}) (U : X.Opens) [Nonempty U] :
    Nontrivial Γ(X, U) :=
  LocallyRingedSpace.component_nontrivial (hU := ‹_›)
/-
**AlgebraicGeometry.irreducibleSpace_of_isIntegral** 是 Mathlib 中的一个实例，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：irreducibleSpace_of_isIntegral [IsIntegral X] : IrreducibleSpace X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `AlgebraicGeometry.IsIntegral.nonempty`：∀ {X : AlgebraicGeometry.Scheme} 
[self : AlgebraicGeometry.IsIntegral X], Nonempty ↥X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Set.not_univ_subset`：not_univ_subset : ¬univ subseteq s ↔ exists a, a ∉ 
s
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `AlgebraicGeometry.IsIntegral.component_integral`：∀ {X : AlgebraicGeometr
y.Scheme} [self : AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty ↥↑U], 
  IsDomain ↑(X.presheaf.obj (Opposite…
· 使用定理 `false_of_nontrivial_of_product_domain`：false_of_nontrivial_of_product_do
main (R S : Type*) [Semiring R] [Semiring S] [IsDomain (R × S)] [Nontrivial R] [
Nontrivial S] : False
· 使用定理 `AlgebraicGeometry.Scheme.component_nontrivial`：∀ (X : AlgebraicGeometry.
Scheme) (U : X.Opens) [Nonempty ↥↑U], Nontrivial ↑(X.presheaf.obj (Opposite.op U
))
-/
instance irreducibleSpace_of_isIntegral [IsIntegral X] : IrreducibleSpace X := by
  by_contra H
  replace H : ¬IsPreirreducible .univ := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  rw [Set.not_univ_subset] at h₂ h₃
  have : Nonempty (⟨Sᶜ, hS.1⟩ : X.Opens) := ⟨⟨_, h₂.choose_spec⟩⟩
  have : Nonempty (⟨Tᶜ, hT.1⟩ : X.Opens) := ⟨⟨_, h₃.choose_spec⟩⟩
  have : Nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : X.Opens) := ⟨⟨_, Or.inl h₂.choose_spec⟩⟩
  let e : Γ(X, _) ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ ?_).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  · have : IsDomain (Γ(X, ⟨Sᶜ, hS.1⟩) × Γ(X, ⟨Tᶜ, hT.1⟩)) :=
      e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    exact false_of_nontrivial_of_product_domain Γ(X, ⟨Sᶜ, hS.1⟩) Γ(X, ⟨Tᶜ, hT.1⟩)
  · ext x
    constructor
    · rintro ⟨hS, hT⟩
      rcases h₁ (show x ∈ ⊤ by trivial) with h | h
      exacts [hS h, hT h]
    · simp
/-
**AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIntegral_of_irreducibleSpace_of_isReduced [IsReduced X] [H : Irreducible
Space X] : IsIntegral X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `nonempty_preirreducible_inter`：nonempty_preirreducible_inter [Preirreduc
ibleSpace X] : IsOpen s -> IsOpen t -> s.Nonempty -> t.Nonempty -> (s inter t).N
onempty
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_zero_iff`：isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `AlgebraicGeometry.Scheme.component_nontrivial`：∀ (X : AlgebraicGeometry.
Scheme) (U : X.Opens) [Nonempty ↥↑U], Nontrivial ↑(X.presheaf.obj (Opposite.op U
))
-/
theorem isIntegral_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X] :
    IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  have := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine ⟨fun {a b} e => ?_⟩
    simp_rw [← basicOpen_eq_bot_iff, ← Opens.not_nonempty_iff_eq_bot]
    by_contra! h
    obtain ⟨x, ⟨hxU, hx₁⟩, _, hx₂⟩ :=
      nonempty_preirreducible_inter (X.basicOpen a).2 (X.basicOpen b).2 h.1 h.2
    replace e := congr_arg (X.presheaf.germ U x hxU) e
    rw [map_mul, map_zero] at e
    refine zero_ne_one' (X.presheaf.stalk x) (isUnit_zero_iff.1 ?_)
    convert! hx₁.mul hx₂
    exact e.symm
  exact NoZeroDivisors.to_isDomain _
/-
**AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIntegral_iff_irreducibleSpace_and_isReduced : IsIntegral X ↔ Irreducible
Space X ∧ IsReduced X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isReduced_of_isIntegral`：∀ (X : AlgebraicGeometry.Sche
me) [AlgebraicGeometry.IsIntegral X], AlgebraicGeometry.IsReduced X
· 使用定理 `AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`：isIntegra
l_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X] : IsIn
tegral X
-/
theorem isIntegral_iff_irreducibleSpace_and_isReduced :
    IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩
/-
**AlgebraicGeometry.isIntegral_of_isOpenImmersion** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：isIntegral_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion 
f] [IsIntegral Y] [Nonempty X] : IsIntegral X
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.IsIntegral.component_integral`：∀ {X : AlgebraicGeometr
y.Scheme} [self : AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty ↥↑U], 
  IsDomain ↑(X.presheaf.obj (Opposite…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatAppObjOpensOpensFunctor
`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenIm
mersion f] (U : X.Opens),   CategoryTheory.IsIso (AlgebraicGeo…
-/
theorem isIntegral_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsIntegral Y] [Nonempty X] : IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  rw [← f.preimage_image_eq U]
  have : IsDomain Γ(Y, f ''ᵁ U) := by
    apply +allowSynthFailures IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.app (f ''ᵁ U) :
    Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
/-
**AlgebraicGeometry.IsIntegral.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.IsIntegral`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [h : AlgebraicGeometry.IsIntegral X] (f
 : X ⟶ Y) [CategoryTheory.IsIso f],   AlgebraicGeometry.IsIntegral Y
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `AlgebraicGeometry.IsIntegral.nonempty`：∀ {X : AlgebraicGeometry.Scheme} 
[self : AlgebraicGeometry.IsIntegral X], Nonempty ↥X
· 使用定理 `AlgebraicGeometry.isIntegral_of_isOpenImmersion`：isIntegral_of_isOpenImm
ersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsIntegral Y] [Nonempty X
] : IsIntegral X
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
-/
lemma IsIntegral.of_isIso {X Y : Scheme.{u}} [h : IsIntegral X] (f : X ⟶ Y) [IsIso f] :
    IsIntegral Y := by
  suffices Nonempty Y from isIntegral_of_isOpenImmersion (inv f)
  exact Nonempty.map f inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} [IsDomain R] : IrreducibleSpace (Spec R) := by
  convert! PrimeSpectrum.irreducibleSpace (R := R)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} [IsDomain R] : IsIntegral (Spec R) :=
  isIntegral_of_irreducibleSpace_of_isReduced _
/-
**AlgebraicGeometry.affine_isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：affine_isIntegral_iff (R : CommRingCat) : IsIntegral (Spec R) ↔ IsDomain R
参数：R : CommRingCat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierObjOppositeOpensCarrierCarrierCommR
ingCatPresheafOpOpensTopOfIsIntegral`：∀ (X : AlgebraicGeometry.Scheme) [Algebrai
cGeometry.IsIntegral X], IsDomain ↑(X.presheaf.obj (Opposite.op ⊤))
· 使用定理 `AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier`：∀ {R : CommRingCa
t} [IsDomain ↑R], AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec R)
-/
theorem affine_isIntegral_iff (R : CommRingCat) :
    IsIntegral (Spec R) ↔ IsDomain R :=
  ⟨fun _ => MulEquiv.isDomain Γ(Spec R, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩
/-
**AlgebraicGeometry.isIntegral_of_isAffine_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：isIntegral_of_isAffine_of_isDomain [IsAffine X] [Nonempty X] [IsDomain Γ(X
, ⊤)] : IsIntegral X
参数：X, ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isIntegral_of_isOpenImmersion`：isIntegral_of_isOpenImm
ersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsIntegral Y] [Nonempty X
] : IsIntegral X
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier`：∀ {R : CommRingCa
t} [IsDomain ↑R], AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec R)
-/
theorem isIntegral_of_isAffine_of_isDomain [IsAffine X] [Nonempty X] [IsDomain Γ(X, ⊤)] :
    IsIntegral X :=
  isIntegral_of_isOpenImmersion X.isoSpec.hom
/-
**AlgebraicGeometry.map_injective_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：map_injective_of_isIntegral [IsIntegral X] {U V : X.Opens} (i : U ⟶ V) [H 
: Nonempty U] : Function.Injective (X.presheaf.map i.op)
参数：i : U ⟶ V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.basicOpen_eq_bot_iff`：basicOpen_eq_bot_iff {X : Scheme
} [IsReduced X] {U : X.Opens} (s : Γ(X, U)) : X.basicOpen s = ⊥ ↔ s = 0
· 使用定理 `AlgebraicGeometry.isReduced_of_isIntegral`：∀ (X : AlgebraicGeometry.Sche
me) [AlgebraicGeometry.IsIntegral X], AlgebraicGeometry.IsReduced X
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nonempty_preirreducible_inter`：nonempty_preirreducible_inter [Preirreduc
ibleSpace X] : IsOpen s -> IsOpen t -> s.Nonempty -> t.Nonempty -> (s inter t).N
onempty
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
-/
theorem map_injective_of_isIntegral [IsIntegral X] {U V : X.Opens} (i : U ⟶ V)
    [H : Nonempty U] : Function.Injective (X.presheaf.map i.op) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← basicOpen_eq_bot_iff] at hx ⊢
  rw [Scheme.basicOpen_res] at hx
  revert hx
  contrapose!
  simp_rw [Ne, ← Opens.not_nonempty_iff_eq_bot, Classical.not_not]
  apply nonempty_preirreducible_inter U.isOpen (RingedSpace.basicOpen _ _).isOpen
  simpa using H

noncomputable
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegral X] : OrderTop X where
  top := genericPoint X
  le_top a := genericPoint_specializes a

open IrreducibleCloseds Set in
@[stacks 02I4]
/-
**AlgebraicGeometry.coheight_eq_of_isOpenImmersion** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：coheight_eq_of_isOpenImmersion {U X : Scheme} {x : U} (f : U ⟶ X) [IsOpenI
mmersion f] : Order.coheight (f.base x) = Order.coheight x
参数：f : U ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsOpenEmbedding.coheight_eq`：Topology.IsOpenEmbedding.coheight_
eq [QuasiSober Y] [T0Space Y] [QuasiSober X] [T0Space X] {x : X} (f : X -> Y) (h
f : IsOpenEmbedding f) : c…
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `AlgebraicGeometry.instT0SpaceCarrierCarrierCommRingCat`：∀ (X : Algebraic
Geometry.Scheme), T0Space ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
-/
lemma coheight_eq_of_isOpenImmersion {U X : Scheme} {x : U} (f : U ⟶ X) [IsOpenImmersion f] :
    Order.coheight (f.base x) = Order.coheight x := f.isOpenEmbedding.coheight_eq

set_option backward.isDefEq.respectTransparency.types false in
open Order in
/-
**AlgebraicGeometry.idealHeight_eq_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：idealHeight_eq_coheight (R : CommRingCat) (x : Spec R) : x.asIdeal.height 
= coheight x
参数：R : CommRingCat；x : Spec R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.height_eq_orderHeight`：PrimeSpectrum.height_eq_orderHeight
 (p : PrimeSpectrum R) : p.asIdeal.height = Order.height p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coheight_orderIso`：coheight_orderIso (f : α ≃o β) (x : α) : coheig
ht (f x) = coheight x
· 使用定理 `Order.height_ofDual`：∀ {α : Type u_1} [inst : Preorder α] (x : αᵒᵈ), Ord
er.height (OrderDual.ofDual x) = Order.coheight x
· 使用定理 `AlgebraicGeometry.specOrderIsoPrimeSpectrum_apply`：∀ (R : CommRingCat) (
x : ↥(AlgebraicGeometry.Spec R)),   (AlgebraicGeometry.specOrderIsoPrimeSpectrum
 R) x = OrderDual.toDual x
· 使用定理 `OrderDual.ofDual_toDual`：∀ {α : Type u_1} (a : α), OrderDual.ofDual (Ord
erDual.toDual a) = a
-/
lemma idealHeight_eq_coheight (R : CommRingCat) (x : Spec R) :
    x.asIdeal.height = coheight x := by
  rw [PrimeSpectrum.height_eq_orderHeight,
    ← Order.coheight_orderIso (specOrderIsoPrimeSpectrum R), ← height_ofDual,
    specOrderIsoPrimeSpectrum_apply, OrderDual.ofDual_toDual]

set_option backward.isDefEq.respectTransparency.types false in
open Order in
@[stacks 02IZ]
/-
**AlgebraicGeometry.ringKrullDim_stalk_eq_coheight** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：ringKrullDim_stalk_eq_coheight {X : Scheme} (x : X) : ringKrullDim (X.pres
heaf.stalk x) = coheight x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.ringKrullDim_eq_height`：IsLocalization.AtPrime.ri
ngKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*) [CommRing A] [Algebra
 R A] [IsLocalization.AtPrime A I] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用引理 `AlgebraicGeometry.idealHeight_eq_coheight`：idealHeight_eq_coheight (R : 
CommRingCat) (x : Spec R) : x.asIdeal.height = coheight x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset`：exist
s_affine_mem_range_and_range_subset {X : Scheme.{u}} {x : X} {U : X.Opens} (hxU 
: x in U) : exists R, exists (f : Spec R ⟶ X), IsOpenIm…
· 使用定理 `trivial`：True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `AlgebraicGeometry.coheight_eq_of_isOpenImmersion`：coheight_eq_of_isOpenI
mmersion {U X : Scheme} {x : U} (f : U ⟶ X) [IsOpenImmersion f] : Order.coheight
 (f.base x) = Order.coheight x
· 使用引理 `Order.krullDim_eq_of_orderIso`：krullDim_eq_of_orderIso (f : α ≃o β) : kr
ullDim α = krullDim β
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
-/
lemma ringKrullDim_stalk_eq_coheight {X : Scheme} (x : X) :
    ringKrullDim (X.presheaf.stalk x) = coheight x := by
  wlog h : ∃ R, X = Spec R
  · obtain ⟨R, f, hf, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (show x ∈ ⊤ from trivial)
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hsub.1
    rw [coheight_eq_of_isOpenImmersion, ← this _ ⟨R, rfl⟩]
    exact Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.comapEquiv (asIso (Scheme.Hom.stalkMap f y)).commRingCatIsoToRingEquiv)
  obtain ⟨R, rfl⟩ := h
  let k : Algebra ↑R ↑((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra (↑R) x
  have : IsLocalization.AtPrime (↑((Spec R).presheaf.stalk x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal ((Spec R).presheaf.stalk x)]
  apply WithBot.coe_eq_coe.mpr
  exact idealHeight_eq_coheight R x

open Order in
variable {X} in
/-
**AlgebraicGeometry.krullDimLE_of_coheight_le** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：krullDimLE_of_coheight_le {z : X} {n : Nat} (hz : coheight z <= n) : Ring.
KrullDimLE n (X.presheaf.stalk z)
参数：hz : coheight z <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.krullDimLE_iff`：Ring.krullDimLE_iff {n : Nat} : KrullDimLE n R ↔ ri
ngKrullDim R <= n
· 使用引理 `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`：ringKrullDim_stalk_eq_
coheight {X : Scheme} (x : X) : ringKrullDim (X.presheaf.stalk x) = coheight x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma krullDimLE_of_coheight_le
    {z : X} {n : ℕ} (hz : coheight z ≤ n) : Ring.KrullDimLE n (X.presheaf.stalk z) := by
  rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight z]
  exact_mod_cast hz
/-
**AlgebraicGeometry.isField_of_isIntegral_of_subsingleton** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：isField_of_isIntegral_of_subsingleton (X : Scheme.{u}) [IsIntegral X] [Sub
singleton X] : IsField Γ(X, ⊤)
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.t1Space_iff_isField`：t1Space_iff_isField [IsDomain R] : T1
Space (PrimeSpectrum R) ↔ IsField R
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierObjOppositeOpensCarrierCarrierCommR
ingCatPresheafOpOpensTopOfIsIntegral`：∀ (X : AlgebraicGeometry.Scheme) [Algebrai
cGeometry.IsIntegral X], IsDomain ↑(X.presheaf.obj (Opposite.op ⊤))
· 使用定理 `Homeomorph.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y),   T1Space Y
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCo
mmRingCat`：∀ {X : AlgebraicGeometry.Scheme} [Finite ↥X] [DiscreteTopology ↥X], A
lgebraicGeometry.IsAffine X
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isField_of_isIntegral_of_subsingleton (X : Scheme.{u}) [IsIntegral X] [Subsingleton X] :
    IsField Γ(X, ⊤) := by
  rw [← PrimeSpectrum.t1Space_iff_isField]
  apply X.isoSpec.hom.homeomorph.t1Space

end AlgebraicGeometry

