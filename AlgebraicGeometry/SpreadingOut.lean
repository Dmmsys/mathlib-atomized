/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Spreading out morphisms

Under certain conditions, a morphism on stalks `Spec 𝒪_{X, x} ⟶ Spec 𝒪_{Y, y}` can be spread
out into a neighborhood of `x`.

## Main result
Given `S`-schemes `X Y` and points `x : X` `y : Y` over `s : S`.
Suppose we have the following diagram of `S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
We would like to spread `Spec(φ)` out to an `S`-morphism on an open subscheme `U ⊆ X`
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    |             |
  Spec(φ)         |
    ↓             ↓
Spec 𝒪_{Y, y} ⟶ Y
```
- `AlgebraicGeometry.spread_out_unique_of_isGermInjective`:
  The lift is "unique" if the germ map is injective at `x`.
- `AlgebraicGeometry.spread_out_of_isGermInjective`:
  The lift exists if `Y` is locally of finite type and the germ map is injective at `x`.

## TODO

Show that certain morphism properties can also be spread out.

-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) {R A : CommRingCat.{u}}

/-- The germ map at `x` is injective if there exists some affine `U ∋ x`
  such that the map `Γ(X, U) ⟶ X_x` is injective -/
/-
**AlgebraicGeometry.Scheme.IsGermInjectiveAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → ↥X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The germ map at `x` is injective if there exists some affine `U ∋ x`
  such that the map `Γ(X, U) ⟶ X_x` is injective
-/
class Scheme.IsGermInjectiveAt (X : Scheme.{u}) (x : X) : Prop where
  cond : ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx)
/-
**AlgebraicGeometry.injective_germ_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：injective_germ_basicOpen (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx :
 x in U) (f : Γ(X, U)) (hf : x in X.basicOpen f) (H : Function.Injective (X.pres
heaf.germ U x hx)) : Function.Injective (X.presheaf.germ (X.basicOpen f) x hf)
参数：U : X.Opens；hU : IsAffineOpen U；x : X；hx : x in U；f : Γ(X, U)；hf : x in X.bas
icOpen f；H : Function.Injective (X.presheaf.germ U x hx)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `RingHom.ker_eq_bot_iff_eq_zero`：ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ for
all x, f x = 0 -> x = 0
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Ideal.mul_unit_mem_iff_mem`：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit 
y) : x * y in I ↔ x in I
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
lemma injective_germ_basicOpen (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (f : Γ(X, U))
    (hf : x ∈ X.basicOpen f)
    (H : Function.Injective (X.presheaf.germ U x hx)) :
    Function.Injective (X.presheaf.germ (X.basicOpen f) x hf) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at H ⊢
  intro t ht
  have := hU.isLocalization_basicOpen f
  obtain ⟨t, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) t
  rw [← RingHom.mem_ker, IsLocalization.mk'_eq_mul_mk'_one, Ideal.mul_unit_mem_iff_mem,
    RingHom.mem_ker, RingHom.algebraMap_toAlgebra, TopCat.Presheaf.germ_res_apply] at ht
  swap; · exact @isUnit_of_invertible _ _ _ (@IsLocalization.invertible_mk'_one ..)
  rw [H _ ht, IsLocalization.mk'_zero]
/-
**AlgebraicGeometry.Scheme.exists_germ_injective** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (x : ↥X) [X.IsGermInjectiveAt x],   ∃ U, 
    ∃ (hx : x ∈ U),       AlgebraicGeometry.IsAffineOpen U ∧         Function.In
jective ⇑(CategoryTheory.ConcreteCategory.hom (X.presheaf.germ U x hx))
参数：X : AlgebraicGeometry.Scheme；x : ↥X；hx : x ∈ U；CategoryTheory.ConcreteCategor
y.hom (X.presheaf.germ U x hx)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsGermInjectiveAt.cond`：∀ {X : AlgebraicGeometr
y.Scheme} {x : ↥X} [self : X.IsGermInjectiveAt x],   ∃ U,     ∃ (hx : x ∈ U),   
    AlgebraicGeometry.IsAffineOpen U …
-/
lemma Scheme.exists_germ_injective (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x] :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx) :=
  Scheme.IsGermInjectiveAt.cond
/-
**AlgebraicGeometry.Scheme.exists_le_and_germ_injective** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (x : ↥X) [X.IsGermInjectiveAt x] (V : X.O
pens),   x ∈ V →     ∃ U,       ∃ (hx : x ∈ U),         AlgebraicGeometry.IsAffi
neOpen U ∧           U ≤ V ∧ Function.Injective ⇑(CategoryTheory.ConcreteCategor
y.hom (X.presheaf.germ U x hx))
参数：X : AlgebraicGeometry.Scheme；x : ↥X；V : X.Opens；hx : x ∈ U；CategoryTheory.Con
creteCategory.hom (X.presheaf.germ U x hx)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsGermInjectiveAt.cond`：∀ {X : AlgebraicGeometr
y.Scheme} {x : ↥X} [self : X.IsGermInjectiveAt x],   ∃ U,     ∃ (hx : x ∈ U),   
    AlgebraicGeometry.IsAffineOpen U …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`：exists_basicOpen_le 
{V : X.Opens} (x : V) (h : ↑x in U) : exists f : Γ(X, U), X.basicOpen f <= V ∧ ↑
x in X.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用引理 `AlgebraicGeometry.injective_germ_basicOpen`：injective_germ_basicOpen (U 
: X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x in U) (f : Γ(X, U)) (hf : x in 
X.basicOpen f) (H : Function.Inj…
-/
lemma Scheme.exists_le_and_germ_injective (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x]
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ U ≤ V ∧ Function.Injective (X.presheaf.germ U x hx) := by
  obtain ⟨U, hx, hU, H⟩ := Scheme.IsGermInjectiveAt.cond (x := x)
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact ⟨X.basicOpen f, hxf, hU.basicOpen f, hf, injective_germ_basicOpen U hU x hx f hxf H⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) [X.IsGermInjectiveAt x] [IsOpenImmersion f] :
    Y.IsGermInjectiveAt (f x) := by
  obtain ⟨U, hxU, hU, H⟩ := X.exists_germ_injective x
  refine ⟨⟨f ''ᵁ U, ⟨x, hxU, rfl⟩, hU.image_of_isOpenImmersion f, ?_⟩⟩
  refine ((MorphismProperty.injective CommRingCat).cancel_right_of_respectsIso _
    (f.stalkMap x)).mp ?_
  refine ((MorphismProperty.injective CommRingCat).cancel_left_of_respectsIso
    (f.appIso U).inv _).mp ?_
  simpa

set_option backward.isDefEq.respectTransparency.types false in
variable {f} in
/-
**AlgebraicGeometry.isGermInjectiveAt_iff_of_isOpenImmersion** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry`。
形式化陈述：isGermInjectiveAt_iff_of_isOpenImmersion {x : X} [IsOpenImmersion f] : Y.I
sGermInjectiveAt (f x) ↔ X.IsGermInjectiveAt x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.exists_le_and_germ_injective`：∀ (X : AlgebraicG
eometry.Scheme) (x : ↥X) [X.IsGermInjectiveAt x] (V : X.Opens),   x ∈ V →     ∃ 
U,       ∃ (hx : x ∈ U),         AlgebraicG…
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_inv_app_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens
) {Z : CommRingCat}   (h :     X.preshe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AlgebraicGeometry.instIsGermInjectiveAtCoeContinuousMapCarrierCarrierCom
mRingCatHomTopCatBaseOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometry.Scheme} (f : 
X ⟶ Y) (x : ↥X) [X.IsGermInjectiveAt x] [AlgebraicGeometry.IsOpenImmersion f],  
 Y.IsGermInjectiveAt…
-/
lemma isGermInjectiveAt_iff_of_isOpenImmersion {x : X} [IsOpenImmersion f] :
    Y.IsGermInjectiveAt (f x) ↔ X.IsGermInjectiveAt x := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨U, hxU, hU, hU', H⟩ :=
    Y.exists_le_and_germ_injective (f x) (V := f.opensRange) ⟨x, rfl⟩
  obtain ⟨V, hV⟩ := (IsOpenImmersion.affineOpensEquiv f).surjective ⟨⟨U, hU⟩, hU'⟩
  obtain rfl : f ''ᵁ V = U := Subtype.ext_iff.mp (Subtype.ext_iff.mp hV)
  obtain ⟨y, hy, e : f y = f x⟩ := hxU
  obtain rfl := f.isOpenEmbedding.injective e
  refine ⟨V, hy, V.2, ?_⟩
  replace H := ((MorphismProperty.injective CommRingCat).cancel_right_of_respectsIso _
    (f.stalkMap y)).mpr H
  replace H := ((MorphismProperty.injective CommRingCat).cancel_left_of_respectsIso
    (f.appIso V).inv _).mpr H
  simpa using! H

/--
The class of schemes such that for each `x : X`,
`Γ(X, U) ⟶ X_x` is injective for some affine `U` containing `x`.

This is typically satisfied when `X` is integral or locally Noetherian.
-/
/-
**AlgebraicGeometry.Scheme.IsGermInjective** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of schemes such that for each `x : X`,
`Γ(X, U) ⟶ X_x` is injective for some affine `U` containing `x`.

This is typically satisfied when `X` is integral or locally Noetherian.
-/
abbrev Scheme.IsGermInjective (X : Scheme.{u}) := ∀ x : X, X.IsGermInjectiveAt x
/-
**AlgebraicGeometry.Scheme.IsGermInjective.of_openCover** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.IsGermInjective`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) [∀ (i : 𝒰.I₀), (𝒰.X i).
IsGermInjective], X.IsGermInjective
参数：𝒰 : X.OpenCover；i : 𝒰.I₀；𝒰.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AlgebraicGeometry.instIsGermInjectiveAtCoeContinuousMapCarrierCarrierCom
mRingCatHomTopCatBaseOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometry.Scheme} (f : 
X ⟶ Y) (x : ↥X) [X.IsGermInjectiveAt x] [AlgebraicGeometry.IsOpenImmersion f],  
 Y.IsGermInjectiveAt…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
-/
lemma Scheme.IsGermInjective.of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) [∀ i, (𝒰.X i).IsGermInjective] : X.IsGermInjective := by
  intro x
  rw [← (𝒰.covers x).choose_spec]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
protected
/-
**AlgebraicGeometry.Scheme.IsGermInjective.Spec** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.IsGermInjective`。
形式化陈述：∀ {R : CommRingCat},   (∀ (I : Ideal ↑R), I.IsPrime → ∃ f ∉ I, ∀ (x y : ↑R
), y * x = 0 → y ∉ I → ∃ n, f ^ n * x = 0) →     (AlgebraicGeometry.Spec R).IsGe
rmInjective
参数：∀ (I : Ideal ↑R), I.IsPrime → ∃ f ∉ I, ∀ (x y : ↑R), y * x = 0 → y ∉ I → ∃ n,
 f ^ n * x = 0；AlgebraicGeometry.Spec R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.basicOpen_eq_of_affine`：basicOpen_eq_of_affine {R : Co
mmRingCat} (f : R) : (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpect
rum.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `RingHom.ker_eq_bot_iff_eq_zero`：ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ for
all x, f x = 0 -> x = 0
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`：∀ (R : Typ
e u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((AlgebraicGeometry.S
pec.structureSheaf R).obj.obj (Opposite.op (PrimeS…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `Mathlib.Tactic.Elementwise.hom_elementwise`：hom_elementwise {C : Type*} 
[Category* C] {FC : outParam <| C -> C -> Type*} {CC : outParam <| C -> Type*} {
_ : outParam <| forall X Y, FunL…
· 使用定理 `AlgebraicGeometry.StructureSheaf.algebraMap_germ`：∀ {R : Type u} [inst :
 CommRing R] (U : TopologicalSpace.Opens ↑(AlgebraicGeometry.PrimeSpectrum.Top R
))   (x : ↑(AlgebraicGeometry.PrimeSpe…
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Ideal.mul_unit_mem_iff_mem`：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit 
y) : x * y in I ↔ x in I
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.mk'_eq_zero_iff`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra 
R S] [inst_3 : IsLoc…
-/
lemma Scheme.IsGermInjective.Spec
    (H : ∀ I : Ideal R, I.IsPrime →
      ∃ f : R, f ∉ I ∧ ∀ (x y : R), y * x = 0 → y ∉ I → ∃ n, f ^ n * x = 0) :
    (Spec R).IsGermInjective := by
  refine fun p ↦ ⟨?_⟩
  obtain ⟨f, hf, H⟩ := H p.asIdeal p.2
  refine ⟨PrimeSpectrum.basicOpen f, hf, ?_, ?_⟩
  · rw [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Spec R)).basicOpen _
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (S := ((Spec.structureSheaf R).obj.obj (.op <| PrimeSpectrum.basicOpen f))) (.powers f) x
  rw [← RingHom.mem_ker, IsLocalization.mk'_eq_mul_mk'_one, Ideal.mul_unit_mem_iff_mem,
    RingHom.mem_ker] at hx
  swap; · exact @isUnit_of_invertible _ _ _ (@IsLocalization.invertible_mk'_one ..)
  -- There is an `Opposite.unop (Opposite.op _)` in `hx` which doesn't seem removable using
  -- `simp`/`rw`.
  erw [elementwise_of% StructureSheaf.algebraMap_germ] at hx
  obtain ⟨⟨y, hy⟩, hy'⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk p) _).mp hx
  obtain ⟨n, hn⟩ := H x y hy' hy
  refine (@IsLocalization.mk'_eq_zero_iff ..).mpr ?_
  exact ⟨⟨_, n, rfl⟩, hn⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsIntegral X] : X.IsGermInjective := by
  refine fun x ↦ ⟨⟨(X.affineCover.f _).opensRange, X.affineCover.covers x,
    (isAffineOpen_opensRange (X.affineCover.f _)), ?_⟩⟩
  have : Nonempty (X.affineCover.f _).opensRange := ⟨⟨_, X.affineCover.covers x⟩⟩
  have := (isAffineOpen_opensRange (X.affineCover.f _)).isLocalization_stalk
    ⟨_, X.affineCover.covers x⟩
  exact @IsLocalization.injective _ _ _ _ _ (show _ from _) this
    (Ideal.primeCompl_le_nonZeroDivisors _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsLocallyNoetherian X] : X.IsGermInjective := by
  suffices ∀ (R : CommRingCat.{u}) (_ : IsNoetherianRing R), (Spec R).IsGermInjective by
    refine @Scheme.IsGermInjective.of_openCover _ (X.affineOpenCover.openCover) (fun i ↦ this _ ?_)
    exact isLocallyNoetherian_Spec.mp
      (isLocallyNoetherian_of_isOpenImmersion (X.affineOpenCover.f i))
  refine fun R hR ↦ Scheme.IsGermInjective.Spec fun I hI ↦ ?_
  let J := RingHom.ker <| algebraMap R (Localization.AtPrime I)
  have hJ (x) : x ∈ J ↔ ∃ y : I.primeCompl, y * x = 0 :=
    IsLocalization.map_eq_zero_iff I.primeCompl _ x
  choose f hf using fun x ↦ (hJ x).mp
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).mp ‹_› J
  have hs' : (s : Set R) ⊆ J := hs ▸ Ideal.subset_span
  refine ⟨_, (s.attach.prod fun x ↦ f x (hs' x.2)).2, fun x y e hy ↦ ⟨1, ?_⟩⟩
  rw [pow_one, mul_comm, ← smul_eq_mul, ← Submodule.mem_annihilator_span_singleton]
  refine SetLike.le_def.mp ?_ ((hJ x).mpr ⟨⟨y, hy⟩, e⟩)
  rw [← hs, Ideal.span_le]
  intro i hi
  rw [SetLike.mem_coe, Submodule.mem_annihilator_span_singleton, smul_eq_mul,
    mul_comm, ← smul_eq_mul, ← Submodule.mem_annihilator_span_singleton, Submonoid.coe_finsetProd]
  refine Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (s.mem_attach ⟨i, hi⟩)) ?_
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  exact hf i _

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `x : X` and `f g : X ⟶ Y` be two morphisms such that `f x = g x`.
If `f` and `g` agree on the stalk of `x`, then they agree on an open neighborhood of `x`,
provided `X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite type.
-/
@[stacks 0BX6]
/-
**AlgebraicGeometry.spread_out_unique_of_isGermInjective** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：spread_out_unique_of_isGermInjective {x : X} [X.IsGermInjectiveAt x] (f g 
: X ⟶ Y) (e : f x = g x) (H : f.stalkMap x = Y.presheaf.stalkSpecializes (Insepa
rable.of_eq e.symm).specializes ≫ g.stalkMap x) : exists (U : X.Opens), x in U ∧
 U.ι ≫ f = U.ι ≫ g
参数：f g : X ⟶ Y；e : f x = g x；H : f.stalkMap x = Y.presheaf.stalkSpecializes (Ins
eparable.of_eq e.symm).specializes ≫ g.stalkMap x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `AlgebraicGeometry.Scheme.exists_le_and_germ_injective`：∀ (X : AlgebraicG
eometry.Scheme) (x : ↥X) [X.IsGermInjectiveAt x] (V : X.Opens),   x ∈ V →     ∃ 
U,       ∃ (hx : x ∈ U),         AlgebraicG…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   (F : TopCat.Presheaf …
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.Hom.le_resLE_preimage_iff`：le_resLE_preimage_if
f {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (O : U.toScheme.Opens) (W : V.t
oScheme.Opens) : W <= (f.resLE U V e) ⁻¹…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Let `x : X` and `f g : X ⟶ Y` be two morphisms such that `f x = g x`.
If `f` and `g` agree on the stalk of `x`, then they agree on an open neighborhoo
d of `x`,
provided `X` is "germ-injective" at `x` (e.g. when it's integral or locally Noet
herian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite type.
-/
lemma spread_out_unique_of_isGermInjective {x : X} [X.IsGermInjectiveAt x]
    (f g : X ⟶ Y) (e : f x = g x)
    (H : f.stalkMap x =
      Y.presheaf.stalkSpecializes (Inseparable.of_eq e.symm).specializes ≫ g.stalkMap x) :
    ∃ (U : X.Opens), x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hxV' : g x ∈ V := e ▸ hxV
  obtain ⟨U, hxU, _, hUV, HU⟩ := X.exists_le_and_germ_injective x (f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V) ⟨hxV, hxV'⟩
  refine ⟨U, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι _ (hUV.trans inf_le_left),
    ← Scheme.Hom.resLE_comp_ι _ (hUV.trans inf_le_right)]
  congr 1
  have : IsAffine V := hV
  suffices ∀ (U₀ V₀) (eU : U = U₀) (eV : V = V₀),
      f.appLE V₀ U₀ (eU ▸ eV ▸ hUV.trans inf_le_left) =
        g.appLE V₀ U₀ (eU ▸ eV ▸ hUV.trans inf_le_right) by
    rw [← cancel_mono V.toScheme.isoSpec.hom]
    simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_naturality,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
    congr 2
    apply this <;> simp
  rintro U V rfl rfl
  have := ConcreteCategory.mono_of_injective _ HU
  rw [← cancel_mono (X.presheaf.germ U x hxU)]
  simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res', ← Scheme.Hom.germ_stalkMap, H]
  simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

set_option backward.isDefEq.respectTransparency.types false in
/--
A variant of `spread_out_unique_of_isGermInjective`
whose condition is an equality of scheme morphisms instead of ring homomorphisms.
-/
/-
**AlgebraicGeometry.spread_out_unique_of_isGermInjective'** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：spread_out_unique_of_isGermInjective' {x : X} [X.IsGermInjectiveAt x] (f g
 : X ⟶ Y) (e : X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : exists (U : X.Op
ens), x in U ∧ U.ι ≫ f = U.ι ≫ g
参数：f g : X ⟶ Y；e : X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.spread_out_unique_of_isGermInjective`：spread_out_uniqu
e_of_isGermInjective {x : X} [X.IsGermInjectiveAt x] (f g : X ⟶ Y) (e : f x = g 
x) (H : f.stalkMap x = Y.presheaf.stalkSpeci…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`：fromSpecStalk_closed
Point {x : X} : X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x
· 使用定理 `AlgebraicGeometry.Spec.map_injective`：∀ {R S : CommRingCat}, Function.In
jective AlgebraicGeometry.Spec.map
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.instIsPreimmersionFromSpecStalk`：∀ {X : AlgebraicGeome
try.Scheme} (x : ↥X), AlgebraicGeometry.IsPreimmersion (X.fromSpecStalk x)
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk`：SpecMap_stalkMa
p_fromSpecStalk {x} : Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecSt
alk x ≫ f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk`：SpecMap
_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) : Spec.map (X.presheaf.sta
lkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStal…

--- 原说明 ---
A variant of `spread_out_unique_of_isGermInjective`
whose condition is an equality of scheme morphisms instead of ring homomorphisms
.
-/
lemma spread_out_unique_of_isGermInjective' {x : X} [X.IsGermInjectiveAt x]
    (f g : X ⟶ Y)
    (e : X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) :
    ∃ (U : X.Opens), x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  fapply spread_out_unique_of_isGermInjective
  · simpa using congr($e (IsLocalRing.closedPoint _))
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk _)]
    simpa [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
/-
**AlgebraicGeometry.exists_lift_of_germInjective_aux** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：exists_lift_of_germInjective_aux {U : X.Opens} {x : X} (hxU) (φ : A ⟶ X.pr
esheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U)) (hφRA : RingHom.FiniteType φRA
.hom) (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU) : exists (V : X.Opens) (hxV 
: x in V), V <= U ∧ RingHom.range φ.hom <= RingHom.range (X.presheaf.germ V x hx
V).hom
参数：hxU；φ : A ⟶ X.presheaf.stalk x；φRA : R ⟶ A；φRX : R ⟶ Γ(X, U)；hφRA : RingHom.F
initeType φRA.hom；e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `TopologicalSpace.Opens.coe_inf`：coe_inf (s t : Opens α) : (↑(s ⊓ t) : Se
t α) = ↑s inter ↑t
· 使用定理 `TopologicalSpace.Opens.coe_finset_inf`：coe_finset_inf (f : ι -> Opens α)
 (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inf_set_eq_iInter`：inf_set_eq_iInter (s : Finset α) (f : α -> Set
 β) : s.inf f = ⋂ x in s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
-/
lemma exists_lift_of_germInjective_aux {U : X.Opens} {x : X} (hxU)
    (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U))
    (hφRA : RingHom.FiniteType φRA.hom)
    (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU) :
    ∃ (V : X.Opens) (hxV : x ∈ V),
      V ≤ U ∧ RingHom.range φ.hom ≤ RingHom.range (X.presheaf.germ V x hxV).hom := by
  let := φRA.hom.toAlgebra
  obtain ⟨s, hs⟩ := hφRA
  choose W hxW f hf using fun t ↦ X.presheaf.exists_germ_eq (φ t)
  have H : x ∈ s.inf W ⊓ U := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_finset_inf]
    exact ⟨by simpa using fun x _ ↦ hxW x, hxU⟩
  refine ⟨s.inf W ⊓ U, H, inf_le_right, ?_⟩
  let := φRX.hom.toAlgebra
  let := (φRX ≫ X.presheaf.germ U x hxU).hom.toAlgebra
  let := (φRX ≫ X.presheaf.map (homOfLE (inf_le_right (a := s.inf W))).op).hom.toAlgebra
  let φ' : A →ₐ[R] X.presheaf.stalk x :=
    { φ.hom with commutes' := DFunLike.congr_fun (congr_arg CommRingCat.Hom.hom e) }
  let ψ : Γ(X, s.inf W ⊓ U) →ₐ[R] X.presheaf.stalk x :=
    { (X.presheaf.germ _ x H).hom with commutes' := fun x ↦ X.presheaf.germ_res_apply _ _ _ _ }
  change AlgHom.range φ' ≤ AlgHom.range ψ
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨i, hi, rfl : φ i = _⟩
  refine ⟨X.presheaf.map (homOfLE (inf_le_left.trans (Finset.inf_le hi))).op (f i), ?_⟩
  exact (X.presheaf.germ_res_apply _ _ _ _).trans (hf _)

/--
Suppose `X` is a scheme, `x : X` such that the germ map at `x` is (locally) injective,
and `U` is a neighborhood of `x`.
Given a commutative diagram of `CommRingCat`
```
R ⟶ Γ(X, U)
↓    ↓
A ⟶ 𝒪_{X, x}
```
such that `R` is of finite type over `A`, we may lift `A ⟶ 𝒪_{X, x}` to some `A ⟶ Γ(X, V)`.
-/
/-
**AlgebraicGeometry.exists_lift_of_germInjective** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：exists_lift_of_germInjective {x : X} [X.IsGermInjectiveAt x] {U : X.Opens}
 (hxU : x in U) (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U)) (
hφRA : RingHom.FiniteType φRA.hom) (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU)
 : exists (V : X.Opens) (hxV : x in V) (φ' : A ⟶ Γ(X, V)) (i : V <= U), IsAffine
Open V ∧ φ = φ' ≫ X.presheaf.germ V x hxV ∧ φRX ≫ X.presheaf.map i.hom.op = φRA 
≫ φ'
参数：hxU : x in U；φ : A ⟶ X.presheaf.stalk x；φRA : R ⟶ A；φRX : R ⟶ Γ(X, U)；hφRA : 
RingHom.FiniteType φRA.hom；e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.exists_lift_of_germInjective_aux`：exists_lift_of_germI
njective_aux {U : X.Opens} {x : X} (hxU) (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶
 A) (φRX : R ⟶ Γ(X, U)) (hφRA : RingHom.…
· 使用定理 `AlgebraicGeometry.Scheme.exists_le_and_germ_injective`：∀ (X : AlgebraicG
eometry.Scheme) (x : ↥X) [X.IsGermInjectiveAt x] (V : X.Opens),   x ∈ V →     ∃ 
U,       ∃ (hx : x ∈ U),         AlgebraicG…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Function.Injective.hasLeftInverse`：∀ {α : Sort u_1} {β : Sort u_2} [None
mpty α] {f : α → β}, Function.Injective f → Function.HasLeftInverse f
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …

--- 原说明 ---
Suppose `X` is a scheme, `x : X` such that the germ map at `x` is (locally) inje
ctive,
and `U` is a neighborhood of `x`.
Given a commutative diagram of `CommRingCat`
```
R ⟶ Γ(X, U)
↓    ↓
A ⟶ 𝒪_{X, x}
```
such that `R` is of finite type over `A`, we may lift `A ⟶ 𝒪_{X, x}` to some `A 
⟶ Γ(X, V)`.
-/
lemma exists_lift_of_germInjective {x : X} [X.IsGermInjectiveAt x] {U : X.Opens} (hxU : x ∈ U)
    (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U))
    (hφRA : RingHom.FiniteType φRA.hom)
    (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (φ' : A ⟶ Γ(X, V)) (i : V ≤ U), IsAffineOpen V ∧
      φ = φ' ≫ X.presheaf.germ V x hxV ∧ φRX ≫ X.presheaf.map i.hom.op = φRA ≫ φ' := by
  obtain ⟨V, hxV, iVU, hV⟩ := exists_lift_of_germInjective_aux hxU φ φRA φRX hφRA e
  obtain ⟨V', hxV', hV', iV'V, H⟩ := X.exists_le_and_germ_injective x V hxV
  let f := X.presheaf.germ V' x hxV'
  have hf' : RingHom.range (X.presheaf.germ V x hxV).hom ≤ RingHom.range f.hom := by
    rw [← X.presheaf.germ_res iV'V.hom _ hxV']
    exact Set.range_comp_subset_range (X.presheaf.map iV'V.hom.op) f
  let e := RingEquiv.ofLeftInverse H.hasLeftInverse.choose_spec
  refine ⟨V', hxV', CommRingCat.ofHom (e.symm.toRingHom.comp
    (φ.hom.codRestrict _ (fun x ↦ hf' (hV ⟨x, rfl⟩)))), iV'V.trans iVU, hV', ?_, ?_⟩
  · ext a
    change φ a = (e (e.symm _)).1
    simp only [RingEquiv.apply_symm_apply]
    rfl
  · ext a
    apply e.injective
    change e _ = e (e.symm _)
    rw [RingEquiv.apply_symm_apply]
    ext
    change X.presheaf.germ _ _ _ (X.presheaf.map _ _) = (φRA ≫ φ) a
    rw [TopCat.Presheaf.germ_res_apply, ‹φRA ≫ φ = _›]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Given `S`-schemes `X Y` and points `x : X` `y : Y` over `s : S`.
Suppose we have the following diagram of `S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
Then the map `Spec(φ)` spreads out to an `S`-morphism on an open subscheme `U ⊆ X`,
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    |             |
  Spec(φ)         |
    ↓             ↓
Spec 𝒪_{Y, y} ⟶ Y
```
provided that `Y` is locally of finite type over `S` and
`X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite presentation.
-/
@[stacks 0BX6]
/-
**AlgebraicGeometry.spread_out_of_isGermInjective** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：spread_out_of_isGermInjective [LocallyOfFiniteType sY] {x : X} [X.IsGermIn
jectiveAt x] {y : Y} (e : sX x = sY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stal
k x) (h : sY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (Inseparable.of_eq e).
specializes ≫ sX.stalkMap x) : exists (U : X.Opens) (hxU : x in U) (f : U.toSche
me ⟶ Y), Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ s
Y = U.ι ≫ sX
参数：e : sX x = sY y；φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x；h : sY.stalkMap y
 ≫ φ = S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkM
ap x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.eq_1`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (e : V ≤ (TopologicalSpace.Opens.m
ap f.base).obj U),   Algebrai…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.Presheaf.germ_res_assoc`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_assoc`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (x : ↥X) (hx : f x ∈ U) {Z : CommRingCat}
   (h : X.presheaf.stalk x ⟶ Z),   Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   (F : TopCat.Presheaf …
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.exists_lift_of_germInjective`：exists_lift_of_germInjec
tive {x : X} [X.IsGermInjectiveAt x] {U : X.Opens} (hxU : x in U) (φ : A ⟶ X.pre
sheaf.stalk x) (φRA : R ⟶ A) (φRX : …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.LocallyOfFiniteType f] {U : Y.Op
ens},   AlgebraicGeometry.IsAffineO…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_toSpecΓ_assoc`：∀ {X : 
AlgebraicGeometry.Scheme} (U : X.Opens) (x : ↥X) (hxU : x ∈ U) {Z : AlgebraicGeo
metry.Scheme}   (h : AlgebraicGeometry.Spec (X.preshe…
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`：∀ {X : Al
gebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x
 : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fr…
· 使用引理 `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`：SpecMap_appLE_fro
mSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffi
neOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.…
· 使用引理 `AlgebraicGeometry.IsAffineOpen.isoSpec_hom`：isoSpec_hom : hU.isoSpec.hom
 = U.toSpecΓ
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Given `S`-schemes `X Y` and points `x : X` `y : Y` over `s : S`.
Suppose we have the following diagram of `S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
Then the map `Spec(φ)` spreads out to an `S`-morphism on an open subscheme `U ⊆ 
X`,
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    |             |
  Spec(φ)         |
    ↓             ↓
Spec 𝒪_{Y, y} ⟶ Y
```
provided that `Y` is locally of finite type over `S` and
`X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite presenta
tion.
-/
lemma spread_out_of_isGermInjective [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] {y : Y}
    (e : sX x = sY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (h : sY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
      f ≫ sY = U.ι ≫ sX := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (sX x)) isOpen_univ
  have hyU : sY y ∈ U := e ▸ hxU
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, iVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (sY ⁻¹ᵁ U).2
  have : sY.appLE U V iVU ≫ Y.presheaf.germ V y hyV ≫ φ =
      sX.app U ≫ X.presheaf.germ (sX ⁻¹ᵁ U) x hxU := by
    rw [Scheme.Hom.appLE, Category.assoc, Y.presheaf.germ_res_assoc,
      ← Scheme.Hom.germ_stalkMap_assoc, h]
    simp
  obtain ⟨W, hxW, φ', i, hW, h₁, h₂⟩ :=
    exists_lift_of_germInjective (R := Γ(S, U)) (A := Γ(Y, V)) (U := sX ⁻¹ᵁ U) (x := x) hxU
    (Y.presheaf.germ _ y hyV ≫ φ) (sY.appLE U V iVU) (sX.app U)
    (sY.finiteType_appLE hU hV _) this
  refine ⟨W, hxW, W.toSpecΓ ≫ Spec.map φ' ≫ hV.fromSpec, ?_, ?_⟩
  · rw [W.fromSpecStalkOfMem_toSpecΓ_assoc x hxW, ← Spec.map_comp_assoc, ← h₁,
      Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk,
      IsAffineOpen.fromSpecStalk_eq_fromSpecStalk]
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec sY hU hV iVU, ← Spec.map_comp_assoc, ← h₂,
      ← Scheme.Hom.appLE, ← hW.isoSpec_hom, IsAffineOpen.SpecMap_appLE_fromSpec sX hU hW i,
      ← Iso.eq_inv_comp, IsAffineOpen.isoSpec_inv_ι_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
Given `S`-schemes `X Y`, a point `x : X`, and an `S`-morphism `φ : Spec 𝒪_{X, x} ⟶ Y`,
we may spread it out to an `S`-morphism `f : U ⟶ Y`
provided that `Y` is locally of finite type over `S` and
`X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite presentation.
-/
/-
**AlgebraicGeometry.spread_out_of_isGermInjective'** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：spread_out_of_isGermInjective' [LocallyOfFiniteType sY] {x : X} [X.IsGermI
njectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.fromSpecStalk 
x ≫ sX) : exists (U : X.Opens) (hxU : x in U) (f : U.toScheme ⟶ Y), φ = U.fromSp
ecStalkOfMem x hxU ≫ f ∧ f ≫ sY = U.ι ≫ sX
参数：φ : Spec (X.presheaf.stalk x) ⟶ Y；h : φ ≫ sY = X.fromSpecStalk x ≫ sX。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用引理 `AlgebraicGeometry.spread_out_of_isGermInjective`：spread_out_of_isGermInj
ective [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] {y : Y} (e : sX 
x = sY y) (φ : Y.presheaf.stalk y ⟶ X…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`：fromSpecStalk_closed
Point {x : X} : X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x
· 使用定理 `AlgebraicGeometry.Spec.map_injective`：∀ {R S : CommRingCat}, Function.In
jective AlgebraicGeometry.Spec.map
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.instIsPreimmersionFromSpecStalk`：∀ {X : AlgebraicGeome
try.Scheme} (x : ↥X), AlgebraicGeometry.IsPreimmersion (X.fromSpecStalk x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk`：SpecMap_stalkMa
p_fromSpecStalk {x} : Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecSt
alk x ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc`：∀ 
{X : AlgebraicGeometry.Scheme} {R : CommRingCat} [inst : IsLocalRing ↑R] (f : Al
gebraicGeometry.Spec R ⟶ X)   {Z : AlgebraicGeometry.Schem…
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk`：SpecMap
_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) : Spec.map (X.presheaf.sta
lkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStal…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk`：Spec_sta
lkClosedPointTo_fromSpecStalk : Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStal
k _ = f

--- 原说明 ---
Given `S`-schemes `X Y`, a point `x : X`, and an `S`-morphism `φ : Spec 𝒪_{X, x}
 ⟶ Y`,
we may spread it out to an `S`-morphism `f : U ⟶ Y`
provided that `Y` is locally of finite type over `S` and
`X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite presenta
tion.
-/
lemma spread_out_of_isGermInjective' [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
    (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      φ = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ sY = U.ι ≫ sX := by
  have := spread_out_of_isGermInjective sX sY ?_ (Scheme.stalkClosedPointTo φ) ?_
  · simpa only [Scheme.Spec_stalkClosedPointTo_fromSpecStalk] using this
  · rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  · apply Spec.map_injective
    rw [← cancel_mono (S.fromSpecStalk _)]
    simpa only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end AlgebraicGeometry

