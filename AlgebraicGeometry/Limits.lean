/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.Tactic.SuppressCompilation
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects -- shake: keep
-- This import adds an instance which, despite failing to trigger,
-- is necessary for some typeclass syntheses in this file to succeed.

/-!
# (Co)Limits of Schemes

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `Mathlib/AlgebraicGeometry/Pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.
* The disjoint union is the coproduct of a family of schemes, and the forgetful functor to
  `LocallyRingedSpace` and `TopCat` preserves them.

## TODO

* Spec preserves finite coproducts.

-/

@[expose] public section

suppress_compilation


universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace AlgebraicGeometry

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
/-
**AlgebraicGeometry.specZIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：specZIsTerminal : IsTerminal (Spec <| .of Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Spec ℤ` is the terminal object in the category of schemes.
-/
noncomputable def specZIsTerminal : IsTerminal (Spec <| .of ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
/-
**AlgebraicGeometry.specULiftZIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：specULiftZIsTerminal : IsTerminal (Spec <| .of <| ULift.{u} Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Spec ℤ` is the terminal object in the category of schemes.
-/
noncomputable def specULiftZIsTerminal : IsTerminal (Spec <| .of <| ULift.{u} ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.isInitial)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTerminal Scheme :=
  hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAffine (⊤_ Scheme.{u}) :=
  .of_isIso (PreservesTerminal.iso Scheme.Spec).inv
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteLimits Scheme :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme.{u}) : X.Over (⊤_ _) := ⟨terminal.from _⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} [X.Over (⊤_ Scheme)] [Y.Over (⊤_ Scheme)] (f : X ⟶ Y) :
    @Scheme.Hom.IsOver _ _ f (⊤_ Scheme) ‹_› ‹_› := ⟨Subsingleton.elim _ _⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme} : Subsingleton (X.Over (⊤_ Scheme)) :=
  ⟨fun ⟨a⟩ ⟨b⟩ ↦ by simp [Subsingleton.elim a b]⟩

section Initial

/-- The map from the empty scheme. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.emptyTo** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → ∅ ⟶ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the empty scheme.
-/
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{  base := TopCat.ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩
      c := { app := fun _ => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩

@[ext]
/-
**AlgebraicGeometry.Scheme.empty_ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (f g : ∅ ⟶ X), f = g
参数：f g : ∅ ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ext'`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 g : X ⟶ Y},   AlgebraicGeometry.Scheme.Hom.toLRSHom f = AlgebraicGeometry.Schem
e.Hom.toLRSHom g → f = …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g :=
  Scheme.Hom.ext' (Subsingleton.elim (α := ∅ ⟶ _) _ _)
/-
**AlgebraicGeometry.Scheme.eq_emptyTo** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (f : ∅ ⟶ X), f = X.emptyTo
参数：f : ∅ ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.empty_ext`：∀ {X : AlgebraicGeometry.Scheme} (f 
g : ∅ ⟶ X), f = g
-/
theorem Scheme.eq_emptyTo {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.emptyTo X :=
  Scheme.empty_ext f (Scheme.emptyTo X)
/-
**AlgebraicGeometry.Scheme.hom_unique_of_empty_source** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → Unique (∅ ⟶ X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Scheme.hom_unique_of_empty_source (X : Scheme.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

/-- The empty scheme is the initial object in the category of schemes. -/
/-
**AlgebraicGeometry.emptyIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：emptyIsInitial : IsInitial (∅ : Scheme.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty scheme is the initial object in the category of schemes.
-/
def emptyIsInitial : IsInitial (∅ : Scheme.{u}) :=
  IsInitial.ofUnique _

@[simp]
/-
**AlgebraicGeometry.emptyIsInitial_to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：emptyIsInitial_to : emptyIsInitial.to = Scheme.emptyTo
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem emptyIsInitial_to : emptyIsInitial.to = Scheme.emptyTo :=
  rfl
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty (∅ : Scheme.{u}) :=
  show IsEmpty PEmpty by infer_instance
/-
**AlgebraicGeometry.spec_punit_isEmpty** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：spec_punit_isEmpty : IsEmpty (Spec <| .of PUnit.{u + 1})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance spec_punit_isEmpty : IsEmpty (Spec <| .of PUnit.{u + 1}) :=
  inferInstanceAs <| IsEmpty (PrimeSpectrum PUnit)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X] : IsOpenImmersion f := by
  apply +allowSynthFailures IsOpenImmersion.of_isIso_stalkMap
  · exact .of_isEmpty (X := X) _
  · intro (i : X); exact isEmptyElim i
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y] :
    IsIso f := by
  have : IsEmpty X := f.base.hom.1.isEmpty
  have : Epi f.base := by
    rw [TopCat.epi_iff_surjective]; rintro (x : Y)
    exact isEmptyElim x
  apply IsOpenImmersion.isIso

/-- A scheme is initial if its underlying space is empty . -/
/-
**AlgebraicGeometry.isInitialOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：isInitialOfIsEmpty {X : Scheme} [IsEmpty X] : IsInitial X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme is initial if its underlying space is empty .
-/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X] : IsInitial X :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
/-
**AlgebraicGeometry.specPUnitIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：specPUnitIsInitial : IsInitial (Spec <| .of PUnit.{u + 1})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Spec 0` is the initial object in the category of schemes.
-/
noncomputable def specPUnitIsInitial : IsInitial (Spec <| .of PUnit.{u + 1}) :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

@[deprecated (since := "2026-02-08")] alias specPunitIsInitial := specPUnitIsInitial
/-
**AlgebraicGeometry.isInitial_iff_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty 
X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isEmpty`：∀ {α : Sort u_1} {β : Sort u_4} (e : α ≃ β) [IsEmpty β], 
IsEmpty α
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty X :=
  ⟨fun ⟨h⟩ ↦ (h.uniqueUpToIso specPUnitIsInitial).hom.homeomorph.isEmpty,
    fun _ ↦ ⟨isInitialOfIsEmpty⟩⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X] : IsAffine X :=
  .of_isIso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Spec <| .of PUnit))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasInitial Scheme.{u} :=
  hasInitial_of_unique ∅
/-
**AlgebraicGeometry.initial_isEmpty** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：initial_isEmpty : IsEmpty (⊥_ Scheme)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasInitialScheme`：CategoryTheory.Limits.HasInitial
 AlgebraicGeometry.Scheme
-/
instance initial_isEmpty : IsEmpty (⊥_ Scheme) :=
  ⟨fun x => ((initial.to Scheme.empty :) x).elim⟩
/-
**AlgebraicGeometry.isAffineOpen_bot** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：isAffineOpen_bot (X : Scheme) : IsAffineOpen (⊥ : X.Opens)
参数：X : Scheme。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isAffine_of_isEmpty`：∀ {X : AlgebraicGeometry.Scheme} 
[IsEmpty ↥X], AlgebraicGeometry.IsAffine X
-/
theorem isAffineOpen_bot (X : Scheme) : IsAffineOpen (⊥ : X.Opens) :=
  @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme} [IsEmpty X] (U : X.Opens) : Subsingleton Γ(X, U) := by
  obtain rfl : U = ⊥ := Subsingleton.elim _ _; infer_instance

-- This is also true for schemes with two points.
-- But there are non-affine schemes with three points.
/-- This is true in general for finite discrete schemes. See below. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is true in general for finite discrete schemes. See below.
-/
instance (priority := low) {X : Scheme.{u}} [Subsingleton X] : IsAffine X := by
  cases isEmpty_or_nonempty X with
  | inl h => infer_instance
  | inr h =>
  obtain ⟨x⟩ := h
  obtain ⟨_, ⟨U, hU : IsAffine _, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  obtain rfl : U = ⊤ := by ext y; simpa [Subsingleton.elim y x]
  exact .of_isIso (Scheme.topIso X).inv
/-
**AlgebraicGeometry.IsAffineOpen.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens}, (↑U).Subsingleton → Algebr
aicGeometry.IsAffineOpen U
参数：↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.coe_sort`：∀ {α : Type u} {s : Set α}, s.Subsingleton → 
Subsingleton ↑s
· 使用定理 `AlgebraicGeometry.instIsAffineOfSubsingletonCarrierCarrierCommRingCat`：∀
 {X : AlgebraicGeometry.Scheme} [Subsingleton ↥X], AlgebraicGeometry.IsAffine X
-/
theorem IsAffineOpen.of_subsingleton {X : Scheme} {U : X.Opens}
    (hU : Set.Subsingleton (U : Set X)) : IsAffineOpen U :=
  have : Subsingleton U := hU.coe_sort
  inferInstanceAs (IsAffine _)

end Initial

section Coproduct

variable {ι : Type u} (f : ι → Scheme.{u})

variable {σ : Type v} (g : σ → Scheme.{u})

noncomputable
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{u} σ] :
    CreatesColimitsOfShape (Discrete σ) Scheme.forgetToLocallyRingedSpace.{u} where
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{u} σ] : PreservesColimitsOfShape (Discrete σ) Scheme.forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete σ) (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{u} σ] : HasColimitsOfShape (Discrete σ) Scheme.{u} :=
  ⟨fun _ ↦ hasColimit_of_created _ Scheme.forgetToLocallyRingedSpace⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.sigma** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sigmaι_eq_iff [Small.{u} σ] (i j : σ) (x y) :
    Sigma.ι g i x = Sigma.ι g j y ↔ (Sigma.mk i x : Σ i, g i) = Sigma.mk j y := by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff _).trans ⟨?_, ?_⟩
  · rintro ⟨k, ⟨⟨⟨⟩⟩⟩, ⟨⟨⟨⟩⟩⟩, x, rfl, rfl⟩; simp
  · simp only [Discrete.functor_obj_eq_as, Sigma.mk.injEq]
    rintro ⟨rfl, e⟩
    obtain rfl := (heq_eq_eq x y).mp e
    exact ⟨⟨i⟩, 𝟙 _, 𝟙 _, x, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The images of each component in the coproduct is disjoint. -/
/-
**AlgebraicGeometry.disjoint_opensRange_sigma** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The images of each component in the coproduct is disjoint.
-/
lemma disjoint_opensRange_sigmaι [Small.{u} σ] (i j : σ) (h : i ≠ j) :
    Disjoint (Sigma.ι g i).opensRange (Sigma.ι g j).opensRange := by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl

variable {g} in
/-
**AlgebraicGeometry.isEmpty_of_commSq_sigma** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isEmpty_of_commSq_sigmaι_of_ne [Small.{u} σ] {i j : σ} {Z : Scheme.{u}} {a : Z ⟶ g i}
    {b : Z ⟶ g j} (h : CommSq a b (Sigma.ι g i) (Sigma.ι g j)) (hij : i ≠ j) :
    IsEmpty Z := by
  refine ⟨fun z ↦ ?_⟩
  fapply eq_bot_iff.mp <| disjoint_iff.mp <| disjoint_opensRange_sigmaι g i j hij
  · exact (a ≫ Sigma.ι g i).base z
  · exact ⟨⟨a.base z, rfl⟩, ⟨b.base z, by rw [← Scheme.Hom.comp_apply, h.w]⟩⟩
/-
**AlgebraicGeometry.isEmpty_pullback_sigma** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isEmpty_pullback_sigmaι_of_ne [Small.{u} σ] {i j : σ} (hij : i ≠ j) :
    IsEmpty ↑(pullback (Sigma.ι g i) (Sigma.ι g j)) :=
  isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Small.{u} σ] : CoproductsOfShapeDisjoint Scheme.{u} σ where
  coproductDisjoint g := by
    refine .of_hasCoproduct (fun _ ↦ pullback.cone _ _) (fun _ ↦ pullback.isLimit _ _) ?_
    intro i j hij
    apply Nonempty.some
    rw [isInitial_iff_isEmpty]
    exact isEmpty_pullback_sigmaι_of_ne _ hij
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoCoprod Scheme.{u} :=
  .mk' fun X Y ↦ ⟨.mk coprod.inl coprod.inr, coprodIsCoprod X Y, inferInstanceAs <| Mono coprod.inl⟩

/-- The cover of `∐ X` by the `Xᵢ`. -/
@[simps!]
/-
**AlgebraicGeometry.sigmaOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：sigmaOpenCover [Small.{u} σ] : (∐ g).OpenCover
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The cover of `∐ X` by the `Xᵢ`.
-/
noncomputable def sigmaOpenCover [Small.{u} σ] : (∐ g).OpenCover :=
  (Scheme.IsLocallyDirected.openCover (Discrete.functor g)).copy σ g (Sigma.ι _)
  (discreteEquiv.symm) (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union. -/
noncomputable
/-
**AlgebraicGeometry.sigmaMk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：sigmaMk : (Σ i, f i) ≃ₜ (∐ f :)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sigmaMk : (Σ i, f i) ≃ₜ (∐ f :) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

@[simp]
/-
**AlgebraicGeometry.sigmaMk_mk** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：sigmaMk_mk (i) (x : f i) : sigmaMk f (.mk i x) = Sigma.ι f i x
参数：i；x : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv_assoc`：∀ {J : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryT
heory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_comp_sigmaComparison`：ι_comp_sigmaComparison [Ha
sCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) : Sigma.ι _ b ≫ sigmaC
omparison G f = G.map (Sigma.ι f b…
-/
lemma sigmaMk_mk (i) (x : f i) :
    sigmaMk f (.mk i x) = Sigma.ι f i x := by
  change ((TopCat.sigmaCofan (fun x ↦ (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exact ι_comp_sigmaComparison Scheme.forgetToTop _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/-
**AlgebraicGeometry.isOpenImmersion_sigmaDesc_aux** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isOpenImmersion_sigmaDesc_aux
    {X : Scheme.{u}} (α : ∀ i, f i ⟶ X) [∀ i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsOpenImmersion (Sigma.desc α) := by
  rw [IsOpenImmersion.iff_isIso_stalkMap]
  constructor
  · suffices Topology.IsOpenEmbedding (Sigma.desc α ∘ sigmaMk f) by
      convert! this.comp (sigmaMk f).symm.isOpenEmbedding; ext; simp
    refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
    · fun_prop
    · rintro ⟨ix, x⟩ ⟨iy, y⟩ e
      have : α ix x = α iy y := by
        simpa [← Scheme.Hom.comp_apply] using e
      obtain rfl : ix = iy := by
        by_contra h
        exact Set.disjoint_iff_forall_ne.mp (hα h) ⟨x, rfl⟩ ⟨y, this.symm⟩ rfl
      rw [(α ix).isOpenEmbedding.injective this]
    · rw [isOpenMap_sigma]
      intro i
      simpa [← Scheme.Hom.comp_apply] using (α i).isOpenEmbedding.isOpenMap
  · intro x
    have ⟨y, hy⟩ := (Scheme.IsLocallyDirected.openCover (Discrete.functor f)).covers x
    rw [← hy]
    refine IsIso.of_isIso_fac_right
      (f := ((Scheme.IsLocallyDirected.openCover (Discrete.functor f)).f _).stalkMap y)
      (h := (X.presheaf.stalkCongr (.of_eq ?_)).hom ≫ (α _).stalkMap _) ?_
    · simp [← Scheme.Hom.comp_apply]
    · simp [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ (colimit.ι_desc _ _)]

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/-
**AlgebraicGeometry.isOpenImmersion_sigmaDesc** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：isOpenImmersion_sigmaDesc [Small.{u} σ] {X : Scheme.{u}} (α : forall i, g 
i ⟶ X) [forall i, IsOpenImmersion (α i)] (hα : Pairwise (Disjoint on (Set.range 
<| α ·))) : IsOpenImmersion (Sigma.desc α)
参数：α : forall i, g i ⟶ X；α i；hα : Pairwise (Disjoint on (Set.range <| α ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `Small.equiv_small`：∀ {α : Type v} [self : Small.{w, v} α], ∃ S, Nonempty
 (α ≃ S)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_reindex_inv_assoc`：∀ {β : Type w} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {γ : Type w'} (ε : β ≃ γ) (f : γ 
→ C)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Limits.0.AlgebraicGeometry.isOpenImme
rsion_sigmaDesc_aux`：∀ {ι : Type u} (f : ι → AlgebraicGeometry.Scheme) {X : Alge
braicGeometry.Scheme} (α : (i : ι) → f i ⟶ X)   [∀ (i : ι), AlgebraicGeometry.Is
O…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma isOpenImmersion_sigmaDesc [Small.{u} σ]
    {X : Scheme.{u}} (α : ∀ i, g i ⟶ X) [∀ i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsOpenImmersion (Sigma.desc α) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small (α := σ)
  convert! IsOpenImmersion.comp ((Sigma.reindex e.symm g).inv) (Sigma.desc fun i ↦ α _)
  · refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨i, rfl⟩ := e.symm.surjective i
    simp
  · apply isOpenImmersion_sigmaDesc_aux
    intro i j hij
    exact hα (fun h ↦ hij (e.symm.injective h))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/-- `S` is the disjoint union of `Xᵢ` if the `Xᵢ` are covering, pairwise disjoint open subschemes
of `S`. -/
/-
**AlgebraicGeometry.nonempty_isColimit_cofanMk_of** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：nonempty_isColimit_cofanMk_of [Small.{u} σ] {X : σ -> Scheme.{u}} {S : Sch
eme.{u}} (f : forall i, X i ⟶ S) [forall i, IsOpenImmersion (f i)] (hcov : ⨆ i, 
(f i).opensRange = ⊤) (hdisj : Pairwise (Disjoint on (f · |>.opensRange))) : Non
empty (IsColimit <| Cofan.mk S f)
参数：f : forall i, X i ⟶ S；f i；hcov : ⨆ i, (f i).opensRange = ⊤；hdisj : Pairwise (
Disjoint on (f · |>.opensRange))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用引理 `AlgebraicGeometry.isOpenImmersion_sigmaDesc`：isOpenImmersion_sigmaDesc [
Small.{u} σ] {X : Scheme.{u}} (α : forall i, g i ⟶ X) [forall i, IsOpenImmersion
 (α i)] (hα : Pairwise (Disjoint …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`：∀ {β
 : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : β → C}   
[inst_1 : CategoryTheory.Limits.HasCoproduct f] (c : Cat…
· 使用引理 `AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top`：isIso_o
f_isOpenImmersion_of_opensRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImm
ersion f] (hf : f.opensRange = ⊤) : IsIso f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`S` is the disjoint union of `Xᵢ` if the `Xᵢ` are covering, pairwise disjoint op
en subschemes
of `S`.
-/
lemma nonempty_isColimit_cofanMk_of [Small.{u} σ]
    {X : σ → Scheme.{u}} {S : Scheme.{u}} (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⨆ i, (f i).opensRange = ⊤) (hdisj : Pairwise (Disjoint on (f · |>.opensRange))) :
    Nonempty (IsColimit <| Cofan.mk S f) := by
  have : IsOpenImmersion (Sigma.desc f) := by
    refine isOpenImmersion_sigmaDesc _ _ (fun i j hij ↦ ?_)
    simpa [Function.onFun_apply, disjoint_iff, Opens.ext_iff] using hdisj hij
  simp only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk S f), cofan_mk_inj, Cofan.mk_pt]
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [eq_top_iff]
  intro x hx
  have : x ∈ ⨆ i, (f i).opensRange := by rwa [hcov]
  obtain ⟨i, y, rfl⟩ := by simpa only [Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion] using this
  use Sigma.ι X i y
  simp [← Scheme.Hom.comp_apply]

variable (X Y : Scheme.{u})

/-- (Implementation Detail)
The coproduct of the two schemes is given by indexed coproducts over `WalkingPair`. -/
noncomputable
/-
**AlgebraicGeometry.coprodIsoSigma** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：coprodIsoSigma : X ⨿ Y ≅ ∐ fun i : ULift.{u} WalkingPair => i.1.casesOn X 
Y
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def coprodIsoSigma : X ⨿ Y ≅ ∐ fun i : ULift.{u} WalkingPair ↦ i.1.casesOn X Y :=
  Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ by exact Iso.refl _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_left_coprodIsoSigma_inv : Sigma.ι _ ⟨.left⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inl :=
  Sigma.ι_comp_map' _ _ _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_right_coprodIsoSigma_inv : Sigma.ι _ ⟨.right⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inr :=
  Sigma.ι_comp_map' _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [← ι_left_coprodIsoSigma_inv]; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [← ι_right_coprodIsoSigma_inv]; infer_instance
/-
**AlgebraicGeometry.isCompl_range_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：isCompl_range_inl_inr : IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.
range (coprod.inr : Y ⟶ X ⨿ Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.binaryCofan_isColimit_iff`：binaryCofan_isColimit_iff {X Y : TopCa
t.{u}} (c : BinaryCofan X Y) : Nonempty (IsColimit c) ↔ IsOpenEmbedding c.inl ∧ 
IsOpenEmbedding c.inr …
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `AlgebraicGeometry.instPreservesColimitsOfShapeSchemeTopCatDiscreteForget
ToTopOfSmall`：∀ {σ : Type v} [Small.{u, v} σ],   CategoryTheory.Limits.Preserves
ColimitsOfShape (CategoryTheory.Discrete σ) AlgebraicGeometry.Scheme.forge…
-/
lemma isCompl_range_inl_inr :
    IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.range (coprod.inr : Y ⟶ X ⨿ Y)) :=
  ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ (coprodIsCoprod X Y)⟩).2.2
/-
**AlgebraicGeometry.isCompl_opensRange_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：isCompl_opensRange_inl_inr : IsCompl (coprod.inl : X ⟶ X ⨿ Y).opensRange (
coprod.inr : Y ⟶ X ⨿ Y).opensRange
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInlScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inl
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInrScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inr
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `AlgebraicGeometry.isCompl_range_inl_inr`：isCompl_range_inl_inr : IsCompl
 (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.range (coprod.inr : Y ⟶ X ⨿ Y))
-/
lemma isCompl_opensRange_inl_inr :
    IsCompl (coprod.inl : X ⟶ X ⨿ Y).opensRange (coprod.inr : Y ⟶ X ⨿ Y).opensRange := by
  convert! isCompl_range_inl_inr X Y
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

@[simp]
/-
**AlgebraicGeometry.inl_ne_inr** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：inl_ne_inr (x : X) (y : Y) : (coprod.inl : X ⟶ X ⨿ Y) x != (coprod.inr : Y
 ⟶ X ⨿ Y) y
参数：x : X；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用引理 `AlgebraicGeometry.isCompl_range_inl_inr`：isCompl_range_inl_inr : IsCompl
 (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.range (coprod.inr : Y ⟶ X ⨿ Y))
-/
lemma inl_ne_inr (x : X) (y : Y) : (coprod.inl : X ⟶ X ⨿ Y) x ≠ (coprod.inr : Y ⟶ X ⨿ Y) y :=
  Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr X Y).disjoint ⟨x, rfl⟩ ⟨y, rfl⟩

@[simp]
/-
**AlgebraicGeometry.inr_ne_inl** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：inr_ne_inl (x : X) (y : Y) : (coprod.inr : Y ⟶ X ⨿ Y) y != (coprod.inl : X
 ⟶ X ⨿ Y) x
参数：x : X；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `AlgebraicGeometry.inl_ne_inr`：inl_ne_inr (x : X) (y : Y) : (coprod.inl :
 X ⟶ X ⨿ Y) x != (coprod.inr : Y ⟶ X ⨿ Y) y
-/
lemma inr_ne_inl (x : X) (y : Y) : (coprod.inr : Y ⟶ X ⨿ Y) y ≠ (coprod.inl : X ⟶ X ⨿ Y) x :=
  (inl_ne_inr _ _ _ _).symm

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union -/
noncomputable
/-
**AlgebraicGeometry.coprodMk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：coprodMk : X oplus Y ≃ₜ (X ⨿ Y : Scheme.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodMk : X ⊕ Y ≃ₜ (X ⨿ Y : Scheme.{u}) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).symm ≪≫
    PreservesColimitPair.iso Scheme.forgetToTop X Y)

@[simp]
/-
**AlgebraicGeometry.coprodMk_inl** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：coprodMk_inl (x : X) : coprodMk X Y (.inl x) = (coprod.inl : X ⟶ X ⨿ Y) x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv_assoc`：∀ {J : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryT
heory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprodComparison_inl`：coprodComparison_inl : copro
d.inl ≫ coprodComparison F A B = F.map coprod.inl
-/
lemma coprodMk_inl (x : X) :
    coprodMk X Y (.inl x) = (coprod.inl : X ⟶ X ⨿ Y) x := by
  change ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inl Scheme.forgetToTop

@[simp]
/-
**AlgebraicGeometry.coprodMk_inr** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：coprodMk_inr (x : Y) : coprodMk X Y (.inr x) = (coprod.inr : Y ⟶ X ⨿ Y) x
参数：x : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv_assoc`：∀ {J : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryT
heory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprodComparison_inr`：coprodComparison_inr : copro
d.inr ≫ coprodComparison F A B = F.map coprod.inr
-/
lemma coprodMk_inr (x : Y) :
    coprodMk X Y (.inr x) = (coprod.inr : Y ⟶ X ⨿ Y) x := by
  change ((TopCat.binaryCofan X Y).inr ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inr x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inr Scheme.forgetToTop

set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the coproduct of two schemes. -/
noncomputable
/-
**AlgebraicGeometry.coprodOpenCover.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodOpenCover.{w} : (X ⨿ Y).OpenCover where
  I₀ := PUnit.{w + 1} ⊕ PUnit.{w + 1}
  X x := x.elim (fun _ ↦ X) (fun _ ↦ Y)
  f x := x.rec (fun _ ↦ coprod.inl) (fun _ ↦ coprod.inr)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun x ↦ x.rec (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)⟩
    use ((coprodMk X Y).symm x).elim (fun _ ↦ Sum.inl .unit) (fun _ ↦ Sum.inr .unit)
    obtain ⟨x, rfl⟩ := (coprodMk X Y).surjective x
    simp only [Sum.elim_inl, Sum.elim_inr, Set.mem_range]
    rw [Homeomorph.symm_apply_apply]
    obtain (x | x) := x
    · simp only [Sum.elim_inl, coprodMk_inl, exists_apply_eq_apply]
    · simp only [Sum.elim_inr, coprodMk_inr, exists_apply_eq_apply]

-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/-- If `X` and `Y` are open disjoint and covering open subschemes of `S`,
`S` is the disjoint union of `X` and `Y`. -/
/-
**AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：nonempty_isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}} (f : X ⟶ 
S) (g : Y ⟶ S) [IsOpenImmersion f] [IsOpenImmersion g] (hf : IsCompl f.opensRang
e g.opensRange) : Nonempty (IsColimit <| BinaryCofan.mk f g)
参数：f : X ⟶ S；g : Y ⟶ S；hf : IsCompl f.opensRange g.opensRange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.nonempty_isColimit_cofanMk_of`：nonempty_isColimit_cofa
nMk_of [Small.{u} σ] {X : σ -> Scheme.{u}} {S : Scheme.{u}} (f : forall i, X i ⟶
 S) [forall i, IsOpenImmersion (f i)]…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x

--- 原说明 ---
If `X` and `Y` are open disjoint and covering open subschemes of `S`,
`S` is the disjoint union of `X` and `Y`.
-/
lemma nonempty_isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : IsCompl f.opensRange g.opensRange) :
    Nonempty (IsColimit <| BinaryCofan.mk f g) := by
  let c' : Cofan fun j ↦ (WalkingPair.casesOn j X Y : Scheme.{u}) :=
    .mk S fun j ↦ WalkingPair.casesOn j f g
  let i : BinaryCofan.mk f g ≅ c' := Cofan.ext (Iso.refl _) (by rintro (b | b) <;> rfl)
  refine ⟨IsColimit.ofIsoColimit (Nonempty.some ?_) i.symm⟩
  let fi (j : WalkingPair) : WalkingPair.casesOn j X Y ⟶ S := WalkingPair.casesOn j f g
  convert! nonempty_isColimit_cofanMk_of fi _ _
  · intro i
    cases i <;> (simp [fi]; infer_instance)
  · simpa [← WalkingPair.equivBool.symm.iSup_comp, iSup_bool_eq, ← codisjoint_iff] using hf.2
  · intro i j hij
    match i, j with
    | .left, .right => simpa [fi] using hf.1
    | .right, .left => simpa [fi] using hf.1.symm
/-
**AlgebraicGeometry.isPullback_inl_inl_coprodMap** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isPullback_inl_inl_coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y 
⟶ Y') : IsPullback f coprod.inl coprod.inl (coprod.map f g)
参数：f : X ⟶ X'；g : Y ⟶ Y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isPullback`：isPullback {U V X Y : Sche
me.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion iU] [
IsOpenImmersion iV] (H : iU ≫ f = …
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInlScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inl
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用引理 `AlgebraicGeometry.coprodMk_inl`：coprodMk_inl (x : X) : coprodMk X Y (.in
l x) = (coprod.inl : X ⟶ X ⨿ Y) x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用引理 `AlgebraicGeometry.isCompl_range_inl_inr`：isCompl_range_inl_inr : IsCompl
 (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.range (coprod.inr : Y ⟶ X ⨿ Y))
· 使用引理 `AlgebraicGeometry.coprodMk_inr`：coprodMk_inr (x : Y) : coprodMk X Y (.in
r x) = (coprod.inr : Y ⟶ X ⨿ Y) x
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
-/
lemma isPullback_inl_inl_coprodMap {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback f coprod.inl coprod.inl (coprod.map f g) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨(x | x), rfl⟩ := (coprodMk _ _).surjective x
    · rw [← SetLike.mem_coe]; simp -- TODO : add `Scheme.Hom.mem_opensRange`
    · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_map] at hxy
      cases Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr _ _).1 ⟨y, rfl⟩ ⟨_, rfl⟩ hxy
  · rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isPullback_inr_inr_coprodMap** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isPullback_inr_inr_coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y 
⟶ Y') : IsPullback g coprod.inr coprod.inr (coprod.map f g)
参数：f : X ⟶ X'；g : Y ⟶ Y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `AlgebraicGeometry.isPullback_inl_inl_coprodMap`：isPullback_inl_inl_copro
dMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback f coprod.in
l coprod.inl (coprod.map f g)
· 使用定理 `AlgebraicGeometry.instHasColimitsOfShapeDiscreteSchemeOfSmall`：∀ {σ : Ty
pe v} [Small.{u, v} σ],   CategoryTheory.Limits.HasColimitsOfShape (CategoryTheo
ry.Discrete σ) AlgebraicGeometry.Scheme
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.coprod.braiding_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts 
C]   (P Q : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
-/
lemma isPullback_inr_inr_coprodMap {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback g coprod.inr coprod.inr (coprod.map f g) :=
  (isPullback_inl_inl_coprodMap g f).of_iso (.refl _) (.refl _) (coprod.braiding _ _)
    (coprod.braiding _ _) (by simp) (by simp) (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinitaryExtensive Scheme where
  hasFiniteCoproducts.out := inferInstance
  van_kampen' {X Y} c hc := by
    suffices IsVanKampenColimit (BinaryCofan.mk (P := X ⨿ Y) coprod.inl coprod.inr) from
      this.of_iso (hc.uniqueUpToIso (coprodIsCoprod _ _)).symm
    refine BinaryCofan.isVanKampen_mk _ _ (fun _ _ ↦ coprodIsCoprod _ _) _
      (fun _ _ ↦ pullbackIsPullback _ _) ?_ ?_
    · intro X' Y' αX αY f h₁ h₂
      have h₁' (x : _) := congr($h₁ x).symm
      have h₂' (x : _) := congr($h₂ x).symm
      dsimp at h₁ h₂ h₁' h₂'
      refine ⟨(IsOpenImmersion.isPullback _ _ _ _ h₁.symm ?_).flip,
        (IsOpenImmersion.isPullback _ _ _ _ h₂.symm ?_).flip⟩ <;>
        ext x <;> obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x <;> simp_all
    · dsimp
      refine fun {Z} f ↦ (nonempty_isColimit_binaryCofanMk_of_isCompl _ _ ?_).some
      rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
      convert! (isCompl_range_inl_inr X Y).map (CompleteLatticeHom.setPreimage f)
      simp [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]

variable {X Y}

/-- The sections on coproducts of schemes are the (categorical) product of the sections
on the components -/
/-
**AlgebraicGeometry.Scheme.coprodPresheafObjIso** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (U : (X ⨿ Y).Opens) →     (X ⨿ Y).pre
sheaf.obj (Opposite.op U) ≅       X.presheaf.obj (Opposite.op ((TopologicalSpace
.Opens.map CategoryTheory.Limits.coprod.inl.base).obj U)) ⨯         Y.presheaf.o
bj (Opposite.op ((TopologicalSpace.Opens.map CategoryTheory.Limits.coprod.inr.ba
se).obj U))
参数：U : (X ⨿ Y).Opens；X ⨿ Y；Opposite.op U；Opposite.op ((TopologicalSpace.Opens.ma
p CategoryTheory.Limits.coprod.inl.base).obj U)；Opposite.op ((TopologicalSpace.O
pens.map CategoryTheory.Limits.coprod.inr.base).obj U)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInlScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inl
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInrScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inr

--- 原说明 ---
The sections on coproducts of schemes are the (categorical) product of the secti
ons
on the components
-/
noncomputable def Scheme.coprodPresheafObjIso (U : (X ⨿ Y).Opens) :
    Γ(X ⨿ Y, U) ≅ Γ(X, coprod.inl (C := Scheme) ⁻¹ᵁ U) ⨯ Γ(Y, coprod.inr (C := Scheme) ⁻¹ᵁ U) :=
  letI ι₁ : X ⟶ X ⨿ Y := coprod.inl
  letI ι₂ : Y ⟶ X ⨿ Y := coprod.inr
  haveI h₁ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊔ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = U := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_sup_right, (isCompl_opensRange_inl_inr X Y).sup_eq_top, top_inf_eq]
  haveI h₂ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊓ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = ⊥ := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_inf_distrib_right, (isCompl_opensRange_inl_inr X Y).inf_eq_bot, bot_inf_eq]
  (X ⨿ Y).presheaf.mapIso (eqToIso h₁).op ≪≫
    ((X ⨿ Y).sheaf.isProductOfDisjoint _ _ h₂).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    prod.mapIso (ι₁.appIso _) (ι₂.appIso _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.coprodPresheafObjIso_hom_fst** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (U : (X ⨿ Y).Opens),   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeometry.Scheme.coprodPresheafObjIso U).hom       C
ategoryTheory.Limits.prod.fst =     AlgebraicGeometry.Scheme.Hom.app CategoryThe
ory.Limits.coprod.inl U
参数：U : (X ⨿ Y).Opens；AlgebraicGeometry.Scheme.coprodPresheafObjIso U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInlScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inl
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInrScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inr
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp_assoc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Ca
tegoryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.coprodPresheafObjIso_hom_fst (U : (X ⨿ Y).Opens) :
    (coprodPresheafObjIso U).hom ≫ prod.fst = (coprod.inl (C := Scheme)).app U := by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.coprodPresheafObjIso_hom_snd** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (U : (X ⨿ Y).Opens),   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeometry.Scheme.coprodPresheafObjIso U).hom       C
ategoryTheory.Limits.prod.snd =     AlgebraicGeometry.Scheme.Hom.app CategoryThe
ory.Limits.coprod.inr U
参数：U : (X ⨿ Y).Opens；AlgebraicGeometry.Scheme.coprodPresheafObjIso U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInlScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inl
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInrScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inr
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp_assoc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Ca
tegoryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.coprodPresheafObjIso_hom_snd (U : (X ⨿ Y).Opens) :
    (coprodPresheafObjIso U).hom ≫ prod.snd = (coprod.inr (C := Scheme)).app U := by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The map `Spec R ⨿ Spec S ⟶ Spec (R × S)`.
This is an isomorphism as witnessed by an `IsIso` instance provided below. -/
noncomputable
/-
**AlgebraicGeometry.coprodSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：coprodSpec : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of <| R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodSpec : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of <| R × S) :=
  coprod.desc (Spec.map (CommRingCat.ofHom <| RingHom.fst _ _))
    (Spec.map (CommRingCat.ofHom <| RingHom.snd _ _))

@[simp, reassoc]
/-
**AlgebraicGeometry.coprodSpec_inl** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：coprodSpec_inl : coprod.inl ≫ coprodSpec R S = Spec.map (CommRingCat.ofHom
 <| RingHom.fst R S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma coprodSpec_inl : coprod.inl ≫ coprodSpec R S =
    Spec.map (CommRingCat.ofHom <| RingHom.fst R S) :=
  coprod.inl_desc _ _

@[simp, reassoc]
/-
**AlgebraicGeometry.coprodSpec_inr** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：coprodSpec_inr : coprod.inr ≫ coprodSpec R S = Spec.map (CommRingCat.ofHom
 <| RingHom.snd R S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma coprodSpec_inr : coprod.inr ≫ coprodSpec R S =
    Spec.map (CommRingCat.ofHom <| RingHom.snd R S) :=
  coprod.inr_desc _ _
/-
**AlgebraicGeometry.coprodSpec_coprodMk** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：coprodSpec_coprodMk (x) : coprodSpec R S (coprodMk _ _ x) = (PrimeSpectrum
.primeSpectrumProd R S).symm x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.coprodMk_inl`：coprodMk_inl (x : X) : coprodMk X Y (.in
l x) = (coprod.inl : X ⟶ X ⨿ Y) x
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `AlgebraicGeometry.coprodMk_inr`：coprodMk_inr (x : Y) : coprodMk X Y (.in
r x) = (coprod.inr : Y ⟶ X ⨿ Y) x
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
lemma coprodSpec_coprodMk (x) :
    coprodSpec R S (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x := by
  apply PrimeSpectrum.ext
  obtain (x | x) := x <;>
    simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
      coprodSpec, coprod.inl_desc, coprod.inr_desc]
  · change Ideal.comap _ _ = x.asIdeal.prod ⊤
    ext; simp [Ideal.prod, CommRingCat.ofHom]
  · change Ideal.comap _ _ = Ideal.prod ⊤ x.asIdeal
    ext; simp [Ideal.prod, CommRingCat.ofHom]
/-
**AlgebraicGeometry.coprodSpec_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：coprodSpec_apply (x) : coprodSpec R S x = (PrimeSpectrum.primeSpectrumProd
 R S).symm ((coprodMk _ _).symm x)
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.coprodSpec_coprodMk`：coprodSpec_coprodMk (x) : coprodS
pec R S (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
-/
lemma coprodSpec_apply (x) :
    coprodSpec R S x = (PrimeSpectrum.primeSpectrumProd R S).symm ((coprodMk _ _).symm x) := by
  rw [← coprodSpec_coprodMk, Homeomorph.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isIso_stalkMap_coprodSpec** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：isIso_stalkMap_coprodSpec (x) : IsIso ((coprodSpec R S).stalkMap x)
参数：x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.coprodMk_inl`：coprodMk_inl (x : X) : coprodMk X Y (.in
l x) = (coprod.inl : X ⟶ X ⨿ Y) x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用引理 `AlgebraicGeometry.coprodSpec_inl`：coprodSpec_inl : coprod.inl ≫ coprodSp
ec R S = Spec.map (CommRingCat.ofHom <| RingHom.fst R S)
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInlScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inl
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_congr_hom`：stalkMap_congr_hom (f g
 : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = (Y.presheaf.stalkCongr (.of_eq 
<| hfg ▸ rfl)).hom ≫ g.stalkMap x
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isLocalization`：∀ {R S : Type u_1} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (f : R) [IsLoca
lization.Away f S],   AlgebraicGeometry.I…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `AlgebraicGeometry.coprodMk_inr`：coprodMk_inr (x : Y) : coprodMk X Y (.in
r x) = (coprod.inr : Y ⟶ X ⨿ Y) x
· 使用引理 `AlgebraicGeometry.coprodSpec_inr`：coprodSpec_inr : coprod.inr ≫ coprodSp
ec R S = Spec.map (CommRingCat.ofHom <| RingHom.snd R S)
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionInrScheme`：∀ (X Y : AlgebraicGeomet
ry.Scheme), AlgebraicGeometry.IsOpenImmersion CategoryTheory.Limits.coprod.inr
-/
lemma isIso_stalkMap_coprodSpec (x) :
    IsIso ((coprodSpec R S).stalkMap x) := by
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
  · have := Scheme.Hom.stalkMap_comp coprod.inl (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq,
      Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inl R S)] at this
    rw [coprodMk_inl, ← this]
    let := (RingHom.fst R S).toAlgebra
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst R S))) :=
      IsOpenImmersion.of_isLocalization (1, 0)
    infer_instance
  · have := Scheme.Hom.stalkMap_comp coprod.inr (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq,
      Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inr R S)] at this
    rw [coprodMk_inr, ← this]
    let := (RingHom.snd R S).toAlgebra
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd R S))) :=
      IsOpenImmersion.of_isLocalization (0, 1)
    infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (coprodSpec R S) := by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, isIso_stalkMap_coprodSpec R S⟩
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec (.of <| R × S)) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S : CommRingCat.{u}ᵒᵖ) : IsIso (coprodComparison Scheme.Spec R S) := by
  obtain ⟨R⟩ := R; obtain ⟨S⟩ := S
  have : coprodComparison Scheme.Spec (.op R) (.op S) ≫ (Spec.map
    ((limit.isoLimitCone ⟨_, CommRingCat.prodFanIsLimit R S⟩).inv ≫
      (opProdIsoCoprod R S).unop.inv)) = coprodSpec R S := by
    ext1
    · rw [coprodComparison_inl_assoc, coprodSpec, coprod.inl_desc, Scheme.Spec_map,
        ← Spec.map_comp, Category.assoc, Iso.unop_inv, opProdIsoCoprod_inv_inl,
        limit.isoLimitCone_inv_π]
      rfl
    · rw [coprodComparison_inr_assoc, coprodSpec, coprod.inr_desc, Scheme.Spec_map,
        ← Spec.map_comp, Category.assoc, Iso.unop_inv, opProdIsoCoprod_inv_inr,
        limit.isoLimitCone_inv_π]
      rfl
  rw [(IsIso.eq_comp_inv _).mpr this]
  infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfShape (Discrete WalkingPair) Scheme.Spec.{u} :=
  ⟨fun {_} ↦
    have (X Y : CommRingCat.{u}ᵒᵖ) := PreservesColimitPair.of_iso_coprod_comparison Scheme.Spec X Y
    preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) Scheme.Spec.{u} := by
  have : IsEmpty (Scheme.Spec.obj (⊥_ CommRingCatᵒᵖ)) :=
    @Function.isEmpty _ _ spec_punit_isEmpty (Scheme.Spec.mapIso
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom
  have := preservesInitial_of_iso Scheme.Spec (asIso (initial.to _))
  exact preservesColimitsOfShape_pempty_of_preservesInitial _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Finite J] : PreservesColimitsOfShape (Discrete J) Scheme.Spec.{u} :=
  PreservesFiniteCoproducts.of_preserves_binary_and_initial _ _

/-- The canonical map `∐ Spec Rᵢ ⟶ Spec (Π Rᵢ)`.
This is an isomorphism when the product is finite. -/
noncomputable
/-
**AlgebraicGeometry.sigmaSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：sigmaSpec (R : ι -> CommRingCat) : (∐ fun i => Spec (R i)) ⟶ Spec (.of <| 
Π i, R i)
参数：R : ι -> CommRingCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sigmaSpec (R : ι → CommRingCat) : (∐ fun i ↦ Spec (R i)) ⟶ Spec (.of <| Π i, R i) :=
  Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)))

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_sigmaSpec (R : ι → CommRingCat) (i) :
    Sigma.ι _ i ≫ sigmaSpec R = Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) :=
  Sigma.ι_desc _ _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i) (R : ι → Type _) [∀ i, CommRing (R i)] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i))) := by
  classical
  let := (Pi.evalRingHom R i).toAlgebra
  have : IsLocalization.Away (Function.update (β := R) 0 i 1) (R i) := by
    apply IsLocalization.away_of_isIdempotentElem_of_mul
    · ext j; by_cases h : j = i <;> aesop
    · intro x y
      constructor
      · intro e; ext j; by_cases h : j = i <;> aesop
      · intro e; simpa using! congr_fun e i
    · exact Function.surjective_eval _
  exact IsOpenImmersion.of_isLocalization (Function.update 0 i 1)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : ι → CommRingCat.{u}) : IsOpenImmersion (sigmaSpec R) := by
  classical
  apply isOpenImmersion_sigmaDesc
  intro ix iy h
  refine Set.disjoint_iff_forall_ne.mpr ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ e
  have : DFinsupp.single (β := (R ·)) iy 1 iy ∈ y.asIdeal :=
    (PrimeSpectrum.ext_iff.mp e).le (x := DFinsupp.single iy 1)
      (show DFinsupp.single (β := (R ·)) iy 1 ix ∈ x.asIdeal by simp [h.symm])
  simp [← Ideal.eq_top_iff_one, y.2.ne_top] at this

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite ι] (R : ι → CommRingCat.{u}) : IsIso (sigmaSpec R) := by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1
    simp; rfl
  rw [this]
  infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite σ] [∀ i, IsAffine (g i)] : IsAffine (∐ g) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  have (i : _) : IsAffine ((g ∘ e.symm) i) := by dsimp; infer_instance
  exact IsAffine.of_isIso ((Sigma.reindex e.symm g).inv ≫
    (Sigma.mapIso (fun i ↦ Scheme.isoSpec _)).hom ≫ sigmaSpec _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAffine X] [IsAffine Y] : IsAffine (X ⨿ Y) :=
  .of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/-- A version with more restrictive universes. See `IsAffineOpen.iSup_of_disjoint`. -/
/-
**AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint_aux** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version with more restrictive universes. See `IsAffineOpen.iSup_of_disjoint`.
-/
private lemma IsAffineOpen.iSup_of_disjoint_aux [Finite ι] {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : Pairwise (Disjoint on U)) :
    IsAffineOpen (iSup U) := by
  have := isOpenImmersion_sigmaDesc _ (fun i ↦ (U i).ι)
    (fun i j e ↦ by convert hU' e; simp [← Opens.coe_disjoint])
  convert! isAffineOpen_opensRange (Sigma.desc fun i ↦ (U i).ι)
  · ext
    simp [(sigmaMk _).symm.exists_congr_left, ← Scheme.Hom.comp_apply, Scheme.Opens.exists_toScheme]
  · have (i : _) : IsAffine _ := hU i
    infer_instance

open scoped Function in
/-
**AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {σ : Type v} {X : AlgebraicGeometry.Scheme} [Finite σ] {U : σ → X.Opens}
,   (∀ (i : σ), AlgebraicGeometry.IsAffineOpen (U i)) →     Pairwise (Function.o
nFun Disjoint U) → AlgebraicGeometry.IsAffineOpen (iSup U)
参数：∀ (i : σ), AlgebraicGeometry.IsAffineOpen (U i)；Function.onFun Disjoint U；iSu
p U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.equiv_small`：∀ {α : Type v} [self : Small.{w, v} α], ∃ S, Nonempty
 (α ≃ S)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Limits.0.AlgebraicGeometry.IsAffineOp
en.iSup_of_disjoint_aux`：∀ {ι : Type u} {X : AlgebraicGeometry.Scheme} [Finite ι
] {U : ι → X.Opens},   (∀ (i : ι), AlgebraicGeometry.IsAffineOpen (U i)) →     P
airwi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma IsAffineOpen.iSup_of_disjoint [Finite σ] {U : σ → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : Pairwise (Disjoint on U)) :
    IsAffineOpen (iSup U) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  rw [← e.symm.iSup_congr fun _ ↦ rfl]
  exact .iSup_of_disjoint_aux (by simp [*]) fun i j h ↦ hU' (e.symm.injective.ne h)

open scoped Function in
/-
**AlgebraicGeometry.IsAffineOpen.biSup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {σ : Type v} {X : AlgebraicGeometry.Scheme} {s : Set σ},   s.Finite →   
  ∀ {U : σ → X.Opens},       (∀ i ∈ s, AlgebraicGeometry.IsAffineOpen (U i)) →  
       s.Pairwise (Function.onFun Disjoint U) → AlgebraicGeometry.IsAffineOpen (
⨆ i ∈ s, U i)
参数：∀ i ∈ s, AlgebraicGeometry.IsAffineOpen (U i)；Function.onFun Disjoint U；⨆ i ∈
 s, U i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint`：∀ {σ : Type v} {X : Alg
ebraicGeometry.Scheme} [Finite σ] {U : σ → X.Opens},   (∀ (i : σ), AlgebraicGeom
etry.IsAffineOpen (U i)) →     Pairwi…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsAffineOpen.biSup_of_disjoint {s : Set σ} (hs : s.Finite)
    {U : σ → X.Opens} (hU : ∀ i ∈ s, IsAffineOpen (U i)) (hU' : s.Pairwise (Disjoint on U)) :
    IsAffineOpen (⨆ i ∈ s, U i) := by
  rw [← iSup_subtype'']
  have := hs.to_subtype
  exact .iSup_of_disjoint (by simpa) fun i j e ↦ hU' i.2 j.2 (by aesop)
/-
**AlgebraicGeometry.IsAffineOpen.sup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens},   AlgebraicGeometry.IsAf
fineOpen U →     AlgebraicGeometry.IsAffineOpen V → Disjoint U V → AlgebraicGeom
etry.IsAffineOpen (U ⊔ V)
参数：U ⊔ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint`：∀ {σ : Type v} {X : Alg
ebraicGeometry.Scheme} [Finite σ] {U : σ → X.Opens},   (∀ (i : σ), AlgebraicGeom
etry.IsAffineOpen (U i)) →     Pairwi…
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsAffineOpen.sup_of_disjoint {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (H : Disjoint U V) :
    IsAffineOpen (U ⊔ V) := by
  convert!
    iSup_of_disjoint (U := fun i : Unit ⊕ Unit ↦ i.elim (fun _ ↦ U) (fun _ ↦ V)) (by simp_all)
      (by simp_all [_root_.Pairwise, Unique.forall_iff, ← Opens.coe_disjoint, disjoint_comm])
  aesop
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Finite X] [DiscreteTopology X] : IsAffine X :=
  have : IsAffineOpen (⨆ (x : X), (⟨{x}, isOpen_discrete _⟩ : X.Opens)) :=
    .iSup_of_disjoint (fun i ↦ .of_subsingleton Set.subsingleton_singleton)
      fun i j e ↦ by simpa [← TopologicalSpace.Opens.coe_disjoint]
  have : IsAffine (⊤ : X.Opens).toScheme := show IsAffineOpen _ by convert! this; ext; simp
  .of_isIso X.topIso.inv

end Coproduct

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (i : WalkingPair) : Mono ((span f g ⋙ Scheme.forget).map (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using! f.isOpenEmbedding.injective
  · simpa using! g.isOpenEmbedding.injective
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    {i j : WalkingSpan} (t : i ⟶ j) : IsOpenImmersion ((span f g).map t) := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa

-- Test that instances on locally directed colimits fire correctly.
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个示例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] : HasPushout f g :=
  inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory Scheme := .ofHasFiniteProducts
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory Scheme := .ofCartesianMonoidalCategory

section IsAffine

/-
**AlgebraicGeometry.Scheme.isAffine_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：∀ {I : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} I] {D : Catego
ryTheory.Functor I AlgebraicGeometry.Scheme}   (c : CategoryTheory.Limits.Cone D
) (hc : CategoryTheory.Limits.IsLimit c)   [∀ (i : I), AlgebraicGeometry.IsAffin
e (D.obj i)], AlgebraicGeometry.IsAffine c.pt
参数：c : CategoryTheory.Limits.Cone D；hc : CategoryTheory.Limits.IsLimit c；i : I；D
.obj i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma Scheme.isAffine_of_isLimit {I : Type*} [Category* I] {D : I ⥤ Scheme.{u}}
    (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)] :
    IsAffine c.pt := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : c.pt ≅ Spec Γ(c.pt, ⊤) := hc.conePointUniqueUpToIso ((IsLimit.postcomposeHomEquiv
    (asIso α).symm _).symm (isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc))
  exact .of_isIso this.hom

end IsAffine

end AlgebraicGeometry

