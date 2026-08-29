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

/--
Definition of `specZIsTerminal` / `specZIsTerminal` 的定义

English:
definition specZIsTerminal
  signature: : IsTerminal (Spec <| .of Int)
  body: @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

中文:
定义 specZIsTerminal
  签名: : 是终止 (Spec <| .of 整数)
  定义体: @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

Depends on / 依赖: CommRingCat, CommRingCat.zIsInitial, IsTerminal, IsTerminal.isTerminalObj, Scheme, Scheme.Spec, isTerminalObj, terminalOpOfInitial, zIsInitial
-/
noncomputable def specZIsTerminal : IsTerminal (Spec <| .of Int) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

/--
Definition of `specULiftZIsTerminal` / `specULiftZIsTerminal` 的定义

English:
definition specULiftZIsTerminal
  signature: : IsTerminal (Spec <| .of <| ULift.{u} Int)
  body: @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.isInitial)

中文:
定义 specULiftZIsTerminal
  签名: : 是终止 (Spec <| .of <| 类型层提升.{u} 整数)
  定义体: @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.isInitial)

Depends on / 依赖: CommRingCat, CommRingCat.isInitial, IsTerminal, IsTerminal.isTerminalObj, Scheme, Scheme.Spec, isInitial, isTerminalObj, terminalOpOfInitial
-/
noncomputable def specULiftZIsTerminal : IsTerminal (Spec <| .of <| ULift.{u} Int) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.isInitial)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTerminal Scheme
  body: hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

中文:
实例 :
  签名: 有终止 概形
  定义体: hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

Depends on / 依赖: Scheme, Scheme.Spec, hasTerminal_of_hasTerminal_of_preservesLimit
-/
instance : HasTerminal Scheme :=
  hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAffine (⊤_ Scheme.{u})
  body: .of_isIso (PreservesTerminal.iso Scheme.Spec).inv

中文:
实例 :
  签名: 是仿射 (⊤_ 概形.{u})
  定义体: .of_isIso (PreservesTerminal.iso Scheme.Spec).inv

Depends on / 依赖: PreservesTerminal, PreservesTerminal.iso, Scheme, Scheme.Spec, of_isIso
-/
instance : IsAffine (⊤_ Scheme.{u}) :=
  .of_isIso (PreservesTerminal.iso Scheme.Spec).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteLimits Scheme
  body: hasFiniteLimits_of_hasTerminal_and_pullbacks

中文:
实例 :
  签名: 有有限极限 概形
  定义体: hasFiniteLimits_of_hasTerminal_and_pullbacks

Depends on / 依赖: hasFiniteLimits_of_hasTerminal_and_pullbacks
-/
instance : HasFiniteLimits Scheme :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance (X : Scheme.{u}) : X.Over (⊤_ _) := ⟨terminal.from _⟩
instance {X Y : Scheme.{u}} [X.Over (⊤_ Scheme)] [Y.Over (⊤_ Scheme)] (f : X ⟶ Y) :
    @Scheme.Hom.IsOver _ _ f (⊤_ Scheme) ‹_› ‹_› := ⟨Subsingleton.elim _ _⟩

instance {X : Scheme} : Subsingleton (X.Over (⊤_ Scheme)) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by simp [Subsingleton.elim a b]⟩

section Initial

/-- The map from the empty scheme. -/
@[simps]
/--
Definition of `Scheme.emptyTo` / `Scheme.emptyTo` 的定义

English:
definition Scheme.emptyTo
  signature: (X : Scheme.{u})
  body: ⟨{ base := TopCat.ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩
      c := { app := fun _ => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩

@[ext]

中文:
定义 概形.emptyTo
  签名: (X : 概形.{u})
  定义体: ⟨{ base := TopCat.ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩
      c := { app := fun _ => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩

@[ext]

Depends on / 依赖: CommRingCat, CommRingCat.punitIsTerminal.from, PEmpty, PEmpty.elim, TopCat, TopCat.ofHom, fun_prop, punitIsTerminal
-/
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{ base := TopCat.ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩
      c := { app := fun _ => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩

@[ext]
/--
theorem `Scheme.empty_ext` / 定理 `Scheme.empty_ext`

English:
theorem Scheme.empty_ext
  given: {X : Scheme.{u}} (f g : ∅ ⟶ X)
  statement: f = g
  proof: Scheme.Hom.ext' (Subsingleton.elim (α := ∅ ⟶ _) _ _)

中文:
定理 概形.empty_ext
  条件: {X : 概形.{u}} (f g : ∅ ⟶ X)
  结论: f = g
  证明: Scheme.Hom.ext' (Subsingleton.elim (α := ∅ ⟶ _) _ _)

Depends on / 依赖: Scheme, Scheme.Hom.ext, Subsingleton, Subsingleton.elim
-/
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g :=
  Scheme.Hom.ext' (Subsingleton.elim (α := ∅ ⟶ _) _ _)

/--
theorem `Scheme.eq_emptyTo` / 定理 `Scheme.eq_emptyTo`

English:
theorem Scheme.eq_emptyTo
  given: {X : Scheme.{u}} (f : ∅ ⟶ X)
  statement: f = Scheme.emptyTo X
  proof: Scheme.empty_ext f (Scheme.emptyTo X)

中文:
定理 概形.eq_emptyTo
  条件: {X : 概形.{u}} (f : ∅ ⟶ X)
  结论: f = 概形.emptyTo X
  证明: Scheme.empty_ext f (Scheme.emptyTo X)

Depends on / 依赖: Scheme, Scheme.emptyTo, Scheme.empty_ext, emptyTo, empty_ext
-/
theorem Scheme.eq_emptyTo {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.emptyTo X :=
  Scheme.empty_ext f (Scheme.emptyTo X)

/--
Instance `Scheme.hom_unique_of_empty_source` / 实例 `Scheme.hom_unique_of_empty_source`

English:
instance Scheme.hom_unique_of_empty_source
  signature: (X : Scheme.{u})
  body: ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

中文:
实例 概形.hom_unique_of_empty_source
  签名: (X : 概形.{u})
  定义体: ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

Depends on / 依赖: Scheme, Scheme.emptyTo, Scheme.empty_ext, emptyTo, empty_ext
-/
instance Scheme.hom_unique_of_empty_source (X : Scheme.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

/--
Definition of `emptyIsInitial` / `emptyIsInitial` 的定义

English:
definition emptyIsInitial
  signature: : IsInitial (∅ : Scheme.{u})
  body: IsInitial.ofUnique _

@[simp]

中文:
定义 emptyIsInitial
  签名: : IsInitial (∅ : 概形.{u})
  定义体: IsInitial.ofUnique _

@[simp]

Depends on / 依赖: IsInitial, IsInitial.ofUnique, ofUnique
-/
def emptyIsInitial : IsInitial (∅ : Scheme.{u}) :=
  IsInitial.ofUnique _

@[simp]
/--
theorem `emptyIsInitial_to` / 定理 `emptyIsInitial_to`

English:
theorem emptyIsInitial_to
  statement: emptyIsInitial.to = Scheme.emptyTo
  proof: rfl

中文:
定理 emptyIsInitial_to
  结论: emptyIsInitial.to = 概形.emptyTo
  证明: rfl
-/
theorem emptyIsInitial_to : emptyIsInitial.to = Scheme.emptyTo :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty (∅ : Scheme.{u})
  body: show IsEmpty PEmpty by infer_instance

中文:
实例 :
  签名: 是空 (∅ : 概形.{u})
  定义体: show IsEmpty PEmpty by infer_instance

Depends on / 依赖: IsEmpty, PEmpty, infer_instance
-/
instance : IsEmpty (∅ : Scheme.{u}) :=
  show IsEmpty PEmpty by infer_instance

/--
Instance `spec_punit_isEmpty` / 实例 `spec_punit_isEmpty`

English:
instance spec_punit_isEmpty
  signature: : IsEmpty (Spec <| .of PUnit.{u + 1})
  body: inferInstanceAs IsEmpty (PrimeSpectrum PUnit)

中文:
实例 spec_punit_isEmpty
  签名: : 是空 (Spec <| .of 命题单元.{u + 1})
  定义体: inferInstanceAs IsEmpty (PrimeSpectrum PUnit)

Depends on / 依赖: IsEmpty, PrimeSpectrum
-/
instance spec_punit_isEmpty : IsEmpty (Spec <| .of PUnit.{u + 1}) :=
inferInstanceAs IsEmpty (PrimeSpectrum PUnit)

instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X] : IsOpenImmersion f := by
  apply +allowSynthFailures IsOpenImmersion.of_isIso_stalkMap
  · exact .of_isEmpty (X := X) _
  · intro (i : X); exact isEmptyElim i

instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y] :
    IsIso f := by
  have : IsEmpty X := f.base.hom.1.isEmpty
  have : Epi f.base := by
    rw [TopCat.epi_iff_surjective]; rintro (x : Y)
    exact isEmptyElim x
  apply IsOpenImmersion.isIso

/--
Definition of `isInitialOfIsEmpty` / `isInitialOfIsEmpty` 的定义

English:
definition isInitialOfIsEmpty
  signature: {X : Scheme} [IsEmpty X]
  body: emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

中文:
定义 isInitialOfIsEmpty
  签名: {X : 概形} [是空 X]
  定义体: emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

Depends on / 依赖: emptyIsInitial, emptyIsInitial.ofIso, emptyIsInitial.to
-/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X] : IsInitial X :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

/--
Definition of `specPUnitIsInitial` / `specPUnitIsInitial` 的定义

English:
definition specPUnitIsInitial
  signature: : IsInitial (Spec <| .of PUnit.{u + 1})
  body: emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

@[deprecated (since := "2026-02-08")] alias specPunitIsInitial := specPUnitIsInitial

中文:
定义 specPUnitIsInitial
  签名: : IsInitial (Spec <| .of 命题单元.{u + 1})
  定义体: emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

@[deprecated (since := "2026-02-08")] alias specPunitIsInitial := specPUnitIsInitial

Depends on / 依赖: emptyIsInitial, emptyIsInitial.ofIso, emptyIsInitial.to
-/
noncomputable def specPUnitIsInitial : IsInitial (Spec <| .of PUnit.{u + 1}) :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

@[deprecated (since := "2026-02-08")] alias specPunitIsInitial := specPUnitIsInitial

/--
lemma `isInitial_iff_isEmpty` / 引理 `isInitial_iff_isEmpty`

English:
lemma isInitial_iff_isEmpty
  given: {X : Scheme.{u}}
  statement: Nonempty (IsInitial X) ↔ IsEmpty X
  proof: ⟨fun ⟨h⟩ => (h.uniqueUpToIso specPUnitIsInitial).hom.homeomorph.isEmpty,
    fun _ => ⟨isInitialOfIsEmpty⟩⟩

中文:
引理 isInitial_iff_isEmpty
  条件: {X : 概形.{u}}
  结论: 非空 (IsInitial X) ↔ 是空 X
  证明: ⟨fun ⟨h⟩ => (h.uniqueUpToIso specPUnitIsInitial).hom.homeomorph.isEmpty,
    fun _ => ⟨isInitialOfIsEmpty⟩⟩

Depends on / 依赖: h.uniqueUpToIso, hom.homeomorph.isEmpty, homeomorph, isEmpty, isInitialOfIsEmpty, specPUnitIsInitial, uniqueUpToIso
-/
lemma isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty X :=
  ⟨fun ⟨h⟩ => (h.uniqueUpToIso specPUnitIsInitial).hom.homeomorph.isEmpty,
    fun _ => ⟨isInitialOfIsEmpty⟩⟩

instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X] : IsAffine X :=
  .of_isIso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Spec <| .of PUnit))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasInitial Scheme.{u}
  body: hasInitial_of_unique ∅

中文:
实例 :
  签名: HasInitial 概形.{u}
  定义体: hasInitial_of_unique ∅

Depends on / 依赖: hasInitial_of_unique
-/
instance : HasInitial Scheme.{u} :=
  hasInitial_of_unique ∅

/--
Instance `initial_isEmpty` / 实例 `initial_isEmpty`

English:
instance initial_isEmpty
  signature: : IsEmpty (⊥_ Scheme)
  body: ⟨fun x => ((initial.to Scheme.empty :) x).elim⟩

中文:
实例 initial_isEmpty
  签名: : 是空 (⊥_ 概形)
  定义体: ⟨fun x => ((initial.to Scheme.empty :) x).elim⟩

Depends on / 依赖: Scheme, Scheme.empty, initial, initial.to
-/
instance initial_isEmpty : IsEmpty (⊥_ Scheme) :=
  ⟨fun x => ((initial.to Scheme.empty :) x).elim⟩

/--
theorem `isAffineOpen_bot` / 定理 `isAffineOpen_bot`

English:
theorem isAffineOpen_bot
  given: (X : Scheme)
  statement: IsAffineOpen (⊥ : X.Opens)
  proof: @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))

中文:
定理 isAffineOpen_bot
  条件: (X : 概形)
  结论: 是仿射开集 (⊥ : X.Opens)
  证明: @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))

Depends on / 依赖: IsEmpty, isAffine_of_isEmpty
-/
theorem isAffineOpen_bot (X : Scheme) : IsAffineOpen (⊥ : X.Opens) :=
  @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasStrictInitialObjects Scheme
  body: hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

中文:
实例 :
  签名: 有StrictInitialObjects 概形
  定义体: hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

Depends on / 依赖: hasStrictInitialObjects_of_initial_is_strict, infer_instance
-/
instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

instance {X : Scheme} [IsEmpty X] (U : X.Opens) : Subsingleton Γ(X, U) := by
  obtain rfl : U = ⊥ := Subsingleton.elim _ _; infer_instance

-- This is also true for schemes with two points.
-- But there are non-affine schemes with three points.
/-- This is true in general for finite discrete schemes. See below. -/
instance (priority := low) {X : Scheme.{u}} [Subsingleton X] : IsAffine X := by
  cases isEmpty_or_nonempty X with
  | inl h => infer_instance
  | inr h =>
  obtain ⟨x⟩ := h
  obtain ⟨_, ⟨U, hU : IsAffine _, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  obtain rfl : U = ⊤ := by ext y; simpa [Subsingleton.elim y x]
  exact .of_isIso (Scheme.topIso X).inv

/--
theorem `IsAffineOpen.of_subsingleton` / 定理 `IsAffineOpen.of_subsingleton`

English:
theorem IsAffineOpen.of_subsingleton
  statement: {X : Scheme} {U : X.Opens}
  proof: have : Subsingleton U := hU.coe_sort
  inferInstanceAs (IsAffine _)

中文:
定理 是仿射开集.of_subsingleton
  结论: {X : 概形} {U : X.Opens}
  证明: have : Subsingleton U := hU.coe_sort
  inferInstanceAs (IsAffine _)

Depends on / 依赖: IsAffine, Subsingleton, coe_sort, hU.coe_sort
-/
theorem IsAffineOpen.of_subsingleton {X : Scheme} {U : X.Opens}
    (hU : Set.Subsingleton (U : Set X)) : IsAffineOpen U :=
  have : Subsingleton U := hU.coe_sort
  inferInstanceAs (IsAffine _)

end Initial

section Coproduct

variable {ι : Type u} (f : ι -> Scheme.{u})

variable {σ : Type v} (g : σ -> Scheme.{u})

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{u}
  signature: σ] :

中文:
实例 [Small.{u}
  签名: σ] :
-/
instance [Small.{u} σ] :
    CreatesColimitsOfShape (Discrete σ) Scheme.forgetToLocallyRingedSpace.{u} where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{u}
  signature: σ] : PreservesColimitsOfShape (Discrete σ) Scheme.forgetToTop.{u}
  body: inferInstanceAs (PreservesColimitsOfShape (Discrete σ) (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

中文:
实例 [Small.{u}
  签名: σ] : 保持形状余极限 (离散 σ) 概形.forgetToTop.{u}
  定义体: inferInstanceAs (PreservesColimitsOfShape (Discrete σ) (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

Depends on / 依赖: CommRingCat, Discrete, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, PreservesColimitsOfShape, Scheme, Scheme.forgetToLocallyRingedSpace, SheafedSpace, SheafedSpace.forget, forget, forgetToLocallyRingedSpace, forgetToSheafedSpace
-/
instance [Small.{u} σ] : PreservesColimitsOfShape (Discrete σ) Scheme.forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete σ) (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{u}
  signature: σ] : HasColimitsOfShape (Discrete σ) Scheme.{u}
  body: ⟨fun _ => hasColimit_of_created _ Scheme.forgetToLocallyRingedSpace⟩

中文:
实例 [Small.{u}
  签名: σ] : 有形状余极限 (离散 σ) 概形.{u}
  定义体: ⟨fun _ => hasColimit_of_created _ Scheme.forgetToLocallyRingedSpace⟩

Depends on / 依赖: Scheme, Scheme.forgetToLocallyRingedSpace, forgetToLocallyRingedSpace, hasColimit_of_created
-/
instance [Small.{u} σ] : HasColimitsOfShape (Discrete σ) Scheme.{u} :=
  ⟨fun _ => hasColimit_of_created _ Scheme.forgetToLocallyRingedSpace⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sigmaι_eq_iff` / 引理 `sigmaι_eq_iff`

English:
lemma sigmaι_eq_iff
  given: [Small.{u} σ] (i j : σ) (x y)
  proof: by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff _).trans ⟨?_, ?_⟩
  · rintro ⟨k, ⟨⟨⟨⟩⟩⟩, ⟨⟨⟨⟩⟩⟩, x, rfl, rfl⟩; simp
  · simp only [Discrete.functor_obj_eq_as, Sigma.mk.injEq]
    rintro ⟨rfl, e⟩
    obtain rfl := (heq_eq_eq x y).mp e
    exact ⟨⟨i⟩, 𝟙 _, 𝟙 _, x, by simp⟩

中文:
引理 sigmaι_eq_iff
  条件: [Small.{u} σ] (i j : σ) (x y)
  证明: by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff _).trans ⟨?_, ?_⟩
  · rintro ⟨k, ⟨⟨⟨⟩⟩⟩, ⟨⟨⟨⟩⟩⟩, x, rfl, rfl⟩; simp
  · simp only [Discrete.functor_obj_eq_as, Sigma.mk.injEq]
    rintro ⟨rfl, e⟩
    obtain rfl := (heq_eq_eq x y).mp e
    exact ⟨⟨i⟩, 𝟙 _, 𝟙 _, x, by simp⟩

Depends on / 依赖: Discrete, Discrete.functor_obj_eq_as, IsLocallyDirected, Scheme, Scheme.IsLocallyDirected, Sigma.mk.injEq, functor_obj_eq_as, heq_eq_eq
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
/--
lemma `disjoint_opensRange_sigmaι` / 引理 `disjoint_opensRange_sigmaι`

English:
lemma disjoint_opensRange_sigmaι
  given: [Small.{u} σ] (i j : σ) (h : i != j)
  proof: by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl

中文:
引理 disjoint_opensRange_sigmaι
  条件: [Small.{u} σ] (i j : σ) (h : i != j)
  证明: by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl
-/
lemma disjoint_opensRange_sigmaι [Small.{u} σ] (i j : σ) (h : i != j) :
    Disjoint (Sigma.ι g i).opensRange (Sigma.ι g j).opensRange := by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl

variable {g} in
/--
lemma `isEmpty_of_commSq_sigmaι_of_ne` / 引理 `isEmpty_of_commSq_sigmaι_of_ne`

English:
lemma isEmpty_of_commSq_sigmaι_of_ne
  statement: [Small.{u} σ] {i j : σ} {Z : Scheme.{u}} {a : Z ⟶ g i}
  proof: by
  refine ⟨fun z => ?_⟩
fapply eq_bot_iff.mp disjoint_iff.mp disjoint_opensRange_sigmaι g i j hij
  · exact (a ≫ Sigma.ι g i).base z
  · exact ⟨⟨a.base z, rfl⟩, ⟨b.base z, by rw [← Scheme.Hom.comp_apply, h.w]⟩⟩

中文:
引理 isEmpty_of_commSq_sigmaι_of_ne
  结论: [Small.{u} σ] {i j : σ} {Z : 概形.{u}} {a : Z ⟶ g i}
  证明: by
  refine ⟨fun z => ?_⟩
fapply eq_bot_iff.mp disjoint_iff.mp disjoint_opensRange_sigmaι g i j hij
  · exact (a ≫ Sigma.ι g i).base z
  · exact ⟨⟨a.base z, rfl⟩, ⟨b.base z, by rw [← Scheme.Hom.comp_apply, h.w]⟩⟩

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, a.base, b.base, comp_apply, disjoint_iff, disjoint_iff.mp, eq_bot_iff, eq_bot_iff.mp, fapply
-/
lemma isEmpty_of_commSq_sigmaι_of_ne [Small.{u} σ] {i j : σ} {Z : Scheme.{u}} {a : Z ⟶ g i}
    {b : Z ⟶ g j} (h : CommSq a b (Sigma.ι g i) (Sigma.ι g j)) (hij : i != j) :
    IsEmpty Z := by
  refine ⟨fun z => ?_⟩
fapply eq_bot_iff.mp disjoint_iff.mp disjoint_opensRange_sigmaι g i j hij
  · exact (a ≫ Sigma.ι g i).base z
  · exact ⟨⟨a.base z, rfl⟩, ⟨b.base z, by rw [← Scheme.Hom.comp_apply, h.w]⟩⟩

/--
lemma `isEmpty_pullback_sigmaι_of_ne` / 引理 `isEmpty_pullback_sigmaι_of_ne`

English:
lemma isEmpty_pullback_sigmaι_of_ne
  given: [Small.{u} σ] {i j : σ} (hij : i != j)
  proof: isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

中文:
引理 isEmpty_pullback_sigmaι_of_ne
  条件: [Small.{u} σ] {i j : σ} (hij : i != j)
  证明: isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

Depends on / 依赖: condition, pullback, pullback.condition
-/
lemma isEmpty_pullback_sigmaι_of_ne [Small.{u} σ] {i j : σ} (hij : i != j) :
    IsEmpty ↑(pullback (Sigma.ι g i) (Sigma.ι g j)) :=
  isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{u}
  signature: σ] : CoproductsOfShapeDisjoint Scheme.{u} σ where
  body: by
    refine .of_hasCoproduct (fun _ => pullback.cone _ _) (fun _ => pullback.isLimit _ _) ?_
    intro i j hij
    apply Nonempty.some
    rw [isInitial_iff_isEmpty]
    exact isEmpty_pullback_sigmaι_of_ne _ hij

中文:
实例 [Small.{u}
  签名: σ] : 余productsOfShapeDisjoint 概形.{u} σ where
  定义体: by
    refine .of_hasCoproduct (fun _ => pullback.cone _ _) (fun _ => pullback.isLimit _ _) ?_
    intro i j hij
    apply Nonempty.some
    rw [isInitial_iff_isEmpty]
    exact isEmpty_pullback_sigmaι_of_ne _ hij

Depends on / 依赖: Nonempty, Nonempty.some, isInitial_iff_isEmpty, isLimit, of_hasCoproduct, pullback, pullback.cone, pullback.isLimit
-/
noncomputable instance [Small.{u} σ] : CoproductsOfShapeDisjoint Scheme.{u} σ where
  coproductDisjoint g := by
    refine .of_hasCoproduct (fun _ => pullback.cone _ _) (fun _ => pullback.isLimit _ _) ?_
    intro i j hij
    apply Nonempty.some
    rw [isInitial_iff_isEmpty]
    exact isEmpty_pullback_sigmaι_of_ne _ hij

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteCoproducts Scheme.{u}
  body: inferInstance

中文:
实例 :
  签名: 有FiniteCoproducts 概形.{u}
  定义体: inferInstance
-/
instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoCoprod Scheme.{u}
  body: .mk' fun X Y => ⟨.mk coprod.inl coprod.inr, coprodIsCoprod X Y, inferInstanceAs Mono coprod.inl⟩

中文:
实例 :
  签名: MonoCoprod 概形.{u}
  定义体: .mk' fun X Y => ⟨.mk coprod.inl coprod.inr, coprodIsCoprod X Y, inferInstanceAs Mono coprod.inl⟩

Depends on / 依赖: coprod, coprod.inl, coprod.inr, coprodIsCoprod
-/
instance : MonoCoprod Scheme.{u} :=
.mk' fun X Y => ⟨.mk coprod.inl coprod.inr, coprodIsCoprod X Y, inferInstanceAs Mono coprod.inl⟩

/-- The cover of `∐ X` by the `Xᵢ`. -/
@[simps!]
/--
Definition of `sigmaOpenCover` / `sigmaOpenCover` 的定义

English:
definition sigmaOpenCover
  signature: [Small.{u} σ]
  body: (Scheme.IsLocallyDirected.openCover (Discrete.functor g)).copy σ g (Sigma.ι _)
  (discreteEquiv.symm) (fun _ => Iso.refl _) (fun _ => rfl)

中文:
定义 sigmaOpenCover
  签名: [Small.{u} σ]
  定义体: (Scheme.IsLocallyDirected.openCover (Discrete.functor g)).copy σ g (Sigma.ι _)
  (discreteEquiv.symm) (fun _ => Iso.refl _) (fun _ => rfl)

Depends on / 依赖: Discrete, Discrete.functor, IsLocallyDirected, Iso.refl, Scheme, Scheme.IsLocallyDirected.openCover, discreteEquiv, discreteEquiv.symm, functor, openCover
-/
noncomputable def sigmaOpenCover [Small.{u} σ] : (∐ g).OpenCover :=
  (Scheme.IsLocallyDirected.openCover (Discrete.functor g)).copy σ g (Sigma.ι _)
  (discreteEquiv.symm) (fun _ => Iso.refl _) (fun _ => rfl)

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union. -/
noncomputable
/--
Definition of `sigmaMk` / `sigmaMk` 的定义

English:
definition sigmaMk
  signature: : (Σ i, f i) ≃ₜ (∐ f :)
  body: TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

@[simp]

中文:
定义 sigmaMk
  签名: : (Σ i, f i) ≃ₜ (∐ f :)
  定义体: TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

@[simp]

Depends on / 依赖: PreservesCoproduct, PreservesCoproduct.iso, Scheme, Scheme.forgetToTop, TopCat, TopCat.homeoOfIso, TopCat.sigmaCofanIsColimit, colimit, colimit.isoColimitCocone, forgetToTop, homeoOfIso, isoColimitCocone, sigmaCofanIsColimit
-/
def sigmaMk : (Σ i, f i) ≃ₜ (∐ f :) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

@[simp]
/--
lemma `sigmaMk_mk` / 引理 `sigmaMk_mk`

English:
lemma sigmaMk_mk
  given: (i) (x : f i)
  proof: by
  change ((TopCat.sigmaCofan (fun x => (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exa

中文:
引理 sigmaMk_mk
  条件: (i) (x : f i)
  证明: by
  change ((TopCat.sigmaCofan (fun x => (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exa

Depends on / 依赖: Scheme, Scheme.forgetToTop, Scheme.forgetToTop.map, TopCat, TopCat.sigmaCofan, TopCat.sigmaCofanIsColimit, colimit, colimit.isoColimitCocone, colimit.isoColimitCocone_, forgetToTop, isoColimitCocone, sigmaCofan, sigmaCofanIsColimit, toTopCat
-/
lemma sigmaMk_mk (i) (x : f i) :
    sigmaMk f (.mk i x) = Sigma.ι f i x := by
  change ((TopCat.sigmaCofan (fun x => (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exact ι_comp_sigmaComparison Scheme.forgetToTop _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/--
lemma `isOpenImmersion_sigmaDesc_aux` / 引理 `isOpenImmersion_sigmaDesc_aux`

English:
lemma isOpenImmersion_sigmaDesc_aux
  proof: by
  rw [IsOpenImmersion.iff_isIso_stalkMap]
  constructor
  · suffices Topology.IsOpenEmbedding (Sigma.desc α ∘ sigmaMk f) by
      convert! this.comp (sigmaMk f).symm.isOpenEmbedding; ext; simp
    refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
    · fun_prop
    · rintro ⟨ix, x⟩ ⟨iy, y⟩ e
   

中文:
引理 isOpenImmersion_sigmaDesc_aux
  证明: by
  rw [IsOpenImmersion.iff_isIso_stalkMap]
  constructor
  · suffices Topology.IsOpenEmbedding (Sigma.desc α ∘ sigmaMk f) by
      convert! this.comp (sigmaMk f).symm.isOpenEmbedding; ext; simp
    refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
    · fun_prop
    · rintro ⟨ix, x⟩ ⟨iy, y⟩ e
   
-/
private lemma isOpenImmersion_sigmaDesc_aux
    {X : Scheme.{u}} (α : forall i, f i ⟶ X) [forall i, IsOpenImmersion (α i)]
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
/--
lemma `isOpenImmersion_sigmaDesc` / 引理 `isOpenImmersion_sigmaDesc`

English:
lemma isOpenImmersion_sigmaDesc
  statement: [Small.{u} σ]
  proof: by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small (α := σ)
  convert! IsOpenImmersion.comp ((Sigma.reindex e.symm g).inv) (Sigma.desc fun i => α _)
  · refine Sigma.hom_ext _ _ fun i => ?_
    obtain ⟨i, rfl⟩ := e.symm.surjective i
    simp
  · apply isOpenImmersion_sigmaDesc_aux
    intro i j hij
    exact

中文:
引理 isOpenImmersion_sigmaDesc
  结论: [Small.{u} σ]
  证明: by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small (α := σ)
  convert! IsOpenImmersion.comp ((Sigma.reindex e.symm g).inv) (Sigma.desc fun i => α _)
  · refine Sigma.hom_ext _ _ fun i => ?_
    obtain ⟨i, rfl⟩ := e.symm.surjective i
    simp
  · apply isOpenImmersion_sigmaDesc_aux
    intro i j hij
    exact

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.comp, Sigma.desc, Sigma.hom_ext, Sigma.reindex, Small.equiv_small, convert, e.symm, e.symm.injective, e.symm.surjective, equiv_small, hom_ext, injective, isOpenImmersion_sigmaDesc_aux, reindex, surjective
-/
lemma isOpenImmersion_sigmaDesc [Small.{u} σ]
    {X : Scheme.{u}} (α : forall i, g i ⟶ X) [forall i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsOpenImmersion (Sigma.desc α) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small (α := σ)
  convert! IsOpenImmersion.comp ((Sigma.reindex e.symm g).inv) (Sigma.desc fun i => α _)
  · refine Sigma.hom_ext _ _ fun i => ?_
    obtain ⟨i, rfl⟩ := e.symm.surjective i
    simp
  · apply isOpenImmersion_sigmaDesc_aux
    intro i j hij
    exact hα (fun h => hij (e.symm.injective h))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/--
lemma `nonempty_isColimit_cofanMk_of` / 引理 `nonempty_isColimit_cofanMk_of`

English:
lemma nonempty_isColimit_cofanMk_of
  statement: [Small.{u} σ]
  proof: by
  have : IsOpenImmersion (Sigma.desc f) := by
    refine isOpenImmersion_sigmaDesc _ _ (fun i j hij => ?_)
    simpa [Function.onFun_apply, disjoint_iff, Opens.ext_iff] using hdisj hij
  simp only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk S f), cofan_mk_inj, Cofan.mk_pt]
  apply isI

中文:
引理 nonempty_isColimit_cofanMk_of
  结论: [Small.{u} σ]
  证明: by
  have : IsOpenImmersion (Sigma.desc f) := by
    refine isOpenImmersion_sigmaDesc _ _ (fun i j hij => ?_)
    simpa [Function.onFun_apply, disjoint_iff, Opens.ext_iff] using hdisj hij
  simp only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk S f), cofan_mk_inj, Cofan.mk_pt]
  apply isI

Depends on / 依赖: Cofan.mk, Cofan.mk_pt, Cofan.nonempty_isColimit_iff_isIso_sigmaDesc, Function, Function.onFun_apply, IsOpenImmersion, Opens.ext_iff, Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion, Sigma.desc, cofan_mk_inj, disjoint_iff, eq_top_iff, ext_iff, iSup_mk, isIso_of_isOpenImmersion_of_opensRange_eq_top, isOpenImmersion_sigmaDesc, mem_iUnion, mem_mk
-/
lemma nonempty_isColimit_cofanMk_of [Small.{u} σ]
    {X : σ -> Scheme.{u}} {S : Scheme.{u}} (f : forall i, X i ⟶ S) [forall i, IsOpenImmersion (f i)]
    (hcov : ⨆ i, (f i).opensRange = ⊤) (hdisj : Pairwise (Disjoint on (f · |>.opensRange))) :
    Nonempty (IsColimit <| Cofan.mk S f) := by
  have : IsOpenImmersion (Sigma.desc f) := by
    refine isOpenImmersion_sigmaDesc _ _ (fun i j hij => ?_)
    simpa [Function.onFun_apply, disjoint_iff, Opens.ext_iff] using hdisj hij
  simp only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk S f), cofan_mk_inj, Cofan.mk_pt]
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [eq_top_iff]
  intro x hx
  have : x in ⨆ i, (f i).opensRange := by rwa [hcov]
  obtain ⟨i, y, rfl⟩ := by simpa only [Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion] using this
  use Sigma.ι X i y
  simp [← Scheme.Hom.comp_apply]

variable (X Y : Scheme.{u})

/-- (Implementation Detail)
The coproduct of the two schemes is given by indexed coproducts over `WalkingPair`. -/
noncomputable
/--
Definition of `coprodIsoSigma` / `coprodIsoSigma` 的定义

English:
definition coprodIsoSigma
  signature: : X ⨿ Y ≅ ∐ fun i : ULift.{u} WalkingPair => i.1.casesOn X Y
  body: Sigma.whiskerEquiv Equiv.ulift.symm (fun _ => by exact Iso.refl _)

中文:
定义 coprodIsoSigma
  签名: : X ⨿ Y ≅ ∐ fun i : 类型层提升.{u} WalkingPair => i.1.casesOn X Y
  定义体: Sigma.whiskerEquiv Equiv.ulift.symm (fun _ => by exact Iso.refl _)

Depends on / 依赖: Equiv.ulift.symm, Iso.refl, Sigma.whiskerEquiv, whiskerEquiv
-/
def coprodIsoSigma : X ⨿ Y ≅ ∐ fun i : ULift.{u} WalkingPair => i.1.casesOn X Y :=
  Sigma.whiskerEquiv Equiv.ulift.symm (fun _ => by exact Iso.refl _)

/--
lemma `ι_left_coprodIsoSigma_inv` / 引理 `ι_left_coprodIsoSigma_inv`

English:
lemma ι_left_coprodIsoSigma_inv
  statement: Sigma.ι _ ⟨.left⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inl
  proof: Sigma.ι_comp_map' _ _ _

中文:
引理 ι_left_coprodIsoSigma_inv
  结论: 依赖和类型.ι _ ⟨.left⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inl
  证明: Sigma.ι_comp_map' _ _ _

Depends on / 依赖: and_true, hom_ext, mk.injEq, s.hom_ext
-/
lemma ι_left_coprodIsoSigma_inv : Sigma.ι _ ⟨.left⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inl :=
  Sigma.ι_comp_map' _ _ _

/--
lemma `ι_right_coprodIsoSigma_inv` / 引理 `ι_right_coprodIsoSigma_inv`

English:
lemma ι_right_coprodIsoSigma_inv
  statement: Sigma.ι _ ⟨.right⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inr
  proof: Sigma.ι_comp_map' _ _ _

中文:
引理 ι_right_coprodIsoSigma_inv
  结论: 依赖和类型.ι _ ⟨.right⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inr
  证明: Sigma.ι_comp_map' _ _ _
-/
lemma ι_right_coprodIsoSigma_inv : Sigma.ι _ ⟨.right⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inr :=
  Sigma.ι_comp_map' _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y)
  body: by
  rw [← ι_left_coprodIsoSigma_inv]; infer_instance

中文:
实例 :
  签名: 是开浸入 (coprod.inl : X ⟶ X ⨿ Y)
  定义体: by
  rw [← ι_left_coprodIsoSigma_inv]; infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [← ι_left_coprodIsoSigma_inv]; infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y)
  body: by
  rw [← ι_right_coprodIsoSigma_inv]; infer_instance

中文:
实例 :
  签名: 是开浸入 (coprod.inr : Y ⟶ X ⨿ Y)
  定义体: by
  rw [← ι_right_coprodIsoSigma_inv]; infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [← ι_right_coprodIsoSigma_inv]; infer_instance

/--
lemma `isCompl_range_inl_inr` / 引理 `isCompl_range_inl_inr`

English:
lemma isCompl_range_inl_inr
  proof: ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ (coprodIsCoprod X Y)⟩).2.2

中文:
引理 isCompl_range_inl_inr
  证明: ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ (coprodIsCoprod X Y)⟩).2.2

Depends on / 依赖: Scheme, Scheme.forgetToTop, TopCat, TopCat.binaryCofan_isColimit_iff, binaryCofan_isColimit_iff, coprodIsCoprod, forgetToTop, mapIsColimitOfPreservesOfIsColimit
-/
lemma isCompl_range_inl_inr :
    IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.range (coprod.inr : Y ⟶ X ⨿ Y)) :=
  ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ (coprodIsCoprod X Y)⟩).2.2

/--
lemma `isCompl_opensRange_inl_inr` / 引理 `isCompl_opensRange_inl_inr`

English:
lemma isCompl_opensRange_inl_inr
  proof: by
  convert! isCompl_range_inl_inr X Y
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

@[simp]

中文:
引理 isCompl_opensRange_inl_inr
  证明: by
  convert! isCompl_range_inl_inr X Y
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

@[simp]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.coe_inj, codisjoint_iff, coe_inj, convert, disjoint_iff, isCompl_iff, isCompl_range_inl_inr
-/
lemma isCompl_opensRange_inl_inr :
    IsCompl (coprod.inl : X ⟶ X ⨿ Y).opensRange (coprod.inr : Y ⟶ X ⨿ Y).opensRange := by
  convert! isCompl_range_inl_inr X Y
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

@[simp]
/--
lemma `inl_ne_inr` / 引理 `inl_ne_inr`

English:
lemma inl_ne_inr
  given: (x : X) (y : Y)
  statement: (coprod.inl : X ⟶ X ⨿ Y) x != (coprod.inr : Y ⟶ X ⨿ Y) y
  proof: Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr X Y).disjoint ⟨x, rfl⟩ ⟨y, rfl⟩

@[simp]

中文:
引理 inl_ne_inr
  条件: (x : X) (y : Y)
  结论: (coprod.inl : X ⟶ X ⨿ Y) x != (coprod.inr : Y ⟶ X ⨿ Y) y
  证明: Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr X Y).disjoint ⟨x, rfl⟩ ⟨y, rfl⟩

@[simp]

Depends on / 依赖: Set.disjoint_iff_forall_ne.mp, disjoint, disjoint_iff_forall_ne, isCompl_range_inl_inr
-/
lemma inl_ne_inr (x : X) (y : Y) : (coprod.inl : X ⟶ X ⨿ Y) x != (coprod.inr : Y ⟶ X ⨿ Y) y :=
  Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr X Y).disjoint ⟨x, rfl⟩ ⟨y, rfl⟩

@[simp]
/--
lemma `inr_ne_inl` / 引理 `inr_ne_inl`

English:
lemma inr_ne_inl
  given: (x : X) (y : Y)
  statement: (coprod.inr : Y ⟶ X ⨿ Y) y != (coprod.inl : X ⟶ X ⨿ Y) x
  proof: (inl_ne_inr _ _ _ _).symm

中文:
引理 inr_ne_inl
  条件: (x : X) (y : Y)
  结论: (coprod.inr : Y ⟶ X ⨿ Y) y != (coprod.inl : X ⟶ X ⨿ Y) x
  证明: (inl_ne_inr _ _ _ _).symm

Depends on / 依赖: inl_ne_inr
-/
lemma inr_ne_inl (x : X) (y : Y) : (coprod.inr : Y ⟶ X ⨿ Y) y != (coprod.inl : X ⟶ X ⨿ Y) x :=
  (inl_ne_inr _ _ _ _).symm

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union -/
noncomputable
/--
Definition of `coprodMk` / `coprodMk` 的定义

English:
definition coprodMk
  signature: : X oplus Y ≃ₜ (X ⨿ Y : Scheme.{u})
  body: TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).symm ≪≫
    PreservesColimitPair.iso Scheme.forgetToTop X Y)

@[simp]

中文:
定义 coprodMk
  签名: : X oplus Y ≃ₜ (X ⨿ Y : 概形.{u})
  定义体: TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).symm ≪≫
    PreservesColimitPair.iso Scheme.forgetToTop X Y)

@[simp]

Depends on / 依赖: PreservesColimitPair, PreservesColimitPair.iso, Scheme, Scheme.forgetToTop, TopCat, TopCat.binaryCofanIsColimit, TopCat.homeoOfIso, binaryCofanIsColimit, colimit, colimit.isoColimitCocone, forgetToTop, homeoOfIso, isoColimitCocone
-/
def coprodMk : X oplus Y ≃ₜ (X ⨿ Y : Scheme.{u}) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).symm ≪≫
    PreservesColimitPair.iso Scheme.forgetToTop X Y)

@[simp]
/--
lemma `coprodMk_inl` / 引理 `coprodMk_inl`

English:
lemma coprodMk_inl
  given: (x : X)
  proof: by
  change ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_

中文:
引理 coprodMk_inl
  条件: (x : X)
  证明: by
  change ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_

Depends on / 依赖: Scheme, Scheme.forgetToTop, Scheme.forgetToTop.map, TopCat, TopCat.binaryCofan, TopCat.binaryCofanIsColimit, binaryCofan, binaryCofanIsColimit, colimit, colimit.isoColimitCocone, colimit.isoColimitCocone_, coprod, coprod.inl, coprodComparison_inl, forgetToTop, isoColimitCocone
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
/--
lemma `coprodMk_inr` / 引理 `coprodMk_inr`

English:
lemma coprodMk_inr
  given: (x : Y)
  proof: by
  change ((TopCat.binaryCofan X Y).inr ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inr x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_

中文:
引理 coprodMk_inr
  条件: (x : Y)
  证明: by
  change ((TopCat.binaryCofan X Y).inr ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inr x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_

Depends on / 依赖: Scheme, Scheme.forgetToTop, Scheme.forgetToTop.map, TopCat, TopCat.binaryCofan, TopCat.binaryCofanIsColimit, binaryCofan, binaryCofanIsColimit, colimit, colimit.isoColimitCocone, colimit.isoColimitCocone_, coprod, coprod.inr, coprodComparison_inr, forgetToTop, isoColimitCocone
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
/--
Definition of `coprodOpenCover.` / `coprodOpenCover.` 的定义

English:
definition coprodOpenCover.{w}
  signature: : (X ⨿ Y).OpenCover where
  body: PUnit.{w + 1} oplus PUnit.{w + 1}
  X x := x.elim (fun _ => X) (fun _ => Y)
  f x := x.rec (fun _ => coprod.inl) (fun _ => coprod.inr)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun x => x.rec (fun _ => inferInstance) (fun _ => inferInstance)⟩
    use ((copro

中文:
定义 coprodOpenCover.{w}
  签名: : (X ⨿ Y).OpenCover where
  定义体: PUnit.{w + 1} oplus PUnit.{w + 1}
  X x := x.elim (fun _ => X) (fun _ => Y)
  f x := x.rec (fun _ => coprod.inl) (fun _ => coprod.inr)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun x => x.rec (fun _ => inferInstance) (fun _ => inferInstance)⟩
    use ((copro
-/
def coprodOpenCover.{w} : (X ⨿ Y).OpenCover where
  I₀ := PUnit.{w + 1} oplus PUnit.{w + 1}
  X x := x.elim (fun _ => X) (fun _ => Y)
  f x := x.rec (fun _ => coprod.inl) (fun _ => coprod.inr)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun x => x.rec (fun _ => inferInstance) (fun _ => inferInstance)⟩
    use ((coprodMk X Y).symm x).elim (fun _ => Sum.inl .unit) (fun _ => Sum.inr .unit)
    obtain ⟨x, rfl⟩ := (coprodMk X Y).surjective x
    simp only [Sum.elim_inl, Sum.elim_inr, Set.mem_range]
    rw [Homeomorph.symm_apply_apply]
    obtain (x | x) := x
    · simp only [Sum.elim_inl, coprodMk_inl, exists_apply_eq_apply]
    · simp only [Sum.elim_inr, coprodMk_inr, exists_apply_eq_apply]

-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/--
lemma `nonempty_isColimit_binaryCofanMk_of_isCompl` / 引理 `nonempty_isColimit_binaryCofanMk_of_isCompl`

English:
lemma nonempty_isColimit_binaryCofanMk_of_isCompl
  statement: {X Y S : Scheme.{u}}
  proof: by
  let c' : Cofan fun j => (WalkingPair.casesOn j X Y : Scheme.{u}) :=
    .mk S fun j => WalkingPair.casesOn j f g
  let i : BinaryCofan.mk f g ≅ c' := Cofan.ext (Iso.refl _) (by rintro (b | b) <;> rfl)
  refine ⟨IsColimit.ofIsoColimit (Nonempty.some ?_) i.symm⟩
  let fi (j : WalkingPair) : Walki

中文:
引理 nonempty_isColimit_binaryCofanMk_of_isCompl
  结论: {X Y S : 概形.{u}}
  证明: by
  let c' : Cofan fun j => (WalkingPair.casesOn j X Y : Scheme.{u}) :=
    .mk S fun j => WalkingPair.casesOn j f g
  let i : BinaryCofan.mk f g ≅ c' := Cofan.ext (Iso.refl _) (by rintro (b | b) <;> rfl)
  refine ⟨IsColimit.ofIsoColimit (Nonempty.some ?_) i.symm⟩
  let fi (j : WalkingPair) : Walki

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, Cofan.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, Nonempty, Nonempty.some, Scheme, WalkingPair, WalkingPair.casesOn, WalkingPair.equivBool.symm.iSup_comp, casesOn, convert, equivBool, i.symm, iSup_bool_eq, iSup_comp, infer_instance, nonempty_isColimit_cofanMk_of
-/
lemma nonempty_isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : IsCompl f.opensRange g.opensRange) :
    Nonempty (IsColimit <| BinaryCofan.mk f g) := by
  let c' : Cofan fun j => (WalkingPair.casesOn j X Y : Scheme.{u}) :=
    .mk S fun j => WalkingPair.casesOn j f g
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

/--
lemma `isPullback_inl_inl_coprodMap` / 引理 `isPullback_inl_inl_coprodMap`

English:
lemma isPullback_inl_inl_coprodMap
  statement: {X Y X' Y' : Scheme.{u}}
  proof: by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨(x | x), rfl⟩ := (coprodMk _ _).surjective x
    · rw [← SetLike.mem_coe]; simp -- TODO : add `Scheme.Hom.mem_opensRange`
    · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.i

中文:
引理 isPullback_inl_inl_coprodMap
  结论: {X Y X' Y' : 概形.{u}}
  证明: by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨(x | x), rfl⟩ := (coprodMk _ _).surjective x
    · rw [← SetLike.mem_coe]; simp -- TODO : add `Scheme.Hom.mem_opensRange`
    · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.i

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isPullback, Scheme, Scheme.Hom.comp_apply, Scheme.Hom.comp_base, Scheme.Hom.mem_opensRange, Set.disjoint_iff_forall_ne.mp, SetLike, SetLike.mem_coe, comp_apply, comp_base, coprod, coprod.inr_map, coprodMk, coprodMk_inr, disjoint_iff_forall_ne, inr_map, isCompl_range_inl_inr, isPullback, le_antisymm
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
/--
lemma `isPullback_inr_inr_coprodMap` / 引理 `isPullback_inr_inr_coprodMap`

English:
lemma isPullback_inr_inr_coprodMap
  statement: {X Y X' Y' : Scheme.{u}}
  proof: (isPullback_inl_inl_coprodMap g f).of_iso (.refl _) (.refl _) (coprod.braiding _ _)
    (coprod.braiding _ _) (by simp) (by simp) (by simp) (by simp)

中文:
引理 isPullback_inr_inr_coprodMap
  结论: {X Y X' Y' : 概形.{u}}
  证明: (isPullback_inl_inl_coprodMap g f).of_iso (.refl _) (.refl _) (coprod.braiding _ _)
    (coprod.braiding _ _) (by simp) (by simp) (by simp) (by simp)

Depends on / 依赖: braiding, coprod, coprod.braiding, isPullback_inl_inl_coprodMap, of_iso
-/
lemma isPullback_inr_inr_coprodMap {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback g coprod.inr coprod.inr (coprod.map f g) :=
  (isPullback_inl_inl_coprodMap g f).of_iso (.refl _) (.refl _) (coprod.braiding _ _)
    (coprod.braiding _ _) (by simp) (by simp) (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinitaryExtensive Scheme
  body: inferInstance
  van_kampen' {X Y} c hc := by
    suffices IsVanKampenColimit (BinaryCofan.mk (P := X ⨿ Y) coprod.inl coprod.inr) from
      this.of_iso (hc.uniqueUpToIso (coprodIsCoprod _ _)).symm
    refine BinaryCofan.isVanKampen_mk _ _ (fun _ _ => coprodIsCoprod _ _) _
      (fun _ _ => pullbackI

中文:
实例 :
  签名: 有限广延 概形
  定义体: inferInstance
  van_kampen' {X Y} c hc := by
    suffices IsVanKampenColimit (BinaryCofan.mk (P := X ⨿ Y) coprod.inl coprod.inr) from
      this.of_iso (hc.uniqueUpToIso (coprodIsCoprod _ _)).symm
    refine BinaryCofan.isVanKampen_mk _ _ (fun _ _ => coprodIsCoprod _ _) _
      (fun _ _ => pullbackI
-/
instance : FinitaryExtensive Scheme where
  hasFiniteCoproducts.out := inferInstance
  van_kampen' {X Y} c hc := by
    suffices IsVanKampenColimit (BinaryCofan.mk (P := X ⨿ Y) coprod.inl coprod.inr) from
      this.of_iso (hc.uniqueUpToIso (coprodIsCoprod _ _)).symm
    refine BinaryCofan.isVanKampen_mk _ _ (fun _ _ => coprodIsCoprod _ _) _
      (fun _ _ => pullbackIsPullback _ _) ?_ ?_
    · intro X' Y' αX αY f h₁ h₂
      have h₁' (x : _) := congr($h₁ x).symm
      have h₂' (x : _) := congr($h₂ x).symm
      dsimp at h₁ h₂ h₁' h₂'
      refine ⟨(IsOpenImmersion.isPullback _ _ _ _ h₁.symm ?_).flip,
        (IsOpenImmersion.isPullback _ _ _ _ h₂.symm ?_).flip⟩ <;>
        ext x <;> obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x <;> simp_all
    · dsimp
      refine fun {Z} f => (nonempty_isColimit_binaryCofanMk_of_isCompl _ _ ?_).some
      rw [Scheme.Hom.opensRange_pullbackFst]; rw [Scheme.Hom.opensRange_pullbackFst]
      convert! (isCompl_range_inl_inr X Y).map (CompleteLatticeHom.setPreimage f)
      simp [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]

variable {X Y}

/--
Definition of `Scheme.coprodPresheafObjIso` / `Scheme.coprodPresheafObjIso` 的定义

English:
definition Scheme.coprodPresheafObjIso
  signature: (U : (X ⨿ Y).Opens)
  body: letI ι₁ : X ⟶ X ⨿ Y := coprod.inl
  letI ι₂ : Y ⟶ X ⨿ Y := coprod.inr
  haveI h₁ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊔ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = U := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_sup_right]; rw [(isCompl_opensRange_inl_inr X Y).sup_eq_top]; rw [top_inf_eq]
  haveI h₂ : ι₁ ''ᵁ ι₁ 

中文:
定义 概形.coprodPresheafObjIso
  签名: (U : (X ⨿ Y).Opens)
  定义体: letI ι₁ : X ⟶ X ⨿ Y := coprod.inl
  letI ι₂ : Y ⟶ X ⨿ Y := coprod.inr
  haveI h₁ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊔ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = U := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_sup_right]; rw [(isCompl_opensRange_inl_inr X Y).sup_eq_top]; rw [top_inf_eq]
  haveI h₂ : ι₁ ''ᵁ ι₁ 

Depends on / 依赖: Scheme, coprod, coprod.inr
-/
noncomputable def Scheme.coprodPresheafObjIso (U : (X ⨿ Y).Opens) :
    Γ(X ⨿ Y, U) ≅ Γ(X, coprod.inl (C := Scheme) ⁻¹ᵁ U) ⨯ Γ(Y, coprod.inr (C := Scheme) ⁻¹ᵁ U) :=
  letI ι₁ : X ⟶ X ⨿ Y := coprod.inl
  letI ι₂ : Y ⟶ X ⨿ Y := coprod.inr
  haveI h₁ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊔ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = U := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_sup_right]; rw [(isCompl_opensRange_inl_inr X Y).sup_eq_top]; rw [top_inf_eq]
  haveI h₂ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊓ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = ⊥ := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_inf_distrib_right]; rw [(isCompl_opensRange_inl_inr X Y).inf_eq_bot]; rw [bot_inf_eq]
  (X ⨿ Y).presheaf.mapIso (eqToIso h₁).op ≪≫
    ((X ⨿ Y).sheaf.isProductOfDisjoint _ _ h₂).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    prod.mapIso (ι₁.appIso _) (ι₂.appIso _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `Scheme.coprodPresheafObjIso_hom_fst` / 引理 `Scheme.coprodPresheafObjIso_hom_fst`

English:
lemma Scheme.coprodPresheafObjIso_hom_fst
  given: (U : (X ⨿ Y).Opens)
  proof: by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

中文:
引理 概形.coprodPresheafObjIso_hom_fst
  条件: (U : (X ⨿ Y).Opens)
  证明: by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

Depends on / 依赖: Functor, Functor.map_comp, Hom.appIso_hom, Scheme, Subsingleton, Subsingleton.elim, appIso_hom, coprodPresheafObjIso, map_comp
-/
lemma Scheme.coprodPresheafObjIso_hom_fst (U : (X ⨿ Y).Opens) :
    (coprodPresheafObjIso U).hom ≫ prod.fst = (coprod.inl (C := Scheme)).app U := by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `Scheme.coprodPresheafObjIso_hom_snd` / 引理 `Scheme.coprodPresheafObjIso_hom_snd`

English:
lemma Scheme.coprodPresheafObjIso_hom_snd
  given: (U : (X ⨿ Y).Opens)
  proof: by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

中文:
引理 概形.coprodPresheafObjIso_hom_snd
  条件: (U : (X ⨿ Y).Opens)
  证明: by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

Depends on / 依赖: Functor, Functor.map_comp, Hom.appIso_hom, Scheme, Subsingleton, Subsingleton.elim, appIso_hom, coprodPresheafObjIso, map_comp
-/
lemma Scheme.coprodPresheafObjIso_hom_snd (U : (X ⨿ Y).Opens) :
    (coprodPresheafObjIso U).hom ≫ prod.snd = (coprod.inr (C := Scheme)).app U := by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The map `Spec R ⨿ Spec S ⟶ Spec (R × S)`.
This is an isomorphism as witnessed by an `IsIso` instance provided below. -/
noncomputable
/--
Definition of `coprodSpec` / `coprodSpec` 的定义

English:
definition coprodSpec
  signature: : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of <| R × S)
  body: coprod.desc (Spec.map (CommRingCat.ofHom <| RingHom.fst _ _))
    (Spec.map (CommRingCat.ofHom <| RingHom.snd _ _))

@[simp, reassoc]

中文:
定义 coprodSpec
  签名: : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of <| R × S)
  定义体: coprod.desc (Spec.map (CommRingCat.ofHom <| RingHom.fst _ _))
    (Spec.map (CommRingCat.ofHom <| RingHom.snd _ _))

@[simp, reassoc]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, RingHom, RingHom.fst, RingHom.snd, Spec.map, coprod, coprod.desc
-/
def coprodSpec : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of <| R × S) :=
  coprod.desc (Spec.map (CommRingCat.ofHom <| RingHom.fst _ _))
    (Spec.map (CommRingCat.ofHom <| RingHom.snd _ _))

@[simp, reassoc]
/--
lemma `coprodSpec_inl` / 引理 `coprodSpec_inl`

English:
lemma coprodSpec_inl
  statement: coprod.inl ≫ coprodSpec R S =
  proof: coprod.inl_desc _ _

@[simp, reassoc]

中文:
引理 coprodSpec_inl
  结论: coprod.inl ≫ coprodSpec R S =
  证明: coprod.inl_desc _ _

@[simp, reassoc]

Depends on / 依赖: coprod, coprod.inl_desc, inl_desc
-/
lemma coprodSpec_inl : coprod.inl ≫ coprodSpec R S =
    Spec.map (CommRingCat.ofHom <| RingHom.fst R S) :=
  coprod.inl_desc _ _

@[simp, reassoc]
/--
lemma `coprodSpec_inr` / 引理 `coprodSpec_inr`

English:
lemma coprodSpec_inr
  statement: coprod.inr ≫ coprodSpec R S =
  proof: coprod.inr_desc _ _

中文:
引理 coprodSpec_inr
  结论: coprod.inr ≫ coprodSpec R S =
  证明: coprod.inr_desc _ _

Depends on / 依赖: coprod, coprod.inr_desc, inr_desc
-/
lemma coprodSpec_inr : coprod.inr ≫ coprodSpec R S =
    Spec.map (CommRingCat.ofHom <| RingHom.snd R S) :=
  coprod.inr_desc _ _

/--
lemma `coprodSpec_coprodMk` / 引理 `coprodSpec_coprodMk`

English:
lemma coprodSpec_coprodMk
  given: (x)
  proof: by
  apply PrimeSpectrum.ext
  obtain (x | x) := x <;>
    simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
      coprodSpec, coprod.inl_desc, coprod.inr_desc]
  · change Ideal.comap _ _ = x.asIdeal.prod ⊤
    ext; simp [Ideal.prod, CommRingCat.ofHom]
  · change Ideal.comap _ _ = Idea

中文:
引理 coprodSpec_coprodMk
  条件: (x)
  证明: by
  apply PrimeSpectrum.ext
  obtain (x | x) := x <;>
    simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
      coprodSpec, coprod.inl_desc, coprod.inr_desc]
  · change Ideal.comap _ _ = x.asIdeal.prod ⊤
    ext; simp [Ideal.prod, CommRingCat.ofHom]
  · change Ideal.comap _ _ = Idea

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Ideal.comap, Ideal.prod, PrimeSpectrum, PrimeSpectrum.ext, Scheme, Scheme.Hom.comp_apply, asIdeal, comp_apply, coprod, coprod.inl_desc, coprod.inr_desc, coprodMk_inl, coprodMk_inr, coprodSpec, inl_desc, inr_desc, x.asIdeal, x.asIdeal.prod
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

/--
lemma `coprodSpec_apply` / 引理 `coprodSpec_apply`

English:
lemma coprodSpec_apply
  given: (x)
  proof: by
  rw [← coprodSpec_coprodMk]; rw [Homeomorph.apply_symm_apply]

中文:
引理 coprodSpec_apply
  条件: (x)
  证明: by
  rw [← coprodSpec_coprodMk]; rw [Homeomorph.apply_symm_apply]

Depends on / 依赖: Homeomorph, Homeomorph.apply_symm_apply, apply_symm_apply, coprodSpec_coprodMk
-/
lemma coprodSpec_apply (x) :
    coprodSpec R S x = (PrimeSpectrum.primeSpectrumProd R S).symm ((coprodMk _ _).symm x) := by
  rw [← coprodSpec_coprodMk]; rw [Homeomorph.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_stalkMap_coprodSpec` / 引理 `isIso_stalkMap_coprodSpec`

English:
lemma isIso_stalkMap_coprodSpec
  given: (x)
  proof: by
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
  · have := Scheme.Hom.stalkMap_comp coprod.inl (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq]; rw [Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inl R S)] at this
    rw [coprodMk_inl]; rw [← this]
    let := (RingHom.fst R S).toAl

中文:
引理 isIso_stalkMap_coprodSpec
  条件: (x)
  证明: by
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
  · have := Scheme.Hom.stalkMap_comp coprod.inl (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq]; rw [Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inl R S)] at this
    rw [coprodMk_inl]; rw [← this]
    let := (RingHom.fst R S).toAl

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsIso.co, IsIso.comp_inv_eq, IsOpenImmersion, IsOpenImmersion.of_isLocalization, RingHom, RingHom.fst, Scheme, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom, Spec.map, comp_inv_eq, coprod, coprod.inl, coprod.inr, coprodMk, coprodMk_inl, coprodSpec, coprodSpec_inl
-/
lemma isIso_stalkMap_coprodSpec (x) :
    IsIso ((coprodSpec R S).stalkMap x) := by
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
  · have := Scheme.Hom.stalkMap_comp coprod.inl (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq]; rw [Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inl R S)] at this
    rw [coprodMk_inl]; rw [← this]
    let := (RingHom.fst R S).toAlgebra
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst R S))) :=
      IsOpenImmersion.of_isLocalization (1, 0)
    infer_instance
  · have := Scheme.Hom.stalkMap_comp coprod.inr (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq]; rw [Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inr R S)] at this
    rw [coprodMk_inr]; rw [← this]
    let := (RingHom.snd R S).toAlgebra
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd R S))) :=
      IsOpenImmersion.of_isLocalization (0, 1)
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (coprodSpec R S)
  body: by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, isIso_stalkMap_coprodSpec R S⟩
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec (.of <| R × S)) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instanc

中文:
实例 :
  签名: 是同构 (coprodSpec R S)
  定义体: by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, isIso_stalkMap_coprodSpec R S⟩
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec (.of <| R × S)) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instanc

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.primeSpectrumProdHomeo.trans, TopCat, TopCat.isoOfHomeo, convert_to, coprodMk, coprodSpec_apply, infer_instance, isIso_iff_isIso_stalkMap, isIso_stalkMap_coprodSpec, isoOfHomeo, primeSpectrumProdHomeo
-/
instance : IsIso (coprodSpec R S) := by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, isIso_stalkMap_coprodSpec R S⟩
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec (.of <| R × S)) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape (Discrete WalkingPair) Scheme.Spec.{u}
  body: ⟨fun {_} =>
    have (X Y : CommRingCat.{u}ᵒᵖ) := PreservesColimitPair.of_iso_coprod_comparison Scheme.Spec X Y
    preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm⟩

中文:
实例 :
  签名: 保持形状余极限 (离散 WalkingPair) 概形.Spec.{u}
  定义体: ⟨fun {_} =>
    have (X Y : CommRingCat.{u}ᵒᵖ) := PreservesColimitPair.of_iso_coprod_comparison Scheme.Spec X Y
    preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm⟩

Depends on / 依赖: CommRingCat, PreservesColimitPair, PreservesColimitPair.of_iso_coprod_comparison, Scheme, Scheme.Spec, diagramIsoPair, of_iso_coprod_comparison, preservesColimit_of_iso_diagram
-/
instance : PreservesColimitsOfShape (Discrete WalkingPair) Scheme.Spec.{u} :=
  ⟨fun {_} =>
    have (X Y : CommRingCat.{u}ᵒᵖ) := PreservesColimitPair.of_iso_coprod_comparison Scheme.Spec X Y
    preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape (Discrete PEmpty.{1}) Scheme.Spec.{u}
  body: by
  have : IsEmpty (Scheme.Spec.obj (⊥_ CommRingCatᵒᵖ)) :=
    @Function.isEmpty _ _ spec_punit_isEmpty (Scheme.Spec.mapIso
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom
  have := preservesInitial_of_iso Scheme.Spec (asIso (initial.to _))
  exact preservesColimi

中文:
实例 :
  签名: 保持形状余极限 (离散 命题空.{1}) 概形.Spec.{u}
  定义体: by
  have : IsEmpty (Scheme.Spec.obj (⊥_ CommRingCatᵒᵖ)) :=
    @Function.isEmpty _ _ spec_punit_isEmpty (Scheme.Spec.mapIso
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom
  have := preservesInitial_of_iso Scheme.Spec (asIso (initial.to _))
  exact preservesColimi

Depends on / 依赖: CommRingCat, CommRingCat.punitIsTerminal, Function, Function.isEmpty, IsEmpty, Scheme, Scheme.Spec, Scheme.Spec.mapIso, Scheme.Spec.obj, initial, initial.to, initialIsoIsInitial, initialOpOfTerminal, isEmpty, mapIso, preservesColimitsOfShape_pempty_of_preservesInitial, preservesInitial_of_iso, punitIsTerminal, spec_punit_isEmpty
-/
instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) Scheme.Spec.{u} := by
  have : IsEmpty (Scheme.Spec.obj (⊥_ CommRingCatᵒᵖ)) :=
    @Function.isEmpty _ _ spec_punit_isEmpty (Scheme.Spec.mapIso
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom
  have := preservesInitial_of_iso Scheme.Spec (asIso (initial.to _))
  exact preservesColimitsOfShape_pempty_of_preservesInitial _

instance {J : Type*} [Finite J] : PreservesColimitsOfShape (Discrete J) Scheme.Spec.{u} :=
  PreservesFiniteCoproducts.of_preserves_binary_and_initial _ _

/-- The canonical map `∐ Spec Rᵢ ⟶ Spec (Π Rᵢ)`.
This is an isomorphism when the product is finite. -/
noncomputable
/--
Definition of `sigmaSpec` / `sigmaSpec` 的定义

English:
definition sigmaSpec
  signature: (R : ι -> CommRingCat)
  body: Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)))

@[reassoc (attr := simp)]

中文:
定义 sigmaSpec
  签名: (R : ι -> 交换环范畴)
  定义体: Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)))

@[reassoc (attr := simp)]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Pi.evalRingHom, Sigma.desc, Spec.map, evalRingHom
-/
def sigmaSpec (R : ι -> CommRingCat) : (∐ fun i => Spec (R i)) ⟶ Spec (.of <| Π i, R i) :=
  Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)))

@[reassoc (attr := simp)]
/--
lemma `ι_sigmaSpec` / 引理 `ι_sigmaSpec`

English:
lemma ι_sigmaSpec
  given: (R : ι -> CommRingCat) (i)
  proof: Sigma.ι_desc _ _

中文:
引理 ι_sigmaSpec
  条件: (R : ι -> 交换环范畴) (i)
  证明: Sigma.ι_desc _ _
-/
lemma ι_sigmaSpec (R : ι -> CommRingCat) (i) :
    Sigma.ι _ i ≫ sigmaSpec R = Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) :=
  Sigma.ι_desc _ _

instance (i) (R : ι -> Type _) [forall i, CommRing (R i)] :
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

instance (R : ι -> CommRingCat.{u}) : IsOpenImmersion (sigmaSpec R) := by
  classical
  apply isOpenImmersion_sigmaDesc
  intro ix iy h
  refine Set.disjoint_iff_forall_ne.mpr ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ e
  have : DFinsupp.single (β := (R ·)) iy 1 iy in y.asIdeal :=
    (PrimeSpectrum.ext_iff.mp e).le (x := DFinsupp.single iy 1)
      (show DFinsupp.single (β := (R ·)) iy 1 ix in x.asIdeal by simp [h.symm])
  simp [← Ideal.eq_top_iff_one, y.2.ne_top] at this

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] (R
  body: by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1
    simp; rfl
  rw [this]
  infer_instance

中文:
实例 [有限
  签名: ι] (R
  定义体: by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1
    simp; rfl
  rw [this]
  infer_instance

Depends on / 依赖: CommRingCat, CommRingCat.piFanIsLimit, Discrete, Discrete.natIsoFunctor.symm, Fan.IsLimit.op, IsColimit, IsColimit.precomposeHomEquiv, IsLimit, Scheme, Scheme.Spec, colimit, colimit.isoColimitCocone, infer_instance, isColimitOfPreserves, isoColimitCocone, natIsoFunctor, piFanIsLimit, precomposeHomEquiv, sigmaSpec
-/
instance [Finite ι] (R : ι -> CommRingCat.{u}) : IsIso (sigmaSpec R) := by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1
    simp; rfl
  rw [this]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: σ] [forall i, IsAffine (g i)] : IsAffine (∐ g)
  body: by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  have (i : _) : IsAffine ((g ∘ e.symm) i) := by dsimp; infer_instance
  exact IsAffine.of_isIso ((Sigma.reindex e.symm g).inv ≫
    (Sigma.mapIso (fun i => Scheme.isoSpec _)).hom ≫ sigmaSpec _)

中文:
实例 [有限
  签名: σ] [对任意 i, 是仿射 (g i)] : 是仿射 (∐ g)
  定义体: by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  have (i : _) : IsAffine ((g ∘ e.symm) i) := by dsimp; infer_instance
  exact IsAffine.of_isIso ((Sigma.reindex e.symm g).inv ≫
    (Sigma.mapIso (fun i => Scheme.isoSpec _)).hom ≫ sigmaSpec _)

Depends on / 依赖: Finite, IsAffine, IsAffine.of_isIso, Scheme, Scheme.isoSpec, Sigma.mapIso, Sigma.reindex, Small.equiv_small, e.finite_iff.mp, e.symm, equiv_small, finite_iff, infer_instance, isoSpec, mapIso, of_isIso, reindex, sigmaSpec
-/
instance [Finite σ] [forall i, IsAffine (g i)] : IsAffine (∐ g) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  have (i : _) : IsAffine ((g ∘ e.symm) i) := by dsimp; infer_instance
  exact IsAffine.of_isIso ((Sigma.reindex e.symm g).inv ≫
    (Sigma.mapIso (fun i => Scheme.isoSpec _)).hom ≫ sigmaSpec _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAffine
  signature: X] [IsAffine Y] : IsAffine (X ⨿ Y)
  body: .of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

中文:
实例 [是仿射
  签名: X] [是仿射 Y] : 是仿射 (X ⨿ Y)
  定义体: .of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

Depends on / 依赖: X.isoSpec, Y.isoSpec, coprod, coprod.mapIso, coprodSpec, isoSpec, mapIso, of_isIso
-/
instance [IsAffine X] [IsAffine Y] : IsAffine (X ⨿ Y) :=
  .of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/--
lemma `IsAffineOpen.iSup_of_disjoint_aux` / 引理 `IsAffineOpen.iSup_of_disjoint_aux`

English:
lemma IsAffineOpen.iSup_of_disjoint_aux
  statement: [Finite ι] {U : ι -> X.Opens}
  proof: by
  have := isOpenImmersion_sigmaDesc _ (fun i => (U i).ι)
    (fun i j e => by convert hU' e; simp [← Opens.coe_disjoint])
  convert! isAffineOpen_opensRange (Sigma.desc fun i => (U i).ι)
  · ext
    simp [(sigmaMk _).symm.exists_congr_left, ← Scheme.Hom.comp_apply, Scheme.Opens.exists_toScheme]
 

中文:
引理 是仿射开集.iSup_of_disjoint_aux
  结论: [有限 ι] {U : ι -> X.Opens}
  证明: by
  have := isOpenImmersion_sigmaDesc _ (fun i => (U i).ι)
    (fun i j e => by convert hU' e; simp [← Opens.coe_disjoint])
  convert! isAffineOpen_opensRange (Sigma.desc fun i => (U i).ι)
  · ext
    simp [(sigmaMk _).symm.exists_congr_left, ← Scheme.Hom.comp_apply, Scheme.Opens.exists_toScheme]
 
-/
private lemma IsAffineOpen.iSup_of_disjoint_aux [Finite ι] {U : ι -> X.Opens}
    (hU : forall i, IsAffineOpen (U i)) (hU' : Pairwise (Disjoint on U)) :
    IsAffineOpen (iSup U) := by
  have := isOpenImmersion_sigmaDesc _ (fun i => (U i).ι)
    (fun i j e => by convert hU' e; simp [← Opens.coe_disjoint])
  convert! isAffineOpen_opensRange (Sigma.desc fun i => (U i).ι)
  · ext
    simp [(sigmaMk _).symm.exists_congr_left, ← Scheme.Hom.comp_apply, Scheme.Opens.exists_toScheme]
  · have (i : _) : IsAffine _ := hU i
    infer_instance

open scoped Function in
/--
lemma `IsAffineOpen.iSup_of_disjoint` / 引理 `IsAffineOpen.iSup_of_disjoint`

English:
lemma IsAffineOpen.iSup_of_disjoint
  statement: [Finite σ] {U : σ -> X.Opens}
  proof: by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  rw [← e.symm.iSup_congr fun _ => rfl]
  exact .iSup_of_disjoint_aux (by simp [*]) fun i j h => hU' (e.symm.injective.ne h)

中文:
引理 是仿射开集.iSup_of_disjoint
  结论: [有限 σ] {U : σ -> X.Opens}
  证明: by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  rw [← e.symm.iSup_congr fun _ => rfl]
  exact .iSup_of_disjoint_aux (by simp [*]) fun i j h => hU' (e.symm.injective.ne h)

Depends on / 依赖: Finite, Small.equiv_small, e.finite_iff.mp, e.symm.iSup_congr, e.symm.injective.ne, equiv_small, finite_iff, iSup_congr, iSup_of_disjoint_aux, injective
-/
lemma IsAffineOpen.iSup_of_disjoint [Finite σ] {U : σ -> X.Opens}
    (hU : forall i, IsAffineOpen (U i)) (hU' : Pairwise (Disjoint on U)) :
    IsAffineOpen (iSup U) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  rw [← e.symm.iSup_congr fun _ => rfl]
  exact .iSup_of_disjoint_aux (by simp [*]) fun i j h => hU' (e.symm.injective.ne h)

open scoped Function in
/--
lemma `IsAffineOpen.biSup_of_disjoint` / 引理 `IsAffineOpen.biSup_of_disjoint`

English:
lemma IsAffineOpen.biSup_of_disjoint
  statement: {s : Set σ} (hs : s.Finite)
  proof: by
  rw [← iSup_subtype'']
  have := hs.to_subtype
  exact .iSup_of_disjoint (by simpa) fun i j e => hU' i.2 j.2 (by aesop)

中文:
引理 是仿射开集.biSup_of_disjoint
  结论: {s : 集合 σ} (hs : s.有限)
  证明: by
  rw [← iSup_subtype'']
  have := hs.to_subtype
  exact .iSup_of_disjoint (by simpa) fun i j e => hU' i.2 j.2 (by aesop)

Depends on / 依赖: SimplicialObject, SimplicialObject.Truncated.cosk.fullyFaithful, Truncated, fullyFaithful, hs.to_subtype, iSup_of_disjoint, iSup_subtype, to_subtype
-/
lemma IsAffineOpen.biSup_of_disjoint {s : Set σ} (hs : s.Finite)
    {U : σ -> X.Opens} (hU : forall i in s, IsAffineOpen (U i)) (hU' : s.Pairwise (Disjoint on U)) :
    IsAffineOpen (⨆ i in s, U i) := by
  rw [← iSup_subtype'']
  have := hs.to_subtype
  exact .iSup_of_disjoint (by simpa) fun i j e => hU' i.2 j.2 (by aesop)

/--
lemma `IsAffineOpen.sup_of_disjoint` / 引理 `IsAffineOpen.sup_of_disjoint`

English:
lemma IsAffineOpen.sup_of_disjoint
  statement: {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  proof: by
  convert!
    iSup_of_disjoint (U := fun i : Unit oplus Unit => i.elim (fun _ => U) (fun _ => V)) (by simp_all)
      (by simp_all [_root_.Pairwise, Unique.forall_iff, ← Opens.coe_disjoint, disjoint_comm])
  aesop

中文:
引理 是仿射开集.sup_of_disjoint
  结论: {U V : X.Opens} (hU : 是仿射开集 U) (hV : 是仿射开集 V)
  证明: by
  convert!
    iSup_of_disjoint (U := fun i : Unit oplus Unit => i.elim (fun _ => U) (fun _ => V)) (by simp_all)
      (by simp_all [_root_.Pairwise, Unique.forall_iff, ← Opens.coe_disjoint, disjoint_comm])
  aesop

Depends on / 依赖: Opens.coe_disjoint, Pairwise, SimplicialObject, SimplicialObject.Truncated.cosk.full, Truncated, Unique, Unique.forall_iff, _root_, _root_.Pairwise, coe_disjoint, convert, disjoint_comm, forall_iff, i.elim, iSup_of_disjoint
-/
lemma IsAffineOpen.sup_of_disjoint {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (H : Disjoint U V) :
    IsAffineOpen (U ⊔ V) := by
  convert!
    iSup_of_disjoint (U := fun i : Unit oplus Unit => i.elim (fun _ => U) (fun _ => V)) (by simp_all)
      (by simp_all [_root_.Pairwise, Unique.forall_iff, ← Opens.coe_disjoint, disjoint_comm])
  aesop

instance (priority := low) [Finite X] [DiscreteTopology X] : IsAffine X :=
  have : IsAffineOpen (⨆ (x : X), (⟨{x}, isOpen_discrete _⟩ : X.Opens)) :=
    .iSup_of_disjoint (fun i => .of_subsingleton Set.subsingleton_singleton)
      fun i j e => by simpa [← TopologicalSpace.Opens.coe_disjoint]
  have : IsAffine (⊤ : X.Opens).toScheme := show IsAffineOpen _ by convert! this; ext; simp
  .of_isIso X.topIso.inv

end Coproduct

instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (i : WalkingPair) : Mono ((span f g ⋙ Scheme.forget).map (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using! f.isOpenEmbedding.injective
  · simpa using! g.isOpenEmbedding.injective

instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    {i j : WalkingSpan} (t : i ⟶ j) : IsOpenImmersion ((span f g).map t) := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa

-- Test that instances on locally directed colimits fire correctly.
example {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] : HasPushout f g :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CartesianMonoidalCategory Scheme
  body: .ofHasFiniteProducts

中文:
实例 :
  签名: CartesianMonoidal范畴 概形
  定义体: .ofHasFiniteProducts

Depends on / 依赖: SimplicialObject, SimplicialObject.Truncated.cosk.faithful, Truncated, faithful, ofHasFiniteProducts
-/
instance : CartesianMonoidalCategory Scheme := .ofHasFiniteProducts
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory Scheme
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: 辫范畴 概形
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: SimplicialObject, SimplicialObject.Truncated.coskAdj.reflective, Truncated, coskAdj, ofCartesianMonoidalCategory, reflective
-/
instance : BraidedCategory Scheme := .ofCartesianMonoidalCategory

section IsAffine

/--
lemma `Scheme.isAffine_of_isLimit` / 引理 `Scheme.isAffine_of_isLimit`

English:
lemma Scheme.isAffine_of_isLimit
  statement: {I : Type*} [Category* I] {D : I ⥤ Scheme.{u}}
  proof: by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : c.pt ≅ Spec Γ(c.pt, ⊤) := hc.conePointUniqueUpToIso ((IsLimit.postcomposeHomEquiv
    (asIso α).sy

中文:
引理 概形.isAffine_of_isLimit
  结论: {I : 类型} [范畴* I] {D : I ⥤ 概形.{u}}
  证明: by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : c.pt ≅ Spec Γ(c.pt, ⊤) := hc.conePointUniqueUpToIso ((IsLimit.postcomposeHomEquiv
    (asIso α).sy

Depends on / 依赖: D.whiskerLeft, IsAffine, IsAffine.affine, IsLimit, IsLimit.postcomposeHomEquiv, NatIso, NatIso.isIso_of_isIso_app, Scheme, Scheme.Spec, SimplicialObject, SimplicialObject.Truncated.sk.fullyFaithful, Spec.adjunction.unit, Truncated, adjunction, affine, c.pt, conePointUniqueUpToIso, fullyFaithful, hc.conePointUniqueUpToIso, isIso_of_isIso_app
-/
lemma Scheme.isAffine_of_isLimit {I : Type*} [Category* I] {D : I ⥤ Scheme.{u}}
    (c : Cone D) (hc : IsLimit c) [forall i, IsAffine (D.obj i)] :
    IsAffine c.pt := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : c.pt ≅ Spec Γ(c.pt, ⊤) := hc.conePointUniqueUpToIso ((IsLimit.postcomposeHomEquiv
    (asIso α).symm _).symm (isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc))
  exact .of_isIso this.hom

end IsAffine

end AlgebraicGeometry
