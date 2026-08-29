/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Sieves

/-!
# The sheaf condition for a presieve

We define what it means for a presheaf `P : Cᵒᵖ ⥤ Type v` to be a sheaf *for* a particular
presieve `R` on `X`:
* A *family of elements* `x` for `P` at `R` is an element `x_f` of `P Y` for every `f : Y ⟶ X` in
  `R`. See `FamilyOfElements`.
* The family `x` is *compatible* if, for any `f₁ : Y₁ ⟶ X` and `f₂ : Y₂ ⟶ X` both in `R`,
  and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂` such that `g₁ ≫ f₁ = g₂ ≫ f₂`, the restriction of
  `x_f₁` along `g₁` agrees with the restriction of `x_f₂` along `g₂`.
  See `FamilyOfElements.Compatible`.
* An *amalgamation* `t` for the family is an element of `P X` such that for every `f : Y ⟶ X` in
  `R`, the restriction of `t` on `f` is `x_f`.
  See `FamilyOfElements.IsAmalgamation`.

We then say `P` is *separated* for `R` if every compatible family has at most one amalgamation,
and it is a *sheaf* for `R` if every compatible family has a unique amalgamation.
See `IsSeparatedFor` and `IsSheafFor`.

In the special case where `R` is a sieve, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` in `R` and `g : Z ⟶ Y`, the restriction of
  `x_f` along `g` agrees with `x_(g ≫ f)` (which is well defined since `g ≫ f` is in `R`).
  See `FamilyOfElements.SieveCompatible` and `compatible_iff_sieveCompatible`.

In the special case where `C` has pullbacks, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` and `g : Z ⟶ X` both in `R`,
  the restriction of `x_f` along `π₁ : pullback f g ⟶ Y` agrees with the restriction of `x_g`
  along `π₂ : pullback f g ⟶ Z`.
  See `FamilyOfElements.PullbackCompatible` and `pullbackCompatible_iff`.

We also provide equivalent conditions to satisfy alternate definitions given in the literature.

* Stacks: The condition of https://stacks.math.columbia.edu/tag/00Z8 is virtually identical to the
  statement of `isSheafFor_iff_yonedaSheafCondition` (since the bijection described there carries
  the same information as the unique existence.)

* Maclane-Moerdijk [MM92]: Using `compatible_iff_sieveCompatible`, the definitions of `IsSheaf`
  are equivalent. There are also alternate definitions given:
  - Yoneda condition: Defined in `yonedaSheafCondition` and equivalence in
    `isSheafFor_iff_yonedaSheafCondition`.
  - Matching family for presieves with pullback: `pullbackCompatible_iff`.

## Implementation

The sheaf condition is given as a proposition, rather than a subsingleton in `Type (max u₁ v)`.
This doesn't seem to make a big difference, other than making a couple of definitions noncomputable,
but it means that equivalent conditions can be given as `↔` statements rather than `≃` statements,
which can be convenient.

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)
* https://stacks.math.columbia.edu/tag/00ZB (sheaves on a topology)

-/

@[expose] public section


universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presieve

variable {C : Type u₁} [Category.{v₁} C]
variable {P Q U : Cᵒᵖ ⥤ Type w}
variable {X Y : C} {S : Sieve X} {R : Presieve X}

/-- A family of elements for a presheaf `P` given a collection of arrows `R` with fixed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *compatible* family of elements has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is also a concrete
version of the elements of the middle object in the Stacks entry which is
more useful for direct calculations. It is also used implicitly in Definition C2.1.2 in [Elephant].
-/
@[stacks 00VM "This is a concrete version of the elements of the middle object there."]
/--
Definition of `FamilyOfElements` / `FamilyOfElements` 的定义

English:
definition FamilyOfElements
  signature: (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
  body: forall ⦃Y : C⦄ (f : Y ⟶ X), R f -> P.obj (op Y)

中文:
定义 FamilyOfElements
  签名: (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
  定义体: forall ⦃Y : C⦄ (f : Y ⟶ X), R f -> P.obj (op Y)

Depends on / 依赖: P.obj
-/
def FamilyOfElements (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) :=
  forall ⦃Y : C⦄ (f : Y ⟶ X), R f -> P.obj (op Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FamilyOfElements P (⊥ : Presieve X))
  body: ⟨fun _ _ => False.elim⟩

@[ext]

中文:
实例 :
  签名: Inhabited (FamilyOfElements P (⊥ : Presieve X))
  定义体: ⟨fun _ _ => False.elim⟩

@[ext]

Depends on / 依赖: False.elim
-/
instance : Inhabited (FamilyOfElements P (⊥ : Presieve X)) :=
  ⟨fun _ _ => False.elim⟩

@[ext]
/--
lemma `FamilyOfElements.ext` / 引理 `FamilyOfElements.ext`

English:
lemma FamilyOfElements.ext
  statement: {R : Presieve X} {x y : R.FamilyOfElements P}
  proof: by
  funext Z f hf
  exact H f hf

中文:
引理 FamilyOfElements.ext
  结论: {R : Presieve X} {x y : R.FamilyOfElements P}
  证明: by
  funext Z f hf
  exact H f hf
-/
lemma FamilyOfElements.ext {R : Presieve X} {x y : R.FamilyOfElements P}
    (H : forall {Y : C} (f : Y ⟶ X) (hf : R f), x f hf = y f hf) :
    x = y := by
  funext Z f hf
  exact H f hf

/--
Definition of `FamilyOfElements.restrict` / `FamilyOfElements.restrict` 的定义

English:
definition FamilyOfElements.restrict
  signature: {R₁ R₂ : Presieve X} (h : R₁ <= R₂)
  body: fun x _ f hf => x f (h _ _ hf)

中文:
定义 FamilyOfElements.restrict
  签名: {R₁ R₂ : Presieve X} (h : R₁ <= R₂)
  定义体: fun x _ f hf => x f (h _ _ hf)
-/
def FamilyOfElements.restrict {R₁ R₂ : Presieve X} (h : R₁ <= R₂) :
    FamilyOfElements P R₂ -> FamilyOfElements P R₁ := fun x _ f hf => x f (h _ _ hf)

/--
Definition of `FamilyOfElements.map` / `FamilyOfElements.map` 的定义

English:
definition FamilyOfElements.map
  signature: (p : FamilyOfElements P R) (φ : P ⟶ Q)
  body: fun _ f hf => φ.app _ (p f hf)

@[simp]

中文:
定义 FamilyOfElements.map
  签名: (p : FamilyOfElements P R) (φ : P ⟶ Q)
  定义体: fun _ f hf => φ.app _ (p f hf)

@[simp]
-/
def FamilyOfElements.map (p : FamilyOfElements P R) (φ : P ⟶ Q) :
    FamilyOfElements Q R :=
  fun _ f hf => φ.app _ (p f hf)

@[simp]
/--
lemma `FamilyOfElements.map_apply` / 引理 `FamilyOfElements.map_apply`

English:
lemma FamilyOfElements.map_apply
  proof: rfl

中文:
引理 FamilyOfElements.map_apply
  证明: rfl
-/
lemma FamilyOfElements.map_apply
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {Y : C} (f : Y ⟶ X) (hf : R f) :
    p.map φ f hf = φ.app _ (p f hf) := rfl

/--
lemma `FamilyOfElements.restrict_map` / 引理 `FamilyOfElements.restrict_map`

English:
lemma FamilyOfElements.restrict_map
  proof: rfl

中文:
引理 FamilyOfElements.restrict_map
  证明: rfl
-/
lemma FamilyOfElements.restrict_map
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {R' : Presieve X} (h : R' <= R) :
    (p.restrict h).map φ = (p.map φ).restrict h := rfl

variable (P) in
/-- A family of elements on `{ f : X ⟶ Y }` is an element of `F(X)`. -/
@[simps apply, simps -isSimp symm_apply]
/--
Definition of `FamilyOfElements.singletonEquiv` / `FamilyOfElements.singletonEquiv` 的定义

English:
definition FamilyOfElements.singletonEquiv
  signature: {X Y : C} (f : X ⟶ Y)
  body: x f (by simp)
  invFun x Z g hg := P.map (eqToHom <| by cases hg; rfl).op x
  left_inv x := by ext _ _ ⟨rfl⟩; simp
  right_inv x := by simp

@[simp]

中文:
定义 FamilyOfElements.singletonEquiv
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: x f (by simp)
  invFun x Z g hg := P.map (eqToHom <| by cases hg; rfl).op x
  left_inv x := by ext _ _ ⟨rfl⟩; simp
  right_inv x := by simp

@[simp]
-/
def FamilyOfElements.singletonEquiv {X Y : C} (f : X ⟶ Y) :
    (singleton f).FamilyOfElements P ≃ P.obj (op X) where
  toFun x := x f (by simp)
  invFun x Z g hg := P.map (eqToHom <| by cases hg; rfl).op x
  left_inv x := by ext _ _ ⟨rfl⟩; simp
  right_inv x := by simp

@[simp]
/--
lemma `FamilyOfElements.singletonEquiv_symm_apply_self` / 引理 `FamilyOfElements.singletonEquiv_symm_apply_self`

English:
lemma FamilyOfElements.singletonEquiv_symm_apply_self
  given: {X Y : C} (f : X ⟶ Y) (x : P.obj (op X))
  proof: by
  simp [singletonEquiv_symm_apply]

中文:
引理 FamilyOfElements.singletonEquiv_symm_apply_self
  条件: {X Y : C} (f : X ⟶ Y) (x : P.obj (op X))
  证明: by
  simp [singletonEquiv_symm_apply]

Depends on / 依赖: singletonEquiv_symm_apply
-/
lemma FamilyOfElements.singletonEquiv_symm_apply_self {X Y : C} (f : X ⟶ Y) (x : P.obj (op X)) :
    (singletonEquiv P f).symm x f ⟨⟩ = x := by
  simp [singletonEquiv_symm_apply]

/--
Definition of `FamilyOfElements.Compatible` / `FamilyOfElements.Compatible` 的定义

English:
definition FamilyOfElements.Compatible
  signature: (x : FamilyOfElements P R)
  body: forall ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ -> P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

中文:
定义 FamilyOfElements.Compatible
  签名: (x : FamilyOfElements P R)
  定义体: forall ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ -> P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

Depends on / 依赖: P.map
-/
def FamilyOfElements.Compatible (x : FamilyOfElements P R) : Prop :=
  forall ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ -> P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

/--
Definition of `FamilyOfElements.PullbackCompatible` / `FamilyOfElements.PullbackCompatible` 的定义

English:
definition FamilyOfElements.PullbackCompatible
  signature: (x : FamilyOfElements P R) [R.HasPairwisePullbacks]
  body: forall ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := HasPairwisePullbacks.has_pullbacks h₁ h₂
    P.map (pullback.fst f₁ f₂).op (x f₁ h₁) = P.map (pullback.snd f₁ f₂).op (x f₂ h₂)

中文:
定义 FamilyOfElements.PullbackCompatible
  签名: (x : FamilyOfElements P R) [R.HasPairwisePullbacks]
  定义体: forall ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := HasPairwisePullbacks.has_pullbacks h₁ h₂
    P.map (pullback.fst f₁ f₂).op (x f₁ h₁) = P.map (pullback.snd f₁ f₂).op (x f₂ h₂)

Depends on / 依赖: HasPairwisePullbacks, HasPairwisePullbacks.has_pullbacks, P.map, has_pullbacks, pullback, pullback.fst, pullback.snd
-/
def FamilyOfElements.PullbackCompatible (x : FamilyOfElements P R) [R.HasPairwisePullbacks] :
    Prop :=
  forall ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := HasPairwisePullbacks.has_pullbacks h₁ h₂
    P.map (pullback.fst f₁ f₂).op (x f₁ h₁) = P.map (pullback.snd f₁ f₂).op (x f₂ h₂)

/--
theorem `pullbackCompatible_iff` / 定理 `pullbackCompatible_iff`

English:
theorem pullbackCompatible_iff
  given: (x : FamilyOfElements P R) [R.HasPairwisePullbacks]
  proof: by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm]; rw [op_comp]; rw

中文:
定理 pullbackCompatible_iff
  条件: (x : FamilyOfElements P R) [R.HasPairwisePullbacks]
  证明: by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm]; rw [op_comp]; rw

Depends on / 依赖: Functor, Functor.map_comp, HasPairwisePullbacks, HasPairwisePullbacks.has_pullbacks, comp_apply, condition, has_pullbacks, lift_fst, lift_snd, map_comp, op_comp, pullback, pullback.condition, pullback.lift_fst, pullback.lift_snd
-/
theorem pullbackCompatible_iff (x : FamilyOfElements P R) [R.HasPairwisePullbacks] :
    x.Compatible ↔ x.PullbackCompatible := by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply]; rw [t hf₁ hf₂]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [pullback.lift_snd]

/--
theorem `FamilyOfElements.Compatible.restrict` / 定理 `FamilyOfElements.Compatible.restrict`

English:
theorem FamilyOfElements.Compatible.restrict
  statement: {R₁ R₂ : Presieve X} (h : R₁ <= R₂)
  proof: fun q _ _ _ g₁ g₂ _ _ h₁ h₂ comm => q g₁ g₂ (h _ _ h₁) (h _ _ h₂) comm

中文:
定理 FamilyOfElements.Compatible.restrict
  结论: {R₁ R₂ : Presieve X} (h : R₁ <= R₂)
  证明: fun q _ _ _ g₁ g₂ _ _ h₁ h₂ comm => q g₁ g₂ (h _ _ h₁) (h _ _ h₂) comm
-/
theorem FamilyOfElements.Compatible.restrict {R₁ R₂ : Presieve X} (h : R₁ <= R₂)
    {x : FamilyOfElements P R₂} : x.Compatible -> (x.restrict h).Compatible :=
  fun q _ _ _ g₁ g₂ _ _ h₁ h₂ comm => q g₁ g₂ (h _ _ h₁) (h _ _ h₂) comm

/--
Definition of `FamilyOfElements.sieveExtend` / `FamilyOfElements.sieveExtend` 的定义

English:
definition FamilyOfElements.sieveExtend
  signature: (x : FamilyOfElements P R)
  body: fun _ _ hf =>
  P.map hf.choose_spec.choose.op (x _ hf.choose_spec.choose_spec.choose_spec.1)

中文:
定义 FamilyOfElements.sieveExtend
  签名: (x : FamilyOfElements P R)
  定义体: fun _ _ hf =>
  P.map hf.choose_spec.choose.op (x _ hf.choose_spec.choose_spec.choose_spec.1)
-/
noncomputable def FamilyOfElements.sieveExtend (x : FamilyOfElements P R) :
    FamilyOfElements P (generate R : Presieve X) := fun _ _ hf =>
  P.map hf.choose_spec.choose.op (x _ hf.choose_spec.choose_spec.choose_spec.1)

/--
theorem `FamilyOfElements.Compatible.sieveExtend` / 定理 `FamilyOfElements.Compatible.sieveExtend`

English:
theorem FamilyOfElements.Compatible.sieveExtend
  given: {x : FamilyOfElements P R} (hx : x.Compatible)
  proof: by
  intro _ _ _ _ _ _ _ h₁ h₂ comm
  simp only [FamilyOfElements.sieveExtend, ← comp_apply, ← Functor.map_comp, ← op_comp]
  apply hx
  simp [comm, h₁.choose_spec.choose_spec.choose_spec.2, h₂.choose_spec.choose_spec.choose_spec.2]

中文:
定理 FamilyOfElements.Compatible.sieveExtend
  条件: {x : FamilyOfElements P R} (hx : x.Compatible)
  证明: by
  intro _ _ _ _ _ _ _ h₁ h₂ comm
  simp only [FamilyOfElements.sieveExtend, ← comp_apply, ← Functor.map_comp, ← op_comp]
  apply hx
  simp [comm, h₁.choose_spec.choose_spec.choose_spec.2, h₂.choose_spec.choose_spec.choose_spec.2]

Depends on / 依赖: FamilyOfElements, FamilyOfElements.sieveExtend, Functor, Functor.map_comp, choose_spec, choose_spec.choose_spec.choose_spec, comp_apply, map_comp, op_comp, sieveExtend
-/
theorem FamilyOfElements.Compatible.sieveExtend {x : FamilyOfElements P R} (hx : x.Compatible) :
    x.sieveExtend.Compatible := by
  intro _ _ _ _ _ _ _ h₁ h₂ comm
  simp only [FamilyOfElements.sieveExtend, ← comp_apply, ← Functor.map_comp, ← op_comp]
  apply hx
  simp [comm, h₁.choose_spec.choose_spec.choose_spec.2, h₂.choose_spec.choose_spec.choose_spec.2]

/--
theorem `extend_agrees` / 定理 `extend_agrees`

English:
theorem extend_agrees
  given: {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f)
  proof: by
  have h := (le_generate R Y _ hf).choose_spec
  unfold FamilyOfElements.sieveExtend
  rw [t h.choose (𝟙 _) _ hf _]
  · simp
  · rw [id_comp]
    exact h.choose_spec.choose_spec.2

中文:
定理 extend_agrees
  条件: {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f)
  证明: by
  have h := (le_generate R Y _ hf).choose_spec
  unfold FamilyOfElements.sieveExtend
  rw [t h.choose (𝟙 _) _ hf _]
  · simp
  · rw [id_comp]
    exact h.choose_spec.choose_spec.2

Depends on / 依赖: FamilyOfElements, FamilyOfElements.sieveExtend, choose_spec, h.choose, h.choose_spec.choose_spec, id_comp, le_generate, sieveExtend
-/
theorem extend_agrees {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f) :
    x.sieveExtend f (le_generate R Y _ hf) = x f hf := by
  have h := (le_generate R Y _ hf).choose_spec
  unfold FamilyOfElements.sieveExtend
  rw [t h.choose (𝟙 _) _ hf _]
  · simp
  · rw [id_comp]
    exact h.choose_spec.choose_spec.2

/-- The restriction of an extension is the original. -/
@[simp]
/--
theorem `restrict_extend` / 定理 `restrict_extend`

English:
theorem restrict_extend
  given: {x : FamilyOfElements P R} (t : x.Compatible)
  proof: by
  funext Y f hf
  exact extend_agrees t hf

中文:
定理 restrict_extend
  条件: {x : FamilyOfElements P R} (t : x.Compatible)
  证明: by
  funext Y f hf
  exact extend_agrees t hf

Depends on / 依赖: extend_agrees
-/
theorem restrict_extend {x : FamilyOfElements P R} (t : x.Compatible) :
    x.sieveExtend.restrict (le_generate R) = x := by
  funext Y f hf
  exact extend_agrees t hf

/--
lemma `FamilyOfElements.Compatible.of_mono` / 引理 `FamilyOfElements.Compatible.of_mono`

English:
lemma FamilyOfElements.Compatible.of_mono
  statement: (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
  proof: by
  intro Y Z W g₁ g₂ f₁ f₂ hf₁ hf₂ heq
  refine injective_of_mono (f.app _) ?_
  simpa using hx _ _ hf₁ hf₂ heq

中文:
引理 FamilyOfElements.Compatible.of_mono
  结论: (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
  证明: by
  intro Y Z W g₁ g₂ f₁ f₂ hf₁ hf₂ heq
  refine injective_of_mono (f.app _) ?_
  simpa using hx _ _ hf₁ hf₂ heq

Depends on / 依赖: f.app, injective_of_mono
-/
lemma FamilyOfElements.Compatible.of_mono (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
    (hx : (x.map f).Compatible) :
    x.Compatible := by
  intro Y Z W g₁ g₂ f₁ f₂ hf₁ hf₂ heq
  refine injective_of_mono (f.app _) ?_
  simpa using hx _ _ hf₁ hf₂ heq

/--
Definition of `FamilyOfElements.SieveCompatible` / `FamilyOfElements.SieveCompatible` 的定义

English:
definition FamilyOfElements.SieveCompatible
  signature: (x : FamilyOfElements P (S : Presieve X))
  body: forall ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)

中文:
定义 FamilyOfElements.SieveCompatible
  签名: (x : FamilyOfElements P (S : Presieve X))
  定义体: forall ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)

Depends on / 依赖: P.map, S.downward_closed, downward_closed, g.op
-/
def FamilyOfElements.SieveCompatible (x : FamilyOfElements P (S : Presieve X)) : Prop :=
  forall ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)

/--
theorem `compatible_iff_sieveCompatible` / 定理 `compatible_iff_sieveCompatible`

English:
theorem compatible_iff_sieveCompatible
  given: (x : FamilyOfElements P (S : Presieve X))
  proof: by
  constructor
  · intro h Y Z f g hf
    simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
  · intro h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k
    simp_rw [← h f₁ g₁ h₁, ← h f₂ g₂ h₂]
    congr

中文:
定理 compatible_iff_sieveCompatible
  条件: (x : FamilyOfElements P (S : Presieve X))
  证明: by
  constructor
  · intro h Y Z f g hf
    simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
  · intro h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k
    simp_rw [← h f₁ g₁ h₁, ← h f₂ g₂ h₂]
    congr

Depends on / 依赖: S.downward_closed, downward_closed, id_comp, simp_rw
-/
theorem compatible_iff_sieveCompatible (x : FamilyOfElements P (S : Presieve X)) :
    x.Compatible ↔ x.SieveCompatible := by
  constructor
  · intro h Y Z f g hf
    simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
  · intro h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k
    simp_rw [← h f₁ g₁ h₁, ← h f₂ g₂ h₂]
    congr

/--
theorem `FamilyOfElements.Compatible.to_sieveCompatible` / 定理 `FamilyOfElements.Compatible.to_sieveCompatible`

English:
theorem FamilyOfElements.Compatible.to_sieveCompatible
  statement: {x : FamilyOfElements P (S : Presieve X)}
  proof: (compatible_iff_sieveCompatible x).1 t

中文:
定理 FamilyOfElements.Compatible.to_sieveCompatible
  结论: {x : FamilyOfElements P (S : Presieve X)}
  证明: (compatible_iff_sieveCompatible x).1 t

Depends on / 依赖: compatible_iff_sieveCompatible
-/
theorem FamilyOfElements.Compatible.to_sieveCompatible {x : FamilyOfElements P (S : Presieve X)}
    (t : x.Compatible) : x.SieveCompatible :=
  (compatible_iff_sieveCompatible x).1 t

/--
Given a family of elements `x` for the sieve `S` generated by a presieve `R`, if `x` is restricted
to `R` and then extended back up to `S`, the resulting extension equals `x`.
-/
@[simp]
/--
theorem `extend_restrict` / 定理 `extend_restrict`

English:
theorem extend_restrict
  given: {x : FamilyOfElements P (generate R).arrows} (t : x.Compatible)
  proof: by
  rw [compatible_iff_sieveCompatible] at t
  funext _ _ h
  apply (t _ _ _).symm.trans
  congr
  exact h.choose_spec.choose_spec.choose_spec.2

中文:
定理 extend_restrict
  条件: {x : FamilyOfElements P (generate R).arrows} (t : x.Compatible)
  证明: by
  rw [compatible_iff_sieveCompatible] at t
  funext _ _ h
  apply (t _ _ _).symm.trans
  congr
  exact h.choose_spec.choose_spec.choose_spec.2

Depends on / 依赖: choose_spec, compatible_iff_sieveCompatible, h.choose_spec.choose_spec.choose_spec, symm.trans
-/
theorem extend_restrict {x : FamilyOfElements P (generate R).arrows} (t : x.Compatible) :
    (x.restrict (le_generate R)).sieveExtend = x := by
  rw [compatible_iff_sieveCompatible] at t
  funext _ _ h
  apply (t _ _ _).symm.trans
  congr
  exact h.choose_spec.choose_spec.choose_spec.2

/--
theorem `restrict_inj` / 定理 `restrict_inj`

English:
theorem restrict_inj
  statement: {x₁ x₂ : FamilyOfElements P (generate R).arrows} (t₁ : x₁.Compatible)
  proof: fun h => by
  rw [← extend_restrict t₁]; rw [← extend_restrict t₂]
  congr

中文:
定理 restrict_inj
  结论: {x₁ x₂ : FamilyOfElements P (generate R).arrows} (t₁ : x₁.Compatible)
  证明: fun h => by
  rw [← extend_restrict t₁]; rw [← extend_restrict t₂]
  congr

Depends on / 依赖: extend_restrict
-/
theorem restrict_inj {x₁ x₂ : FamilyOfElements P (generate R).arrows} (t₁ : x₁.Compatible)
    (t₂ : x₂.Compatible) : x₁.restrict (le_generate R) = x₂.restrict (le_generate R) -> x₁ = x₂ :=
  fun h => by
  rw [← extend_restrict t₁]; rw [← extend_restrict t₂]
  congr

/-- Compatible families of elements for a presheaf of types `P` and a presieve `R`
are in 1-1 correspondence with compatible families for the same presheaf and
the sieve generated by `R`, through extension and restriction. -/
@[simps]
/--
Definition of `compatibleEquivGenerateSieveCompatible` / `compatibleEquivGenerateSieveCompatible` 的定义

English:
definition compatibleEquivGenerateSieveCompatible
  signature: :
  body: ⟨x.1.sieveExtend, x.2.sieveExtend⟩
  invFun x := ⟨x.1.restrict (le_generate R), x.2.restrict _⟩
  left_inv x := Subtype.ext (restrict_extend x.2)
  right_inv x := Subtype.ext (extend_restrict x.2)

中文:
定义 compatibleEquivGenerateSieveCompatible
  签名: :
  定义体: ⟨x.1.sieveExtend, x.2.sieveExtend⟩
  invFun x := ⟨x.1.restrict (le_generate R), x.2.restrict _⟩
  left_inv x := Subtype.ext (restrict_extend x.2)
  right_inv x := Subtype.ext (extend_restrict x.2)

Depends on / 依赖: sieveExtend
-/
noncomputable def compatibleEquivGenerateSieveCompatible :
    { x : FamilyOfElements P R // x.Compatible } ≃
      { x : FamilyOfElements P (generate R : Presieve X) // x.Compatible } where
  toFun x := ⟨x.1.sieveExtend, x.2.sieveExtend⟩
  invFun x := ⟨x.1.restrict (le_generate R), x.2.restrict _⟩
  left_inv x := Subtype.ext (restrict_extend x.2)
  right_inv x := Subtype.ext (extend_restrict x.2)

/--
theorem `FamilyOfElements.comp_of_compatible` / 定理 `FamilyOfElements.comp_of_compatible`

English:
theorem FamilyOfElements.comp_of_compatible
  statement: (S : Sieve X) {x : FamilyOfElements P S}
  proof: by
  simpa using t (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)

中文:
定理 FamilyOfElements.comp_of_compatible
  结论: (S : Sieve X) {x : FamilyOfElements P S}
  证明: by
  simpa using t (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)

Depends on / 依赖: S.downward_closed, downward_closed, id_comp
-/
theorem FamilyOfElements.comp_of_compatible (S : Sieve X) {x : FamilyOfElements P S}
    (t : x.Compatible) {f : Y ⟶ X} (hf : S f) {Z} (g : Z ⟶ Y) :
    x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf) := by
  simpa using t (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)

/--
lemma `FamilyOfElements.compatible_singleton_iff` / 引理 `FamilyOfElements.compatible_singleton_iff`

English:
lemma FamilyOfElements.compatible_singleton_iff
  proof: by
  refine ⟨fun H Z p₁ p₂ h => H _ _ _ _ h, fun H Y₁ Y₂ Z g₁ g₂ f₁ f₂ => ?_⟩
  rintro ⟨rfl⟩ ⟨rfl⟩ h
  exact H _ _ h

中文:
引理 FamilyOfElements.compatible_singleton_iff
  证明: by
  refine ⟨fun H Z p₁ p₂ h => H _ _ _ _ h, fun H Y₁ Y₂ Z g₁ g₂ f₁ f₂ => ?_⟩
  rintro ⟨rfl⟩ ⟨rfl⟩ h
  exact H _ _ h
-/
lemma FamilyOfElements.compatible_singleton_iff
    {X Y : C} (f : X ⟶ Y) (x : (singleton f).FamilyOfElements P) :
    x.Compatible ↔ forall {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f ->
      P.map p₁.op (x f ⟨⟩) = P.map p₂.op (x f ⟨⟩) := by
  refine ⟨fun H Z p₁ p₂ h => H _ _ _ _ h, fun H Y₁ Y₂ Z g₁ g₂ f₁ f₂ => ?_⟩
  rintro ⟨rfl⟩ ⟨rfl⟩ h
  exact H _ _ h

section FunctorPullback

variable {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C) {Z : D}
variable {T : Presieve (F.obj Z)} {x : FamilyOfElements P T}

/--
Definition of `FamilyOfElements.functorPullback` / `FamilyOfElements.functorPullback` 的定义

English:
definition FamilyOfElements.functorPullback
  signature: (x : FamilyOfElements P T)
  body: fun _ f hf => x (F.map f) hf

中文:
定义 FamilyOfElements.functorPullback
  签名: (x : FamilyOfElements P T)
  定义体: fun _ f hf => x (F.map f) hf

Depends on / 依赖: F.map
-/
def FamilyOfElements.functorPullback (x : FamilyOfElements P T) :
    FamilyOfElements (F.op ⋙ P) (T.functorPullback F) := fun _ f hf => x (F.map f) hf

/--
theorem `FamilyOfElements.Compatible.functorPullback` / 定理 `FamilyOfElements.Compatible.functorPullback`

English:
theorem FamilyOfElements.Compatible.functorPullback
  given: (h : x.Compatible)
  proof: by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])

中文:
定理 FamilyOfElements.Compatible.functorPullback
  条件: (h : x.Compatible)
  证明: by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])

Depends on / 依赖: F.map, F.map_comp, map_comp
-/
theorem FamilyOfElements.Compatible.functorPullback (h : x.Compatible) :
    (x.functorPullback F).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])

end FunctorPullback

/--
Definition of `FamilyOfElements.functorPushforward` / `FamilyOfElements.functorPushforward` 的定义

English:
definition FamilyOfElements.functorPushforward
  signature: {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)
  body: fun Y f h => by
  obtain ⟨Z, g, h, h₁, _⟩ := getFunctorPushforwardStructure h
  exact P.map h.op (x g h₁)

中文:
定义 FamilyOfElements.functorPushforward
  签名: {D : 类型u₂} [Category.{v₂} D] (F : D ⥤ C)
  定义体: fun Y f h => by
  obtain ⟨Z, g, h, h₁, _⟩ := getFunctorPushforwardStructure h
  exact P.map h.op (x g h₁)

Depends on / 依赖: P.map, getFunctorPushforwardStructure, h.op
-/
noncomputable def FamilyOfElements.functorPushforward {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)
    {X : D} {T : Presieve X} (x : FamilyOfElements (F.op ⋙ P) T) :
    FamilyOfElements P (T.functorPushforward F) := fun Y f h => by
  obtain ⟨Z, g, h, h₁, _⟩ := getFunctorPushforwardStructure h
  exact P.map h.op (x g h₁)

section Pullback

/--
Definition of `FamilyOfElements.pullback` / `FamilyOfElements.pullback` 的定义

English:
definition FamilyOfElements.pullback
  signature: (f : Y ⟶ X) (x : FamilyOfElements P (S : Presieve X))
  body: fun _ g hg => x (g ≫ f) hg

中文:
定义 FamilyOfElements.pullback
  签名: (f : Y ⟶ X) (x : FamilyOfElements P (S : Presieve X))
  定义体: fun _ g hg => x (g ≫ f) hg
-/
def FamilyOfElements.pullback (f : Y ⟶ X) (x : FamilyOfElements P (S : Presieve X)) :
    FamilyOfElements P (S.pullback f : Presieve Y) := fun _ g hg => x (g ≫ f) hg

/--
theorem `FamilyOfElements.Compatible.pullback` / 定理 `FamilyOfElements.Compatible.pullback`

English:
theorem FamilyOfElements.Compatible.pullback
  statement: (f : Y ⟶ X) {x : FamilyOfElements P S.arrows}
  proof: by
  simp only [compatible_iff_sieveCompatible] at h ⊢
  intro W Z f₁ f₂ hf
  unfold FamilyOfElements.pullback
  rw [← h (f₁ ≫ f) f₂ hf]
  congr 1
  simp only [assoc]

中文:
定理 FamilyOfElements.Compatible.pullback
  结论: (f : Y ⟶ X) {x : FamilyOfElements P S.arrows}
  证明: by
  simp only [compatible_iff_sieveCompatible] at h ⊢
  intro W Z f₁ f₂ hf
  unfold FamilyOfElements.pullback
  rw [← h (f₁ ≫ f) f₂ hf]
  congr 1
  simp only [assoc]

Depends on / 依赖: FamilyOfElements, FamilyOfElements.pullback, compatible_iff_sieveCompatible, pullback
-/
theorem FamilyOfElements.Compatible.pullback (f : Y ⟶ X) {x : FamilyOfElements P S.arrows}
    (h : x.Compatible) : (x.pullback f).Compatible := by
  simp only [compatible_iff_sieveCompatible] at h ⊢
  intro W Z f₁ f₂ hf
  unfold FamilyOfElements.pullback
  rw [← h (f₁ ≫ f) f₂ hf]
  congr 1
  simp only [assoc]

end Pullback

@[simp]
/--
lemma `FamilyOfElements.map_id` / 引理 `FamilyOfElements.map_id`

English:
lemma FamilyOfElements.map_id
  given: (x : FamilyOfElements P R)
  proof: rfl

@[simp]

中文:
引理 FamilyOfElements.map_id
  条件: (x : FamilyOfElements P R)
  证明: rfl

@[simp]
-/
lemma FamilyOfElements.map_id (x : FamilyOfElements P R) :
    x.map (𝟙 _) = x :=
  rfl

@[simp]
/--
lemma `FamilyOfElements.map_comp` / 引理 `FamilyOfElements.map_comp`

English:
lemma FamilyOfElements.map_comp
  given: (x : FamilyOfElements P R) (f : P ⟶ Q) (g : Q ⟶ U)
  proof: by
  rfl

中文:
引理 FamilyOfElements.map_comp
  条件: (x : FamilyOfElements P R) (f : P ⟶ Q) (g : Q ⟶ U)
  证明: by
  rfl
-/
lemma FamilyOfElements.map_comp (x : FamilyOfElements P R) (f : P ⟶ Q) (g : Q ⟶ U) :
    (x.map f).map g = x.map (f ≫ g) := by
  rfl

/--
theorem `FamilyOfElements.Compatible.map` / 定理 `FamilyOfElements.Compatible.map`

English:
theorem FamilyOfElements.Compatible.map
  statement: (f : P ⟶ Q) {x : FamilyOfElements P R}
  proof: by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  unfold FamilyOfElements.map
  rwa [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h]

中文:
定理 FamilyOfElements.Compatible.map
  结论: (f : P ⟶ Q) {x : FamilyOfElements P R}
  证明: by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  unfold FamilyOfElements.map
  rwa [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h]

Depends on / 依赖: FamilyOfElements, FamilyOfElements.map, NatTrans, NatTrans.naturality_apply, naturality_apply
-/
theorem FamilyOfElements.Compatible.map (f : P ⟶ Q) {x : FamilyOfElements P R}
    (h : x.Compatible) : (x.map f).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  unfold FamilyOfElements.map
  rwa [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h]

/--
Definition of `FamilyOfElements.IsAmalgamation` / `FamilyOfElements.IsAmalgamation` 的定义

English:
definition FamilyOfElements.IsAmalgamation
  signature: (x : FamilyOfElements P R) (t : P.obj (op X))
  body: forall ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

中文:
定义 FamilyOfElements.IsAmalgamation
  签名: (x : FamilyOfElements P R) (t : P.obj (op X))
  定义体: forall ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

Depends on / 依赖: P.map, f.op
-/
def FamilyOfElements.IsAmalgamation (x : FamilyOfElements P R) (t : P.obj (op X)) : Prop :=
  forall ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

/--
theorem `FamilyOfElements.IsAmalgamation.map` / 定理 `FamilyOfElements.IsAmalgamation.map`

English:
theorem FamilyOfElements.IsAmalgamation.map
  statement: {x : FamilyOfElements P R} {t} (f : P ⟶ Q)
  proof: by
  intro Y g hg
  dsimp [FamilyOfElements.map]
  change (f.app _ ≫ Q.map _) _ = _
  rw [← f.naturality]; rw [comp_apply]; rw [h g hg]

中文:
定理 FamilyOfElements.IsAmalgamation.map
  结论: {x : FamilyOfElements P R} {t} (f : P ⟶ Q)
  证明: by
  intro Y g hg
  dsimp [FamilyOfElements.map]
  change (f.app _ ≫ Q.map _) _ = _
  rw [← f.naturality]; rw [comp_apply]; rw [h g hg]

Depends on / 依赖: FamilyOfElements, FamilyOfElements.map, Q.map, comp_apply, f.app, f.naturality, naturality
-/
theorem FamilyOfElements.IsAmalgamation.map {x : FamilyOfElements P R} {t} (f : P ⟶ Q)
    (h : x.IsAmalgamation t) : (x.map f).IsAmalgamation (f.app (op X) t) := by
  intro Y g hg
  dsimp [FamilyOfElements.map]
  change (f.app _ ≫ Q.map _) _ = _
  rw [← f.naturality]; rw [comp_apply]; rw [h g hg]

/--
theorem `is_compatible_of_exists_amalgamation` / 定理 `is_compatible_of_exists_amalgamation`

English:
theorem is_compatible_of_exists_amalgamation
  statement: (x : FamilyOfElements P R)
  proof: by
  obtain ⟨t, ht⟩ := h
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  rw [← ht _ h₁]; rw [← ht _ h₂]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [comm]
  simp

中文:
定理 is_compatible_of_exists_amalgamation
  结论: (x : FamilyOfElements P R)
  证明: by
  obtain ⟨t, ht⟩ := h
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  rw [← ht _ h₁]; rw [← ht _ h₂]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [comm]
  simp

Depends on / 依赖: Functor, Functor.map_comp, comp_apply, map_comp, op_comp
-/
theorem is_compatible_of_exists_amalgamation (x : FamilyOfElements P R)
    (h : exists t, x.IsAmalgamation t) : x.Compatible := by
  obtain ⟨t, ht⟩ := h
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  rw [← ht _ h₁]; rw [← ht _ h₂]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [comm]
  simp

/--
theorem `isAmalgamation_restrict` / 定理 `isAmalgamation_restrict`

English:
theorem isAmalgamation_restrict
  statement: {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂)
  proof: fun Y f hf =>
  ht f (h Y _ hf)

中文:
定理 isAmalgamation_restrict
  结论: {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂)
  证明: fun Y f hf =>
  ht f (h Y _ hf)
-/
theorem isAmalgamation_restrict {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂)
    (t : P.obj (op X)) (ht : x.IsAmalgamation t) : (x.restrict h).IsAmalgamation t := fun Y f hf =>
  ht f (h Y _ hf)

/--
theorem `isAmalgamation_sieveExtend` / 定理 `isAmalgamation_sieveExtend`

English:
theorem isAmalgamation_sieveExtend
  statement: {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X))
  proof: by
  intro Y f hf
  dsimp [FamilyOfElements.sieveExtend]
  rw [← ht _]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [hf.choose_spec.choose_spec.choose_spec.2]

@[simp]

中文:
定理 isAmalgamation_sieveExtend
  结论: {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X))
  证明: by
  intro Y f hf
  dsimp [FamilyOfElements.sieveExtend]
  rw [← ht _]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [hf.choose_spec.choose_spec.choose_spec.2]

@[simp]

Depends on / 依赖: FamilyOfElements, FamilyOfElements.sieveExtend, Functor, Functor.map_comp, choose_spec, comp_apply, hf.choose_spec.choose_spec.choose_spec, map_comp, op_comp, sieveExtend
-/
theorem isAmalgamation_sieveExtend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X))
    (ht : x.IsAmalgamation t) : x.sieveExtend.IsAmalgamation t := by
  intro Y f hf
  dsimp [FamilyOfElements.sieveExtend]
  rw [← ht _]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [hf.choose_spec.choose_spec.choose_spec.2]

@[simp]
/--
lemma `FamilyOfElements.isAmalgamation_singleton_iff` / 引理 `FamilyOfElements.isAmalgamation_singleton_iff`

English:
lemma FamilyOfElements.isAmalgamation_singleton_iff
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨fun H => H _ _, ?_⟩
  rintro H Y g ⟨rfl⟩
  exact H

中文:
引理 FamilyOfElements.isAmalgamation_singleton_iff
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨fun H => H _ _, ?_⟩
  rintro H Y g ⟨rfl⟩
  exact H
-/
lemma FamilyOfElements.isAmalgamation_singleton_iff {X Y : C} (f : X ⟶ Y)
    (x : (singleton f).FamilyOfElements P) (y : P.obj (op Y)) :
    x.IsAmalgamation y ↔ P.map f.op y = x f ⟨⟩ := by
  refine ⟨fun H => H _ _, ?_⟩
  rintro H Y g ⟨rfl⟩
  exact H

/--
lemma `FamilyOfElements.IsAmalgamation.of_mono` / 引理 `FamilyOfElements.IsAmalgamation.of_mono`

English:
lemma FamilyOfElements.IsAmalgamation.of_mono
  statement: (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
  proof: by
  intro Y u hu
  refine injective_of_mono (f.app _) ?_
  simpa using ht _ hu

中文:
引理 FamilyOfElements.IsAmalgamation.of_mono
  结论: (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
  证明: by
  intro Y u hu
  refine injective_of_mono (f.app _) ?_
  simpa using ht _ hu

Depends on / 依赖: f.app, injective_of_mono
-/
lemma FamilyOfElements.IsAmalgamation.of_mono (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
    {t : P.obj (.op X)} (ht : (x.map f).IsAmalgamation (f.app _ t)) :
    x.IsAmalgamation t := by
  intro Y u hu
  refine injective_of_mono (f.app _) ?_
  simpa using ht _ hu

/--
Definition of `IsSeparatedFor` / `IsSeparatedFor` 的定义

English:
definition IsSeparatedFor
  signature: (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
  body: forall (x : FamilyOfElements P R) (t₁ t₂), x.IsAmalgamation t₁ -> x.IsAmalgamation t₂ -> t₁ = t₂

中文:
定义 IsSeparatedFor
  签名: (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
  定义体: forall (x : FamilyOfElements P R) (t₁ t₂), x.IsAmalgamation t₁ -> x.IsAmalgamation t₂ -> t₁ = t₂

Depends on / 依赖: FamilyOfElements, IsAmalgamation, x.IsAmalgamation
-/
def IsSeparatedFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  forall (x : FamilyOfElements P R) (t₁ t₂), x.IsAmalgamation t₁ -> x.IsAmalgamation t₂ -> t₁ = t₂

/--
theorem `IsSeparatedFor.ext` / 定理 `IsSeparatedFor.ext`

English:
theorem IsSeparatedFor.ext
  statement: {R : Presieve X} (hR : IsSeparatedFor P R) {t₁ t₂ : P.obj (op X)}
  proof: hR (fun _ f _ => P.map f.op t₂) t₁ t₂ (fun _ _ hf => h hf) fun _ _ _ => rfl

中文:
定理 IsSeparatedFor.ext
  结论: {R : Presieve X} (hR : IsSeparatedFor P R) {t₁ t₂ : P.obj (op X)}
  证明: hR (fun _ f _ => P.map f.op t₂) t₁ t₂ (fun _ _ hf => h hf) fun _ _ _ => rfl

Depends on / 依赖: P.map, f.op
-/
theorem IsSeparatedFor.ext {R : Presieve X} (hR : IsSeparatedFor P R) {t₁ t₂ : P.obj (op X)}
    (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), P.map f.op t₁ = P.map f.op t₂) : t₁ = t₂ :=
  hR (fun _ f _ => P.map f.op t₂) t₁ t₂ (fun _ _ hf => h hf) fun _ _ _ => rfl

/--
theorem `isSeparatedFor_iff_generate` / 定理 `isSeparatedFor_iff_generate`

English:
theorem isSeparatedFor_iff_generate
  proof: by
  constructor
  · intro h x t₁ t₂ ht₁ ht₂
    apply h (x.restrict (le_generate R)) t₁ t₂ _ _
    · exact isAmalgamation_restrict _ x t₁ ht₁
    · exact isAmalgamation_restrict _ x t₂ ht₂
  · intro h x t₁ t₂ ht₁ ht₂
    apply h x.sieveExtend
    · exact isAmalgamation_sieveExtend x t₁ ht₁
    · ex

中文:
定理 isSeparatedFor_iff_generate
  证明: by
  constructor
  · intro h x t₁ t₂ ht₁ ht₂
    apply h (x.restrict (le_generate R)) t₁ t₂ _ _
    · exact isAmalgamation_restrict _ x t₁ ht₁
    · exact isAmalgamation_restrict _ x t₂ ht₂
  · intro h x t₁ t₂ ht₁ ht₂
    apply h x.sieveExtend
    · exact isAmalgamation_sieveExtend x t₁ ht₁
    · ex

Depends on / 依赖: isAmalgamation_restrict, isAmalgamation_sieveExtend, le_generate, restrict, sieveExtend, x.restrict, x.sieveExtend
-/
theorem isSeparatedFor_iff_generate :
    IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X) := by
  constructor
  · intro h x t₁ t₂ ht₁ ht₂
    apply h (x.restrict (le_generate R)) t₁ t₂ _ _
    · exact isAmalgamation_restrict _ x t₁ ht₁
    · exact isAmalgamation_restrict _ x t₂ ht₂
  · intro h x t₁ t₂ ht₁ ht₂
    apply h x.sieveExtend
    · exact isAmalgamation_sieveExtend x t₁ ht₁
    · exact isAmalgamation_sieveExtend x t₂ ht₂

/--
theorem `isSeparatedFor_top` / 定理 `isSeparatedFor_top`

English:
theorem isSeparatedFor_top
  given: (P : Cᵒᵖ ⥤ Type w)
  statement: IsSeparatedFor P (⊤ : Presieve X)
  proof: fun x t₁ t₂ h₁ h₂ => by
  have q₁ := h₁ (𝟙 X) (by tauto)
  have q₂ := h₂ (𝟙 X) (by tauto)
  simp only [op_id, Functor.map_id, id_apply] at q₁ q₂
  rw [q₁]; rw [q₂]

中文:
定理 isSeparatedFor_top
  条件: (P : Cᵒᵖ ⥤ Type w)
  结论: IsSeparatedFor P (⊤ : Presieve X)
  证明: fun x t₁ t₂ h₁ h₂ => by
  have q₁ := h₁ (𝟙 X) (by tauto)
  have q₂ := h₂ (𝟙 X) (by tauto)
  simp only [op_id, Functor.map_id, id_apply] at q₁ q₂
  rw [q₁]; rw [q₂]

Depends on / 依赖: Functor, Functor.map_id, id_apply, map_id, op_id
-/
theorem isSeparatedFor_top (P : Cᵒᵖ ⥤ Type w) : IsSeparatedFor P (⊤ : Presieve X) :=
  fun x t₁ t₂ h₁ h₂ => by
  have q₁ := h₁ (𝟙 X) (by tauto)
  have q₂ := h₂ (𝟙 X) (by tauto)
  simp only [op_id, Functor.map_id, id_apply] at q₁ q₂
  rw [q₁]; rw [q₂]

/--
Definition of `IsSheafFor` / `IsSheafFor` 的定义

English:
definition IsSheafFor
  signature: (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
  body: forall x : FamilyOfElements P R, x.Compatible -> exists! t, x.IsAmalgamation t

中文:
定义 IsSheafFor
  签名: (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
  定义体: forall x : FamilyOfElements P R, x.Compatible -> exists! t, x.IsAmalgamation t

Depends on / 依赖: Compatible, FamilyOfElements, IsAmalgamation, x.Compatible, x.IsAmalgamation
-/
def IsSheafFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  forall x : FamilyOfElements P R, x.Compatible -> exists! t, x.IsAmalgamation t

/-- This is an equivalent condition to be a sheaf, which is useful for the abstraction to local
operators on elementary toposes. However this definition is defined only for sieves, not presieves.
The equivalence between this and `IsSheafFor` is given in `isSheafFor_iff_yonedaSheafCondition`.
This version is also useful to establish that being a sheaf is preserved under isomorphism of
presheaves.

See the discussion before Equation (3) of [MM92], Chapter III, Section 4. See also C2.1.4 of
[Elephant]. -/
@[stacks 00Z8 "Direct reformulation"]
/--
Definition of `YonedaSheafCondition` / `YonedaSheafCondition` 的定义

English:
definition YonedaSheafCondition
  signature: (P : Cᵒᵖ ⥤ Type v₁) (S : Sieve X)
  body: forall f : S.functor ⟶ P, exists! g, S.functorInclusion ≫ g = f

中文:
定义 YonedaSheafCondition
  签名: (P : Cᵒᵖ ⥤ 类型v₁) (S : Sieve X)
  定义体: forall f : S.functor ⟶ P, exists! g, S.functorInclusion ≫ g = f

Depends on / 依赖: S.functor, S.functorInclusion, functor, functorInclusion
-/
def YonedaSheafCondition (P : Cᵒᵖ ⥤ Type v₁) (S : Sieve X) : Prop :=
  forall f : S.functor ⟶ P, exists! g, S.functorInclusion ≫ g = f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). This is a (primarily internal) equivalence between natural transformations
and compatible families.

Cf the discussion after Lemma 7.47.10 in <https://stacks.math.columbia.edu/tag/00YW>. See also
the proof of C2.1.4 of [Elephant], and the discussion in [MM92], Chapter III, Section 4.
-/
@[simps]
/--
Definition of `shrinkFunctorHomEquiv` / `shrinkFunctorHomEquiv` 的定义

English:
definition shrinkFunctorHomEquiv
  signature: [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w}
  body: ⟨fun Y f hf => t.app _ ⟨shrinkYonedaObjObjEquiv.symm f, by simpa⟩, by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    simp only [shrinkFunctor_obj, ← NatTrans.naturality_apply]
    rw! [shrinkYonedaObjObjEquiv_symm_comp]
    rfl⟩
  invFun t :=
    { app X := ↾fun f => t.1 _

中文:
定义 shrinkFunctorHomEquiv
  签名: [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w}
  定义体: ⟨fun Y f hf => t.app _ ⟨shrinkYonedaObjObjEquiv.symm f, by simpa⟩, by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    simp only [shrinkFunctor_obj, ← NatTrans.naturality_apply]
    rw! [shrinkYonedaObjObjEquiv_symm_comp]
    rfl⟩
  invFun t :=
    { app X := ↾fun f => t.1 _

Depends on / 依赖: Equiv.apply_, NatTrans, NatTrans.naturality_apply, Opposite, Opposite.op_unop, Presieve, Presieve.compatible_iff_sieveCompatible, apply_, cat_disch, compatible_iff_sieveCompatible, convert, f.mem, invFun, left_inv, naturality, naturality_apply, op_unop, right_inv, shrinkFunctor_obj, shrinkYonedaObjObjEquiv
-/
noncomputable def shrinkFunctorHomEquiv [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w} :
    (S.shrinkFunctor.toFunctor ⟶ F) ≃ { x : S.arrows.FamilyOfElements F // x.Compatible } where
  toFun t := ⟨fun Y f hf => t.app _ ⟨shrinkYonedaObjObjEquiv.symm f, by simpa⟩, by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    simp only [shrinkFunctor_obj, ← NatTrans.naturality_apply]
    rw! [shrinkYonedaObjObjEquiv_symm_comp]
    rfl⟩
  invFun t :=
    { app X := ↾fun f => t.1 _ f.mem
      naturality Y Z g := by
        ext ⟨f, hf⟩
        dsimp
        convert! t.2.to_sieveCompatible _ _ _
        simp only [Opposite.op_unop, shrinkYonedaObjObjEquiv_obj_map]
        rfl }
  left_inv t := by cat_disch
  right_inv x := by
    ext
    dsimp
    rw! [Equiv.apply_symm_apply]
    simp

@[deprecated "In terms of `Sieve.shrinkFunctor`" (since := "2026-03-13")]
alias natTransEquivCompatibleFamily := shrinkFunctorHomEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkFunctor_ι_comp_eq_iff_isAmalgamation` / 引理 `shrinkFunctor_ι_comp_eq_iff_isAmalgamation`

English:
lemma shrinkFunctor_ι_comp_eq_iff_isAmalgamation
  statement: [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w)
  proof: by
  dsimp [Presieve.FamilyOfElements.IsAmalgamation]
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl Y f hf
    simp [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
  · ext Y ⟨u, hu⟩
    convert! h (shrinkYonedaObjObjEquiv u) hu
    · rw [shrinkYonedaEquiv_natur

中文:
引理 shrinkFunctor_ι_comp_eq_iff_isAmalgamation
  结论: [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w)
  证明: by
  dsimp [Presieve.FamilyOfElements.IsAmalgamation]
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl Y f hf
    simp [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
  · ext Y ⟨u, hu⟩
    convert! h (shrinkYonedaObjObjEquiv u) hu
    · rw [shrinkYonedaEquiv_natur

Depends on / 依赖: Equiv.symm_apply_apply, FamilyOfElements, IsAmalgamation, Presieve, Presieve.FamilyOfElements.IsAmalgamation, convert, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_shrinkYoneda_map, shrinkYonedaObjObjEquiv, symm_apply_apply
-/
lemma shrinkFunctor_ι_comp_eq_iff_isAmalgamation [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w)
    (f : S.shrinkFunctor.toFunctor ⟶ F) (g : shrinkYoneda.{w}.obj X ⟶ F) :
    S.shrinkFunctor.ι ≫ g = f ↔
      (shrinkFunctorHomEquiv f).1.IsAmalgamation (shrinkYonedaEquiv g) := by
  dsimp [Presieve.FamilyOfElements.IsAmalgamation]
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl Y f hf
    simp [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
  · ext Y ⟨u, hu⟩
    convert! h (shrinkYonedaObjObjEquiv u) hu
    · rw [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
      simp
    · rw! [Equiv.symm_apply_apply]
      rfl

@[deprecated "In terms of `Sieve.shrinkFunctor`" (since := "2026-03-13")]
alias extension_iff_amalgamation := shrinkFunctor_ι_comp_eq_iff_isAmalgamation

/--
lemma `isSheafFor_iff_bijective_shrinkFunctor_ι_comp` / 引理 `isSheafFor_iff_bijective_shrinkFunctor_ι_comp`

English:
lemma isSheafFor_iff_bijective_shrinkFunctor_ι_comp
  statement: [LocallySmall.{w} C] {X : C}
  proof: by
  simp only [IsSheafFor, Function.bijective_iff_existsUnique,
    shrinkFunctor_ι_comp_eq_iff_isAmalgamation, shrinkFunctorHomEquiv.forall_congr_left,
    Subtype.forall]
  exact forall₂_congr fun x hx => by simp [Equiv.existsUnique_congr_right]

中文:
引理 isSheafFor_iff_bijective_shrinkFunctor_ι_comp
  结论: [LocallySmall.{w} C] {X : C}
  证明: by
  simp only [IsSheafFor, Function.bijective_iff_existsUnique,
    shrinkFunctor_ι_comp_eq_iff_isAmalgamation, shrinkFunctorHomEquiv.forall_congr_left,
    Subtype.forall]
  exact forall₂_congr fun x hx => by simp [Equiv.existsUnique_congr_right]

Depends on / 依赖: Equiv.existsUnique_congr_right, Function, Function.bijective_iff_existsUnique, IsSheafFor, Subtype, Subtype.forall, bijective_iff_existsUnique, existsUnique_congr_right, forall_congr_left, shrinkFunctorHomEquiv, shrinkFunctorHomEquiv.forall_congr_left
-/
lemma isSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C}
    (S : Sieve X) (F : Cᵒᵖ ⥤ Type w) :
    IsSheafFor F S.arrows ↔
      Function.Bijective (fun g : _ ⟶ F => S.shrinkFunctor.ι ≫ g) := by
  simp only [IsSheafFor, Function.bijective_iff_existsUnique,
    shrinkFunctor_ι_comp_eq_iff_isAmalgamation, shrinkFunctorHomEquiv.forall_congr_left,
    Subtype.forall]
  exact forall₂_congr fun x hx => by simp [Equiv.existsUnique_congr_right]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSheafFor_iff_yonedaSheafCondition` / 定理 `isSheafFor_iff_yonedaSheafCondition`

English:
theorem isSheafFor_iff_yonedaSheafCondition
  given: {P : Cᵒᵖ ⥤ Type v₁}
  proof: by
  rw [isSheafFor_iff_bijective_shrinkFunctor_ι_comp]; rw [YonedaSheafCondition]; rw [Function.bijective_iff_existsUnique]; rw [Equiv.forall_congr_left S.shrinkFunctorIsoFunctor.homFromEquiv]
  refine forall_congr' fun a => ?_
  rw [Equiv.existsUnique_congr_left (shrinkYonedaIsoYoneda.app X).homFr

中文:
定理 isSheafFor_iff_yonedaSheafCondition
  条件: {P : Cᵒᵖ ⥤ 类型v₁}
  证明: by
  rw [isSheafFor_iff_bijective_shrinkFunctor_ι_comp]; rw [YonedaSheafCondition]; rw [Function.bijective_iff_existsUnique]; rw [Equiv.forall_congr_left S.shrinkFunctorIsoFunctor.homFromEquiv]
  refine forall_congr' fun a => ?_
  rw [Equiv.existsUnique_congr_left (shrinkYonedaIsoYoneda.app X).homFr

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext_iff, Equiv.existsUnique_congr_left, Equiv.forall_congr_left, Function, Function.bijective_iff_existsUnique, NatTrans, NatTrans.ext_iff, S.shrinkFunctorIsoFunctor.homFromEquiv, YonedaSheafCondition, bijective_iff_existsUnique, existsUnique_congr, existsUnique_congr_left, ext_iff, forall_congr, forall_congr_left, funext_iff, homFromEquiv, hom_ext_iff, shrinkFunctorIsoFunctor
-/
theorem isSheafFor_iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} :
    IsSheafFor P (S : Presieve X) ↔ YonedaSheafCondition P S := by
  rw [isSheafFor_iff_bijective_shrinkFunctor_ι_comp]; rw [YonedaSheafCondition]; rw [Function.bijective_iff_existsUnique]; rw [Equiv.forall_congr_left S.shrinkFunctorIsoFunctor.homFromEquiv]
  refine forall_congr' fun a => ?_
  rw [Equiv.existsUnique_congr_left (shrinkYonedaIsoYoneda.app X).homFromEquiv]
  refine existsUnique_congr fun b => ?_
  dsimp
  rw [NatTrans.ext_iff]; rw [NatTrans.ext_iff]; rw [funext_iff]; rw [funext_iff]
  congr!
  rw [ConcreteCategory.hom_ext_iff]; rw [ConcreteCategory.hom_ext_iff]
  dsimp [functor]
  simp only [Subtype.forall, shrinkYonedaObjObjEquiv.forall_congr_left, Equiv.apply_symm_apply]
  congr!
  simp

/--
Definition of `IsSheafFor.extend` / `IsSheafFor.extend` 的定义

English:
definition IsSheafFor.extend
  signature: {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
  body: (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose

中文:
定义 IsSheafFor.extend
  签名: {P : Cᵒᵖ ⥤ 类型v₁} (h : IsSheafFor P (S : Presieve X))
  定义体: (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose

Depends on / 依赖: exists.choose, isSheafFor_iff_yonedaSheafCondition
-/
noncomputable def IsSheafFor.extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (f : S.functor ⟶ P) : yoneda.obj X ⟶ P :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose

/--
Show that the extension of `f : S.functor ⟶ P` to all of `yoneda.obj X` is in fact an extension,
i.e. that the triangle below commutes, provided `P` is a sheaf for `S`
```
      f
   S → P
   ↓ ↗
   yX
```
-/
@[reassoc (attr := simp)]
/--
theorem `IsSheafFor.functorInclusion_comp_extend` / 定理 `IsSheafFor.functorInclusion_comp_extend`

English:
theorem IsSheafFor.functorInclusion_comp_extend
  statement: {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
  proof: (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose_spec

中文:
定理 IsSheafFor.functorInclusion_comp_extend
  结论: {P : Cᵒᵖ ⥤ 类型v₁} (h : IsSheafFor P S.arrows)
  证明: (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose_spec

Depends on / 依赖: choose_spec, exists.choose_spec, isSheafFor_iff_yonedaSheafCondition
-/
theorem IsSheafFor.functorInclusion_comp_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
    (f : S.functor ⟶ P) : S.functorInclusion ≫ h.extend f = f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose_spec

/--
theorem `IsSheafFor.unique_extend` / 定理 `IsSheafFor.unique_extend`

English:
theorem IsSheafFor.unique_extend
  statement: {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
  proof: (isSheafFor_iff_yonedaSheafCondition.1 h f).unique ht (h.functorInclusion_comp_extend f)

中文:
定理 IsSheafFor.unique_extend
  结论: {P : Cᵒᵖ ⥤ 类型v₁} (h : IsSheafFor P S.arrows)
  证明: (isSheafFor_iff_yonedaSheafCondition.1 h f).unique ht (h.functorInclusion_comp_extend f)

Depends on / 依赖: functorInclusion_comp_extend, h.functorInclusion_comp_extend, isSheafFor_iff_yonedaSheafCondition, unique
-/
theorem IsSheafFor.unique_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
    {f : S.functor ⟶ P} (t : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t = f) :
    t = h.extend f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).unique ht (h.functorInclusion_comp_extend f)

/--
theorem `IsSheafFor.hom_ext` / 定理 `IsSheafFor.hom_ext`

English:
theorem IsSheafFor.hom_ext
  statement: {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
  proof: (h.unique_extend t₁ ht).trans (h.unique_extend t₂ rfl).symm

中文:
定理 IsSheafFor.hom_ext
  结论: {P : Cᵒᵖ ⥤ 类型v₁} (h : IsSheafFor P (S : Presieve X))
  证明: (h.unique_extend t₁ ht).trans (h.unique_extend t₂ rfl).symm

Depends on / 依赖: h.unique_extend, unique_extend
-/
theorem IsSheafFor.hom_ext {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (t₁ t₂ : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t₁ = S.functorInclusion ≫ t₂) :
    t₁ = t₂ :=
  (h.unique_extend t₁ ht).trans (h.unique_extend t₂ rfl).symm

/--
theorem `isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor` / 定理 `isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor`

English:
theorem isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor
  proof: by
  rw [IsSeparatedFor]; rw [← forall_and]
  apply forall_congr'
  intro x
  constructor
  · intro z hx
    exact existsUnique_of_exists_of_unique (z.2 hx) z.1
  · intro h
    refine ⟨?_, ExistsUnique.exists ∘ h⟩
    intro t₁ t₂ ht₁ ht₂
    apply (h _).unique ht₁ ht₂
    exact is_compatible_of_exis

中文:
定理 isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor
  证明: by
  rw [IsSeparatedFor]; rw [← forall_and]
  apply forall_congr'
  intro x
  constructor
  · intro z hx
    exact existsUnique_of_exists_of_unique (z.2 hx) z.1
  · intro h
    refine ⟨?_, ExistsUnique.exists ∘ h⟩
    intro t₁ t₂ ht₁ ht₂
    apply (h _).unique ht₁ ht₂
    exact is_compatible_of_exis

Depends on / 依赖: ExistsUnique, ExistsUnique.exists, IsSeparatedFor, existsUnique_of_exists_of_unique, forall_and, forall_congr, is_compatible_of_exists_amalgamation, unique
-/
theorem isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor :
    (IsSeparatedFor P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x.IsAmalgamation t) ↔
      IsSheafFor P R := by
  rw [IsSeparatedFor]; rw [← forall_and]
  apply forall_congr'
  intro x
  constructor
  · intro z hx
    exact existsUnique_of_exists_of_unique (z.2 hx) z.1
  · intro h
    refine ⟨?_, ExistsUnique.exists ∘ h⟩
    intro t₁ t₂ ht₁ ht₂
    apply (h _).unique ht₁ ht₂
    exact is_compatible_of_exists_amalgamation x ⟨_, ht₂⟩

/--
theorem `IsSeparatedFor.isSheafFor` / 定理 `IsSeparatedFor.isSheafFor`

English:
theorem IsSeparatedFor.isSheafFor
  given: (t : IsSeparatedFor P R)
  proof: by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact And.intro t

中文:
定理 IsSeparatedFor.isSheafFor
  条件: (t : IsSeparatedFor P R)
  证明: by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact And.intro t

Depends on / 依赖: And.intro, isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor
-/
theorem IsSeparatedFor.isSheafFor (t : IsSeparatedFor P R) :
    (forall x : FamilyOfElements P R, x.Compatible -> exists t, x.IsAmalgamation t) -> IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact And.intro t

/--
theorem `IsSheafFor.isSeparatedFor` / 定理 `IsSheafFor.isSeparatedFor`

English:
theorem IsSheafFor.isSeparatedFor
  statement: IsSheafFor P R -> IsSeparatedFor P R
  proof: fun q =>
  (isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 q).1

中文:
定理 IsSheafFor.isSeparatedFor
  结论: IsSheafFor P R -> IsSeparatedFor P R
  证明: fun q =>
  (isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 q).1
-/
theorem IsSheafFor.isSeparatedFor : IsSheafFor P R -> IsSeparatedFor P R := fun q =>
  (isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 q).1

/--
Definition of `IsSheafFor.amalgamate` / `IsSheafFor.amalgamate` 的定义

English:
definition IsSheafFor.amalgamate
  signature: (t : IsSheafFor P R) (x : FamilyOfElements P R)
  body: (t x hx).exists.choose

中文:
定义 IsSheafFor.amalgamate
  签名: (t : IsSheafFor P R) (x : FamilyOfElements P R)
  定义体: (t x hx).exists.choose

Depends on / 依赖: exists.choose
-/
noncomputable def IsSheafFor.amalgamate (t : IsSheafFor P R) (x : FamilyOfElements P R)
    (hx : x.Compatible) : P.obj (op X) :=
  (t x hx).exists.choose

/--
theorem `IsSheafFor.isAmalgamation` / 定理 `IsSheafFor.isAmalgamation`

English:
theorem IsSheafFor.isAmalgamation
  statement: (t : IsSheafFor P R) {x : FamilyOfElements P R}
  proof: (t x hx).exists.choose_spec

@[simp]

中文:
定理 IsSheafFor.isAmalgamation
  结论: (t : IsSheafFor P R) {x : FamilyOfElements P R}
  证明: (t x hx).exists.choose_spec

@[simp]

Depends on / 依赖: choose_spec, exists.choose_spec
-/
theorem IsSheafFor.isAmalgamation (t : IsSheafFor P R) {x : FamilyOfElements P R}
    (hx : x.Compatible) : x.IsAmalgamation (t.amalgamate x hx) :=
  (t x hx).exists.choose_spec

@[simp]
/--
theorem `IsSheafFor.valid_glue` / 定理 `IsSheafFor.valid_glue`

English:
theorem IsSheafFor.valid_glue
  statement: (t : IsSheafFor P R) {x : FamilyOfElements P R} (hx : x.Compatible)
  proof: t.isAmalgamation hx f Hf

中文:
定理 IsSheafFor.valid_glue
  结论: (t : IsSheafFor P R) {x : FamilyOfElements P R} (hx : x.Compatible)
  证明: t.isAmalgamation hx f Hf

Depends on / 依赖: isAmalgamation, t.isAmalgamation
-/
theorem IsSheafFor.valid_glue (t : IsSheafFor P R) {x : FamilyOfElements P R} (hx : x.Compatible)
    (f : Y ⟶ X) (Hf : R f) : P.map f.op (t.amalgamate x hx) = x f Hf :=
  t.isAmalgamation hx f Hf

/--
theorem `isSheafFor_iff_generate` / 定理 `isSheafFor_iff_generate`

English:
theorem isSheafFor_iff_generate
  given: (R : Presieve X)
  proof: by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_iff_generate]
  apply and_congr (Iff.refl _)
  constructor
  · intro q x hx
    apply Exists.imp _ (q _ (hx.restrict (le_generate R)))
    intro

中文:
定理 isSheafFor_iff_generate
  条件: (R : Presieve X)
  证明: by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_iff_generate]
  apply and_congr (Iff.refl _)
  constructor
  · intro q x hx
    apply Exists.imp _ (q _ (hx.restrict (le_generate R)))
    intro

Depends on / 依赖: Exists, Exists.imp, Iff.refl, and_congr, hx.restrict, hx.sieveExtend, isAmalgamation_restrict, isAmalgamation_sieveExtend, isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, isSeparatedFor_iff_generate, le_generate, restrict, sieveExtend
-/
theorem isSheafFor_iff_generate (R : Presieve X) :
    IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X) := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_iff_generate]
  apply and_congr (Iff.refl _)
  constructor
  · intro q x hx
    apply Exists.imp _ (q _ (hx.restrict (le_generate R)))
    intro t ht
    simpa [hx] using isAmalgamation_sieveExtend _ _ ht
  · intro q x hx
    apply Exists.imp _ (q _ hx.sieveExtend)
    intro t ht
    simpa [hx] using isAmalgamation_restrict (le_generate R) _ _ ht

/--
theorem `isSheafFor_singleton_iso` / 定理 `isSheafFor_singleton_iso`

English:
theorem isSheafFor_singleton_iso
  given: (P : Cᵒᵖ ⥤ Type w)
  proof: by
  intro x _
  refine ⟨x _ (Presieve.singleton_self _), ?_, ?_⟩
  · rintro _ _ ⟨rfl, rfl⟩
    simp
  · intro t ht
    simpa using ht _ (Presieve.singleton_self _)

中文:
定理 isSheafFor_singleton_iso
  条件: (P : Cᵒᵖ ⥤ Type w)
  证明: by
  intro x _
  refine ⟨x _ (Presieve.singleton_self _), ?_, ?_⟩
  · rintro _ _ ⟨rfl, rfl⟩
    simp
  · intro t ht
    simpa using ht _ (Presieve.singleton_self _)

Depends on / 依赖: Presieve, Presieve.singleton_self, singleton_self
-/
theorem isSheafFor_singleton_iso (P : Cᵒᵖ ⥤ Type w) :
    IsSheafFor P (Presieve.singleton (𝟙 X)) := by
  intro x _
  refine ⟨x _ (Presieve.singleton_self _), ?_, ?_⟩
  · rintro _ _ ⟨rfl, rfl⟩
    simp
  · intro t ht
    simpa using ht _ (Presieve.singleton_self _)

/--
theorem `isSheafFor_top` / 定理 `isSheafFor_top`

English:
theorem isSheafFor_top
  given: (P : Cᵒᵖ ⥤ Type w)
  statement: IsSheafFor P (⊤ : Presieve X)
  proof: by
  rw [← arrows_top]; rw [← generate_of_singleton_isSplitEpi (𝟙 X)]
  rw [← isSheafFor_iff_generate]
  apply isSheafFor_singleton_iso

@[deprecated (since := "2026-01-22")]
alias isSheafFor_top_sieve := isSheafFor_top

中文:
定理 isSheafFor_top
  条件: (P : Cᵒᵖ ⥤ Type w)
  结论: IsSheafFor P (⊤ : Presieve X)
  证明: by
  rw [← arrows_top]; rw [← generate_of_singleton_isSplitEpi (𝟙 X)]
  rw [← isSheafFor_iff_generate]
  apply isSheafFor_singleton_iso

@[deprecated (since := "2026-01-22")]
alias isSheafFor_top_sieve := isSheafFor_top

Depends on / 依赖: arrows_top, generate_of_singleton_isSplitEpi, isSheafFor_iff_generate, isSheafFor_singleton_iso
-/
theorem isSheafFor_top (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (⊤ : Presieve X) := by
  rw [← arrows_top]; rw [← generate_of_singleton_isSplitEpi (𝟙 X)]
  rw [← isSheafFor_iff_generate]
  apply isSheafFor_singleton_iso

@[deprecated (since := "2026-01-22")]
alias isSheafFor_top_sieve := isSheafFor_top

/--
lemma `isSheafFor_of_nat_equiv` / 引理 `isSheafFor_of_nat_equiv`

English:
lemma isSheafFor_of_nat_equiv
  statement: {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
  proof: fun x₂ hx₂ => by
  have he' : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₂.obj (op Y)),
    e.symm (P₂.map f.op x) = P₁.map f.op (e.symm x) := fun X Y f x =>
      e.injective (by simp only [Equiv.apply_symm_apply, he])
  let x₁ : FamilyOfElements P₁ R := fun Y f hf => e.symm (x₂ f hf)
  have hx₁ : x₁.Compa

中文:
引理 isSheafFor_of_nat_equiv
  结论: {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
  证明: fun x₂ hx₂ => by
  have he' : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₂.obj (op Y)),
    e.symm (P₂.map f.op x) = P₁.map f.op (e.symm x) := fun X Y f x =>
      e.injective (by simp only [Equiv.apply_symm_apply, he])
  let x₁ : FamilyOfElements P₁ R := fun Y f hf => e.symm (x₂ f hf)
  have hx₁ : x₁.Compa

Depends on / 依赖: Compatible, Equiv.apply_symm_apply, FamilyOfElements, IsAmalgamation, apply_symm_apply, e.injective, e.symm, f.op, injective
-/
lemma isSheafFor_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : forall ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X))
    (he : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x))
    {X : C} {R : Presieve X} (hP₁ : IsSheafFor P₁ R) :
    IsSheafFor P₂ R := fun x₂ hx₂ => by
  have he' : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₂.obj (op Y)),
    e.symm (P₂.map f.op x) = P₁.map f.op (e.symm x) := fun X Y f x =>
      e.injective (by simp only [Equiv.apply_symm_apply, he])
  let x₁ : FamilyOfElements P₁ R := fun Y f hf => e.symm (x₂ f hf)
  have hx₁ : x₁.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac => e.injective
    (by simp only [he, Equiv.apply_symm_apply, hx₂ g₁ g₂ h₁ h₂ fac, x₁])
  have : forall (t₂ : P₂.obj (op X)),
      x₂.IsAmalgamation t₂ ↔ x₁.IsAmalgamation (e.symm t₂) := fun t₂ => by
    simp only [FamilyOfElements.IsAmalgamation, x₁,
      ← he', EmbeddingLike.apply_eq_iff_eq]
  refine ⟨e (hP₁.amalgamate x₁ hx₁), ?_, ?_⟩
  · dsimp
    simp only [this, Equiv.symm_apply_apply]
    exact IsSheafFor.isAmalgamation hP₁ hx₁
  · intro t₂ ht₂
    refine e.symm.injective ?_
    simp only [Equiv.symm_apply_apply]
    exact hP₁.isSeparatedFor x₁ _ _ (by simpa only [this] using ht₂)
      (IsSheafFor.isAmalgamation hP₁ hx₁)

/--
lemma `isSheafFor_iff_of_nat_equiv` / 引理 `isSheafFor_iff_of_nat_equiv`

English:
lemma isSheafFor_iff_of_nat_equiv
  statement: {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
  proof: by
  refine ⟨fun h => isSheafFor_of_nat_equiv _ he h,
      fun h => isSheafFor_of_nat_equiv (fun _ => (@e _).symm) ?_ h⟩
  intro X Y f x
  obtain ⟨y, rfl⟩ := e.surjective x
  refine e.injective ?_
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, he]

中文:
引理 isSheafFor_iff_of_nat_equiv
  结论: {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
  证明: by
  refine ⟨fun h => isSheafFor_of_nat_equiv _ he h,
      fun h => isSheafFor_of_nat_equiv (fun _ => (@e _).symm) ?_ h⟩
  intro X Y f x
  obtain ⟨y, rfl⟩ := e.surjective x
  refine e.injective ?_
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, he]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_apply, apply_symm_apply, e.injective, e.surjective, injective, isSheafFor_of_nat_equiv, surjective, symm_apply_apply
-/
lemma isSheafFor_iff_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : forall ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X))
    (he : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x))
    {X : C} {R : Presieve X} :
    IsSheafFor P₁ R ↔ IsSheafFor P₂ R := by
  refine ⟨fun h => isSheafFor_of_nat_equiv _ he h,
      fun h => isSheafFor_of_nat_equiv (fun _ => (@e _).symm) ?_ h⟩
  intro X Y f x
  obtain ⟨y, rfl⟩ := e.surjective x
  refine e.injective ?_
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, he]

/--
theorem `isSheafFor_iso` / 定理 `isSheafFor_iso`

English:
theorem isSheafFor_iso
  given: {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSheafFor P R)
  proof: isSheafFor_of_nat_equiv (fun X => (i.app (op X)).toEquiv)
    (fun _ _ f x => ConcreteCategory.congr_hom (i.hom.naturality f.op) x) hP

中文:
定理 isSheafFor_iso
  条件: {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSheafFor P R)
  证明: isSheafFor_of_nat_equiv (fun X => (i.app (op X)).toEquiv)
    (fun _ _ f x => ConcreteCategory.congr_hom (i.hom.naturality f.op) x) hP

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, f.op, i.app, i.hom.naturality, isSheafFor_of_nat_equiv, naturality, toEquiv
-/
theorem isSheafFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSheafFor P R) :
    IsSheafFor P' R :=
  isSheafFor_of_nat_equiv (fun X => (i.app (op X)).toEquiv)
    (fun _ _ f x => ConcreteCategory.congr_hom (i.hom.naturality f.op) x) hP

/--
theorem `isSheafFor_iff_of_iso` / 定理 `isSheafFor_iff_of_iso`

English:
theorem isSheafFor_iff_of_iso
  given: {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P')
  proof: ⟨isSheafFor_iso i, isSheafFor_iso i.symm⟩

中文:
定理 isSheafFor_iff_of_iso
  条件: {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P')
  证明: ⟨isSheafFor_iso i, isSheafFor_iso i.symm⟩

Depends on / 依赖: i.symm, isSheafFor_iso
-/
theorem isSheafFor_iff_of_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') :
    IsSheafFor P R ↔ IsSheafFor P' R :=
  ⟨isSheafFor_iso i, isSheafFor_iso i.symm⟩

/--
theorem `isSeparatedFor_iso` / 定理 `isSeparatedFor_iso`

English:
theorem isSeparatedFor_iso
  given: {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSeparatedFor P R)
  proof: by
  intro x t₁ t₂ ht₁ ht₂
simpa using congrArg (i.hom.app _) hP (x.map i.inv) _ _ (ht₁.map i.inv) (ht₂.map i.inv)

中文:
定理 isSeparatedFor_iso
  条件: {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSeparatedFor P R)
  证明: by
  intro x t₁ t₂ ht₁ ht₂
simpa using congrArg (i.hom.app _) hP (x.map i.inv) _ _ (ht₁.map i.inv) (ht₂.map i.inv)

Depends on / 依赖: i.hom.app, i.inv, x.map
-/
theorem isSeparatedFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSeparatedFor P R) :
    IsSeparatedFor P' R := by
  intro x t₁ t₂ ht₁ ht₂
simpa using congrArg (i.hom.app _) hP (x.map i.inv) _ _ (ht₁.map i.inv) (ht₂.map i.inv)

/--
lemma `IsSeparatedFor.of_mono` / 引理 `IsSeparatedFor.of_mono`

English:
lemma IsSeparatedFor.of_mono
  given: (f : P ⟶ Q) [Mono f] (h : R.IsSeparatedFor Q)
  proof: by
  intro x t₁ t₂ ht₁ ht₂
exact injective_of_mono _ h (x.map f) _ _ (ht₁.map f) (ht₂.map f)

中文:
引理 IsSeparatedFor.of_mono
  条件: (f : P ⟶ Q) [Mono f] (h : R.IsSeparatedFor Q)
  证明: by
  intro x t₁ t₂ ht₁ ht₂
exact injective_of_mono _ h (x.map f) _ _ (ht₁.map f) (ht₂.map f)

Depends on / 依赖: injective_of_mono, x.map
-/
lemma IsSeparatedFor.of_mono (f : P ⟶ Q) [Mono f] (h : R.IsSeparatedFor Q) :
    R.IsSeparatedFor P := by
  intro x t₁ t₂ ht₁ ht₂
exact injective_of_mono _ h (x.map f) _ _ (ht₁.map f) (ht₂.map f)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isSheafFor_subsieve_aux` / 定理 `isSheafFor_subsieve_aux`

English:
theorem isSheafFor_subsieve_aux
  statement: (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
  proof: by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  · intro x t₁ t₂ ht₁ ht₂
    exact
      hS.isSeparatedFor _ _ _ (isAmalgamation_restrict h x t₁ ht₁)
        (isAmalgamation_restrict h x t₂ ht₂)
  · intro x hx
    use hS.amalgamate _ (hx.restrict h)
    intro W j h

中文:
定理 isSheafFor_subsieve_aux
  结论: (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
  证明: by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  · intro x t₁ t₂ ht₁ ht₂
    exact
      hS.isSeparatedFor _ _ _ (isAmalgamation_restrict h x t₁ ht₁)
        (isAmalgamation_restrict h x t₂ ht₂)
  · intro x hx
    use hS.amalgamate _ (hx.restrict h)
    intro W j h

Depends on / 依赖: FamilyOfElements, FamilyOfElements.restrict, Functor, Functor.map_comp, amalgamate, comp_apply, hS.amalgamate, hS.isSeparatedFor, hS.valid_glue, hx.restrict, id_comp, isAmalgamation_restrict, isSeparatedFor, isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, map_comp, op_comp, restrict, valid_glue
-/
theorem isSheafFor_subsieve_aux (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) <= R) (hS : IsSheafFor P (S : Presieve X))
    (trans : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f -> IsSeparatedFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  · intro x t₁ t₂ ht₁ ht₂
    exact
      hS.isSeparatedFor _ _ _ (isAmalgamation_restrict h x t₁ ht₁)
        (isAmalgamation_restrict h x t₂ ht₂)
  · intro x hx
    use hS.amalgamate _ (hx.restrict h)
    intro W j hj
    apply (trans hj).ext
    intro Y f hf
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [hS.valid_glue (hx.restrict h) _ hf]; rw [FamilyOfElements.restrict]; rw [← hx (𝟙 _) f (h _ _ hf) _ (id_comp _)]
    simp

/--
theorem `isSheafFor_subsieve` / 定理 `isSheafFor_subsieve`

English:
theorem isSheafFor_subsieve
  statement: (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
  proof: isSheafFor_subsieve_aux P h (by simpa using trans (𝟙 _)) fun _ f _ => (trans f).isSeparatedFor

中文:
定理 isSheafFor_subsieve
  结论: (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
  证明: isSheafFor_subsieve_aux P h (by simpa using trans (𝟙 _)) fun _ f _ => (trans f).isSeparatedFor

Depends on / 依赖: isSeparatedFor, isSheafFor_subsieve_aux
-/
theorem isSheafFor_subsieve (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) <= R) (trans : forall ⦃Y⦄ (f : Y ⟶ X),
      IsSheafFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R :=
  isSheafFor_subsieve_aux P h (by simpa using trans (𝟙 _)) fun _ f _ => (trans f).isSeparatedFor

section Arrows

variable {B : C} {I : Type*} {X : I -> C} (π : (i : I) -> X i ⟶ B) (P)

/--
Definition of `Arrows.Compatible` / `Arrows.Compatible` 的定义

English:
definition Arrows.Compatible
  signature: (x : (i : I) -> P.obj (op (X i)))
  body: forall i j Z (gi : Z ⟶ X i) (gj : Z ⟶ X j), gi ≫ π i = gj ≫ π j ->
    P.map gi.op (x i) = P.map gj.op (x j)

中文:
定义 Arrows.Compatible
  签名: (x : (i : I) -> P.obj (op (X i)))
  定义体: forall i j Z (gi : Z ⟶ X i) (gj : Z ⟶ X j), gi ≫ π i = gj ≫ π j ->
    P.map gi.op (x i) = P.map gj.op (x j)

Depends on / 依赖: P.map, gi.op, gj.op
-/
def Arrows.Compatible (x : (i : I) -> P.obj (op (X i))) : Prop :=
  forall i j Z (gi : Z ⟶ X i) (gj : Z ⟶ X j), gi ≫ π i = gj ≫ π j ->
    P.map gi.op (x i) = P.map gj.op (x j)

/--
lemma `FamilyOfElements.isAmalgamation_iff_ofArrows` / 引理 `FamilyOfElements.isAmalgamation_iff_ofArrows`

English:
lemma FamilyOfElements.isAmalgamation_iff_ofArrows
  statement: (x : FamilyOfElements P (ofArrows X π))
  proof: ⟨fun h i => h _ (ofArrows.mk i), fun h _ f ⟨i⟩ => h i⟩

中文:
引理 FamilyOfElements.isAmalgamation_iff_ofArrows
  结论: (x : FamilyOfElements P (ofArrows X π))
  证明: ⟨fun h i => h _ (ofArrows.mk i), fun h _ f ⟨i⟩ => h i⟩

Depends on / 依赖: ofArrows, ofArrows.mk
-/
lemma FamilyOfElements.isAmalgamation_iff_ofArrows (x : FamilyOfElements P (ofArrows X π))
    (t : P.obj (op B)) :
    x.IsAmalgamation t ↔ forall (i : I), P.map (π i).op t = x _ (ofArrows.mk i) :=
  ⟨fun h i => h _ (ofArrows.mk i), fun h _ f ⟨i⟩ => h i⟩

namespace Arrows.Compatible

variable {x : (i : I) -> P.obj (op (X i))}
variable {P π}

/--
theorem `exists_familyOfElements` / 定理 `exists_familyOfElements`

English:
theorem exists_familyOfElements
  given: (hx : Compatible P π x)
  proof: by
  choose i h h' using @ofArrows_surj _ _ _ _ _ π
  exact ⟨fun Y f hf => P.map (eqToHom (h f hf).symm).op (x _),
fun j => (hx _ j (X j) _ (𝟙 _) <| by rw [← h', id_comp]).trans by simp⟩

中文:
定理 exists_familyOfElements
  条件: (hx : Compatible P π x)
  证明: by
  choose i h h' using @ofArrows_surj _ _ _ _ _ π
  exact ⟨fun Y f hf => P.map (eqToHom (h f hf).symm).op (x _),
fun j => (hx _ j (X j) _ (𝟙 _) <| by rw [← h', id_comp]).trans by simp⟩

Depends on / 依赖: P.map, eqToHom, id_comp, ofArrows_surj
-/
theorem exists_familyOfElements (hx : Compatible P π x) :
    exists (x' : FamilyOfElements P (ofArrows X π)), forall (i : I), x' _ (ofArrows.mk i) = x i := by
  choose i h h' using @ofArrows_surj _ _ _ _ _ π
  exact ⟨fun Y f hf => P.map (eqToHom (h f hf).symm).op (x _),
fun j => (hx _ j (X j) _ (𝟙 _) <| by rw [← h', id_comp]).trans by simp⟩

variable (hx : Compatible P π x)

/--
A `FamilyOfElements` associated to an explicit family of elements.
-/
noncomputable
/--
Definition of `familyOfElements` / `familyOfElements` 的定义

English:
definition familyOfElements
  signature: : FamilyOfElements P (ofArrows X π)
  body: (exists_familyOfElements hx).choose

@[simp]

中文:
定义 familyOfElements
  签名: : FamilyOfElements P (ofArrows X π)
  定义体: (exists_familyOfElements hx).choose

@[simp]

Depends on / 依赖: exists_familyOfElements
-/
def familyOfElements : FamilyOfElements P (ofArrows X π) :=
  (exists_familyOfElements hx).choose

@[simp]
/--
theorem `familyOfElements_ofArrows_mk` / 定理 `familyOfElements_ofArrows_mk`

English:
theorem familyOfElements_ofArrows_mk
  given: (i : I)
  proof: (exists_familyOfElements hx).choose_spec _

中文:
定理 familyOfElements_ofArrows_mk
  条件: (i : I)
  证明: (exists_familyOfElements hx).choose_spec _

Depends on / 依赖: choose_spec, exists_familyOfElements
-/
theorem familyOfElements_ofArrows_mk (i : I) :
    hx.familyOfElements _ (ofArrows.mk i) = x i :=
  (exists_familyOfElements hx).choose_spec _

/--
theorem `familyOfElements_compatible` / 定理 `familyOfElements_compatible`

English:
theorem familyOfElements_compatible
  statement: hx.familyOfElements.Compatible
  proof: by
  rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i⟩ ⟨j⟩ hgf
  simp [hx i j Z g₁ g₂ hgf]

中文:
定理 familyOfElements_compatible
  结论: hx.familyOfElements.Compatible
  证明: by
  rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i⟩ ⟨j⟩ hgf
  simp [hx i j Z g₁ g₂ hgf]
-/
theorem familyOfElements_compatible : hx.familyOfElements.Compatible := by
  rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i⟩ ⟨j⟩ hgf
  simp [hx i j Z g₁ g₂ hgf]

end Arrows.Compatible

/--
theorem `isSheafFor_arrows_iff` / 定理 `isSheafFor_arrows_iff`

English:
theorem isSheafFor_arrows_iff
  statement: (ofArrows X π).IsSheafFor P ↔
  proof: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := h _ hx.familyOfElements_compatible
    refine ⟨t, fun i => ?_, fun t' ht' => ht₂ _ fun _ _ ⟨i⟩ => ?_⟩
    · rw [ht₁ _ (ofArrows.mk i), hx.familyOfElements_ofArrows_mk]
    · rw [ht', hx.familyOfElements_ofArrows_mk]
  · obt

中文:
定理 isSheafFor_arrows_iff
  结论: (ofArrows X π).IsSheafFor P ↔
  证明: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := h _ hx.familyOfElements_compatible
    refine ⟨t, fun i => ?_, fun t' ht' => ht₂ _ fun _ _ ⟨i⟩ => ?_⟩
    · rw [ht₁ _ (ofArrows.mk i), hx.familyOfElements_ofArrows_mk]
    · rw [ht', hx.familyOfElements_ofArrows_mk]
  · obt

Depends on / 依赖: familyOfElements_compatible, familyOfElements_ofArrows_mk, hx.familyOfElements_compatible, hx.familyOfElements_ofArrows_mk, ofArrows, ofArrows.mk
-/
theorem isSheafFor_arrows_iff : (ofArrows X π).IsSheafFor P ↔
    (forall (x : (i : I) -> P.obj (op (X i))), Arrows.Compatible P π x ->
    exists! t, forall i, P.map (π i).op t = x i) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := h _ hx.familyOfElements_compatible
    refine ⟨t, fun i => ?_, fun t' ht' => ht₂ _ fun _ _ ⟨i⟩ => ?_⟩
    · rw [ht₁ _ (ofArrows.mk i), hx.familyOfElements_ofArrows_mk]
    · rw [ht', hx.familyOfElements_ofArrows_mk]
  · obtain ⟨t, hA, ht⟩ := h (fun i => x (π i) (ofArrows.mk _))
      (fun i j Z gi gj => hx gi gj (ofArrows.mk _) (ofArrows.mk _))
    exact ⟨t, fun Y f ⟨i⟩ => hA i, fun y hy => ht y (fun i => hy (π i) (ofArrows.mk _))⟩

/-- If `P` is a presheaf of types and `π : (i : I) → X i ⟶ B` is a family
of morphisms, this is the map from `P.obj (op B)` to the subtype of compatible
families in `P.obj (op (X i))`. -/
@[simps]
/--
Definition of `Arrows.toCompatible` / `Arrows.toCompatible` 的定义

English:
definition Arrows.toCompatible
  signature: (s : P.obj (op B))
  body: P.map (π i).op s
  property i j Z gi gj h := by
    simp [← comp_apply, ← Functor.map_comp, ← op_comp, h]

中文:
定义 Arrows.toCompatible
  签名: (s : P.obj (op B))
  定义体: P.map (π i).op s
  property i j Z gi gj h := by
    simp [← comp_apply, ← Functor.map_comp, ← op_comp, h]

Depends on / 依赖: P.map
-/
def Arrows.toCompatible (s : P.obj (op B)) :
    Subtype (Arrows.Compatible P π) where
  val i := P.map (π i).op s
  property i j Z gi gj h := by
    simp [← comp_apply, ← Functor.map_comp, ← op_comp, h]

/--
theorem `isSheafFor_ofArrows_iff_bijective_toCompabible` / 定理 `isSheafFor_ofArrows_iff_bijective_toCompabible`

English:
theorem isSheafFor_ofArrows_iff_bijective_toCompabible
  proof: by
  rw [isSheafFor_arrows_iff]
  refine ⟨fun h => ⟨fun x₁ x₂ hx =>
      (h _ (Arrows.toCompatible P π x₁).property).unique (fun _ => rfl)
        (congr_fun (congr_arg Subtype.val hx.symm)),
      fun ⟨y, hy⟩ => ?_⟩, fun h x hx => ?_⟩
  · obtain ⟨x, hx, _⟩ := h y hy
    exact ⟨x, by ext; apply hx⟩

中文:
定理 isSheafFor_ofArrows_iff_bijective_toCompabible
  证明: by
  rw [isSheafFor_arrows_iff]
  refine ⟨fun h => ⟨fun x₁ x₂ hx =>
      (h _ (Arrows.toCompatible P π x₁).property).unique (fun _ => rfl)
        (congr_fun (congr_arg Subtype.val hx.symm)),
      fun ⟨y, hy⟩ => ?_⟩, fun h x hx => ?_⟩
  · obtain ⟨x, hx, _⟩ := h y hy
    exact ⟨x, by ext; apply hx⟩

Depends on / 依赖: Arrows, Arrows.toCompatible, Subtype, Subtype.ext_iff, Subtype.val, congr_arg, congr_fun, ext_iff, hx.symm, isSheafFor_arrows_iff, property, toCompatible, unique
-/
theorem isSheafFor_ofArrows_iff_bijective_toCompabible :
    IsSheafFor P (ofArrows X π) ↔
      Function.Bijective (Arrows.toCompatible P π) := by
  rw [isSheafFor_arrows_iff]
  refine ⟨fun h => ⟨fun x₁ x₂ hx =>
      (h _ (Arrows.toCompatible P π x₁).property).unique (fun _ => rfl)
        (congr_fun (congr_arg Subtype.val hx.symm)),
      fun ⟨y, hy⟩ => ?_⟩, fun h x hx => ?_⟩
  · obtain ⟨x, hx, _⟩ := h y hy
    exact ⟨x, by ext; apply hx⟩
  · obtain ⟨y, hy⟩ := h.2 ⟨x, hx⟩
    rw [Subtype.ext_iff] at hy
    dsimp at hy
    subst hy
    exact ⟨y, fun _ => rfl, fun y' hy' => h.1 (by ext; apply hy')⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `isSheafFor_pullback_iff` / 引理 `isSheafFor_pullback_iff`

English:
lemma isSheafFor_pullback_iff
  statement: (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X)
  proof: by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have := Sieve.pullback_ofArrows_of_iso _ g (asIso f)
  dsimp at this
  let e : Subtype (Arrows.Compatible P g) ≃
    Subtype (Arrows.Compatible P (fun i => g i ≫ inv f)) :=
    { toFun s := ⟨fun i => s.val i, fun i₁ i₂ W g₁ g₂ h => by
        simp

中文:
引理 isSheafFor_pullback_iff
  结论: (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X)
  证明: by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have := Sieve.pullback_ofArrows_of_iso _ g (asIso f)
  dsimp at this
  let e : Subtype (Arrows.Compatible P g) ≃
    Subtype (Arrows.Compatible P (fun i => g i ≫ inv f)) :=
    { toFun s := ⟨fun i => s.val i, fun i₁ i₂ W g₁ g₂ h => by
        simp

Depends on / 依赖: Arrows, Arrows.Compatible, Category, Category.assoc, Compatible, IsIso.inv_hom_id, R.exists_eq_ofArrows, Sieve.pullback_ofArrows_of_iso, Subtype, cancel_mono, comp_id, exists_eq_ofArrows, invFun, inv_hom_id, property, pullback_ofArrows_of_iso, replace, s.property, s.val
-/
lemma isSheafFor_pullback_iff (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X)
    {Y : C} (f : Y ⟶ X) [IsIso f] :
    IsSheafFor P (Sieve.pullback f R).arrows ↔ IsSheafFor P R.arrows := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have := Sieve.pullback_ofArrows_of_iso _ g (asIso f)
  dsimp at this
  let e : Subtype (Arrows.Compatible P g) ≃
    Subtype (Arrows.Compatible P (fun i => g i ≫ inv f)) :=
    { toFun s := ⟨fun i => s.val i, fun i₁ i₂ W g₁ g₂ h => by
        simp only [← cancel_mono f, assoc, IsIso.inv_hom_id, comp_id] at h
        exact s.property _ _ _ _ _ h⟩
      invFun s := ⟨fun i => s.val i, fun i₁ i₂ W g₁ g₂ h => by
        replace h := h =≫ inv f
        simp only [Category.assoc] at h
        exact s.property _ _ _ _ _ h⟩ }
  simp only [this, ← isSheafFor_iff_generate,
    isSheafFor_ofArrows_iff_bijective_toCompabible, ← e.bijective.of_comp_iff',
    ← Function.Bijective.of_comp_iff _ (P.mapIso (asIso f).symm.op).toEquiv.bijective]
  convert! Iff.rfl using 2
  ext
  simp [e]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSheafFor_over_map_op_comp_ofArrows_iff` / 引理 `isSheafFor_over_map_op_comp_ofArrows_iff`

English:
lemma isSheafFor_over_map_op_comp_ofArrows_iff
  proof: by
  let e : Subtype (Arrows.Compatible ((Over.map p).op ⋙ P) f) ≃
      Subtype (Arrows.Compatible P (fun i => (Over.map p).map (f i))) :=
    { toFun s := ⟨fun i => s.val i, fun i₁ i₂ Z g₁ g₂ h => by
        replace h := (Over.forget _).congr_map h
        dsimp at h
        have := s.property i₁ 

中文:
引理 isSheafFor_over_map_op_comp_ofArrows_iff
  证明: by
  let e : Subtype (Arrows.Compatible ((Over.map p).op ⋙ P) f) ≃
      Subtype (Arrows.Compatible P (fun i => (Over.map p).map (f i))) :=
    { toFun s := ⟨fun i => s.val i, fun i₁ i₂ Z g₁ g₂ h => by
        replace h := (Over.forget _).congr_map h
        dsimp at h
        have := s.property i₁ 

Depends on / 依赖: Arrows, Arrows.Compatible, Compatible, Over.forget, Over.homMk, Over.map, Over.mk, Over.w, Subtype, X.hom, cat_disch, congr_map, forget, property, reassoc_of, replace, s.property, s.val
-/
lemma isSheafFor_over_map_op_comp_ofArrows_iff
    {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w)
    {X : Over B} {Y : I -> Over B} (f : forall i, Y i ⟶ X) :
    IsSheafFor ((Over.map p).op ⋙ P) (Presieve.ofArrows _ f) ↔
      IsSheafFor P (Presieve.ofArrows _ (fun i => (Over.map p).map (f i))) := by
  let e : Subtype (Arrows.Compatible ((Over.map p).op ⋙ P) f) ≃
      Subtype (Arrows.Compatible P (fun i => (Over.map p).map (f i))) :=
    { toFun s := ⟨fun i => s.val i, fun i₁ i₂ Z g₁ g₂ h => by
        replace h := (Over.forget _).congr_map h
        dsimp at h
        have := s.property i₁ i₂ (Over.mk (g₁.left ≫ (f i₁).left ≫ X.hom))
          (Over.homMk g₁.left) (Over.homMk g₂.left (by
            have := Over.w (f i₂)
            dsimp at this ⊢
            rw [reassoc_of% h]; rw [this])) (by cat_disch)
        let φ : Z ⟶ (Over.map p).obj (Over.mk (g₁.left ≫ (f i₁).left ≫ X.hom)) :=
          Over.homMk (𝟙 _) (by simpa using Over.w g₁)
        replace this := congr_arg (P.map φ.op) this
        dsimp at this
        simp only [← comp_apply, ← Functor.map_comp, ← op_comp] at this
        convert! this <;> cat_disch⟩
      invFun s := ⟨fun i => s.val i, fun i₁ i₂ Z g₁ g₂ h =>
        s.property i₁ i₂ _ ((Over.map p).map g₁) ((Over.map p).map g₂)
          (by simp only [← Functor.map_comp, h])⟩ }
  simp only [isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← e.bijective.of_comp_iff']
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isSheafFor_over_map_op_comp_iff` / 引理 `isSheafFor_over_map_op_comp_iff`

English:
lemma isSheafFor_over_map_op_comp_iff
  proof: by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  rw [← isSheafFor_iff_generate]; rw [isSheafFor_pullback_iff]; rw [isSheafFor_over_map_op_comp_ofArrows_iff]; rw [isSheafFor_iff_generate]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro W _ ⟨T, _, a, ⟨_, b, _, ⟨i⟩, rfl⟩, rfl⟩
    refine ⟨

中文:
引理 isSheafFor_over_map_op_comp_iff
  证明: by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  rw [← isSheafFor_iff_generate]; rw [isSheafFor_pullback_iff]; rw [isSheafFor_over_map_op_comp_ofArrows_iff]; rw [isSheafFor_iff_generate]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro W _ ⟨T, _, a, ⟨_, b, _, ⟨i⟩, rfl⟩, rfl⟩
    refine ⟨

Depends on / 依赖: Iff.rfl, Over.homMk, Over.map, Over.w, Over.w_assoc, R.exists_eq_ofArrows, Sieve.ofArrows_mk, a.left, b.left, cat_disch, convert, exists_eq_ofArrows, isSheafFor_iff_generate, isSheafFor_over_map_op_comp_ofArrows_iff, isSheafFor_pullback_iff, le_antisymm, ofArrows_mk, w_assoc
-/
lemma isSheafFor_over_map_op_comp_iff
    {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w)
    {X : Over B} (R : Sieve X) {X' : Over B'}
    (e : (Over.map p).obj X ≅ X') :
    IsSheafFor ((Over.map p).op ⋙ P) R.arrows ↔
      IsSheafFor P (Sieve.pullback e.inv (Sieve.functorPushforward (Over.map p) R)).arrows := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  rw [← isSheafFor_iff_generate]; rw [isSheafFor_pullback_iff]; rw [isSheafFor_over_map_op_comp_ofArrows_iff]; rw [isSheafFor_iff_generate]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro W _ ⟨T, _, a, ⟨_, b, _, ⟨i⟩, rfl⟩, rfl⟩
    refine ⟨(Over.map p).obj (Z i), Over.homMk (a.left ≫ b.left) ?_, _, ⟨i⟩, ?_⟩
    · simpa [(Over.w_assoc b)] using Over.w a
    · cat_disch
  · rintro W _ ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, _, _, Sieve.ofArrows_mk _ _ i, rfl⟩

variable [(ofArrows X π).HasPairwisePullbacks]

/--
Definition of `Arrows.PullbackCompatible` / `Arrows.PullbackCompatible` 的定义

English:
definition Arrows.PullbackCompatible
  signature: (x : (i : I) -> P.obj (op (X i)))
  body: forall i j, P.map (pullback.fst (π i) (π j)).op (x i) =
    P.map (pullback.snd (π i) (π j)).op (x j)

中文:
定义 Arrows.PullbackCompatible
  签名: (x : (i : I) -> P.obj (op (X i)))
  定义体: forall i j, P.map (pullback.fst (π i) (π j)).op (x i) =
    P.map (pullback.snd (π i) (π j)).op (x j)

Depends on / 依赖: P.map, pullback, pullback.fst, pullback.snd
-/
def Arrows.PullbackCompatible (x : (i : I) -> P.obj (op (X i))) : Prop :=
  forall i j, P.map (pullback.fst (π i) (π j)).op (x i) =
    P.map (pullback.snd (π i) (π j)).op (x j)

/--
theorem `Arrows.pullbackCompatible_iff` / 定理 `Arrows.pullbackCompatible_iff`

English:
theorem Arrows.pullbackCompatible_iff
  given: (x : (i : I) -> P.obj (op (X i)))
  proof: by
  refine ⟨fun t i j => ?_, fun t i j Z gi gj comm => ?_⟩
  · apply t
    exact pullback.condition
  · rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply, t i j,
      ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]

中文:
定理 Arrows.pullbackCompatible_iff
  条件: (x : (i : I) -> P.obj (op (X i)))
  证明: by
  refine ⟨fun t i j => ?_, fun t i j Z gi gj comm => ?_⟩
  · apply t
    exact pullback.condition
  · rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply, t i j,
      ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]

Depends on / 依赖: Functor, Functor.map_comp, comp_apply, condition, lift_fst, lift_snd, map_comp, op_comp, pullback, pullback.condition, pullback.lift_fst, pullback.lift_snd
-/
theorem Arrows.pullbackCompatible_iff (x : (i : I) -> P.obj (op (X i))) :
    Compatible P π x ↔ PullbackCompatible P π x := by
  refine ⟨fun t i j => ?_, fun t i j Z gi gj comm => ?_⟩
  · apply t
    exact pullback.condition
  · rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply, t i j,
      ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]

/--
theorem `isSheafFor_arrows_iff_pullbacks` / 定理 `isSheafFor_arrows_iff_pullbacks`

English:
theorem isSheafFor_arrows_iff_pullbacks
  statement: (ofArrows X π).IsSheafFor P ↔
  proof: by
  simp_rw [← Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff]

中文:
定理 isSheafFor_arrows_iff_pullbacks
  结论: (ofArrows X π).IsSheafFor P ↔
  证明: by
  simp_rw [← Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff]

Depends on / 依赖: Arrows, Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff, pullbackCompatible_iff, simp_rw
-/
theorem isSheafFor_arrows_iff_pullbacks : (ofArrows X π).IsSheafFor P ↔
    (forall (x : (i : I) -> P.obj (op (X i))), Arrows.PullbackCompatible P π x ->
    exists! t, forall i, P.map (π i).op t = x i) := by
  simp_rw [← Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff]

end Arrows

@[simp]
/--
lemma `isSeparatedFor_singleton` / 引理 `isSeparatedFor_singleton`

English:
lemma isSeparatedFor_singleton
  given: {X Y : C} {f : X ⟶ Y}
  proof: by
  rw [IsSeparatedFor]; rw [Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.isAmalgamation_singleton_iff,
    FamilyOfElements.singletonEquiv_symm_apply_self, Function.Injective]
  aesop

中文:
引理 isSeparatedFor_singleton
  条件: {X Y : C} {f : X ⟶ Y}
  证明: by
  rw [IsSeparatedFor]; rw [Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.isAmalgamation_singleton_iff,
    FamilyOfElements.singletonEquiv_symm_apply_self, Function.Injective]
  aesop

Depends on / 依赖: Equiv.forall_congr_left, FamilyOfElements, FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self, Function, Function.Injective, Injective, IsSeparatedFor, Presieve, Presieve.FamilyOfElements.singletonEquiv, forall_congr_left, isAmalgamation_singleton_iff, simp_rw, singletonEquiv, singletonEquiv_symm_apply_self
-/
lemma isSeparatedFor_singleton {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSeparatedFor P (.singleton f) ↔
      Function.Injective (P.map f.op) := by
  rw [IsSeparatedFor]; rw [Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.isAmalgamation_singleton_iff,
    FamilyOfElements.singletonEquiv_symm_apply_self, Function.Injective]
  aesop

/--
lemma `isSheafFor_singleton` / 引理 `isSheafFor_singleton`

English:
lemma isSheafFor_singleton
  given: {X Y : C} {f : X ⟶ Y}
  proof: by
  rw [IsSheafFor]; rw [Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.compatible_singleton_iff,
    FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self]

中文:
引理 isSheafFor_singleton
  条件: {X Y : C} {f : X ⟶ Y}
  证明: by
  rw [IsSheafFor]; rw [Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.compatible_singleton_iff,
    FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self]

Depends on / 依赖: Equiv.forall_congr_left, FamilyOfElements, FamilyOfElements.compatible_singleton_iff, FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self, IsSheafFor, Presieve, Presieve.FamilyOfElements.singletonEquiv, compatible_singleton_iff, forall_congr_left, isAmalgamation_singleton_iff, simp_rw, singletonEquiv, singletonEquiv_symm_apply_self
-/
lemma isSheafFor_singleton {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSheafFor P (.singleton f) ↔
      forall (x : P.obj (op X)),
        (forall {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f -> P.map p₁.op x = P.map p₂.op x) ->
        exists! y, P.map f.op y = x := by
  rw [IsSheafFor]; rw [Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.compatible_singleton_iff,
    FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self]

/--
theorem `isSheafFor_bind` / 定理 `isSheafFor_bind`

English:
theorem isSheafFor_bind
  statement: (P : Cᵒᵖ ⥤ Type*) (U : Sieve X)
  proof: by
  intro s hs
  let y : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.FamilyOfElements P (B hf : Presieve Y) :=
    fun Y f hf Z g hg => s _ (Presieve.bind_comp _ _ hg)
  have hy : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible := by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply h

中文:
定理 isSheafFor_bind
  结论: (P : Cᵒᵖ ⥤ 类型) (U : Sieve X)
  证明: by
  intro s hs
  let y : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.FamilyOfElements P (B hf : Presieve Y) :=
    fun Y f hf Z g hg => s _ (Presieve.bind_comp _ _ hg)
  have hy : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible := by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply h

Depends on / 依赖: Compatible, FamilyOfElements, IsAmalgamation, Presieve, Presieve.FamilyOfElements, Presieve.bind_comp, amalgamate, bind_comp, reassoc_of
-/
theorem isSheafFor_bind (P : Cᵒᵖ ⥤ Type*) (U : Sieve X)
    (B : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f -> Sieve Y)
    (hU : Presieve.IsSheafFor P (U : Presieve X))
    (hB : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.IsSheafFor P (B hf : Presieve Y))
    (hB' : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y),
      Presieve.IsSeparatedFor P (((B h).pullback g) : Presieve Z)) :
    Presieve.IsSheafFor P (Sieve.bind (U : Presieve X) B : Presieve X) := by
  intro s hs
  let y : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.FamilyOfElements P (B hf : Presieve Y) :=
    fun Y f hf Z g hg => s _ (Presieve.bind_comp _ _ hg)
  have hy : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible := by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply hs
    apply reassoc_of% comm
  let t : Presieve.FamilyOfElements P (U : Presieve X) :=
    fun Y f hf => (hB hf).amalgamate (y hf) (hy hf)
  have ht : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).IsAmalgamation (t f hf) := fun Y f hf =>
    (hB hf).isAmalgamation _
  have hT : t.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W f h hf
    apply (hB (U.downward_closed hf h)).isSeparatedFor.ext
    intro Y l hl
    apply (hB' hf (l ≫ h)).ext
    intro M m hm
    have : Sieve.bind U B (m ≫ l ≫ h ≫ f) := by simpa using (bind_comp f hf hm : Sieve.bind U B _)
    trans s (m ≫ l ≫ h ≫ f) this
    · have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)
      simp only [op_comp, Functor.map_comp, comp_apply] at this
      grind
    · have h : s _ _ = _ := (ht hf _ hm).symm
      -- Porting note: this was done by `simp only [assoc] at`
      conv_lhs at h => congr; rw [assoc, assoc]
      simp [h]
  refine ⟨hU.amalgamate t hT, ?_, ?_⟩
  · rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩
    rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply]; rw [Presieve.IsSheafFor.valid_glue _ _ _ hg]
    apply ht hg _ hf
  · intro y hy
    apply hU.isSeparatedFor.ext
    intro Y f hf
    apply (hB hf).isSeparatedFor.ext
    intro Z g hg
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [hy _ (Presieve.bind_comp _ _ hg)]; rw [hU.valid_glue _ _ hf]; rw [ht hf _ hg]

/--
theorem `isSheafFor_trans` / 定理 `isSheafFor_trans`

English:
theorem isSheafFor_trans
  statement: (P : Cᵒᵖ ⥤ Type*) (R S : Sieve X)
  proof: by
  have : (Sieve.bind R fun Y f _ => S.pullback f : Presieve X) <= S := by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply Presieve.isSheafFor_subsieve_aux P this
  · apply isSheafFor_bind _ _ _ hR hS
    intro Y f hf Z g
    rw [← Sieve.pullback_comp]
    apply (hS (R.downward_cl

中文:
定理 isSheafFor_trans
  结论: (P : Cᵒᵖ ⥤ 类型) (R S : Sieve X)
  证明: by
  have : (Sieve.bind R fun Y f _ => S.pullback f : Presieve X) <= S := by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply Presieve.isSheafFor_subsieve_aux P this
  · apply isSheafFor_bind _ _ _ hR hS
    intro Y f hf Z g
    rw [← Sieve.pullback_comp]
    apply (hS (R.downward_cl

Depends on / 依赖: Presieve, Presieve.isSheafFor_subsieve_aux, R.downward_closed, R.pullback, S.pullback, Sieve.bind, Sieve.pullback, Sieve.pullback_comp, downward_closed, isSeparatedFor, isSheafFor_bind, isSheafFor_subsieve_aux, pullback, pullback_apply, pullback_comp
-/
theorem isSheafFor_trans (P : Cᵒᵖ ⥤ Type*) (R S : Sieve X)
    (hR : Presieve.IsSheafFor P (R : Presieve X))
    (hR' : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : S f), Presieve.IsSeparatedFor P (R.pullback f : Presieve Y))
    (hS : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), Presieve.IsSheafFor P (S.pullback f : Presieve Y)) :
    Presieve.IsSheafFor P (S : Presieve X) := by
  have : (Sieve.bind R fun Y f _ => S.pullback f : Presieve X) <= S := by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply Presieve.isSheafFor_subsieve_aux P this
  · apply isSheafFor_bind _ _ _ hR hS
    intro Y f hf Z g
    rw [← Sieve.pullback_comp]
    apply (hS (R.downward_closed hf _)).isSeparatedFor
  · intro Y f hf
    have : Sieve.pullback f (Sieve.bind R fun T (k : T ⟶ X) (_ : R k) => Sieve.pullback k S) =
        R.pullback f := by
      ext Z g
      constructor
      · rintro ⟨W, k, l, hl, _, comm⟩
        rw [pullback_apply]; rw [← comm]
        simp [hl]
      · intro a
        refine ⟨Z, 𝟙 Z, _, a, ?_⟩
        simp [hf]
    rw [this]
    apply hR' hf

end Presieve

end CategoryTheory
