/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Coproducts in `Type`

If `F : J → Type max v u` (with `J : Type v`), we show that the coproduct
of `F` exists in `Type max v u` and identifies to the sigma type `Σ j, F j`.
Similarly, the binary coproduct of two types `X` and `Y` identifies to
`X ⊕ Y`, and the initial object of `Type u` if `PEmpty`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits

variable {C : Type u} (F : C -> Type v)

/--
Definition of `CofanTypes` / `CofanTypes` 的定义

English:
abbreviation CofanTypes
  body: Functor.CoconeTypes.{w} (Discrete.functor F)

中文:
缩写 CofanTypes
  定义体: Functor.CoconeTypes.{w} (Discrete.functor F)

Depends on / 依赖: CoconeTypes, Discrete, Discrete.functor, Functor, Functor.CoconeTypes, functor
-/
abbrev CofanTypes := Functor.CoconeTypes.{w} (Discrete.functor F)

variable {F}

namespace CofanTypes

/--
Definition of `inj` / `inj` 的定义

English:
abbreviation inj
  signature: (c : CofanTypes.{w} F) (i : C)
  body: c.ι ⟨i⟩

中文:
缩写 inj
  签名: (c : CofanTypes.{w} F) (i : C)
  定义体: c.ι ⟨i⟩
-/
abbrev inj (c : CofanTypes.{w} F) (i : C) : F i -> c.pt := c.ι ⟨i⟩

variable (F) in
/-- The cofan given by a sigma type. -/
@[simps]
/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: : CofanTypes F where
  body: Σ (i : C), F i
  ι := fun ⟨i⟩ x => ⟨i, x⟩
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

@[simp]

中文:
定义 sigma
  签名: : CofanTypes F where
  定义体: Σ (i : C), F i
  ι := fun ⟨i⟩ x => ⟨i, x⟩
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

@[simp]
-/
def sigma : CofanTypes F where
  pt := Σ (i : C), F i
  ι := fun ⟨i⟩ x => ⟨i, x⟩
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

@[simp]
/--
lemma `sigma_inj` / 引理 `sigma_inj`

English:
lemma sigma_inj
  given: (i : C) (x : F i)
  proof: rfl

中文:
引理 sigma_inj
  条件: (i : C) (x : F i)
  证明: rfl
-/
lemma sigma_inj (i : C) (x : F i) :
    (sigma F).inj i x = ⟨i, x⟩ := rfl

/--
lemma `isColimit_mk` / 引理 `isColimit_mk`

English:
lemma isColimit_mk
  statement: (c : CofanTypes.{w} F)
  proof: by
    constructor
    · intro x y h
      obtain ⟨⟨i⟩, x, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective x
      obtain ⟨⟨j⟩, y, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective y
      obtain rfl := h₃ _ _ _ _ h
      obtain rfl := h₂ _ h
      rfl
    · intro x
      obtain ⟨i, y, rfl⟩ := h₁ x
      exact ⟨(Discrete.functor F).ιColimitType ⟨i⟩ y, rfl⟩

中文:
引理 isColimit_mk
  结论: (c : CofanTypes.{w} F)
  证明: by
    constructor
    · intro x y h
      obtain ⟨⟨i⟩, x, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective x
      obtain ⟨⟨j⟩, y, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective y
      obtain rfl := h₃ _ _ _ _ h
      obtain rfl := h₂ _ h
      rfl
    · intro x
      obtain ⟨i, y, rfl⟩ := h₁ x
      exact ⟨(Discrete.functor F).ιColimitType ⟨i⟩ y, rfl⟩

Depends on / 依赖: Discrete, Discrete.functor, functor
-/
lemma isColimit_mk (c : CofanTypes.{w} F)
    (h₁ : forall (x : c.pt), exists (i : C) (y : F i), c.inj i y = x)
    (h₂ : forall (i : C), Function.Injective (c.inj i))
    (h₃ : forall (i j : C) (x : F i) (y : F j), c.inj i x = c.inj j y -> i = j) :
    Functor.CoconeTypes.IsColimit c where
  bijective := by
    constructor
    · intro x y h
      obtain ⟨⟨i⟩, x, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective x
      obtain ⟨⟨j⟩, y, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective y
      obtain rfl := h₃ _ _ _ _ h
      obtain rfl := h₂ _ h
      rfl
    · intro x
      obtain ⟨i, y, rfl⟩ := h₁ x
      exact ⟨(Discrete.functor F).ιColimitType ⟨i⟩ y, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/--
lemma `isColimit_sigma` / 引理 `isColimit_sigma`

English:
lemma isColimit_sigma
  statement: Functor.CoconeTypes.IsColimit (sigma F)
  proof: isColimit_mk _ (by aesop)
    (fun _ _ _ h => by rw [Sigma.ext_iff] at h; simpa using h)
    (fun _ _ _ _ h => congr_arg Sigma.fst h)

中文:
引理 isColimit_sigma
  结论: 函子.余coneTypes.是余极限 (sigma F)
  证明: isColimit_mk _ (by aesop)
    (fun _ _ _ h => by rw [Sigma.ext_iff] at h; simpa using h)
    (fun _ _ _ _ h => congr_arg Sigma.fst h)

Depends on / 依赖: Sigma.ext_iff, Sigma.fst, congr_arg, ext_iff, isColimit_mk
-/
lemma isColimit_sigma : Functor.CoconeTypes.IsColimit (sigma F) :=
  isColimit_mk _ (by aesop)
    (fun _ _ _ h => by rw [Sigma.ext_iff] at h; simpa using h)
    (fun _ _ _ _ h => congr_arg Sigma.fst h)

variable (F) in
/-- Given a cofan of a functor to types, this is a canonical map
from the Sigma type to the point of the cofan. -/
@[simp]
/--
Definition of `fromSigma` / `fromSigma` 的定义

English:
definition fromSigma
  signature: (c : CofanTypes.{w} F) (x : Σ (i : C), F i)
  body: c.inj x.1 x.2

中文:
定义 fromSigma
  签名: (c : CofanTypes.{w} F) (x : Σ (i : C), F i)
  定义体: c.inj x.1 x.2

Depends on / 依赖: c.inj
-/
def fromSigma (c : CofanTypes.{w} F) (x : Σ (i : C), F i) : c.pt :=
  c.inj x.1 x.2

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isColimit_iff_bijective_fromSigma` / 引理 `isColimit_iff_bijective_fromSigma`

English:
lemma isColimit_iff_bijective_fromSigma
  given: (c : CofanTypes.{w} F)
  proof: by
  rw [(isColimit_sigma F).iff_bijective]
  aesop

中文:
引理 isColimit_iff_bijective_fromSigma
  条件: (c : CofanTypes.{w} F)
  证明: by
  rw [(isColimit_sigma F).iff_bijective]
  aesop

Depends on / 依赖: iff_bijective, isColimit_sigma
-/
lemma isColimit_iff_bijective_fromSigma (c : CofanTypes.{w} F) :
    c.IsColimit ↔ Function.Bijective c.fromSigma := by
  rw [(isColimit_sigma F).iff_bijective]
  aesop

section

variable {c : CofanTypes.{w} F} (hc : Functor.CoconeTypes.IsColimit c)

include hc

/--
lemma `bijective_fromSigma_of_isColimit` / 引理 `bijective_fromSigma_of_isColimit`

English:
lemma bijective_fromSigma_of_isColimit
  proof: by
  rwa [← isColimit_iff_bijective_fromSigma]

中文:
引理 bijective_fromSigma_of_isColimit
  证明: by
  rwa [← isColimit_iff_bijective_fromSigma]

Depends on / 依赖: isColimit_iff_bijective_fromSigma
-/
lemma bijective_fromSigma_of_isColimit :
    Function.Bijective c.fromSigma := by
  rwa [← isColimit_iff_bijective_fromSigma]

/--
Definition of `equivOfIsColimit` / `equivOfIsColimit` 的定义

English:
definition equivOfIsColimit
  signature: :
  body: Equiv.ofBijective _ (bijective_fromSigma_of_isColimit hc)

@[simp]

中文:
定义 equivOfIsColimit
  签名: :
  定义体: Equiv.ofBijective _ (bijective_fromSigma_of_isColimit hc)

@[simp]

Depends on / 依赖: Equiv.ofBijective, bijective_fromSigma_of_isColimit, ofBijective
-/
noncomputable def equivOfIsColimit :
    (Σ (i : C), F i) ≃ c.pt :=
  Equiv.ofBijective _ (bijective_fromSigma_of_isColimit hc)

@[simp]
/--
lemma `equivOfIsColimit_apply` / 引理 `equivOfIsColimit_apply`

English:
lemma equivOfIsColimit_apply
  given: (i : C) (x : F i)
  proof: rfl

@[simp]

中文:
引理 equivOfIsColimit_apply
  条件: (i : C) (x : F i)
  证明: rfl

@[simp]
-/
lemma equivOfIsColimit_apply (i : C) (x : F i) :
    equivOfIsColimit hc ⟨i, x⟩ = c.inj i x := rfl

@[simp]
/--
lemma `equivOfIsColimit_symm_apply` / 引理 `equivOfIsColimit_symm_apply`

English:
lemma equivOfIsColimit_symm_apply
  given: (i : C) (x : F i)
  proof: (equivOfIsColimit hc).injective (by simp)

中文:
引理 equivOfIsColimit_symm_apply
  条件: (i : C) (x : F i)
  证明: (equivOfIsColimit hc).injective (by simp)

Depends on / 依赖: equivOfIsColimit, injective
-/
lemma equivOfIsColimit_symm_apply (i : C) (x : F i) :
    (equivOfIsColimit hc).symm (c.inj i x) = ⟨i, x⟩ :=
  (equivOfIsColimit hc).injective (by simp)

/--
lemma `inj_jointly_surjective_of_isColimit` / 引理 `inj_jointly_surjective_of_isColimit`

English:
lemma inj_jointly_surjective_of_isColimit
  given: (x : c.pt)
  proof: by
  obtain ⟨⟨i⟩, y, rfl⟩ := hc.ι_jointly_surjective x
  exact ⟨i, y, rfl⟩

中文:
引理 inj_jointly_surjective_of_isColimit
  条件: (x : c.pt)
  证明: by
  obtain ⟨⟨i⟩, y, rfl⟩ := hc.ι_jointly_surjective x
  exact ⟨i, y, rfl⟩
-/
lemma inj_jointly_surjective_of_isColimit (x : c.pt) :
    exists (i : C) (y : F i), c.inj i y = x := by
  obtain ⟨⟨i⟩, y, rfl⟩ := hc.ι_jointly_surjective x
  exact ⟨i, y, rfl⟩

/--
lemma `inj_injective_of_isColimit` / 引理 `inj_injective_of_isColimit`

English:
lemma inj_injective_of_isColimit
  given: (i : C)
  proof: by
  intro y₁ y₂ h
  simpa using (equivOfIsColimit hc).injective (a₁ := ⟨i, y₁⟩) (a₂ := ⟨i, y₂⟩) h

中文:
引理 inj_injective_of_isColimit
  条件: (i : C)
  证明: by
  intro y₁ y₂ h
  simpa using (equivOfIsColimit hc).injective (a₁ := ⟨i, y₁⟩) (a₂ := ⟨i, y₂⟩) h

Depends on / 依赖: equivOfIsColimit, injective
-/
lemma inj_injective_of_isColimit (i : C) :
    Function.Injective (c.inj i) := by
  intro y₁ y₂ h
  simpa using (equivOfIsColimit hc).injective (a₁ := ⟨i, y₁⟩) (a₂ := ⟨i, y₂⟩) h

/--
lemma `eq_of_inj_apply_eq_of_isColimit` / 引理 `eq_of_inj_apply_eq_of_isColimit`

English:
lemma eq_of_inj_apply_eq_of_isColimit
  proof: congr_arg Sigma.fst ((equivOfIsColimit hc).injective (a₁ := ⟨i₁, y₁⟩) (a₂ := ⟨i₂, y₂⟩) h)

中文:
引理 eq_of_inj_apply_eq_of_isColimit
  证明: congr_arg Sigma.fst ((equivOfIsColimit hc).injective (a₁ := ⟨i₁, y₁⟩) (a₂ := ⟨i₂, y₂⟩) h)

Depends on / 依赖: Sigma.fst, congr_arg, equivOfIsColimit, injective
-/
lemma eq_of_inj_apply_eq_of_isColimit
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) :
    i₁ = i₂ :=
  congr_arg Sigma.fst ((equivOfIsColimit hc).injective (a₁ := ⟨i₁, y₁⟩) (a₂ := ⟨i₂, y₂⟩) h)

/--
lemma `inj_apply_eq_iff_of_isColimit` / 引理 `inj_apply_eq_iff_of_isColimit`

English:
lemma inj_apply_eq_iff_of_isColimit
  proof: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => by subst h₁ h₂; rfl⟩
  obtain rfl := eq_of_inj_apply_eq_of_isColimit hc _ _ h
  exact ⟨rfl, (inj_injective_of_isColimit hc i₁ h).symm⟩

中文:
引理 inj_apply_eq_iff_of_isColimit
  证明: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => by subst h₁ h₂; rfl⟩
  obtain rfl := eq_of_inj_apply_eq_of_isColimit hc _ _ h
  exact ⟨rfl, (inj_injective_of_isColimit hc i₁ h).symm⟩

Depends on / 依赖: eq_of_inj_apply_eq_of_isColimit, inj_injective_of_isColimit
-/
lemma inj_apply_eq_iff_of_isColimit
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) :
    c.inj i₁ y₁ = c.inj i₂ y₂ ↔ exists (h : i₁ = i₂), y₂ = cast (by rw [h]) y₁ := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => by subst h₁ h₂; rfl⟩
  obtain rfl := eq_of_inj_apply_eq_of_isColimit hc _ _ h
  exact ⟨rfl, (inj_injective_of_isColimit hc i₁ h).symm⟩

end

end CofanTypes

namespace Cofan

variable {C : Type u} {F : C -> Type v} (c : Cofan F)

/-- If `F : C → Type v`, then the data of a "type-theoretic" cofan of `F`
with a point in `Type v` is the same as the data of a cocone (in a categorical sense). -/
@[simps]
/--
Definition of `cofanTypes` / `cofanTypes` 的定义

English:
definition cofanTypes
  signature: :
  body: c.pt
  ι := fun ⟨j⟩ => c.inj j
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

中文:
定义 cofanTypes
  签名: :
  定义体: c.pt
  ι := fun ⟨j⟩ => c.inj j
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

Depends on / 依赖: c.pt
-/
def cofanTypes :
    CofanTypes.{v} F where
  pt := c.pt
  ι := fun ⟨j⟩ => c.inj j
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

/--
lemma `isColimit_cofanTypes_iff` / 引理 `isColimit_cofanTypes_iff`

English:
lemma isColimit_cofanTypes_iff
  proof: Functor.CoconeTypes.isColimit_iff _

中文:
引理 isColimit_cofanTypes_iff
  证明: Functor.CoconeTypes.isColimit_iff _

Depends on / 依赖: CoconeTypes, Functor, Functor.CoconeTypes.isColimit_iff, isColimit_iff
-/
lemma isColimit_cofanTypes_iff :
    c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c) :=
  Functor.CoconeTypes.isColimit_iff _

/--
lemma `nonempty_isColimit_iff_bijective_fromSigma` / 引理 `nonempty_isColimit_iff_bijective_fromSigma`

English:
lemma nonempty_isColimit_iff_bijective_fromSigma
  proof: by
  rw [← isColimit_cofanTypes_iff]; rw [CofanTypes.isColimit_iff_bijective_fromSigma]

中文:
引理 nonempty_isColimit_iff_bijective_fromSigma
  证明: by
  rw [← isColimit_cofanTypes_iff]; rw [CofanTypes.isColimit_iff_bijective_fromSigma]

Depends on / 依赖: CofanTypes, CofanTypes.isColimit_iff_bijective_fromSigma, isColimit_cofanTypes_iff, isColimit_iff_bijective_fromSigma
-/
lemma nonempty_isColimit_iff_bijective_fromSigma :
    Nonempty (IsColimit c) ↔ Function.Bijective c.cofanTypes.fromSigma := by
  rw [← isColimit_cofanTypes_iff]; rw [CofanTypes.isColimit_iff_bijective_fromSigma]

variable {c}

/--
lemma `inj_jointly_surjective_of_isColimit` / 引理 `inj_jointly_surjective_of_isColimit`

English:
lemma inj_jointly_surjective_of_isColimit
  given: (hc : IsColimit c) (x : c.pt)
  proof: CofanTypes.inj_jointly_surjective_of_isColimit
    ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) x

中文:
引理 inj_jointly_surjective_of_isColimit
  条件: (hc : 是余极限 c) (x : c.pt)
  证明: CofanTypes.inj_jointly_surjective_of_isColimit
    ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) x

Depends on / 依赖: CofanTypes, CofanTypes.inj_jointly_surjective_of_isColimit, inj_jointly_surjective_of_isColimit, isColimit_cofanTypes_iff
-/
lemma inj_jointly_surjective_of_isColimit (hc : IsColimit c) (x : c.pt) :
    exists (i : C) (y : F i), c.inj i y = x :=
  CofanTypes.inj_jointly_surjective_of_isColimit
    ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) x

/--
lemma `inj_injective_of_isColimit` / 引理 `inj_injective_of_isColimit`

English:
lemma inj_injective_of_isColimit
  given: (hc : IsColimit c) (i : C)
  proof: CofanTypes.inj_injective_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) i

中文:
引理 inj_injective_of_isColimit
  条件: (hc : 是余极限 c) (i : C)
  证明: CofanTypes.inj_injective_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) i

Depends on / 依赖: CofanTypes, CofanTypes.inj_injective_of_isColimit, inj_injective_of_isColimit, isColimit_cofanTypes_iff
-/
lemma inj_injective_of_isColimit (hc : IsColimit c) (i : C) :
    Function.Injective (c.inj i) :=
  CofanTypes.inj_injective_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) i

/--
lemma `eq_of_inj_apply_eq_of_isColimit` / 引理 `eq_of_inj_apply_eq_of_isColimit`

English:
lemma eq_of_inj_apply_eq_of_isColimit
  statement: (hc : IsColimit c)
  proof: CofanTypes.eq_of_inj_apply_eq_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _ h

中文:
引理 eq_of_inj_apply_eq_of_isColimit
  结论: (hc : 是余极限 c)
  证明: CofanTypes.eq_of_inj_apply_eq_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _ h

Depends on / 依赖: CofanTypes, CofanTypes.eq_of_inj_apply_eq_of_isColimit, eq_of_inj_apply_eq_of_isColimit, isColimit_cofanTypes_iff
-/
lemma eq_of_inj_apply_eq_of_isColimit (hc : IsColimit c)
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) :
    i₁ = i₂ :=
  CofanTypes.eq_of_inj_apply_eq_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _ h

/--
lemma `inj_apply_eq_iff_of_isColimit` / 引理 `inj_apply_eq_iff_of_isColimit`

English:
lemma inj_apply_eq_iff_of_isColimit
  given: (hc : IsColimit c) {i j : C} (x : F i) (y : F j)
  proof: CofanTypes.inj_apply_eq_iff_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _

中文:
引理 inj_apply_eq_iff_of_isColimit
  条件: (hc : 是余极限 c) {i j : C} (x : F i) (y : F j)
  证明: CofanTypes.inj_apply_eq_iff_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _

Depends on / 依赖: CofanTypes, CofanTypes.inj_apply_eq_iff_of_isColimit, inj_apply_eq_iff_of_isColimit, isColimit_cofanTypes_iff
-/
lemma inj_apply_eq_iff_of_isColimit (hc : IsColimit c) {i j : C} (x : F i) (y : F j) :
    c.inj i x = c.inj j y ↔ exists (hij : i = j), y = cast (by rw [hij]) x :=
  CofanTypes.inj_apply_eq_iff_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _

end Cofan

namespace Types

/--
Definition of `initialColimitCocone` / `initialColimitCocone` 的定义

English:
definition initialColimitCocone
  signature: : Limits.ColimitCocone (Functor.empty (Type u)) where
  body: { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => ↾fun x => x.elim
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by ext x; cases x }

中文:
定义 initialColimitCocone
  签名: : Limits.余极限余锥 (函子.empty (类型u)) where
  定义体: { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => ↾fun x => x.elim
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by ext x; cases x }

Depends on / 依赖: Functor, Functor.uniqueFromEmpty, PEmpty, isColimit, uniqueFromEmpty, x.elim
-/
def initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
  -- Porting note: tidy was able to fill the structure automatically
  cocone :=
    { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => ↾fun x => x.elim
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by ext x; cases x }

/--
Definition of `initialIso` / `initialIso` 的定义

English:
definition initialIso
  signature: : ⊥_ Type u ≅ PEmpty
  body: colimit.isoColimitCocone initialColimitCocone.{u, 0}

中文:
定义 initialIso
  签名: : ⊥_ 类型u ≅ 命题空
  定义体: colimit.isoColimitCocone initialColimitCocone.{u, 0}

Depends on / 依赖: colimit, colimit.isoColimitCocone, initialColimitCocone, isoColimitCocone
-/
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone.{u, 0}

/--
Definition of `isInitialPEmpty` / `isInitialPEmpty` 的定义

English:
definition isInitialPEmpty
  signature: : IsInitial (PEmpty : Type u)
  body: initialIsInitial.ofIso initialIso

@[deprecated (since := "2026-02-08")] alias isInitialPunit := isInitialPEmpty

中文:
定义 isInitialPEmpty
  签名: : IsInitial (命题空 : 类型u)
  定义体: initialIsInitial.ofIso initialIso

@[deprecated (since := "2026-02-08")] alias isInitialPunit := isInitialPEmpty

Depends on / 依赖: initialIsInitial, initialIsInitial.ofIso, initialIso
-/
noncomputable def isInitialPEmpty : IsInitial (PEmpty : Type u) :=
  initialIsInitial.ofIso initialIso

@[deprecated (since := "2026-02-08")] alias isInitialPunit := isInitialPEmpty

/--
lemma `initial_iff_empty` / 引理 `initial_iff_empty`

English:
lemma initial_iff_empty
  given: (X : Type u)
  statement: Nonempty (IsInitial X) ↔ IsEmpty X
  proof: by
  constructor
  · intro ⟨h⟩
    exact Function.isEmpty (IsInitial.to h PEmpty)
  · intro h
exact ⟨IsInitial.ofIso Types.isInitialPEmpty Equiv.toIso Equiv.equivOfIsEmpty PEmpty X⟩

中文:
引理 initial_iff_empty
  条件: (X : 类型u)
  结论: 非空 (IsInitial X) ↔ 是空 X
  证明: by
  constructor
  · intro ⟨h⟩
    exact Function.isEmpty (IsInitial.to h PEmpty)
  · intro h
exact ⟨IsInitial.ofIso Types.isInitialPEmpty Equiv.toIso Equiv.equivOfIsEmpty PEmpty X⟩

Depends on / 依赖: Equiv.equivOfIsEmpty, Equiv.toIso, Function, Function.isEmpty, IsInitial, IsInitial.ofIso, IsInitial.to, PEmpty, Types.isInitialPEmpty, equivOfIsEmpty, isEmpty, isInitialPEmpty
-/
lemma initial_iff_empty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  · intro ⟨h⟩
    exact Function.isEmpty (IsInitial.to h PEmpty)
  · intro h
exact ⟨IsInitial.ofIso Types.isInitialPEmpty Equiv.toIso Equiv.equivOfIsEmpty PEmpty X⟩


/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps!]
/--
Definition of `binaryCoproductCocone` / `binaryCoproductCocone` 的定义

English:
definition binaryCoproductCocone
  signature: (X Y : Type u)
  body: BinaryCofan.mk (↾Sum.inl) (↾Sum.inr)

中文:
定义 binaryCoproductCocone
  签名: (X Y : 类型u)
  定义体: BinaryCofan.mk (↾Sum.inl) (↾Sum.inr)

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, Sum.inl, Sum.inr
-/
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk (↾Sum.inl) (↾Sum.inr)

open CategoryTheory.Limits.WalkingPair

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
/--
Definition of `binaryCoproductColimit` / `binaryCoproductColimit` 的定义

English:
definition binaryCoproductColimit
  signature: (X Y : Type u)
  body: fun s : BinaryCofan X Y => ↾(Sum.elim s.inl s.inr)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext ⟨⟩
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) _, ConcreteCategory.congr_hom (w ⟨right⟩) _]

中文:
定义 binaryCoproductColimit
  签名: (X Y : 类型u)
  定义体: fun s : BinaryCofan X Y => ↾(Sum.elim s.inl s.inr)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext ⟨⟩
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) _, ConcreteCategory.congr_hom (w ⟨right⟩) _]

Depends on / 依赖: BinaryCofan, Sum.elim, s.inl, s.inr
-/
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => ↾(Sum.elim s.inl s.inr)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext ⟨⟩
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) _, ConcreteCategory.congr_hom (w ⟨right⟩) _]

/--
Definition of `binaryCoproductColimitCocone` / `binaryCoproductColimitCocone` 的定义

English:
definition binaryCoproductColimitCocone
  signature: (X Y : Type u)
  body: ⟨_, binaryCoproductColimit X Y⟩

中文:
定义 binaryCoproductColimitCocone
  签名: (X Y : 类型u)
  定义体: ⟨_, binaryCoproductColimit X Y⟩

Depends on / 依赖: binaryCoproductColimit
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩

/--
Definition of `binaryCoproductIso` / `binaryCoproductIso` 的定义

English:
definition binaryCoproductIso
  signature: (X Y : Type u)
  body: colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)

中文:
定义 binaryCoproductIso
  签名: (X Y : 类型u)
  定义体: colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)

Depends on / 依赖: binaryCoproductColimitCocone, colimit, colimit.isoColimitCocone, isoColimitCocone
-/
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ X oplus Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)

--open CategoryTheory.Type

@[elementwise (attr := simp)]
/--
theorem `binaryCoproductIso_inl_comp_hom` / 定理 `binaryCoproductIso_inl_comp_hom`

English:
theorem binaryCoproductIso_inl_comp_hom
  given: (X Y : Type u)
  proof: colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

中文:
定理 binaryCoproductIso_inl_comp_hom
  条件: (X Y : 类型u)
  证明: colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

Depends on / 依赖: WalkingPair, WalkingPair.left, binaryCoproductColimitCocone, colimit, colimit.isoColimitCocone_
-/
theorem binaryCoproductIso_inl_comp_hom (X Y : Type u) :
    Limits.coprod.inl ≫ (binaryCoproductIso X Y).hom = ↾Sum.inl :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
/--
theorem `binaryCoproductIso_inr_comp_hom` / 定理 `binaryCoproductIso_inr_comp_hom`

English:
theorem binaryCoproductIso_inr_comp_hom
  given: (X Y : Type u)
  proof: colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]

中文:
定理 binaryCoproductIso_inr_comp_hom
  条件: (X Y : 类型u)
  证明: colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]

Depends on / 依赖: WalkingPair, WalkingPair.right, binaryCoproductColimitCocone, colimit, colimit.isoColimitCocone_
-/
theorem binaryCoproductIso_inr_comp_hom (X Y : Type u) :
    Limits.coprod.inr ≫ (binaryCoproductIso X Y).hom = ↾Sum.inr :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]
/--
theorem `binaryCoproductIso_inl_comp_inv` / 定理 `binaryCoproductIso_inl_comp_inv`

English:
theorem binaryCoproductIso_inl_comp_inv
  given: (X Y : Type u)
  proof: colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

中文:
定理 binaryCoproductIso_inl_comp_inv
  条件: (X Y : 类型u)
  证明: colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

Depends on / 依赖: WalkingPair, WalkingPair.left, binaryCoproductColimitCocone, colimit, colimit.isoColimitCocone_
-/
theorem binaryCoproductIso_inl_comp_inv (X Y : Type u) :
    ↾Sum.inl ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inl :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
/--
theorem `binaryCoproductIso_inr_comp_inv` / 定理 `binaryCoproductIso_inr_comp_inv`

English:
theorem binaryCoproductIso_inr_comp_inv
  given: (X Y : Type u)
  proof: colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

中文:
定理 binaryCoproductIso_inr_comp_inv
  条件: (X Y : 类型u)
  证明: colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

Depends on / 依赖: WalkingPair, WalkingPair.right, binaryCoproductColimitCocone, colimit, colimit.isoColimitCocone_
-/
theorem binaryCoproductIso_inr_comp_inv (X Y : Type u) :
    ↾Sum.inr ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inr :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

open Function (Injective)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `binaryCofan_isColimit_iff` / 定理 `binaryCofan_isColimit_iff`

English:
theorem binaryCofan_isColimit_iff
  given: {X Y : Type u} (c : BinaryCofan X Y)
  proof: by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩]; rw [← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, ?_⟩
      rw [types_comp]; rw [Set.range_comp]; rw [← eq_compl_iff_isCompl]; rw [types_comp]
      dsimp
      rw [Set.range_comp _ Sum.inr]; rw [← dsimp% [Iso.toEquiv] Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : forall x, x in Set.range c.inl ∨ x in Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ↾fun x => ?_
        exact
          if h : x in Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        ext x
        simp
      · intro T f g
        ext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply, dite_eq_right_iff,
          forall_exists_index]
        intro y e
        have : c.inr x in Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        ext x
        simp only [TypeCat.Fun.toFun_apply, Functor.const_obj_obj, pair_obj_left, Set.mem_range,
          comp_apply, pair_obj_right, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

中文:
定理 binaryCofan_isColimit_iff
  条件: {X Y : 类型u} (c : BinaryCofan X Y)
  证明: by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩]; rw [← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, ?_⟩
      rw [types_comp]; rw [Set.range_comp]; rw [← eq_compl_iff_isCompl]; rw [types_comp]
      dsimp
      rw [Set.range_comp _ Sum.inr]; rw [← dsimp% [Iso.toEquiv] Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : forall x, x in Set.range c.inl ∨ x in Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ↾fun x => ?_
        exact
          if h : x in Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        ext x
        simp
      · intro T f g
        ext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply, dite_eq_right_iff,
          forall_exists_index]
        intro y e
        have : c.inr x in Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        ext x
        simp only [TypeCat.Fun.toFun_apply, Functor.const_obj_obj, pair_obj_left, Set.mem_range,
          comp_apply, pair_obj_right, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

Depends on / 依赖: Sum.inl_injective, Sum.inr_i, WalkingPair, WalkingPair.left, WalkingPair.right, binaryCoproductCocone, binaryCoproductColimit, c.inl, c.inr, classical, coconePointUniqueUpToIso, comp_coconePointUniqueUpToIso_inv, h.coconePointUniqueUpToIso, h.comp_coconePointUniqueUpToIso_inv, injective, inl_injective, inr_i, symm.toEquiv.injective.comp, toEquiv
-/
theorem binaryCofan_isColimit_iff {X Y : Type u} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩]; rw [← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, ?_⟩
      rw [types_comp]; rw [Set.range_comp]; rw [← eq_compl_iff_isCompl]; rw [types_comp]
      dsimp
      rw [Set.range_comp _ Sum.inr]; rw [← dsimp% [Iso.toEquiv] Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : forall x, x in Set.range c.inl ∨ x in Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ↾fun x => ?_
        exact
          if h : x in Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        ext x
        simp
      · intro T f g
        ext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply, dite_eq_right_iff,
          forall_exists_index]
        intro y e
        have : c.inr x in Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        ext x
        simp only [TypeCat.Fun.toFun_apply, Functor.const_obj_obj, pair_obj_left, Set.mem_range,
          comp_apply, pair_obj_right, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

/--
Definition of `isCoprodOfMono` / `isCoprodOfMono` 的定义

English:
definition isCoprodOfMono
  signature: {X Y : Type u} (f : X ⟶ Y) [Mono f]
  body: by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, ?_⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val

中文:
定义 isCoprodOfMono
  签名: {X Y : 类型u} (f : X ⟶ Y) [单态射 f]
  定义体: by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, ?_⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val

Depends on / 依赖: Nonempty, Nonempty.some, Subtype, Subtype.range_val, Subtype.val_injective, binaryCofan_isColimit_iff, eq_compl_iff_isCompl, mono_iff_injective, range_val, val_injective
-/
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (↾(Subtype.val : ↑(Set.range f)ᶜ -> Y))) := by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, ?_⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val

/--
Definition of `coproductColimitCocone` / `coproductColimitCocone` 的定义

English:
definition coproductColimitCocone
  signature: {J : Type v} (F : J -> Type (max v u))
  body: { pt := Σ j, F j
      ι := Discrete.natTrans (fun ⟨j⟩ => ↾fun x => ⟨j, x⟩) }
  isColimit :=
    { desc := fun s => ↾fun x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        ext ⟨j, x⟩
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

中文:
定义 coproductColimitCocone
  签名: {J : 类型v} (F : J -> 类型 (最大值 v u))
  定义体: { pt := Σ j, F j
      ι := Discrete.natTrans (fun ⟨j⟩ => ↾fun x => ⟨j, x⟩) }
  isColimit :=
    { desc := fun s => ↾fun x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        ext ⟨j, x⟩
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Discrete, Discrete.natTrans, congr_hom, isColimit, natTrans
-/
def coproductColimitCocone {J : Type v} (F : J -> Type (max v u)) :
    Limits.ColimitCocone (Discrete.functor F) where
  cocone :=
    { pt := Σ j, F j
      ι := Discrete.natTrans (fun ⟨j⟩ => ↾fun x => ⟨j, x⟩) }
  isColimit :=
    { desc := fun s => ↾fun x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        ext ⟨j, x⟩
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

/--
Definition of `coproductIso` / `coproductIso` 的定义

English:
definition coproductIso
  signature: {J : Type v} (F : J -> Type (max v u))
  body: colimit.isoColimitCocone (coproductColimitCocone F)

@[elementwise (attr := simp)]

中文:
定义 coproductIso
  签名: {J : 类型v} (F : J -> 类型 (最大值 v u))
  定义体: colimit.isoColimitCocone (coproductColimitCocone F)

@[elementwise (attr := simp)]

Depends on / 依赖: colimit, colimit.isoColimitCocone, coproductColimitCocone, isoColimitCocone
-/
noncomputable def coproductIso {J : Type v} (F : J -> Type (max v u)) :
    ∐ F ≅ (Σ j, F j) :=
  colimit.isoColimitCocone (coproductColimitCocone F)

@[elementwise (attr := simp)]
/--
theorem `coproductIso_ι_comp_hom` / 定理 `coproductIso_ι_comp_hom`

English:
theorem coproductIso_ι_comp_hom
  given: {J : Type v} (F : J -> Type (max v u)) (j : J)
  proof: colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩

@[elementwise (attr := simp)]

中文:
定理 coproductIso_ι_comp_hom
  条件: {J : 类型v} (F : J -> 类型 (最大值 v u)) (j : J)
  证明: colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩

@[elementwise (attr := simp)]

Depends on / 依赖: AddCommGroup, DMatrix, colimit, colimit.isoColimitCocone_, coproductColimitCocone
-/
theorem coproductIso_ι_comp_hom {J : Type v} (F : J -> Type (max v u)) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = ↾fun x => ⟨j, x⟩ :=
  colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩

@[elementwise (attr := simp)]
/--
theorem `coproductIso_mk_comp_inv` / 定理 `coproductIso_mk_comp_inv`

English:
theorem coproductIso_mk_comp_inv
  given: {J : Type v} (F : J -> Type (max v u)) (j : J)
  proof: rfl

中文:
定理 coproductIso_mk_comp_inv
  条件: {J : 类型v} (F : J -> 类型 (最大值 v u)) (j : J)
  证明: rfl
-/
theorem coproductIso_mk_comp_inv {J : Type v} (F : J -> Type (max v u)) (j : J) :
    (↾fun x => ⟨j, x⟩) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl

end CategoryTheory.Limits.Types
