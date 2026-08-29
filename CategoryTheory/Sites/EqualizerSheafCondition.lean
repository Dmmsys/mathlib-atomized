/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Tactic.ApplyFun

/-!
# The equalizer diagram sheaf condition for a presieve

In `Mathlib/CategoryTheory/Sites/IsSheafFor.lean` it is defined what it means for a presheaf to be a
sheaf *for* a particular presieve. In this file we provide equivalent conditions in terms of
equalizer diagrams.

* In `Equalizer.Presieve.sheaf_condition`, the sheaf condition at a presieve is shown to be
  equivalent to that of https://stacks.math.columbia.edu/tag/00VM (and combined with
  `isSheaf_pretopology`, this shows the notions of `IsSheaf` are exactly equivalent.)

* In `Equalizer.Sieve.equalizer_sheaf_condition`, the sheaf condition at a sieve is shown to be
  equivalent to that of Equation (3) p. 122 in Maclane-Moerdijk [MM92].

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)

-/

@[expose] public section


universe t w v u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Equalizer

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type (max v u)) {X : C} (R : Presieve X)
  (S : Sieve X)

noncomputable section

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of the Stacks entry.
-/
@[stacks 00VM "This is the middle object of the fork diagram there."]
/--
Definition of `FirstObj` / `FirstObj` 的定义

English:
abbreviation FirstObj
  signature: : Type (max v u)
  body: ∏ᶜ fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)

中文:
缩写 FirstObj
  签名: : 类型 (最大值 v u)
  定义体: ∏ᶜ fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)

Depends on / 依赖: P.obj
-/
abbrev FirstObj : Type (max v u) :=
  ∏ᶜ fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)

variable {P R}

@[ext]
/--
lemma `FirstObj.ext` / 引理 `FirstObj.ext`

English:
lemma FirstObj.ext
  statement: (z₁ z₂ : FirstObj P R) (h : forall (Y : C) (f : Y ⟶ X)
  proof: by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, f, hf⟩⟩
  exact h Y f hf

中文:
引理 FirstObj.ext
  结论: (z₁ z₂ : FirstObj P R) (h : 对任意 (Y : C) (f : Y ⟶ X)
  证明: by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, f, hf⟩⟩
  exact h Y f hf

Depends on / 依赖: Limits, Limits.Types.limit_ext, limit_ext
-/
lemma FirstObj.ext (z₁ z₂ : FirstObj P R) (h : forall (Y : C) (f : Y ⟶ X)
    (hf : R f), (Pi.π _ ⟨Y, f, hf⟩ : FirstObj P R ⟶ _) z₁ =
      (Pi.π _ ⟨Y, f, hf⟩ : FirstObj P R ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, f, hf⟩⟩
  exact h Y f hf

variable (P R)

set_option backward.isDefEq.respectTransparency.types false in
/-- Show that `FirstObj` is isomorphic to `FamilyOfElements`. -/
@[simps]
/--
Definition of `firstObjEqFamily` / `firstObjEqFamily` 的定义

English:
definition firstObjEqFamily
  signature: : FirstObj P R ≅ (R.FamilyOfElements P) where
  body: ↾fun t _ _ hf =>
    Pi.π (fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)) ⟨_, _, hf⟩ t
  inv := Pi.lift fun f => ↾fun x => x _ f.2.2

中文:
定义 firstObjEqFamily
  签名: : FirstObj P R ≅ (R.FamilyOfElements P) where
  定义体: ↾fun t _ _ hf =>
    Pi.π (fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)) ⟨_, _, hf⟩ t
  inv := Pi.lift fun f => ↾fun x => x _ f.2.2
-/
def firstObjEqFamily : FirstObj P R ≅ (R.FamilyOfElements P) where
  hom := ↾fun t _ _ hf =>
    Pi.π (fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)) ⟨_, _, hf⟩ t
  inv := Pi.lift fun f => ↾fun x => x _ f.2.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FirstObj P (⊥ : Presieve X))
  body: (firstObjEqFamily P _).toEquiv.inhabited

中文:
实例 :
  签名: 可居 (FirstObj P (⊥ : Presieve X))
  定义体: (firstObjEqFamily P _).toEquiv.inhabited

Depends on / 依赖: firstObjEqFamily, inhabited, toEquiv, toEquiv.inhabited
-/
instance : Inhabited (FirstObj P (⊥ : Presieve X)) :=
  (firstObjEqFamily P _).toEquiv.inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FirstObj P ((⊥ : Sieve X) : Presieve X))
  body: inferInstanceAs Inhabited (FirstObj P (⊥ : Presieve X))

中文:
实例 :
  签名: 可居 (FirstObj P ((⊥ : 筛 X) : Presieve X))
  定义体: inferInstanceAs Inhabited (FirstObj P (⊥ : Presieve X))

Depends on / 依赖: FirstObj, Inhabited, Presieve
-/
instance : Inhabited (FirstObj P ((⊥ : Sieve X) : Presieve X)) :=
inferInstanceAs Inhabited (FirstObj P (⊥ : Presieve X))

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of the Stacks entry.
-/
@[stacks 00VM "This is the left morphism of the fork diagram there."]
/--
Definition of `forkMap` / `forkMap` 的定义

English:
definition forkMap
  signature: : P.obj (op X) ⟶ FirstObj P R
  body: Pi.lift fun f => P.map f.2.1.op

中文:
定义 forkMap
  签名: : P.obj (op X) ⟶ FirstObj P R
  定义体: Pi.lift fun f => P.map f.2.1.op

Depends on / 依赖: P.map, Pi.lift
-/
def forkMap : P.obj (op X) ⟶ FirstObj P R :=
  Pi.lift fun f => P.map f.2.1.op

/-!
This section establishes the equivalence between the sheaf condition of Equation (3) [MM92] and
the definition of `IsSheafFor`.
-/


namespace Sieve

/--
Definition of `SecondObj` / `SecondObj` 的定义

English:
abbreviation SecondObj
  signature: : Type (max v u)
  body: ∏ᶜ fun f : Σ (Y Z : _) (_ : Z ⟶ Y), { f' : Y ⟶ X // S f' } => P.obj (op f.2.1)

中文:
缩写 SecondObj
  签名: : 类型 (最大值 v u)
  定义体: ∏ᶜ fun f : Σ (Y Z : _) (_ : Z ⟶ Y), { f' : Y ⟶ X // S f' } => P.obj (op f.2.1)

Depends on / 依赖: P.obj
-/
abbrev SecondObj : Type (max v u) :=
  ∏ᶜ fun f : Σ (Y Z : _) (_ : Z ⟶ Y), { f' : Y ⟶ X // S f' } => P.obj (op f.2.1)

variable {P S}

@[ext]
/--
lemma `SecondObj.ext` / 引理 `SecondObj.ext`

English:
lemma SecondObj.ext
  statement: (z₁ z₂ : SecondObj P S) (h : forall (Y Z : C) (g : Z ⟶ Y) (f : Y ⟶ X)
  proof: by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, Z, g, f, hf⟩⟩
  apply h

中文:
引理 SecondObj.ext
  结论: (z₁ z₂ : SecondObj P S) (h : 对任意 (Y Z : C) (g : Z ⟶ Y) (f : Y ⟶ X)
  证明: by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, Z, g, f, hf⟩⟩
  apply h

Depends on / 依赖: Limits, Limits.Types.limit_ext, limit_ext
-/
lemma SecondObj.ext (z₁ z₂ : SecondObj P S) (h : forall (Y Z : C) (g : Z ⟶ Y) (f : Y ⟶ X)
    (hf : S.arrows f), (Pi.π _ ⟨Y, Z, g, f, hf⟩ : SecondObj P S ⟶ _) z₁ =
      (Pi.π _ ⟨Y, Z, g, f, hf⟩ : SecondObj P S ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, Z, g, f, hf⟩⟩
  apply h

variable (P S)

/--
Definition of `firstMap` / `firstMap` 的定义

English:
definition firstMap
  signature: : FirstObj P (S : Presieve X) ⟶ SecondObj P S
  body: Pi.lift fun fg =>
    Pi.π _ (⟨_, _, S.downward_closed fg.2.2.2.2 fg.2.2.1⟩ : Σ Y, { f : Y ⟶ X // S f })

中文:
定义 firstMap
  签名: : FirstObj P (S : Presieve X) ⟶ SecondObj P S
  定义体: Pi.lift fun fg =>
    Pi.π _ (⟨_, _, S.downward_closed fg.2.2.2.2 fg.2.2.1⟩ : Σ Y, { f : Y ⟶ X // S f })

Depends on / 依赖: Pi.lift, S.downward_closed, downward_closed
-/
def firstMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg =>
    Pi.π _ (⟨_, _, S.downward_closed fg.2.2.2.2 fg.2.2.1⟩ : Σ Y, { f : Y ⟶ X // S f })

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SecondObj P (⊥ : Sieve X))
  body: ⟨firstMap _ _ default⟩

中文:
实例 :
  签名: 可居 (SecondObj P (⊥ : 筛 X))
  定义体: ⟨firstMap _ _ default⟩

Depends on / 依赖: firstMap
-/
instance : Inhabited (SecondObj P (⊥ : Sieve X)) :=
  ⟨firstMap _ _ default⟩

/--
Definition of `secondMap` / `secondMap` 的定义

English:
definition secondMap
  signature: : FirstObj P (S : Presieve X) ⟶ SecondObj P S
  body: Pi.lift fun fg => Pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map fg.2.2.1.op

中文:
定义 secondMap
  签名: : FirstObj P (S : Presieve X) ⟶ SecondObj P S
  定义体: Pi.lift fun fg => Pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map fg.2.2.1.op

Depends on / 依赖: P.map, Pi.lift
-/
def secondMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg => Pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map fg.2.2.1.op

/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P S
  proof: by
  ext
  simp [firstMap, secondMap, forkMap]

中文:
定理 w
  结论: forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P S
  证明: by
  ext
  simp [firstMap, secondMap, forkMap]

Depends on / 依赖: firstMap, forkMap, secondMap
-/
theorem w : forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P S := by
  ext
  simp [firstMap, secondMap, forkMap]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `compatible_iff` / 定理 `compatible_iff`

English:
theorem compatible_iff
  given: (x : FirstObj P S.arrows)
  proof: by
  rw [Presieve.compatible_iff_sieveCompatible]
  constructor
  · intro t
    apply SecondObj.ext
    intro Y Z g f hf
    simpa [firstMap, secondMap] using t _ g hf
  · intro t Y Z f g hf
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨Y, Z, g, f, hf⟩⟩

中文:
定理 compatible_iff
  条件: (x : FirstObj P S.arrows)
  证明: by
  rw [Presieve.compatible_iff_sieveCompatible]
  constructor
  · intro t
    apply SecondObj.ext
    intro Y Z g f hf
    simpa [firstMap, secondMap] using t _ g hf
  · intro t Y Z f g hf
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨Y, Z, g, f, hf⟩⟩

Depends on / 依赖: Presieve, Presieve.compatible_iff_sieveCompatible, SecondObj, SecondObj.ext, Types.limit_ext_iff, compatible_iff_sieveCompatible, firstMap, limit_ext_iff, secondMap
-/
theorem compatible_iff (x : FirstObj P S.arrows) :
    ((firstObjEqFamily P S.arrows).hom x).Compatible ↔ firstMap P S x = secondMap P S x := by
  rw [Presieve.compatible_iff_sieveCompatible]
  constructor
  · intro t
    apply SecondObj.ext
    intro Y Z g f hf
    simpa [firstMap, secondMap] using t _ g hf
  · intro t Y Z f g hf
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨Y, Z, g, f, hf⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `equalizer_sheaf_condition` / 定理 `equalizer_sheaf_condition`

English:
theorem equalizer_sheaf_condition
  proof: by
  rw [Types.type_equalizer_iff_unique]; rw [← Equiv.forall_congr_right (firstObjEqFamily P (S : Presieve X)).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1, 2]; rw [(firstObjEqFamily P S.arrows).toEquiv_symm_apply]
  simp only [Iso.inv_hom_id_apply]
  apply forall₂_congr
 

中文:
定理 equalizer_sheaf_condition
  证明: by
  rw [Types.type_equalizer_iff_unique]; rw [← Equiv.forall_congr_right (firstObjEqFamily P (S : Presieve X)).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1, 2]; rw [(firstObjEqFamily P S.arrows).toEquiv_symm_apply]
  simp only [Iso.inv_hom_id_apply]
  apply forall₂_congr
 

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.forall_congr_right, Iso.inv_hom_id_apply, Iso.toEquiv, Presieve, S.arrows, Types.type_equalizer_iff_unique, arrows, compatible_iff, eq_symm_apply, existsUnique_congr, firstObjEqFamily, forall_congr_right, forkMap, inv_hom_id_apply, simp_rw, toEquiv, toEquiv.symm, toEquiv_symm_apply, type_equalizer_iff_unique
-/
theorem equalizer_sheaf_condition :
    Presieve.IsSheafFor P (S : Presieve X) ↔ Nonempty (IsLimit (Fork.ofι _ (w P S))) := by
  rw [Types.type_equalizer_iff_unique]; rw [← Equiv.forall_congr_right (firstObjEqFamily P (S : Presieve X)).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1, 2]; rw [(firstObjEqFamily P S.arrows).toEquiv_symm_apply]
  simp only [Iso.inv_hom_id_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    ext Y f hf
    simpa [Iso.toEquiv, forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [Iso.toEquiv, forkMap]

end Sieve

/-!
This section establishes the equivalence between the sheaf condition of
https://stacks.math.columbia.edu/tag/00VM and the definition of `isSheafFor`.
-/


namespace Presieve

variable [R.HasPairwisePullbacks]

/--
The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp, stacks 00VM "This is the rightmost object of the fork diagram there."]
/--
Definition of `SecondObj` / `SecondObj` 的定义

English:
definition SecondObj
  signature: : Type (max v u)
  body: ∏ᶜ fun fg : (Σ Y, { f : Y ⟶ X // R f }) × Σ Z, { g : Z ⟶ X // R g } =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

中文:
定义 SecondObj
  签名: : 类型 (最大值 v u)
  定义体: ∏ᶜ fun fg : (Σ Y, { f : Y ⟶ X // R f }) × Σ Z, { g : Z ⟶ X // R g } =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

Depends on / 依赖: HasPairwisePullbacks, P.obj, Presieve, Presieve.HasPairwisePullbacks.has_pullbacks, has_pullbacks, pullback
-/
def SecondObj : Type (max v u) :=
  ∏ᶜ fun fg : (Σ Y, { f : Y ⟶ X // R f }) × Σ Z, { g : Z ⟶ X // R g } =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "This is the map `pr₀*` there."]
/--
Definition of `firstMap` / `firstMap` 的定义

English:
definition firstMap
  signature: : FirstObj P R ⟶ SecondObj P R
  body: Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.fst _ _).op

中文:
定义 firstMap
  签名: : FirstObj P R ⟶ SecondObj P R
  定义体: Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.fst _ _).op

Depends on / 依赖: HasPairwisePullbacks, P.map, Pi.lift, Presieve, Presieve.HasPairwisePullbacks.has_pullbacks, has_pullbacks, pullback, pullback.fst
-/
def firstMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullbacks
  signature: C] : Inhabited (SecondObj P (⊥ : Presieve X))
  body: ⟨firstMap _ _ default⟩

中文:
实例 [有Pullbacks
  签名: C] : 可居 (SecondObj P (⊥ : Presieve X))
  定义体: ⟨firstMap _ _ default⟩

Depends on / 依赖: firstMap
-/
instance [HasPullbacks C] : Inhabited (SecondObj P (⊥ : Presieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `pr₁*` of the Stacks entry. -/
@[stacks 00VM "This is the map `pr₁*` there."]
/--
Definition of `secondMap` / `secondMap` 的定义

English:
definition secondMap
  signature: : FirstObj P R ⟶ SecondObj P R
  body: Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.snd _ _).op

中文:
定义 secondMap
  签名: : FirstObj P R ⟶ SecondObj P R
  定义体: Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.snd _ _).op

Depends on / 依赖: HasPairwisePullbacks, P.map, Pi.lift, Presieve, Presieve.HasPairwisePullbacks.has_pullbacks, has_pullbacks, pullback, pullback.snd
-/
def secondMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R
  proof: by
  dsimp
  ext fg
  simp only [firstMap, secondMap, forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
  rw [← P.map_comp]; rw [← op_comp]; rw [pullback.condition]
  simp

中文:
定理 w
  结论: forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R
  证明: by
  dsimp
  ext fg
  simp only [firstMap, secondMap, forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
  rw [← P.map_comp]; rw [← op_comp]; rw [pullback.condition]
  simp

Depends on / 依赖: Fan.mk_, HasPairwisePullbacks, P.map_comp, Presieve, Presieve.HasPairwisePullbacks.has_pullbacks, condition, firstMap, forkMap, has_pullbacks, limit.lift_, map_comp, op_comp, pullback, pullback.condition, secondMap
-/
theorem w : forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R := by
  dsimp
  ext fg
  simp only [firstMap, secondMap, forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
  rw [← P.map_comp]; rw [← op_comp]; rw [pullback.condition]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `compatible_iff` / 定理 `compatible_iff`

English:
theorem compatible_iff
  given: (x : FirstObj P R)
  proof: by
  rw [Presieve.pullbackCompatible_iff]
  constructor
  · intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap, secondMap] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨⟨Y, f, hf⟩, Z, g

中文:
定理 compatible_iff
  条件: (x : FirstObj P R)
  证明: by
  rw [Presieve.pullbackCompatible_iff]
  constructor
  · intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap, secondMap] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨⟨Y, f, hf⟩, Z, g

Depends on / 依赖: Limits, Limits.Types.limit_ext, Presieve, Presieve.pullbackCompatible_iff, Types.limit_ext_iff, firstMap, limit_ext, limit_ext_iff, pullbackCompatible_iff, secondMap
-/
theorem compatible_iff (x : FirstObj P R) :
    ((firstObjEqFamily P R).hom x).Compatible ↔ firstMap P R x = secondMap P R x := by
  rw [Presieve.pullbackCompatible_iff]
  constructor
  · intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap, secondMap] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨⟨Y, f, hf⟩, Z, g, hg⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer. -/
@[stacks 00VM]
/--
theorem `sheaf_condition` / 定理 `sheaf_condition`

English:
theorem sheaf_condition
  statement: R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R)))
  proof: by
  rw [Types.type_equalizer_iff_unique]; rw [← Equiv.forall_congr_right (firstObjEqFamily P R).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1]; rw [← Iso.toEquiv_apply]
  simp_rw [Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t

中文:
定理 sheaf_condition
  结论: R.IsSheafFor P ↔ 非空 (是极限 (叉.ofι _ (w P R)))
  证明: by
  rw [Types.type_equalizer_iff_unique]; rw [← Equiv.forall_congr_right (firstObjEqFamily P R).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1]; rw [← Iso.toEquiv_apply]
  simp_rw [Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.eq_symm_apply, Equiv.forall_congr_right, Iso.toEquiv, Iso.toEquiv_apply, Types.type_equalizer_iff_unique, apply_symm_apply, compatible_iff, eq_symm_apply, existsUnique_congr, firstObjEqFamily, forall_congr_right, forkMap, simp_rw, toEquiv, toEquiv.symm, toEquiv_apply, type_equalizer_iff_unique
-/
theorem sheaf_condition : R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R))) := by
  rw [Types.type_equalizer_iff_unique]; rw [← Equiv.forall_congr_right (firstObjEqFamily P R).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1]; rw [← Iso.toEquiv_apply]
  simp_rw [Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [Iso.toEquiv, forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [Iso.toEquiv, forkMap]

namespace Arrows

variable (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Presieve X) (S : Sieve X)

open Presieve

variable {B : C} {I : Type t} [Small.{w} I] (X : I -> C) (π : (i : I) -> X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks]

/--
The middle object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.FirstObj P (ofArrows X π)` arises if the family of
arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
@[stacks 00VM "The middle object of the fork diagram there."]
/--
Definition of `FirstObj` / `FirstObj` 的定义

English:
abbreviation FirstObj
  signature: : Type w
  body: ∏ᶜ (fun i => P.obj (op (X i)))

@[ext]

中文:
缩写 FirstObj
  签名: : 类型 w
  定义体: ∏ᶜ (fun i => P.obj (op (X i)))

@[ext]

Depends on / 依赖: P.obj
-/
abbrev FirstObj : Type w := ∏ᶜ (fun i => P.obj (op (X i)))

@[ext]
/--
lemma `FirstObj.ext` / 引理 `FirstObj.ext`

English:
lemma FirstObj.ext
  statement: (z₁ z₂ : FirstObj P X) (h : forall i, (Pi.π _ i : FirstObj P X ⟶ _) z₁ =
  proof: by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

中文:
引理 FirstObj.ext
  结论: (z₁ z₂ : FirstObj P X) (h : 对任意 i, (依赖函数类型.π _ i : FirstObj P X ⟶ _) z₁ =
  证明: by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i
-/
lemma FirstObj.ext (z₁ z₂ : FirstObj P X) (h : forall i, (Pi.π _ i : FirstObj P X ⟶ _) z₁ =
    (Pi.π _ i : FirstObj P X ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
The rightmost object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.Presieve.SecondObj P (ofArrows X π)` arises if the
family of arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
@[stacks 00VM "The rightmost object of the fork diagram there."]
/--
Definition of `SecondObj` / `SecondObj` 的定义

English:
abbreviation SecondObj
  signature: : Type w
  body: ∏ᶜ (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2))))

@[ext]

中文:
缩写 SecondObj
  签名: : 类型 w
  定义体: ∏ᶜ (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2))))

@[ext]

Depends on / 依赖: P.obj, pullback
-/
abbrev SecondObj : Type w :=
  ∏ᶜ (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2))))

@[ext]
/--
lemma `SecondObj.ext` / 引理 `SecondObj.ext`

English:
lemma SecondObj.ext
  statement: (z₁ z₂ : SecondObj P X π) (h : forall ij, (Pi.π _ ij : SecondObj P X π ⟶ _) z₁ =
  proof: by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

中文:
引理 SecondObj.ext
  结论: (z₁ z₂ : SecondObj P X π) (h : 对任意 ij, (依赖函数类型.π _ ij : SecondObj P X π ⟶ _) z₁ =
  证明: by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i
-/
lemma SecondObj.ext (z₁ z₂ : SecondObj P X π) (h : forall ij, (Pi.π _ ij : SecondObj P X π ⟶ _) z₁ =
    (Pi.π _ ij : SecondObj P X π ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
Definition of `forkMap` / `forkMap` 的定义

English:
definition forkMap
  signature: : P.obj (op B) ⟶ FirstObj P X
  body: Pi.lift (fun i => P.map (π i).op)

中文:
定义 forkMap
  签名: : P.obj (op B) ⟶ FirstObj P X
  定义体: Pi.lift (fun i => P.map (π i).op)

Depends on / 依赖: P.map, Pi.lift
-/
def forkMap : P.obj (op B) ⟶ FirstObj P X := Pi.lift (fun i => P.map (π i).op)

/--
Definition of `firstMap` / `firstMap` 的定义

English:
definition firstMap
  signature: : FirstObj P X ⟶ SecondObj P X π
  body: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

中文:
定义 firstMap
  签名: : FirstObj P X ⟶ SecondObj P X π
  定义体: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

Depends on / 依赖: P.map, Pi.lift, pullback, pullback.fst
-/
def firstMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/--
Definition of `secondMap` / `secondMap` 的定义

English:
definition secondMap
  signature: : FirstObj P X ⟶ SecondObj P X π
  body: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

中文:
定义 secondMap
  签名: : FirstObj P X ⟶ SecondObj P X π
  定义体: Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

Depends on / 依赖: P.map, Pi.lift, pullback, pullback.snd
-/
def secondMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π
  proof: by
  ext x ij
  dsimp [forkMap, firstMap, secondMap]
  simp [← comp_apply, -types_comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition]

中文:
定理 w
  结论: forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π
  证明: by
  ext x ij
  dsimp [forkMap, firstMap, secondMap]
  simp [← comp_apply, -types_comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition]

Depends on / 依赖: Functor, Functor.map_comp, comp_apply, condition, firstMap, forkMap, map_comp, op_comp, pullback, pullback.condition, secondMap, types_comp_apply
-/
theorem w : forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π := by
  ext x ij
  dsimp [forkMap, firstMap, secondMap]
  simp [← comp_apply, -types_comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition]

/--
theorem `compatible_iff` / 定理 `compatible_iff`

English:
theorem compatible_iff
  statement: {I : Type w} (X : I -> C) (π : (i : I) -> X i ⟶ B)
  proof: by
  rw [Arrows.pullbackCompatible_iff]
  constructor
  · intro t
    ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · intro t i j
    apply_fun Pi.π (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

中文:
定理 compatible_iff
  结论: {I : 类型 w} (X : I -> C) (π : (i : I) -> X i ⟶ B)
  证明: by
  rw [Arrows.pullbackCompatible_iff]
  constructor
  · intro t
    ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · intro t i j
    apply_fun Pi.π (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

Depends on / 依赖: Arrows, Arrows.pullbackCompatible_iff, P.obj, apply_fun, firstMap, pullback, pullbackCompatible_iff, secondMap
-/
theorem compatible_iff {I : Type w} (X : I -> C) (π : (i : I) -> X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks] (x : FirstObj P X) :
    (Arrows.Compatible P π ((Types.productIso _).hom x)) ↔
      firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  constructor
  · intro t
    ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · intro t i j
    apply_fun Pi.π (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

/--
lemma `compatible_iff_of_small` / 引理 `compatible_iff_of_small`

English:
lemma compatible_iff_of_small
  given: (x : FirstObj P X)
  proof: by
  rw [Arrows.pullbackCompatible_iff]
  refine ⟨fun t => ?_, fun t i j => ?_⟩
  · ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · apply_fun Pi.π (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

中文:
引理 compatible_iff_of_small
  条件: (x : FirstObj P X)
  证明: by
  rw [Arrows.pullbackCompatible_iff]
  refine ⟨fun t => ?_, fun t i j => ?_⟩
  · ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · apply_fun Pi.π (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

Depends on / 依赖: Arrows, Arrows.pullbackCompatible_iff, P.obj, apply_fun, firstMap, pullback, pullbackCompatible_iff, secondMap
-/
lemma compatible_iff_of_small (x : FirstObj P X) :
    (Arrows.Compatible P π ((equivShrink _).symm ((Types.Small.productIso _).hom x))) ↔
      firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  refine ⟨fun t => ?_, fun t i j => ?_⟩
  · ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · apply_fun Pi.π (fun (ij : I × I) => P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

set_option backward.isDefEq.respectTransparency.types false in
/-- `P` is a sheaf for `Presieve.ofArrows X π`, iff the fork given by `w` is an equalizer. -/
@[stacks 00VM]
/--
theorem `sheaf_condition` / 定理 `sheaf_condition`

English:
theorem sheaf_condition
  statement: (Presieve.ofArrows X π).IsSheafFor P ↔
  proof: by
  rw [Types.type_equalizer_iff_unique]; rw [isSheafFor_arrows_iff]
  simp only [FirstObj]
  rw [← Equiv.forall_congr_right ((equivShrink _).trans (Types.Small.productIso _).toEquiv.symm)]
  simp_rw [← compatible_iff_of_small, ← Iso.toEquiv_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equ

中文:
定理 sheaf_condition
  结论: (Presieve.ofArrows X π).IsSheafFor P ↔
  证明: by
  rw [Types.type_equalizer_iff_unique]; rw [isSheafFor_arrows_iff]
  simp only [FirstObj]
  rw [← Equiv.forall_congr_right ((equivShrink _).trans (Types.Small.productIso _).toEquiv.symm)]
  simp_rw [← compatible_iff_of_small, ← Iso.toEquiv_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equ

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.eq_symm_apply, Equiv.forall_congr_right, Equiv.symm_apply_apply, Equiv.symm_apply_eq, Equiv.trans_apply, FirstObj, Iso.toEquiv, Iso.toEquiv_apply, Types.Small.productIso, Types.type_equalizer_iff_unique, apply_symm_apply, compatible_iff_of_small, eq_symm_apply, equivShrink, existsUnique_congr, forall_congr_right, forkMap, isSheafFor_arrows_iff, productIso
-/
theorem sheaf_condition : (Presieve.ofArrows X π).IsSheafFor P ↔
    Nonempty (IsLimit (Fork.ofι (forkMap P X π) (w P X π))) := by
  rw [Types.type_equalizer_iff_unique]; rw [isSheafFor_arrows_iff]
  simp only [FirstObj]
  rw [← Equiv.forall_congr_right ((equivShrink _).trans (Types.Small.productIso _).toEquiv.symm)]
  simp_rw [← compatible_iff_of_small, ← Iso.toEquiv_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply]; rw [← Equiv.symm_apply_eq]
  constructor
  · intro q
    funext i
    simpa [Iso.toEquiv, forkMap] using q i
  · intro q i
    rw [← q]
    simp [Iso.toEquiv, forkMap]

end Arrows

/--
lemma `isSheafFor_singleton_iff` / 引理 `isSheafFor_singleton_iff`

English:
lemma isSheafFor_singleton_iff
  statement: {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
  proof: by
  have h (x : F.obj (op X)) : (forall {Z : C} (p₁ p₂ : Z ⟶ X),
      p₁ ≫ f = p₂ ≫ f -> F.map p₁.op x = F.map p₂.op x) ↔ F.map c.fst.op x = F.map c.snd.op x := by
    refine ⟨fun H => H _ _ c.condition, fun H Z p₁ p₂ h => ?_⟩
    rw [← PullbackCone.IsLimit.lift_fst hc _ _ h]; rw [op_comp]; rw [Fu

中文:
引理 isSheafFor_singleton_iff
  结论: {F : Cᵒᵖ ⥤ 类型} {X Y : C} {f : X ⟶ Y}
  证明: by
  have h (x : F.obj (op X)) : (forall {Z : C} (p₁ p₂ : Z ⟶ X),
      p₁ ≫ f = p₂ ≫ f -> F.map p₁.op x = F.map p₂.op x) ↔ F.map c.fst.op x = F.map c.snd.op x := by
    refine ⟨fun H => H _ _ c.condition, fun H Z p₁ p₂ h => ?_⟩
    rw [← PullbackCone.IsLimit.lift_fst hc _ _ h]; rw [op_comp]; rw [Fu

Depends on / 依赖: F.map, c.fst.op, c.snd.op
-/
lemma isSheafFor_singleton_iff {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    (c : PullbackCone f f) (hc : IsLimit c) :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map c.fst.op) (g := F.map c.snd.op)
          (by simp [← Functor.map_comp, ← op_comp, c.condition]))) := by
  have h (x : F.obj (op X)) : (forall {Z : C} (p₁ p₂ : Z ⟶ X),
      p₁ ≫ f = p₂ ≫ f -> F.map p₁.op x = F.map p₂.op x) ↔ F.map c.fst.op x = F.map c.snd.op x := by
    refine ⟨fun H => H _ _ c.condition, fun H Z p₁ p₂ h => ?_⟩
    rw [← PullbackCone.IsLimit.lift_fst hc _ _ h]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply]; rw [H]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  rw [Types.type_equalizer_iff_unique]; rw [Presieve.isSheafFor_singleton]
  simp_rw [h]

/--
lemma `isSheafFor_singleton_iff_of_hasPullback` / 引理 `isSheafFor_singleton_iff_of_hasPullback`

English:
lemma isSheafFor_singleton_iff_of_hasPullback
  statement: {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
  proof: isSheafFor_singleton_iff (pullback.cone f f) (pullback.isLimit f f)

中文:
引理 isSheafFor_singleton_iff_of_hasPullback
  结论: {F : Cᵒᵖ ⥤ 类型} {X Y : C} {f : X ⟶ Y}
  证明: isSheafFor_singleton_iff (pullback.cone f f) (pullback.isLimit f f)

Depends on / 依赖: F.map, pullback, pullback.fst
-/
lemma isSheafFor_singleton_iff_of_hasPullback {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    [HasPullback f f] :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map (pullback.fst f f).op)
          (g := F.map (pullback.snd f f).op)
          (by simp [← Functor.map_comp, ← op_comp, pullback.condition]))) :=
  isSheafFor_singleton_iff (pullback.cone f f) (pullback.isLimit f f)

end Presieve

end

end Equalizer

end CategoryTheory
