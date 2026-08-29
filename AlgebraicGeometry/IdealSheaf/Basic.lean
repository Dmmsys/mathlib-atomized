/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.DepRewrite

/-!
# Ideal sheaves on schemes

We define ideal sheaves of schemes and provide various constructors for it.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData`: A structure that contains the data to uniquely define
  an ideal sheaf, consisting of
  1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
  2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`:
  The largest ideal sheaf contained in a family of ideals.
* `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`:
  Over affine schemes, ideal sheaves are in bijection with ideals of the global sections.
* `AlgebraicGeometry.Scheme.IdealSheafData.support`: The support of an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`: The vanishing ideal of a set.
* `AlgebraicGeometry.Scheme.Hom.ker`: The kernel of a morphism.

## Main results
* `AlgebraicGeometry.Scheme.IdealSheafData.gc`:
  `support` and `vanishingIdeal` forms a Galois connection.
* `AlgebraicGeometry.Scheme.Hom.support_ker`: The support of a kernel of a quasi-compact morphism
  is the closure of the range.

## Implementation detail

Ideal sheaves are not yet defined in this file as actual subsheaves of `𝒪ₓ`.
Instead, for the ease of development and application,
we define the structure `IdealSheafData` containing all necessary data to uniquely define an
ideal sheaf. This should be refactored as a constructor for ideal sheaves once they are introduced
into mathlib.

-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/--
Definition of `IdealSheafData` / `IdealSheafData` 的定义

English:
structure IdealSheafData
  parameters: (X : Scheme.{u})
  axioms and operations (4):
    - ideal : forall U : X.affineOpens, Ideal Γ(X, U)
    - map_ideal_basicOpen : forall (U : X.affineOpens) (f : Γ(X, U)), (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom = ideal (X.affineBasicOpen f)
    - supportSet : Set X  [default: ⋂ U, X.zeroLocus (U := U.1) (ideal U)]
    - supportSet_eq_iInter_zeroLocus : supportSet = ⋂ U, X.zeroLocus (U := U.1) (ideal U)  [default: by rfl]

中文:
结构 IdealSheafData
  参数: (X : 概形.{u})
  公理与运算 (4 个):
    - ideal : 对任意 U : X.affineOpens, 理想 Γ(X, U)
    - map_ideal_basicOpen : 对任意 (U : X.affineOpens) (f : Γ(X, U)), (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom = ideal (X.affineBasicOpen f)
    - supportSet : 集合 X  [默认: ⋂ U, X.zeroLocus (U := U.1) (ideal U)]
    - supportSet_eq_iInter_zeroLocus : supportSet = ⋂ U, X.zeroLocus (U := U.1) (ideal U)  [默认: by rfl]

Depends on / 依赖: X.zeroLocus, zeroLocus
-/
structure IdealSheafData (X : Scheme.{u}) : Type u where
  /-- The component of an ideal sheaf at an affine open. -/
  ideal : forall U : X.affineOpens, Ideal Γ(X, U)
  /-- Also see `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` -/
  map_ideal_basicOpen : forall (U : X.affineOpens) (f : Γ(X, U)),
    (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
      ideal (X.affineBasicOpen f)
  /-- The support of an ideal sheaf. Use `IdealSheafData.support` instead for most occasions. -/
  supportSet : Set X := ⋂ U, X.zeroLocus (U := U.1) (ideal U)
  supportSet_eq_iInter_zeroLocus : supportSet = ⋂ U, X.zeroLocus (U := U.1) (ideal U) := by rfl

namespace IdealSheafData

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {I J : X.IdealSheafData} (h : I.ideal = J.ideal)
  statement: I = J
  proof: by
  obtain ⟨i, _, s, hs⟩ := I
  obtain ⟨j, _, t, ht⟩ := J
  subst h
  congr
  rw [hs]; rw [ht]

中文:
引理 ext
  条件: {I J : X.IdealSheafData} (h : I.ideal = J.ideal)
  结论: I = J
  证明: by
  obtain ⟨i, _, s, hs⟩ := I
  obtain ⟨j, _, t, ht⟩ := J
  subst h
  congr
  rw [hs]; rw [ht]
-/
protected lemma ext {I J : X.IdealSheafData} (h : I.ideal = J.ideal) : I = J := by
  obtain ⟨i, _, s, hs⟩ := I
  obtain ⟨j, _, t, ht⟩ := J
  subst h
  congr
  rw [hs]; rw [ht]

section Order

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (IdealSheafData X)
  body: PartialOrder.lift ideal fun _ _ => IdealSheafData.ext

中文:
实例 :
  签名: 偏序 (IdealSheafData X)
  定义体: PartialOrder.lift ideal fun _ _ => IdealSheafData.ext

Depends on / 依赖: IdealSheafData, IdealSheafData.ext, PartialOrder, PartialOrder.lift
-/
instance : PartialOrder (IdealSheafData X) := PartialOrder.lift ideal fun _ _ => IdealSheafData.ext

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {I J : IdealSheafData X}
  statement: I <= J ↔ forall U, I.ideal U <= J.ideal U
  proof: .rfl

中文:
引理 le_def
  条件: {I J : IdealSheafData X}
  结论: I <= J ↔ 对任意 U, I.ideal U <= J.ideal U
  证明: .rfl
-/
lemma le_def {I J : IdealSheafData X} : I <= J ↔ forall U, I.ideal U <= J.ideal U := .rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeSup (IdealSheafData X)
  body: { ideal := sSup (ideal '' s),
    map_ideal_basicOpen := by
      have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
        conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
        rfl
      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
  isLUB_sS

中文:
实例 :
  签名: 余mpleteSemilatticeSup (IdealSheafData X)
  定义体: { ideal := sSup (ideal '' s),
    map_ideal_basicOpen := by
      have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
        conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
        rfl
      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
  isLUB_sS

Depends on / 依赖: Ideal.map_iSup, Set.range_comp, Subtype, Subtype.range_val, conv_lhs, iSup_apply, implies_true, isLUB_sSup, le_def, map_iSup, map_ideal_basicOpen, of_image, range_comp, range_val
-/
instance : CompleteSemilatticeSup (IdealSheafData X) where
  sSup s :=
  { ideal := sSup (ideal '' s),
    map_ideal_basicOpen := by
      have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
        conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
        rfl
      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
  isLUB_sSup _ := .of_image (f := ideal) le_def (isLUB_sSup _)

/--
Definition of `ofIdeals` / `ofIdeals` 的定义

English:
definition ofIdeals
  signature: (I : forall U : X.affineOpens, Ideal Γ(X, U))
  body: sSup { J : IdealSheafData X | J.ideal <= I }

中文:
定义 ofIdeals
  签名: (I : 对任意 U : X.affineOpens, 理想 Γ(X, U))
  定义体: sSup { J : IdealSheafData X | J.ideal <= I }

Depends on / 依赖: IdealSheafData, J.ideal
-/
def ofIdeals (I : forall U : X.affineOpens, Ideal Γ(X, U)) : IdealSheafData X :=
  sSup { J : IdealSheafData X | J.ideal <= I }

/--
lemma `ideal_ofIdeals_le` / 引理 `ideal_ofIdeals_le`

English:
lemma ideal_ofIdeals_le
  given: (I : forall U : X.affineOpens, Ideal Γ(X, U))
  proof: sSup_le (Set.forall_mem_image.mpr fun _ => id)

中文:
引理 ideal_ofIdeals_le
  条件: (I : 对任意 U : X.affineOpens, 理想 Γ(X, U))
  证明: sSup_le (Set.forall_mem_image.mpr fun _ => id)

Depends on / 依赖: Set.forall_mem_image.mpr, forall_mem_image, sSup_le
-/
lemma ideal_ofIdeals_le (I : forall U : X.affineOpens, Ideal Γ(X, U)) :
    (ofIdeals I).ideal <= I :=
  sSup_le (Set.forall_mem_image.mpr fun _ => id)

/--
Definition of `gci` / `gci` 的定义

English:
definition gci
  signature: : GaloisCoinsertion ideal (ofIdeals (X := X)) where
  body: { ideal := I
    map_ideal_basicOpen U f :=
      (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f }
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ => id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))

中文:
定义 gci
  签名: : Galois余嵌入 ideal (ofIdeals (X := X)) where
  定义体: { ideal := I
    map_ideal_basicOpen U f :=
      (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f }
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ => id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))
-/
protected def gci : GaloisCoinsertion ideal (ofIdeals (X := X)) where
  choice I hI :=
  { ideal := I
    map_ideal_basicOpen U f :=
      (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f }
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ => id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))

/--
lemma `strictMono_ideal` / 引理 `strictMono_ideal`

English:
lemma strictMono_ideal
  statement: StrictMono (ideal (X := X))
  proof: IdealSheafData.gci.strictMono_l

中文:
引理 strictMono_ideal
  结论: 严格递增 (ideal (X := X))
  证明: IdealSheafData.gci.strictMono_l

Depends on / 依赖: IdealSheafData, IdealSheafData.gci.strictMono_l, strictMono_l
-/
lemma strictMono_ideal : StrictMono (ideal (X := X)) := IdealSheafData.gci.strictMono_l
/--
lemma `ideal_mono` / 引理 `ideal_mono`

English:
lemma ideal_mono
  statement: Monotone (ideal (X := X))
  proof: strictMono_ideal.monotone

中文:
引理 ideal_mono
  结论: 递增 (ideal (X := X))
  证明: strictMono_ideal.monotone

Depends on / 依赖: monotone, strictMono_ideal, strictMono_ideal.monotone
-/
lemma ideal_mono : Monotone (ideal (X := X)) := strictMono_ideal.monotone
/--
lemma `ofIdeals_mono` / 引理 `ofIdeals_mono`

English:
lemma ofIdeals_mono
  statement: Monotone (ofIdeals (X := X))
  proof: IdealSheafData.gci.gc.monotone_u

中文:
引理 ofIdeals_mono
  结论: 递增 (ofIdeals (X := X))
  证明: IdealSheafData.gci.gc.monotone_u

Depends on / 依赖: IdealSheafData, IdealSheafData.gci.gc.monotone_u, monotone_u
-/
lemma ofIdeals_mono : Monotone (ofIdeals (X := X)) := IdealSheafData.gci.gc.monotone_u
/--
lemma `ofIdeals_ideal` / 引理 `ofIdeals_ideal`

English:
lemma ofIdeals_ideal
  given: (I : IdealSheafData X)
  statement: ofIdeals I.ideal = I
  proof: IdealSheafData.gci.u_l_eq _

中文:
引理 ofIdeals_ideal
  条件: (I : IdealSheafData X)
  结论: ofIdeals I.ideal = I
  证明: IdealSheafData.gci.u_l_eq _

Depends on / 依赖: IdealSheafData, IdealSheafData.gci.u_l_eq, u_l_eq
-/
lemma ofIdeals_ideal (I : IdealSheafData X) : ofIdeals I.ideal = I := IdealSheafData.gci.u_l_eq _
/--
lemma `le_ofIdeals_iff` / 引理 `le_ofIdeals_iff`

English:
lemma le_ofIdeals_iff
  given: {I : IdealSheafData X} {J}
  statement: I <= ofIdeals J ↔ I.ideal <= J
  proof: IdealSheafData.gci.gc.le_iff_le.symm

中文:
引理 le_ofIdeals_iff
  条件: {I : IdealSheafData X} {J}
  结论: I <= ofIdeals J ↔ I.ideal <= J
  证明: IdealSheafData.gci.gc.le_iff_le.symm

Depends on / 依赖: IdealSheafData, IdealSheafData.gci.gc.le_iff_le.symm, le_iff_le
-/
lemma le_ofIdeals_iff {I : IdealSheafData X} {J} : I <= ofIdeals J ↔ I.ideal <= J :=
  IdealSheafData.gci.gc.le_iff_le.symm

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (IdealSheafData X)
  body: ⊤
  top.map_ideal_basicOpen := by simp [Ideal.map_top]
  top.supportSet := ⊥
  top.supportSet_eq_iInter_zeroLocus := by
    ext x
    simpa using X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  le_top I U := le_top

中文:
实例 :
  签名: 有顶序 (IdealSheafData X)
  定义体: ⊤
  top.map_ideal_basicOpen := by simp [Ideal.map_top]
  top.supportSet := ⊥
  top.supportSet_eq_iInter_zeroLocus := by
    ext x
    simpa using X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  le_top I U := le_top
-/
instance : OrderTop (IdealSheafData X) where
  top.ideal := ⊤
  top.map_ideal_basicOpen := by simp [Ideal.map_top]
  top.supportSet := ⊥
  top.supportSet_eq_iInter_zeroLocus := by
    ext x
    simpa using X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  le_top I U := le_top

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (IdealSheafData X)
  body: ⊥
  bot.map_ideal_basicOpen := by simp
  bot.supportSet := ⊤
  bot.supportSet_eq_iInter_zeroLocus := by ext; simp
  bot_le I U := bot_le

中文:
实例 :
  签名: 有底序 (IdealSheafData X)
  定义体: ⊥
  bot.map_ideal_basicOpen := by simp
  bot.supportSet := ⊤
  bot.supportSet_eq_iInter_zeroLocus := by ext; simp
  bot_le I U := bot_le
-/
instance : OrderBot (IdealSheafData X) where
  bot.ideal := ⊥
  bot.map_ideal_basicOpen := by simp
  bot.supportSet := ⊤
  bot.supportSet_eq_iInter_zeroLocus := by ext; simp
  bot_le I U := bot_le

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (IdealSheafData X)
  body: { ideal := I.ideal ⊓ J.ideal
    map_ideal_basicOpen U f := by
      dsimp
      have : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap _ _ := rfl
      have inst := U.2.isLocalization_basicOpen f
      rw [← I.map_ideal_basicOpen U f]; rw [← J.map_ideal_basicOpen U f]; rw [this]
 

中文:
实例 :
  签名: SemilatticeInf (IdealSheafData X)
  定义体: { ideal := I.ideal ⊓ J.ideal
    map_ideal_basicOpen U f := by
      dsimp
      have : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap _ _ := rfl
      have inst := U.2.isLocalization_basicOpen f
      rw [← I.map_ideal_basicOpen U f]; rw [← J.map_ideal_basicOpen U f]; rw [this]
 

Depends on / 依赖: I.ideal, I.map_ideal_basicOpen, Ideal.mem_inf, IsLocalization, IsLocalization.exists_mk, IsLocalization.mk, J.ideal, J.map_ideal_basicOpen, Submonoid, Submonoid.mem_powers_iff, X.basicOpen_le, X.presheaf.map, _mem_map_algebraMap_iff, algebraMap, basicOpen_le, exists_exists_eq_and, exists_mk, homOfLE, isLocalization_basicOpen, map_ideal_basicOpen
-/
instance : SemilatticeInf (IdealSheafData X) where
  inf I J :=
  { ideal := I.ideal ⊓ J.ideal
    map_ideal_basicOpen U f := by
      dsimp
      have : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap _ _ := rfl
      have inst := U.2.isLocalization_basicOpen f
      rw [← I.map_ideal_basicOpen U f]; rw [← J.map_ideal_basicOpen U f]; rw [this]
      ext x
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
      simp only [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff, Ideal.mem_inf,
        exists_exists_eq_and]
      refine ⟨fun ⟨n, h₁, h₂⟩ => ⟨⟨n, h₁⟩, ⟨n, h₂⟩⟩, ?_⟩
      rintro ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
      refine ⟨n₁ + n₂, ?_, ?_⟩
      · rw [add_comm, pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₁
      · rw [pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₂ }
  inf_le_left I J U := inf_le_left
  inf_le_right I J U := inf_le_right
  le_inf I J K hIJ hIK U := le_inf (hIJ U) (hIK U)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (IdealSheafData X)
  body: (inferInstance : OrderTop (IdealSheafData X))
  __ := (inferInstance : OrderBot (IdealSheafData X))
  __ := (inferInstance : SemilatticeInf (IdealSheafData X))
  __ := (inferInstance : CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

@[simp]

中文:
实例 :
  签名: 完备格 (IdealSheafData X)
  定义体: (inferInstance : OrderTop (IdealSheafData X))
  __ := (inferInstance : OrderBot (IdealSheafData X))
  __ := (inferInstance : SemilatticeInf (IdealSheafData X))
  __ := (inferInstance : CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

@[simp]

Depends on / 依赖: IdealSheafData, OrderTop
-/
instance : CompleteLattice (IdealSheafData X) where
  __ := (inferInstance : OrderTop (IdealSheafData X))
  __ := (inferInstance : OrderBot (IdealSheafData X))
  __ := (inferInstance : SemilatticeInf (IdealSheafData X))
  __ := (inferInstance : CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

@[simp]
/--
lemma `ideal_top` / 引理 `ideal_top`

English:
lemma ideal_top
  statement: ideal (X := X) ⊤ = ⊤
  proof: rfl

@[simp]

中文:
引理 ideal_top
  结论: ideal (X := X) ⊤ = ⊤
  证明: rfl

@[simp]
-/
lemma ideal_top : ideal (X := X) ⊤ = ⊤ := rfl

@[simp]
/--
lemma `ideal_bot` / 引理 `ideal_bot`

English:
lemma ideal_bot
  statement: ideal (X := X) ⊥ = ⊥
  proof: rfl

@[simp]

中文:
引理 ideal_bot
  结论: ideal (X := X) ⊥ = ⊥
  证明: rfl

@[simp]
-/
lemma ideal_bot : ideal (X := X) ⊥ = ⊥ := rfl

@[simp]
/--
lemma `ideal_sup` / 引理 `ideal_sup`

English:
lemma ideal_sup
  given: {I J : IdealSheafData X}
  statement: (I ⊔ J).ideal = I.ideal ⊔ J.ideal
  proof: rfl

@[simp]

中文:
引理 ideal_sup
  条件: {I J : IdealSheafData X}
  结论: (I ⊔ J).ideal = I.ideal ⊔ J.ideal
  证明: rfl

@[simp]
-/
lemma ideal_sup {I J : IdealSheafData X} : (I ⊔ J).ideal = I.ideal ⊔ J.ideal := rfl

@[simp]
/--
lemma `ideal_sSup` / 引理 `ideal_sSup`

English:
lemma ideal_sSup
  given: {I : Set (IdealSheafData X)}
  statement: (sSup I).ideal = sSup (ideal '' I)
  proof: rfl

@[simp]

中文:
引理 ideal_sSup
  条件: {I : 集合 (IdealSheafData X)}
  结论: (sSup I).ideal = sSup (ideal '' I)
  证明: rfl

@[simp]
-/
lemma ideal_sSup {I : Set (IdealSheafData X)} : (sSup I).ideal = sSup (ideal '' I) := rfl

@[simp]
/--
lemma `ideal_iSup` / 引理 `ideal_iSup`

English:
lemma ideal_iSup
  given: {ι : Type*} {I : ι -> IdealSheafData X}
  statement: (iSup I).ideal = ⨆ i, (I i).ideal
  proof: by
  rw [← sSup_range]; rw [← sSup_range]; rw [ideal_sSup]; rw [← Set.range_comp]; rw [Function.comp_def]

@[simp]

中文:
引理 ideal_iSup
  条件: {ι : 类型} {I : ι -> IdealSheafData X}
  结论: (iSup I).ideal = ⨆ i, (I i).ideal
  证明: by
  rw [← sSup_range]; rw [← sSup_range]; rw [ideal_sSup]; rw [← Set.range_comp]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, comp_def, ideal_sSup, range_comp, sSup_range
-/
lemma ideal_iSup {ι : Type*} {I : ι -> IdealSheafData X} : (iSup I).ideal = ⨆ i, (I i).ideal := by
  rw [← sSup_range]; rw [← sSup_range]; rw [ideal_sSup]; rw [← Set.range_comp]; rw [Function.comp_def]

@[simp]
/--
lemma `ideal_inf` / 引理 `ideal_inf`

English:
lemma ideal_inf
  given: {I J : IdealSheafData X}
  statement: (I ⊓ J).ideal = I.ideal ⊓ J.ideal
  proof: rfl

@[simp]

中文:
引理 ideal_inf
  条件: {I J : IdealSheafData X}
  结论: (I ⊓ J).ideal = I.ideal ⊓ J.ideal
  证明: rfl

@[simp]
-/
lemma ideal_inf {I J : IdealSheafData X} : (I ⊓ J).ideal = I.ideal ⊓ J.ideal := rfl

@[simp]
/--
lemma `ideal_biInf` / 引理 `ideal_biInf`

English:
lemma ideal_biInf
  given: {ι : Type*} (I : ι -> IdealSheafData X) {s : Set ι} (hs : s.Finite)
  proof: by
  refine hs.induction_on _ (by simp) fun {i s} his hs e => ?_
  simp only [iInf_insert, e, ideal_inf]

@[simp]

中文:
引理 ideal_biInf
  条件: {ι : 类型} (I : ι -> IdealSheafData X) {s : 集合 ι} (hs : s.有限)
  证明: by
  refine hs.induction_on _ (by simp) fun {i s} his hs e => ?_
  simp only [iInf_insert, e, ideal_inf]

@[simp]

Depends on / 依赖: hs.induction_on, iInf_insert, ideal_inf, induction_on
-/
lemma ideal_biInf {ι : Type*} (I : ι -> IdealSheafData X) {s : Set ι} (hs : s.Finite) :
    (⨅ i in s, I i).ideal = ⨅ i in s, (I i).ideal := by
  refine hs.induction_on _ (by simp) fun {i s} his hs e => ?_
  simp only [iInf_insert, e, ideal_inf]

@[simp]
/--
lemma `ideal_iInf` / 引理 `ideal_iInf`

English:
lemma ideal_iInf
  given: {ι : Type*} (I : ι -> IdealSheafData X) [Finite ι]
  proof: by
  simpa using ideal_biInf I Set.finite_univ

中文:
引理 ideal_iInf
  条件: {ι : 类型} (I : ι -> IdealSheafData X) [有限 ι]
  证明: by
  simpa using ideal_biInf I Set.finite_univ

Depends on / 依赖: Set.finite_univ, finite_univ, ideal_biInf
-/
lemma ideal_iInf {ι : Type*} (I : ι -> IdealSheafData X) [Finite ι] :
    (⨅ i, I i).ideal = ⨅ i, (I i).ideal := by
  simpa using ideal_biInf I Set.finite_univ

end Order

variable (I : IdealSheafData X)

section map_ideal

/--
lemma `map_ideal_basicOpen_of_eq` / 引理 `map_ideal_basicOpen_of_eq`

English:
lemma map_ideal_basicOpen_of_eq
  proof: by
  subst hV; exact I.map_ideal_basicOpen _ _

中文:
引理 map_ideal_basicOpen_of_eq
  证明: by
  subst hV; exact I.map_ideal_basicOpen _ _
-/
private lemma map_ideal_basicOpen_of_eq
    {U V : X.affineOpens} (f : Γ(X, U)) (hV : V = X.affineBasicOpen f) :
    (I.ideal U).map (X.presheaf.map
        (homOfLE (X := X.Opens) (hV.trans_le (X.affineBasicOpen_le f))).op).hom =
      I.ideal V := by
  subst hV; exact I.map_ideal_basicOpen _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_ideal` / 引理 `map_ideal`

English:
lemma map_ideal
  given: {U V : X.affineOpens} (h : U <= V)
  proof: by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, h hxU⟩
  have := I.map_ideal_basicOpen_of_eq (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
  rw [← I.map_ideal_basicOpen] at this
  apply_fun Ideal.map (X.presheaf.germ (X.ba

中文:
引理 map_ideal
  条件: {U V : X.affineOpens} (h : U <= V)
  证明: by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, h hxU⟩
  have := I.map_ideal_basicOpen_of_eq (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
  rw [← I.map_ideal_basicOpen] at this
  apply_fun Ideal.map (X.presheaf.germ (X.ba

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, I.map_ideal_basicOpen, I.map_ideal_basicOpen_of_eq, Ideal.map, Ideal.map_map, Presheaf, Subtype, Subtype.ext, TopCat, TopCat.Presheaf.germ_res, X.affineBasicOpen, X.basicOpen, X.presheaf.germ, X.presheaf.germ_res, affineBasicOpen, affineBasicOpen_coe, apply_fun, basicOpen, exists_basicOpen_le_affine_inter
-/
lemma map_ideal {U V : X.affineOpens} (h : U <= V) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = I.ideal U := by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, h hxU⟩
  have := I.map_ideal_basicOpen_of_eq (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
  rw [← I.map_ideal_basicOpen] at this
  apply_fun Ideal.map (X.presheaf.germ (X.basicOpen g) x (hfg ▸ hxf)).hom at this
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, affineBasicOpen_coe, X.presheaf.germ_res]
    at this ⊢
  simp only [homOfLE_leOfHom, TopCat.Presheaf.germ_res', this]

/--
lemma `map_ideal'` / 引理 `map_ideal'`

English:
lemma map_ideal'
  given: {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1)
  proof: map_ideal _ _

中文:
引理 map_ideal'
  条件: {U V : X.affineOpens} (h : 对偶.op V.1 ⟶ .op U.1)
  证明: map_ideal _ _

Depends on / 依赖: map_ideal
-/
lemma map_ideal' {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) :
    (I.ideal V).map (X.presheaf.map h).hom = I.ideal U :=
  map_ideal _ _

/--
lemma `ideal_le_comap_ideal` / 引理 `ideal_le_comap_ideal`

English:
lemma ideal_le_comap_ideal
  given: {U V : X.affineOpens} (h : U <= V)
  proof: by
  rw [← Ideal.map_le_iff_le_comap]; rw [← I.map_ideal h]

中文:
引理 ideal_le_comap_ideal
  条件: {U V : X.affineOpens} (h : U <= V)
  证明: by
  rw [← Ideal.map_le_iff_le_comap]; rw [← I.map_ideal h]

Depends on / 依赖: I.map_ideal, Ideal.map_le_iff_le_comap, map_ideal, map_le_iff_le_comap
-/
lemma ideal_le_comap_ideal {U V : X.affineOpens} (h : U <= V) :
    I.ideal V <= (I.ideal U).comap (X.presheaf.map (homOfLE h).op).hom := by
  rw [← Ideal.map_le_iff_le_comap]; rw [← I.map_ideal h]

/--
lemma `le_of_iSup_eq_top` / 引理 `le_of_iSup_eq_top`

English:
lemma le_of_iSup_eq_top
  statement: {I J : X.IdealSheafData} {ι : Type*}
  proof: by
  intro V
  have : forall x : V.1, exists (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 in X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter

中文:
引理 le_of_iSup_eq_top
  结论: {I J : X.IdealSheafData} {ι : 类型}
  证明: by
  intro V
  have : forall x : V.1, exists (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 in X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter

Depends on / 依赖: Ideal.span, Set.mem_univ, Set.range, TopologicalSpace, TopologicalSpace.Opens.mem_iSup.mp, TopologicalSpace.Opens.mem_iSup.mpr, X.basicOpen, basicOpen, exists_basicOpen_le_affine_inter, hU.ge, mem_iSup, mem_univ, self_le_iSup_basicOpen_iff
-/
lemma le_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
    (U : ι -> X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (H : forall i, I.ideal (U i) <= J.ideal (U i)) :
    I <= J := by
  intro V
  have : forall x : V.1, exists (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 in X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter V.2 (U i).2 _ ⟨hxV, hi⟩⟩
  choose i r rU e hxr using this
  have : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.le_of_isLocalized_span _ this (fun i => Γ(X, X.basicOpen i.1))
    (fun i => Algebra.linearMap Γ(X, V.1) Γ(X, X.basicOpen i.1)) ?_
  rintro ⟨_, j, rfl⟩
  simp only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (r j)),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  erw [I.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j)),
    J.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j))]
  delta algebra_section_section_basicOpen
  rw! [e]
  rw [← I.map_ideal (V := (U _)) (X.basicOpen_le _)]; rw [← J.map_ideal (V := (U _)) (X.basicOpen_le _)]
  exact Ideal.map_mono (f := (X.presheaf.map (homOfLE (X.basicOpen_le (rU j))).op).hom) (H (i j))

/--
lemma `ext_of_iSup_eq_top` / 引理 `ext_of_iSup_eq_top`

English:
lemma ext_of_iSup_eq_top
  statement: {I J : X.IdealSheafData} {ι : Type*}
  proof: (le_of_iSup_eq_top U hU (by aesop)).antisymm (le_of_iSup_eq_top U hU (by aesop))

中文:
引理 ext_of_iSup_eq_top
  结论: {I J : X.IdealSheafData} {ι : 类型}
  证明: (le_of_iSup_eq_top U hU (by aesop)).antisymm (le_of_iSup_eq_top U hU (by aesop))

Depends on / 依赖: antisymm, le_of_iSup_eq_top
-/
lemma ext_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
    (U : ι -> X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (H : forall i, I.ideal (U i) = J.ideal (U i)) :
    I = J :=
  (le_of_iSup_eq_top U hU (by aesop)).antisymm (le_of_iSup_eq_top U hU (by aesop))

end map_ideal

section support

/--
lemma `mem_supportSet_iff` / 引理 `mem_supportSet_iff`

English:
lemma mem_supportSet_iff
  given: {I : IdealSheafData X} {x}
  proof: (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

中文:
引理 mem_supportSet_iff
  条件: {I : IdealSheafData X} {x}
  证明: (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

Depends on / 依赖: I.ideal
-/
lemma mem_supportSet_iff {I : IdealSheafData X} {x} :
    x in I.supportSet ↔ forall U, x in X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

/--
lemma `supportSet_subset_zeroLocus` / 引理 `supportSet_subset_zeroLocus`

English:
lemma supportSet_subset_zeroLocus
  given: (I : IdealSheafData X) (U : X.affineOpens)
  proof: I.supportSet_eq_iInter_zeroLocus.trans_subset (Set.iInter_subset _ _)

中文:
引理 supportSet_subset_zeroLocus
  条件: (I : IdealSheafData X) (U : X.affineOpens)
  证明: I.supportSet_eq_iInter_zeroLocus.trans_subset (Set.iInter_subset _ _)

Depends on / 依赖: I.ideal
-/
lemma supportSet_subset_zeroLocus (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet subseteq X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus.trans_subset (Set.iInter_subset _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `zeroLocus_inter_subset_supportSet` / 引理 `zeroLocus_inter_subset_supportSet`

English:
lemma zeroLocus_inter_subset_supportSet
  given: (I : IdealSheafData X) (U : X.affineOpens)
  proof: by
  rw [I.supportSet_eq_iInter_zeroLocus]
  refine Set.subset_iInter fun V => ?_
  apply (X.codisjoint_zeroLocus (U := V) (I.ideal V)).symm.left_le_of_le_inf_right
  rintro x ⟨⟨hx, hxU⟩, hxV⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx ⊢
  intro s hfU hxs
  obtain ⟨f, g, hfg, hxf⟩

中文:
引理 zeroLocus_inter_subset_supportSet
  条件: (I : IdealSheafData X) (U : X.affineOpens)
  证明: by
  rw [I.supportSet_eq_iInter_zeroLocus]
  refine Set.subset_iInter fun V => ?_
  apply (X.codisjoint_zeroLocus (U := V) (I.ideal V)).symm.left_le_of_le_inf_right
  rintro x ⟨⟨hx, hxU⟩, hxV⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx ⊢
  intro s hfU hxs
  obtain ⟨f, g, hfg, hxf⟩

Depends on / 依赖: I.ideal, I.map_ideal, I.supportSet, I.supportSet_eq_iInter_zeroLocus, Scheme, Scheme.mem_zeroLocus_iff, Set.subset_iInter, SetLike, SetLike.mem_coe, X.affineBasicOpen, X.codisjoint_zeroLocus, affineBasicOpen, codisjoint_zeroLocus, exists_basicOpen_le_affine_inter, hfg.trans_le, isLocalization_basicOpen, left_le_of_le_inf_right, map_ideal, mem_coe, mem_zeroLocus_iff
-/
lemma zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpens) :
    X.zeroLocus (U := U.1) (I.ideal U) inter U subseteq I.supportSet := by
  rw [I.supportSet_eq_iInter_zeroLocus]
  refine Set.subset_iInter fun V => ?_
  apply (X.codisjoint_zeroLocus (U := V) (I.ideal V)).symm.left_le_of_le_inf_right
  rintro x ⟨⟨hx, hxU⟩, hxV⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx ⊢
  intro s hfU hxs
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have inst := U.2.isLocalization_basicOpen f
  have := (I.map_ideal (U := X.affineBasicOpen f) (hfg.trans_le (X.basicOpen_le g))).le
    (Ideal.mem_map_of_mem _ hfU)
  rw [← I.map_ideal_basicOpen] at this
  obtain ⟨⟨s', ⟨_, n, rfl⟩⟩, hs'⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (.powers f) Γ(X, X.basicOpen f)).mp this
  apply_fun (x in X.basicOpen ·) at hs'
  refine hx s' s'.2 ?_
  cases n <;>
    simpa [RingHom.algebraMap_toAlgebra, ← hfg, hxf, hxs, Scheme.basicOpen_pow] using hs'

/--
lemma `mem_supportSet_iff_of_mem` / 引理 `mem_supportSet_iff_of_mem`

English:
lemma mem_supportSet_iff_of_mem
  given: {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x in U.1)
  proof: ⟨I.supportSet_eq_iInter_zeroLocus ▸ fun h => Set.iInter_subset _ U h,
    fun h => I.zeroLocus_inter_subset_supportSet U ⟨h, hxU⟩⟩

中文:
引理 mem_supportSet_iff_of_mem
  条件: {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x in U.1)
  证明: ⟨I.supportSet_eq_iInter_zeroLocus ▸ fun h => Set.iInter_subset _ U h,
    fun h => I.zeroLocus_inter_subset_supportSet U ⟨h, hxU⟩⟩

Depends on / 依赖: I.ideal
-/
lemma mem_supportSet_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x in U.1) :
    x in I.supportSet ↔ x in X.zeroLocus (U := U.1) (I.ideal U) :=
  ⟨I.supportSet_eq_iInter_zeroLocus ▸ fun h => Set.iInter_subset _ U h,
    fun h => I.zeroLocus_inter_subset_supportSet U ⟨h, hxU⟩⟩

/--
lemma `supportSet_inter` / 引理 `supportSet_inter`

English:
lemma supportSet_inter
  given: (I : IdealSheafData X) (U : X.affineOpens)
  proof: by
  ext x
  by_cases hxU : x in U.1
  · simp [hxU, mem_supportSet_iff_of_mem hxU]
  · simp [hxU]

中文:
引理 supportSet_inter
  条件: (I : IdealSheafData X) (U : X.affineOpens)
  证明: by
  ext x
  by_cases hxU : x in U.1
  · simp [hxU, mem_supportSet_iff_of_mem hxU]
  · simp [hxU]

Depends on / 依赖: I.ideal, mem_supportSet_iff_of_mem
-/
lemma supportSet_inter (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet inter U = X.zeroLocus (U := U.1) (I.ideal U) inter U := by
  ext x
  by_cases hxU : x in U.1
  · simp [hxU, mem_supportSet_iff_of_mem hxU]
  · simp [hxU]

/--
lemma `isClosed_supportSet` / 引理 `isClosed_supportSet`

English:
lemma isClosed_supportSet
  given: (I : IdealSheafData X)
  statement: IsClosed I.supportSet
  proof: by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set

中文:
引理 isClosed_supportSet
  条件: (I : IdealSheafData X)
  结论: 是闭集 I.supportSet
  证明: by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set

Depends on / 依赖: I.ideal, I.supportSet_inter, IsOpenCover, Set.image_preimage_eq_inter_range, Set.preimage_compl, Subtype, Subtype.val_injective.image_injective, TopologicalSpace, TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage, X.zeroLocus, X.zeroLocus_isClosed, compl_inj_iff, iSup_affineOpens_eq_top, image_injective, image_preimage_eq_inter_range, isClosed_iff_coe_preimage, isOpen_compl, preimage_compl, supportSet_inter, val_injective
-/
lemma isClosed_supportSet (I : IdealSheafData X) : IsClosed I.supportSet := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set.image_preimage_eq_inter_range, I.supportSet_inter]

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: : Closeds X
  body: ⟨I.supportSet, I.isClosed_supportSet⟩

中文:
定义 support
  签名: : Closeds X
  定义体: ⟨I.supportSet, I.isClosed_supportSet⟩

Depends on / 依赖: I.isClosed_supportSet, I.supportSet, isClosed_supportSet, supportSet
-/
def support : Closeds X := ⟨I.supportSet, I.isClosed_supportSet⟩

/--
lemma `coe_support_eq_eq_iInter_zeroLocus` / 引理 `coe_support_eq_eq_iInter_zeroLocus`

English:
lemma coe_support_eq_eq_iInter_zeroLocus
  proof: I.supportSet_eq_iInter_zeroLocus

中文:
引理 coe_support_eq_eq_i整数er_zeroLocus
  证明: I.supportSet_eq_iInter_zeroLocus

Depends on / 依赖: I.ideal
-/
lemma coe_support_eq_eq_iInter_zeroLocus :
    (I.support : Set X) = ⋂ U, X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus

/--
lemma `mem_supportSet_iff_mem_support` / 引理 `mem_supportSet_iff_mem_support`

English:
lemma mem_supportSet_iff_mem_support
  given: {I : IdealSheafData X} {x}
  proof: .rfl

中文:
引理 mem_supportSet_iff_mem_support
  条件: {I : IdealSheafData X} {x}
  证明: .rfl
-/
@[simp] lemma mem_supportSet_iff_mem_support {I : IdealSheafData X} {x} :
    x in I.supportSet ↔ x in I.support := .rfl

/--
lemma `mem_support_iff` / 引理 `mem_support_iff`

English:
lemma mem_support_iff
  given: {I : IdealSheafData X} {x}
  proof: (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

中文:
引理 mem_support_iff
  条件: {I : IdealSheafData X} {x}
  证明: (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

Depends on / 依赖: I.ideal
-/
lemma mem_support_iff {I : IdealSheafData X} {x} :
    x in I.support ↔ forall U, x in X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

/--
lemma `mem_support_iff_of_mem` / 引理 `mem_support_iff_of_mem`

English:
lemma mem_support_iff_of_mem
  given: {I : IdealSheafData X} {x : X} {U : X.affineOpens} (h : x in U.1)
  proof: by
  simpa [-mem_zeroLocus_iff, h] using congr(x in $(I.supportSet_inter U))

中文:
引理 mem_support_iff_of_mem
  条件: {I : IdealSheafData X} {x : X} {U : X.affineOpens} (h : x in U.1)
  证明: by
  simpa [-mem_zeroLocus_iff, h] using congr(x in $(I.supportSet_inter U))

Depends on / 依赖: I.ideal, I.supportSet_inter, mem_zeroLocus_iff, supportSet_inter
-/
lemma mem_support_iff_of_mem {I : IdealSheafData X} {x : X} {U : X.affineOpens} (h : x in U.1) :
    x in I.support ↔ x in X.zeroLocus (U := U.1) (I.ideal U) := by
  simpa [-mem_zeroLocus_iff, h] using congr(x in $(I.supportSet_inter U))

/--
lemma `coe_support_inter` / 引理 `coe_support_inter`

English:
lemma coe_support_inter
  given: (I : IdealSheafData X) (U : X.affineOpens)
  proof: I.supportSet_inter U

中文:
引理 coe_support_inter
  条件: (I : IdealSheafData X) (U : X.affineOpens)
  证明: I.supportSet_inter U

Depends on / 依赖: I.ideal
-/
lemma coe_support_inter (I : IdealSheafData X) (U : X.affineOpens) :
    (I.support : Set X) inter U = X.zeroLocus (U := U.1) (I.ideal U) inter U :=
  I.supportSet_inter U

/--
Definition of `Simps.coe_support` / `Simps.coe_support` 的定义

English:
definition Simps.coe_support
  signature: : Set X
  body: I.support

initialize_simps_projections IdealSheafData (supportSet -> coe_support, as_prefix coe_support)

中文:
定义 Simps.coe_support
  签名: : 集合 X
  定义体: I.support

initialize_simps_projections IdealSheafData (supportSet -> coe_support, as_prefix coe_support)

Depends on / 依赖: I.support, support
-/
def Simps.coe_support : Set X := I.support

initialize_simps_projections IdealSheafData (supportSet -> coe_support, as_prefix coe_support)

/-- A useful constructor of `IdealSheafData`
with the condition on `supportSet` being easier to check. -/
@[simps ideal coe_support]
/--
Definition of `mkOfMemSupportIff` / `mkOfMemSupportIff` 的定义

English:
definition mkOfMemSupportIff
  body: ideal
  map_ideal_basicOpen := map_ideal_basicOpen
  supportSet := supportSet
  supportSet_eq_iInter_zeroLocus := by
    let I' : X.IdealSheafData := { ideal := ideal, map_ideal_basicOpen := map_ideal_basicOpen }
    change supportSet = I'.supportSet
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=

中文:
定义 mkOfMemSupportIff
  定义体: ideal
  map_ideal_basicOpen := map_ideal_basicOpen
  supportSet := supportSet
  supportSet_eq_iInter_zeroLocus := by
    let I' : X.IdealSheafData := { ideal := ideal, map_ideal_basicOpen := map_ideal_basicOpen }
    change supportSet = I'.supportSet
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
-/
def mkOfMemSupportIff
    (ideal : forall U : X.affineOpens, Ideal Γ(X, U))
    (map_ideal_basicOpen : forall (U : X.affineOpens) (f : Γ(X, U)),
      (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
        ideal (X.affineBasicOpen f))
    (supportSet : Set X)
    (supportSet_inter :
      forall U : X.affineOpens, forall x in U.1, x in supportSet ↔ x in X.zeroLocus (U := U.1) (ideal U)) :
    X.IdealSheafData where
  ideal := ideal
  map_ideal_basicOpen := map_ideal_basicOpen
  supportSet := supportSet
  supportSet_eq_iInter_zeroLocus := by
    let I' : X.IdealSheafData := { ideal := ideal, map_ideal_basicOpen := map_ideal_basicOpen }
    change supportSet = I'.supportSet
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (supportSet_inter ⟨U, hU⟩ x hxU).trans
      (I'.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).symm

@[simp]
/--
lemma `support_top` / 引理 `support_top`

English:
lemma support_top
  statement: support (X := X) ⊤ = ⊥
  proof: rfl

@[simp]

中文:
引理 support_top
  结论: support (X := X) ⊤ = ⊥
  证明: rfl

@[simp]
-/
lemma support_top : support (X := X) ⊤ = ⊥ := rfl

@[simp]
/--
lemma `support_bot` / 引理 `support_bot`

English:
lemma support_bot
  statement: support (X := X) ⊥ = ⊤
  proof: rfl

中文:
引理 support_bot
  结论: support (X := X) ⊥ = ⊤
  证明: rfl
-/
lemma support_bot : support (X := X) ⊥ = ⊤ := rfl

/--
lemma `support_antitone` / 引理 `support_antitone`

English:
lemma support_antitone
  statement: Antitone (support (X := X))
  proof: by
  intro I J h
  rw [← SetLike.coe_subset_coe]; rw [I.coe_support_eq_eq_iInter_zeroLocus]; rw [J.coe_support_eq_eq_iInter_zeroLocus]
  exact Set.iInter_mono fun U => X.zeroLocus_mono (h U)

中文:
引理 support_antitone
  结论: 递减 (support (X := X))
  证明: by
  intro I J h
  rw [← SetLike.coe_subset_coe]; rw [I.coe_support_eq_eq_iInter_zeroLocus]; rw [J.coe_support_eq_eq_iInter_zeroLocus]
  exact Set.iInter_mono fun U => X.zeroLocus_mono (h U)

Depends on / 依赖: I.coe_support_eq_eq_iInter_zeroLocus, J.coe_support_eq_eq_iInter_zeroLocus, Set.iInter_mono, SetLike, SetLike.coe_subset_coe, X.zeroLocus_mono, coe_subset_coe, coe_support_eq_eq_iInter_zeroLocus, iInter_mono, zeroLocus_mono
-/
lemma support_antitone : Antitone (support (X := X)) := by
  intro I J h
  rw [← SetLike.coe_subset_coe]; rw [I.coe_support_eq_eq_iInter_zeroLocus]; rw [J.coe_support_eq_eq_iInter_zeroLocus]
  exact Set.iInter_mono fun U => X.zeroLocus_mono (h U)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `support_eq_bot_iff` / 引理 `support_eq_bot_iff`

English:
lemma support_eq_bot_iff
  statement: support I = ⊥ ↔ I = ⊤
  proof: by
  refine ⟨fun H => top_le_iff.mp fun U => ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_supportSet I U).trans H.le)
  simp only [Set.subset_empty_iff, Set.image_eq_empty, Closeds.coe_bot] at this
  simp [PrimeSpectrum.zeroLocus_empty

中文:
引理 support_eq_bot_iff
  结论: support I = ⊥ ↔ I = ⊤
  证明: by
  refine ⟨fun H => top_le_iff.mp fun U => ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_supportSet I U).trans H.le)
  simp only [Set.subset_empty_iff, Set.image_eq_empty, Closeds.coe_bot] at this
  simp [PrimeSpectrum.zeroLocus_empty

Depends on / 依赖: Closeds, Closeds.coe_bot, H.le, PrimeSpectrum, PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp, Set.image_eq_empty, Set.subset_empty_iff, coe_bot, contextual, fromSpec_image_zeroLocus, image_eq_empty, subset_empty_iff, top_le_iff, top_le_iff.mp, trans_subset, zeroLocus_empty_iff_eq_top, zeroLocus_inter_subset_supportSet
-/
lemma support_eq_bot_iff : support I = ⊥ ↔ I = ⊤ := by
  refine ⟨fun H => top_le_iff.mp fun U => ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_supportSet I U).trans H.le)
  simp only [Set.subset_empty_iff, Set.image_eq_empty, Closeds.coe_bot] at this
  simp [PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp this]

end support

section Semiring

variable (I J K : X.IdealSheafData)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero X.IdealSheafData
  body: ⊥

中文:
实例 :
  签名: 零 X.IdealSheafData
  定义体: ⊥
-/
instance : Zero X.IdealSheafData where zero := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One X.IdealSheafData
  body: ⊤

中文:
实例 :
  签名: 幺 X.IdealSheafData
  定义体: ⊤
-/
instance : One X.IdealSheafData where one := ⊤
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add X.IdealSheafData
  body: (· ⊔ ·)

中文:
实例 :
  签名: 加法 X.IdealSheafData
  定义体: (· ⊔ ·)
-/
instance : Add X.IdealSheafData where add := (· ⊔ ·)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul X.IdealSheafData
  body: mkOfMemSupportIff (I.ideal * J.ideal) (by simp [Ideal.map_mul, map_ideal_basicOpen])
    (I.supportSet union J.supportSet) fun U x hxU => by
    simp [-mem_zeroLocus_iff, zeroLocus_mul, mem_support_iff_of_mem hxU]

中文:
实例 :
  签名: 乘法 X.IdealSheafData
  定义体: mkOfMemSupportIff (I.ideal * J.ideal) (by simp [Ideal.map_mul, map_ideal_basicOpen])
    (I.supportSet union J.supportSet) fun U x hxU => by
    simp [-mem_zeroLocus_iff, zeroLocus_mul, mem_support_iff_of_mem hxU]

Depends on / 依赖: I.ideal, Ideal.map_mul, J.ideal, map_ideal_basicOpen, map_mul, mkOfMemSupportIff
-/
instance : Mul X.IdealSheafData where
  mul I J := mkOfMemSupportIff (I.ideal * J.ideal) (by simp [Ideal.map_mul, map_ideal_basicOpen])
    (I.supportSet union J.supportSet) fun U x hxU => by
    simp [-mem_zeroLocus_iff, zeroLocus_mul, mem_support_iff_of_mem hxU]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow X.IdealSheafData Nat
  body: mkOfMemSupportIff (I.ideal ^ n) (by simp [Ideal.map_pow, map_ideal_basicOpen])
(if n = 0 then ∅ else I.supportSet) fun U x hxU => .symm by
    induction n <;> simp_all [-mem_zeroLocus_iff, zeroLocus_mul,
      pow_succ, mem_support_iff_of_mem hxU]

中文:
实例 :
  签名: 幂 X.IdealSheafData 自然数
  定义体: mkOfMemSupportIff (I.ideal ^ n) (by simp [Ideal.map_pow, map_ideal_basicOpen])
(if n = 0 then ∅ else I.supportSet) fun U x hxU => .symm by
    induction n <;> simp_all [-mem_zeroLocus_iff, zeroLocus_mul,
      pow_succ, mem_support_iff_of_mem hxU]

Depends on / 依赖: I.ideal, Ideal.map_pow, map_ideal_basicOpen, map_pow, mkOfMemSupportIff
-/
instance : Pow X.IdealSheafData Nat where
  pow I n := mkOfMemSupportIff (I.ideal ^ n) (by simp [Ideal.map_pow, map_ideal_basicOpen])
(if n = 0 then ∅ else I.supportSet) fun U x hxU => .symm by
    induction n <;> simp_all [-mem_zeroLocus_iff, zeroLocus_mul,
      pow_succ, mem_support_iff_of_mem hxU]

/--
lemma `ideal_mul` / 引理 `ideal_mul`

English:
lemma ideal_mul
  statement: (I * J).ideal = I.ideal * J.ideal
  proof: rfl

中文:
引理 ideal_mul
  结论: (I * J).ideal = I.ideal * J.ideal
  证明: rfl

Depends on / 依赖: SimplicialObject, infer_instance
-/
@[simp] lemma ideal_mul : (I * J).ideal = I.ideal * J.ideal := rfl
/--
lemma `support_mul` / 引理 `support_mul`

English:
lemma support_mul
  statement: (I * J).support = I.support ⊔ J.support
  proof: rfl

中文:
引理 support_mul
  结论: (I * J).support = I.support ⊔ J.support
  证明: rfl
-/
@[simp] lemma support_mul : (I * J).support = I.support ⊔ J.support := rfl
/--
lemma `ideal_pow` / 引理 `ideal_pow`

English:
lemma ideal_pow
  given: (n : Nat)
  statement: (I ^ n).ideal = I.ideal ^ n
  proof: rfl

中文:
引理 ideal_pow
  条件: (n : 自然数)
  结论: (I ^ n).ideal = I.ideal ^ n
  证明: rfl

Depends on / 依赖: SimplicialObject, infer_instance
-/
@[simp] lemma ideal_pow (n : Nat) : (I ^ n).ideal = I.ideal ^ n := rfl
/--
lemma `support_pow_succ` / 引理 `support_pow_succ`

English:
lemma support_pow_succ
  given: (n : Nat)
  statement: (I ^ (n + 1)).support = I.support
  proof: rfl

中文:
引理 support_pow_succ
  条件: (n : 自然数)
  结论: (I ^ (n + 1)).support = I.support
  证明: rfl
-/
@[simp] lemma support_pow_succ (n : Nat) : (I ^ (n + 1)).support = I.support := rfl
/--
lemma `support_pow` / 引理 `support_pow`

English:
lemma support_pow
  given: (n : Nat) (hn : n != 0)
  statement: (I ^ n).support = I.support
  proof: by cases n <;> simp_all

中文:
引理 support_pow
  条件: (n : 自然数) (hn : n != 0)
  结论: (I ^ n).support = I.support
  证明: by cases n <;> simp_all
-/
lemma support_pow (n : Nat) (hn : n != 0) : (I ^ n).support = I.support := by cases n <;> simp_all

/--
lemma `top_mul` / 引理 `top_mul`

English:
lemma top_mul
  statement: ⊤ * I = I
  proof: by ext; simp

中文:
引理 top_mul
  结论: ⊤ * I = I
  证明: by ext; simp
-/
@[simp] lemma top_mul : ⊤ * I = I := by ext; simp
/--
lemma `mul_top` / 引理 `mul_top`

English:
lemma mul_top
  statement: I * ⊤ = I
  proof: by ext; simp

中文:
引理 mul_top
  结论: I * ⊤ = I
  证明: by ext; simp
-/
@[simp] lemma mul_top : I * ⊤ = I := by ext; simp
/--
lemma `bot_mul` / 引理 `bot_mul`

English:
lemma bot_mul
  statement: ⊥ * I = ⊥
  proof: by ext; simp

中文:
引理 bot_mul
  结论: ⊥ * I = ⊥
  证明: by ext; simp
-/
@[simp] lemma bot_mul : ⊥ * I = ⊥ := by ext; simp
/--
lemma `mul_bot` / 引理 `mul_bot`

English:
lemma mul_bot
  statement: I * ⊥ = ⊥
  proof: by ext; simp

中文:
引理 mul_bot
  结论: I * ⊥ = ⊥
  证明: by ext; simp
-/
@[simp] lemma mul_bot : I * ⊥ = ⊥ := by ext; simp
/--
lemma `mul_inf` / 引理 `mul_inf`

English:
lemma mul_inf
  statement: I * (J ⊔ K) = I * J ⊔ I * K
  proof: by ext U : 2; exact mul_add _ _ _

中文:
引理 mul_inf
  结论: I * (J ⊔ K) = I * J ⊔ I * K
  证明: by ext U : 2; exact mul_add _ _ _

Depends on / 依赖: mul_add
-/
lemma mul_inf : I * (J ⊔ K) = I * J ⊔ I * K := by ext U : 2; exact mul_add _ _ _
/--
lemma `inf_mul` / 引理 `inf_mul`

English:
lemma inf_mul
  statement: (I ⊔ J) * K = I * K ⊔ J * K
  proof: by ext U : 2; exact add_mul _ _ _

中文:
引理 inf_mul
  结论: (I ⊔ J) * K = I * K ⊔ J * K
  证明: by ext U : 2; exact add_mul _ _ _

Depends on / 依赖: add_mul
-/
lemma inf_mul : (I ⊔ J) * K = I * K ⊔ J * K := by ext U : 2; exact add_mul _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IdemCommSemiring X.IdealSheafData
  body: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc _ _ _ := IdealSheafData.ext (mul_assoc _ _ _)
  mul_comm _ _ := IdealSheafData.ext (mul_comm _ _)
  zero_mul := bot_mul
  mul_zero := mul_bot
  one_mul := top_mul
  mul_one := mul_top
  nsmul := nsmulRec
 

中文:
实例 :
  签名: IdemCommSemiring X.IdealSheafData
  定义体: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc _ _ _ := IdealSheafData.ext (mul_assoc _ _ _)
  mul_comm _ _ := IdealSheafData.ext (mul_comm _ _)
  zero_mul := bot_mul
  mul_zero := mul_bot
  one_mul := top_mul
  mul_one := mul_top
  nsmul := nsmulRec
 

Depends on / 依赖: sup_assoc
-/
instance : IdemCommSemiring X.IdealSheafData where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc _ _ _ := IdealSheafData.ext (mul_assoc _ _ _)
  mul_comm _ _ := IdealSheafData.ext (mul_comm _ _)
  zero_mul := bot_mul
  mul_zero := mul_bot
  one_mul := top_mul
  mul_one := mul_top
  nsmul := nsmulRec
  left_distrib := mul_inf
  right_distrib := inf_mul
  npow n I := I ^ n
  npow_zero _ := by ext; simp [show (1 : X.IdealSheafData) = ⊤ from rfl]
  npow_succ _ _ := by ext; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedRing X.IdealSheafData

中文:
实例 :
  签名: 是Ordered环 X.IdealSheafData
-/
instance : IsOrderedRing X.IdealSheafData where

/--
lemma `zero_eq_bot` / 引理 `zero_eq_bot`

English:
lemma zero_eq_bot
  statement: (0 : X.IdealSheafData) = ⊥
  proof: rfl

中文:
引理 zero_eq_bot
  结论: (0 : X.IdealSheafData) = ⊥
  证明: rfl
-/
@[simp] lemma zero_eq_bot : (0 : X.IdealSheafData) = ⊥ := rfl
/--
lemma `one_eq_top` / 引理 `one_eq_top`

English:
lemma one_eq_top
  statement: (1 : X.IdealSheafData) = ⊤
  proof: rfl

中文:
引理 one_eq_top
  结论: (1 : X.IdealSheafData) = ⊤
  证明: rfl
-/
@[simp] lemma one_eq_top : (1 : X.IdealSheafData) = ⊤ := rfl
/--
lemma `add_eq_sup` / 引理 `add_eq_sup`

English:
lemma add_eq_sup
  statement: I + J = I ⊔ J
  proof: rfl

中文:
引理 add_eq_sup
  结论: I + J = I ⊔ J
  证明: rfl
-/
@[simp] lemma add_eq_sup : I + J = I ⊔ J := rfl

end Semiring

section IsAffine

/-- The ideal sheaf induced by an ideal of the global sections. -/
@[simps! ideal coe_support]
/--
Definition of `ofIdealTop` / `ofIdealTop` 的定义

English:
definition ofIdealTop
  signature: (I : Ideal Γ(X, ⊤))
  body: mkOfMemSupportIff
    (fun U => I.map (X.presheaf.map (homOfLE le_top).op).hom)
    (fun U f => by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (X.zeroLocus (U := ⊤) I)
    (fun U x hxU => by
      simp only [Ideal.map, zeroLocus_span, zeroLocus_map, Set.mem_union, Set.me

中文:
定义 ofIdealTop
  签名: (I : 理想 Γ(X, ⊤))
  定义体: mkOfMemSupportIff
    (fun U => I.map (X.presheaf.map (homOfLE le_top).op).hom)
    (fun U f => by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (X.zeroLocus (U := ⊤) I)
    (fun U x hxU => by
      simp only [Ideal.map, zeroLocus_span, zeroLocus_map, Set.mem_union, Set.me

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, Functor, Functor.map_comp, I.map, Ideal.map, Ideal.map_map, IsEmpty, IsEmpty.forall_iff, Set.mem_compl_iff, Set.mem_union, SetLike, SetLike.mem_coe, X.presheaf.map, X.zeroLocus, forall_iff, homOfLE, hom_comp, iff_self_or, le_top
-/
def ofIdealTop (I : Ideal Γ(X, ⊤)) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U => I.map (X.presheaf.map (homOfLE le_top).op).hom)
    (fun U f => by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (X.zeroLocus (U := ⊤) I)
    (fun U x hxU => by
      simp only [Ideal.map, zeroLocus_span, zeroLocus_map, Set.mem_union, Set.mem_compl_iff,
        SetLike.mem_coe, hxU, not_true_eq_false, iff_self_or, IsEmpty.forall_iff])

/--
lemma `le_of_isAffine` / 引理 `le_of_isAffine`

English:
lemma le_of_isAffine
  statement: [IsAffine X] {I J : IdealSheafData X}
  proof: by
  intro U
  rw [← map_ideal (U := U) (V := ⟨⊤]; rw [isAffineOpen_top X⟩) I (le_top (a := U.1))]; rw [← map_ideal (U := U) (V := ⟨⊤]; rw [isAffineOpen_top X⟩) J (le_top (a := U.1))]
  exact Ideal.map_mono H

中文:
引理 le_of_isAffine
  结论: [是仿射 X] {I J : IdealSheafData X}
  证明: by
  intro U
  rw [← map_ideal (U := U) (V := ⟨⊤]; rw [isAffineOpen_top X⟩) I (le_top (a := U.1))]; rw [← map_ideal (U := U) (V := ⟨⊤]; rw [isAffineOpen_top X⟩) J (le_top (a := U.1))]
  exact Ideal.map_mono H

Depends on / 依赖: Ideal.map_mono, isAffineOpen_top, le_top, map_ideal, map_mono
-/
lemma le_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ <= J.ideal ⟨⊤, isAffineOpen_top X⟩) : I <= J := by
  intro U
  rw [← map_ideal (U := U) (V := ⟨⊤]; rw [isAffineOpen_top X⟩) I (le_top (a := U.1))]; rw [← map_ideal (U := U) (V := ⟨⊤]; rw [isAffineOpen_top X⟩) J (le_top (a := U.1))]
  exact Ideal.map_mono H

/--
lemma `ext_of_isAffine` / 引理 `ext_of_isAffine`

English:
lemma ext_of_isAffine
  statement: [IsAffine X] {I J : IdealSheafData X}
  proof: (le_of_isAffine H.le).antisymm (le_of_isAffine H.ge)

中文:
引理 ext_of_isAffine
  结论: [是仿射 X] {I J : IdealSheafData X}
  证明: (le_of_isAffine H.le).antisymm (le_of_isAffine H.ge)

Depends on / 依赖: H.ge, H.le, antisymm, le_of_isAffine
-/
lemma ext_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  (le_of_isAffine H.le).antisymm (le_of_isAffine H.ge)

/--
Definition of `equivOfIsAffine` / `equivOfIsAffine` 的定义

English:
definition equivOfIsAffine
  signature: [IsAffine X]
  body: (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp
  map_mul' := by simp
  map_add' := by simp
  map_le_map_iff' := ⟨le_of_isAffine, (· _)⟩

@[simp]

中文:
定义 equivOfIsAffine
  签名: [是仿射 X]
  定义体: (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp
  map_mul' := by simp
  map_add' := by simp
  map_le_map_iff' := ⟨le_of_isAffine, (· _)⟩

@[simp]

Depends on / 依赖: isAffineOpen_top
-/
def equivOfIsAffine [IsAffine X] : IdealSheafData X ≃+*o Ideal Γ(X, ⊤) where
  toFun := (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp
  map_mul' := by simp
  map_add' := by simp
  map_le_map_iff' := ⟨le_of_isAffine, (· _)⟩

@[simp]
/--
lemma `equivOfIsAffine_apply` / 引理 `equivOfIsAffine_apply`

English:
lemma equivOfIsAffine_apply
  given: [IsAffine X] (I : IdealSheafData X)
  proof: rfl

@[simp]

中文:
引理 equivOfIsAffine_apply
  条件: [是仿射 X] (I : IdealSheafData X)
  证明: rfl

@[simp]
-/
lemma equivOfIsAffine_apply [IsAffine X] (I : IdealSheafData X) :
    equivOfIsAffine I = I.ideal ⟨⊤, isAffineOpen_top X⟩ := rfl

@[simp]
/--
lemma `equivOfIsAffine_symm_apply` / 引理 `equivOfIsAffine_symm_apply`

English:
lemma equivOfIsAffine_symm_apply
  given: [IsAffine X] (I : Ideal Γ(X, ⊤))
  proof: rfl

中文:
引理 equivOfIsAffine_symm_apply
  条件: [是仿射 X] (I : 理想 Γ(X, ⊤))
  证明: rfl
-/
lemma equivOfIsAffine_symm_apply [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    equivOfIsAffine.symm I = ofIdealTop I := rfl

end IsAffine

section ofIsClosed

open _root_.PrimeSpectrum TopologicalSpace

/-- The radical of an ideal sheaf. -/
@[simps! ideal]
/--
Definition of `radical` / `radical` 的定义

English:
definition radical
  signature: (I : IdealSheafData X)
  body: mkOfMemSupportIff
  (fun U => (I.ideal U).radical)
  (fun U f =>
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLoca

中文:
定义 radical
  签名: (I : IdealSheafData X)
  定义体: mkOfMemSupportIff
  (fun U => (I.ideal U).radical)
  (fun U f =>
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLoca

Depends on / 依赖: Algebra, AlgebraicGeometry, AlgebraicGeometry.Scheme.zeroLocu, I.ideal, I.map_ideal_basicOpen, I.supportSet, IsLocalization, IsLocalization.Away, IsLocalization.map_radical, Scheme, X.affineBasicOpen, X.basicOpen, X.basicOpen_le, X.presheaf.map, affineBasicOpen, basicOpen, basicOpen_le, hom.toAlgebra, homOfLE, isLocalization_of_eq_basicOpen
-/
def radical (I : IdealSheafData X) : IdealSheafData X :=
  mkOfMemSupportIff
  (fun U => (I.ideal U).radical)
  (fun U f =>
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLocalization.map_radical (.powers f) Γ(X, X.basicOpen f) (I.ideal U)).trans
      congr($(I.map_ideal_basicOpen U f).radical))
  I.supportSet
  (fun U x hx => by
    simp only [mem_supportSet_iff_of_mem hx, AlgebraicGeometry.Scheme.zeroLocus_radical])

@[simp]
/--
lemma `support_radical` / 引理 `support_radical`

English:
lemma support_radical
  given: (I : IdealSheafData X)
  statement: I.radical.support = I.support
  proof: rfl

中文:
引理 support_radical
  条件: (I : IdealSheafData X)
  结论: I.radical.support = I.support
  证明: rfl
-/
lemma support_radical (I : IdealSheafData X) : I.radical.support = I.support := rfl

/--
Definition of `_root_.AlgebraicGeometry.Scheme.nilradical` / `_root_.AlgebraicGeometry.Scheme.nilradical` 的定义

English:
definition _root_.AlgebraicGeometry.Scheme.nilradical
  signature: (X : Scheme.{u})
  body: .radical ⊥

@[simp]

中文:
定义 _root_.AlgebraicGeometry.概形.nilradical
  签名: (X : 概形.{u})
  定义体: .radical ⊥

@[simp]

Depends on / 依赖: radical
-/
def _root_.AlgebraicGeometry.Scheme.nilradical (X : Scheme.{u}) : IdealSheafData X :=
  .radical ⊥

@[simp]
/--
lemma `_root_.AlgebraicGeometry.Scheme.support_nilradical` / 引理 `_root_.AlgebraicGeometry.Scheme.support_nilradical`

English:
lemma _root_.AlgebraicGeometry.Scheme.support_nilradical
  given: (X : Scheme.{u})
  proof: rfl

中文:
引理 _root_.AlgebraicGeometry.概形.support_nilradical
  条件: (X : 概形.{u})
  证明: rfl
-/
lemma _root_.AlgebraicGeometry.Scheme.support_nilradical (X : Scheme.{u}) :
    X.nilradical.support = ⊤ := rfl

/--
lemma `le_radical` / 引理 `le_radical`

English:
lemma le_radical
  statement: I <= I.radical
  proof: fun _ => Ideal.le_radical

@[simp]

中文:
引理 le_radical
  结论: I <= I.radical
  证明: fun _ => Ideal.le_radical

@[simp]

Depends on / 依赖: Ideal.le_radical, le_radical
-/
lemma le_radical : I <= I.radical := fun _ => Ideal.le_radical

@[simp]
/--
lemma `radical_top` / 引理 `radical_top`

English:
lemma radical_top
  statement: radical (X := X) ⊤ = ⊤
  proof: top_le_iff.mp (le_radical _)

中文:
引理 radical_top
  结论: radical (X := X) ⊤ = ⊤
  证明: top_le_iff.mp (le_radical _)

Depends on / 依赖: le_radical, top_le_iff, top_le_iff.mp
-/
lemma radical_top : radical (X := X) ⊤ = ⊤ := top_le_iff.mp (le_radical _)

/--
lemma `radical_bot` / 引理 `radical_bot`

English:
lemma radical_bot
  statement: radical ⊥ = nilradical X
  proof: rfl

中文:
引理 radical_bot
  结论: radical ⊥ = nilradical X
  证明: rfl
-/
lemma radical_bot : radical ⊥ = nilradical X := rfl

/--
lemma `radical_sup` / 引理 `radical_sup`

English:
lemma radical_sup
  given: {I J : IdealSheafData X}
  proof: by
  ext U : 2
  exact (Ideal.radical_sup (I.ideal U) (J.ideal U))

@[simp]

中文:
引理 radical_sup
  条件: {I J : IdealSheafData X}
  证明: by
  ext U : 2
  exact (Ideal.radical_sup (I.ideal U) (J.ideal U))

@[simp]

Depends on / 依赖: I.ideal, Ideal.radical_sup, J.ideal, radical_sup
-/
lemma radical_sup {I J : IdealSheafData X} :
    radical (I ⊔ J) = radical (radical I ⊔ radical J) := by
  ext U : 2
  exact (Ideal.radical_sup (I.ideal U) (J.ideal U))

@[simp]
/--
lemma `radical_inf` / 引理 `radical_inf`

English:
lemma radical_inf
  given: {I J : IdealSheafData X}
  proof: by
  ext U : 2
  simp only [radical_ideal, ideal_inf, Pi.inf_apply, Ideal.radical_inf]

@[simp]

中文:
引理 radical_inf
  条件: {I J : IdealSheafData X}
  证明: by
  ext U : 2
  simp only [radical_ideal, ideal_inf, Pi.inf_apply, Ideal.radical_inf]

@[simp]

Depends on / 依赖: Ideal.radical_inf, Pi.inf_apply, ideal_inf, inf_apply, radical_ideal, radical_inf
-/
lemma radical_inf {I J : IdealSheafData X} :
    radical (I ⊓ J) = radical I ⊓ radical J := by
  ext U : 2
  simp only [radical_ideal, ideal_inf, Pi.inf_apply, Ideal.radical_inf]

@[simp]
/--
lemma `radical_mul` / 引理 `radical_mul`

English:
lemma radical_mul
  given: {I J : IdealSheafData X}
  proof: by
  ext U : 2
  simp only [radical_ideal, ideal_mul, Pi.mul_apply, Ideal.radical_mul, ideal_inf, Pi.inf_apply]

中文:
引理 radical_mul
  条件: {I J : IdealSheafData X}
  证明: by
  ext U : 2
  simp only [radical_ideal, ideal_mul, Pi.mul_apply, Ideal.radical_mul, ideal_inf, Pi.inf_apply]

Depends on / 依赖: Ideal.radical_mul, Pi.inf_apply, Pi.mul_apply, ideal_inf, ideal_mul, inf_apply, mul_apply, radical_ideal, radical_mul
-/
lemma radical_mul {I J : IdealSheafData X} :
    radical (I * J) = radical I ⊓ radical J := by
  ext U : 2
  simp only [radical_ideal, ideal_mul, Pi.mul_apply, Ideal.radical_mul, ideal_inf, Pi.inf_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The vanishing ideal sheaf of a closed set,
which is the largest ideal sheaf whose support is equal to it.
The reduced induced scheme structure on the closed set is the quotient of this ideal. -/
@[simps! ideal coe_support]
noncomputable nonrec def vanishingIdeal (Z : Closeds X) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U => vanishingIdeal (U.2.fromSpec ⁻¹' Z))
    (fun U f => by
      let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        suffices forall p, (X.affineBasicOpen f).2.fromSpec p in Z -> F.hom x in p.asIdeal by
          simpa [PrimeSpectrum.mem_vanishingIdeal] using! this
        intro x hxZ
        refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx
          (Spec.map (X.presheaf.map (homOfLE _).op) x) ?_
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply,
          IsAffineOpen.map_fromSpec _ (X.affineBasicOpen f).2]
      · let : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) := F.hom.toAlgebra
        have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
          U.2.isLocalization_of_eq_basicOpen _ _ rfl
        intro x hx
        dsimp only at hx ⊢
        have : Topology.IsOpenEmbedding (Spec.map F) :=
          localization_away_isOpenEmbedding Γ(X, X.basicOpen f) f
        rw [← U.2.map_fromSpec (X.affineBasicOpen f).2 (homOfLE (X.basicOpen_le f)).op]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp] at hx
        generalize U.2.fromSpec ⁻¹' Z = Z' at hx ⊢
        replace hx : x in vanishingIdeal (Spec.map F ⁻¹' Z') := hx
        obtain ⟨I, hI, e⟩ :=
          (isClosed_iff_zeroLocus_radical_ideal _).mp (isClosed_closure (s := Z'))
        rw [← vanishingIdeal_closure]; rw [← this.isOpenMap.preimage_closure_eq_closure_preimage this.continuous]; rw [e] at hx
        rw [← vanishingIdeal_closure]; rw [e]
        erw [preimage_comap_zeroLocus] at hx
        rwa [← PrimeSpectrum.zeroLocus_span, ← Ideal.map, vanishingIdeal_zeroLocus_eq_radical,
          ← RingHom.algebraMap_toAlgebra (X.presheaf.map _).hom,
          ← IsLocalization.map_radical (.powers f), ← vanishingIdeal_zeroLocus_eq_radical] at hx)
    Z
    (fun U x hxU => by
      trans x in X.zeroLocus (U := U.1) (vanishingIdeal (U.2.fromSpec ⁻¹' Z)) inter U.1
      · rw [← U.2.fromSpec_image_zeroLocus, zeroLocus_vanishingIdeal_eq_closure,
          ← U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
            U.2.fromSpec.continuous,
          Set.image_preimage_eq_inter_range, Z.isClosed.closure_eq, IsAffineOpen.range_fromSpec]
        simp [hxU]
      · simp [hxU])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `le_support_iff_le_vanishingIdeal` / 引理 `le_support_iff_le_vanishingIdeal`

English:
lemma le_support_iff_le_vanishingIdeal
  given: {I : X.IdealSheafData} {Z : Closeds X}
  proof: by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans forall U : X.affineOpens, (Z : Set X) inter U subseteq I.support inter U
  · refine ⟨fun H U x hx => ⟨H hx.1, hx.2⟩, fun H x hx => ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis

中文:
引理 le_support_iff_le_vanishingIdeal
  条件: {I : X.IdealSheafData} {Z : Closeds X}
  证明: by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans forall U : X.affineOpens, (Z : Set X) inter U subseteq I.support inter U
  · refine ⟨fun H U x hx => ⟨H hx.1, hx.2⟩, fun H x hx => ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis

Depends on / 依赖: I.support, PrimeSpectrum, PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal, Set.image_subset_image_iff, Set.mem_univ, X.affineOpens, X.isBasis_affineOpens.exists_subset_of_mem_open, affineOpens, coe_support_inter, exists_subset_of_mem_open, forall_congr, fromSpec, fromSpec.isOpenEmbedding, image_subset_image_iff, isBasis_affineOpens, isOpenEmbedding, isOpen_univ, le_def, mem_univ, subset_zeroLocus_iff_le_vanishingIdeal
-/
lemma le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} :
    Z <= I.support ↔ I <= vanishingIdeal Z := by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans forall U : X.affineOpens, (Z : Set X) inter U subseteq I.support inter U
  · refine ⟨fun H U x hx => ⟨H hx.1, hx.2⟩, fun H x hx => ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (H ⟨U, hU⟩ ⟨hx, hxU⟩).1
  refine forall_congr' fun U => ?_
  rw [coe_support_inter]; rw [← Set.image_subset_image_iff U.2.fromSpec.isOpenEmbedding.injective]; rw [Set.image_preimage_eq_inter_range]; rw [IsAffineOpen.fromSpec_image_zeroLocus]; rw [IsAffineOpen.range_fromSpec]

/--
lemma `gc` / 引理 `gc`

English:
lemma gc
  statement: @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
  proof: fun _ _ => le_support_iff_le_vanishingIdeal

中文:
引理 gc
  结论: @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·)
  证明: fun _ _ => le_support_iff_le_vanishingIdeal

Depends on / 依赖: le_support_iff_le_vanishingIdeal
-/
lemma gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
  fun _ _ => le_support_iff_le_vanishingIdeal

/--
lemma `vanishingIdeal_antimono` / 引理 `vanishingIdeal_antimono`

English:
lemma vanishingIdeal_antimono
  given: {S T : Closeds X} (h : S <= T)
  statement: vanishingIdeal T <= vanishingIdeal S
  proof: gc.monotone_u h

中文:
引理 vanishingIdeal_antimono
  条件: {S T : Closeds X} (h : S <= T)
  结论: vanishingIdeal T <= vanishingIdeal S
  证明: gc.monotone_u h

Depends on / 依赖: gc.monotone_u, monotone_u
-/
lemma vanishingIdeal_antimono {S T : Closeds X} (h : S <= T) : vanishingIdeal T <= vanishingIdeal S :=
  gc.monotone_u h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `vanishingIdeal_support` / 引理 `vanishingIdeal_support`

English:
lemma vanishingIdeal_support
  given: {I : IdealSheafData X}
  proof: by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range]; rw [IsAffineOpen.range_fromSpec]; rw [IsAffineOpen.fromSpec_image_zeroLocus]; rw [coe_support_inter]

中文:
引理 vanishingIdeal_support
  条件: {I : IdealSheafData X}
  证明: by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range]; rw [IsAffineOpen.range_fromSpec]; rw [IsAffineOpen.fromSpec_image_zeroLocus]; rw [coe_support_inter]

Depends on / 依赖: IsAffineOpen, IsAffineOpen.fromSpec_image_zeroLocus, IsAffineOpen.range_fromSpec, Set.image_preimage_eq_inter_range, coe_support_inter, fromSpec, fromSpec.isOpenEmbedding.injective.image_injective, fromSpec_image_zeroLocus, image_injective, image_preimage_eq_inter_range, injective, isOpenEmbedding, range_fromSpec, vanishingIdeal_zeroLocus_eq_radical
-/
lemma vanishingIdeal_support {I : IdealSheafData X} :
    vanishingIdeal I.support = I.radical := by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range]; rw [IsAffineOpen.range_fromSpec]; rw [IsAffineOpen.fromSpec_image_zeroLocus]; rw [coe_support_inter]

/--
lemma `vanishingIdeal_bot` / 引理 `vanishingIdeal_bot`

English:
lemma vanishingIdeal_bot
  statement: vanishingIdeal (X := X) ⊥ = ⊤
  proof: gc.u_top

中文:
引理 vanishingIdeal_bot
  结论: vanishingIdeal (X := X) ⊥ = ⊤
  证明: gc.u_top
-/
@[simp] lemma vanishingIdeal_bot : vanishingIdeal (X := X) ⊥ = ⊤ := gc.u_top

/--
lemma `vanishingIdeal_top` / 引理 `vanishingIdeal_top`

English:
lemma vanishingIdeal_top
  statement: vanishingIdeal (X := X) ⊤ = X.nilradical
  proof: by
  rw [← support_bot]; rw [vanishingIdeal_support]; rw [nilradical]

中文:
引理 vanishingIdeal_top
  结论: vanishingIdeal (X := X) ⊤ = X.nilradical
  证明: by
  rw [← support_bot]; rw [vanishingIdeal_support]; rw [nilradical]
-/
@[simp] lemma vanishingIdeal_top : vanishingIdeal (X := X) ⊤ = X.nilradical := by
  rw [← support_bot]; rw [vanishingIdeal_support]; rw [nilradical]

/--
lemma `vanishingIdeal_iSup` / 引理 `vanishingIdeal_iSup`

English:
lemma vanishingIdeal_iSup
  given: {ι : Sort*} (Z : ι -> Closeds X)
  proof: gc.u_iInf

中文:
引理 vanishingIdeal_iSup
  条件: {ι : 类型层*} (Z : ι -> Closeds X)
  证明: gc.u_iInf
-/
@[simp] lemma vanishingIdeal_iSup {ι : Sort*} (Z : ι -> Closeds X) :
    vanishingIdeal (iSup Z) = ⨅ i, vanishingIdeal (Z i) := gc.u_iInf

/--
lemma `vanishingIdeal_sSup` / 引理 `vanishingIdeal_sSup`

English:
lemma vanishingIdeal_sSup
  given: (Z : Set (Closeds X))
  proof: gc.u_sInf

中文:
引理 vanishingIdeal_sSup
  条件: (Z : 集合 (Closeds X))
  证明: gc.u_sInf
-/
@[simp] lemma vanishingIdeal_sSup (Z : Set (Closeds X)) :
    vanishingIdeal (sSup Z) = ⨅ z in Z, vanishingIdeal z := gc.u_sInf

/--
lemma `vanishingIdeal_sup` / 引理 `vanishingIdeal_sup`

English:
lemma vanishingIdeal_sup
  given: (Z Z' : TopologicalSpace.Closeds X)
  proof: gc.u_inf

中文:
引理 vanishingIdeal_sup
  条件: (Z Z' : 拓扑空间.Closeds X)
  证明: gc.u_inf
-/
@[simp] lemma vanishingIdeal_sup (Z Z' : TopologicalSpace.Closeds X) :
    vanishingIdeal (Z ⊔ Z') = vanishingIdeal Z ⊓ vanishingIdeal Z' := gc.u_inf

/--
lemma `support_sup` / 引理 `support_sup`

English:
lemma support_sup
  given: (I J : X.IdealSheafData)
  proof: gc.l_sup

中文:
引理 support_sup
  条件: (I J : X.IdealSheafData)
  证明: gc.l_sup
-/
@[simp] lemma support_sup (I J : X.IdealSheafData) :
    (I ⊔ J).support = I.support ⊓ J.support := gc.l_sup

/--
lemma `support_iSup` / 引理 `support_iSup`

English:
lemma support_iSup
  given: {ι : Sort*} (I : ι -> X.IdealSheafData)
  proof: gc.l_iSup

中文:
引理 support_iSup
  条件: {ι : 类型层*} (I : ι -> X.IdealSheafData)
  证明: gc.l_iSup
-/
@[simp] lemma support_iSup {ι : Sort*} (I : ι -> X.IdealSheafData) :
    (iSup I).support = ⨅ i, (I i).support := gc.l_iSup

/--
lemma `support_sSup` / 引理 `support_sSup`

English:
lemma support_sSup
  given: (I : Set X.IdealSheafData)
  proof: gc.l_sSup

中文:
引理 support_sSup
  条件: (I : 集合 X.IdealSheafData)
  证明: gc.l_sSup
-/
@[simp] lemma support_sSup (I : Set X.IdealSheafData) :
    (sSup I).support = ⨅ i in I, i.support := gc.l_sSup

end ofIsClosed

end IdealSheafData

section IsReduced

/--
lemma `nilradical_eq_bot` / 引理 `nilradical_eq_bot`

English:
lemma nilradical_eq_bot
  given: [IsReduced X]
  statement: X.nilradical = ⊥
  proof: by
  ext; simp [nilradical, Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]

中文:
引理 nilradical_eq_bot
  条件: [是既约 X]
  结论: X.nilradical = ⊥
  证明: by
  ext; simp [nilradical, Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]

Depends on / 依赖: Ideal.isRadical_bot, Ideal.radical_eq_iff.mpr, isRadical_bot, nilradical, radical_eq_iff
-/
lemma nilradical_eq_bot [IsReduced X] : X.nilradical = ⊥ := by
  ext; simp [nilradical, Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]

/--
lemma `IdealSheafData.support_eq_top_iff` / 引理 `IdealSheafData.support_eq_top_iff`

English:
lemma IdealSheafData.support_eq_top_iff
  given: [IsReduced X] {I : X.IdealSheafData}
  proof: by
  rw [← top_le_iff]; rw [le_support_iff_le_vanishingIdeal]; rw [vanishingIdeal_top]; rw [nilradical_eq_bot]; rw [le_bot_iff]

中文:
引理 IdealSheafData.support_eq_top_iff
  条件: [是既约 X] {I : X.IdealSheafData}
  证明: by
  rw [← top_le_iff]; rw [le_support_iff_le_vanishingIdeal]; rw [vanishingIdeal_top]; rw [nilradical_eq_bot]; rw [le_bot_iff]

Depends on / 依赖: le_bot_iff, le_support_iff_le_vanishingIdeal, nilradical_eq_bot, top_le_iff, vanishingIdeal_top
-/
lemma IdealSheafData.support_eq_top_iff [IsReduced X] {I : X.IdealSheafData} :
    I.support = ⊤ ↔ I = ⊥ := by
  rw [← top_le_iff]; rw [le_support_iff_le_vanishingIdeal]; rw [vanishingIdeal_top]; rw [nilradical_eq_bot]; rw [le_bot_iff]

end IsReduced

section ker

open IdealSheafData

variable {Y Z : Scheme.{u}}

/--
Definition of `Hom.ker` / `Hom.ker` 的定义

English:
definition Hom.ker
  signature: (f : X.Hom Y)
  body: ofIdeals fun U => RingHom.ker (f.app U).hom

中文:
定义 态射.ker
  签名: (f : X.态射 Y)
  定义体: ofIdeals fun U => RingHom.ker (f.app U).hom

Depends on / 依赖: RingHom, RingHom.ker, f.app, ofIdeals
-/
def Hom.ker (f : X.Hom Y) : IdealSheafData Y :=
  ofIdeals fun U => RingHom.ker (f.app U).hom

/--
lemma `Hom.ideal_ker_le` / 引理 `Hom.ideal_ker_le`

English:
lemma Hom.ideal_ker_le
  given: (f : X.Hom Y) (U : Y.affineOpens)
  proof: ideal_ofIdeals_le _ _

中文:
引理 态射.ideal_ker_le
  条件: (f : X.态射 Y) (U : Y.affineOpens)
  证明: ideal_ofIdeals_le _ _

Depends on / 依赖: ideal_ofIdeals_le
-/
lemma Hom.ideal_ker_le (f : X.Hom Y) (U : Y.affineOpens) :
    f.ker.ideal U <= RingHom.ker (f.app U).hom :=
  ideal_ofIdeals_le _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Hom.ker_apply` / 引理 `Hom.ker_apply`

English:
lemma Hom.ker_apply
  given: (f : X.Hom Y) [QuasiCompact f] (U : Y.affineOpens)
  proof: by
  let I : IdealSheafData Y := ⟨fun U => RingHom.ker (f.app U).hom, ?_, _, rfl⟩
  · exact congr($(ofIdeals_ideal I).ideal U)
  intro U s
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    simp_rw [RingHom.comap_ker, ← CommRingCat.hom_comp, Scheme.affineBasicOpen_coe, f

中文:
引理 态射.ker_apply
  条件: (f : X.态射 Y) [拟紧 f] (U : Y.affineOpens)
  证明: by
  let I : IdealSheafData Y := ⟨fun U => RingHom.ker (f.app U).hom, ?_, _, rfl⟩
  · exact congr($(ofIdeals_ideal I).ideal U)
  intro U s
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    simp_rw [RingHom.comap_ker, ← CommRingCat.hom_comp, Scheme.affineBasicOpen_coe, f

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, Ideal.ker_le_comap, Ideal.map_le_iff_le_comap.mpr, IdealSheafData, IsLocalization, IsLocalization.exists_mk, RingHom, RingHom.comap_ker, RingHom.ker, Scheme, Scheme.affineBasicOpen_coe, affineBasicOpen_coe, comap_ker, exists_mk, f.app, f.naturality, hom_comp, isLocalization_basicOpen, ker_le_comap
-/
lemma Hom.ker_apply (f : X.Hom Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := by
  let I : IdealSheafData Y := ⟨fun U => RingHom.ker (f.app U).hom, ?_, _, rfl⟩
  · exact congr($(ofIdeals_ideal I).ideal U)
  intro U s
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    simp_rw [RingHom.comap_ker, ← CommRingCat.hom_comp, Scheme.affineBasicOpen_coe, f.naturality,
      CommRingCat.hom_comp, ← RingHom.comap_ker]
    exact Ideal.ker_le_comap _ hx
  · intro x hx
    have := U.2.isLocalization_basicOpen s
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    refine (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ?_
    suffices exists (V : X.Opens) (hV : V = X.basicOpen ((f.app U).hom s)),
        letI := hV.trans_le (X.basicOpen_le _); ((f.app U).hom x |_ V) = 0 by
      obtain ⟨_, rfl, H⟩ := this
      obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        X (U := f ⁻¹ᵁ U) (QuasiCompact.isCompact_preimage (f := f) _ U.1.2 U.2.isCompact)
        (f.app U x) (f.app U s) H
      exact ⟨_, ⟨n, rfl⟩, by simpa using hn⟩
    refine ⟨f ⁻¹ᵁ Y.basicOpen s, by simp, ?_⟩
    replace hx : (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op ≫ f.app _).hom x = 0 := by
      trans (f.app (Y.basicOpen s)).hom (algebraMap Γ(Y, U) _ x)
      · simp [-NatTrans.naturality, RingHom.algebraMap_toAlgebra]
      · simp only [Scheme.affineBasicOpen_coe, RingHom.mem_ker] at hx
        rw [← IsLocalization.mk'_spec' (M := .powers s)]; rw [map_mul]; rw [hx]; rw [mul_zero]
    rwa [f.naturality] at hx

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.le_ker_comp` / 引理 `Hom.le_ker_comp`

English:
lemma Hom.le_ker_comp
  given: (f : X ⟶ Y) (g : Y.Hom Z)
  statement: g.ker <= (f ≫ g).ker
  proof: by
  refine ofIdeals_mono fun U => ?_
  rw [Scheme.Hom.comp_app f g U]; rw [CommRingCat.hom_comp]; rw [← RingHom.comap_ker]
  exact Ideal.ker_le_comap _

中文:
引理 态射.le_ker_comp
  条件: (f : X ⟶ Y) (g : Y.态射 Z)
  结论: g.ker <= (f ≫ g).ker
  证明: by
  refine ofIdeals_mono fun U => ?_
  rw [Scheme.Hom.comp_app f g U]; rw [CommRingCat.hom_comp]; rw [← RingHom.comap_ker]
  exact Ideal.ker_le_comap _

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, Ideal.ker_le_comap, RingHom, RingHom.comap_ker, Scheme, Scheme.Hom.comp_app, comap_ker, comp_app, hom_comp, ker_le_comap, ofIdeals_mono
-/
lemma Hom.le_ker_comp (f : X ⟶ Y) (g : Y.Hom Z) : g.ker <= (f ≫ g).ker := by
  refine ofIdeals_mono fun U => ?_
  rw [Scheme.Hom.comp_app f g U]; rw [CommRingCat.hom_comp]; rw [← RingHom.comap_ker]
  exact Ideal.ker_le_comap _

/--
lemma `ker_eq_top_of_isEmpty` / 引理 `ker_eq_top_of_isEmpty`

English:
lemma ker_eq_top_of_isEmpty
  given: (f : X.Hom Y) [IsEmpty X]
  statement: f.ker = ⊤
  proof: top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ => by simpa using Subsingleton.elim _ _)

@[simp]

中文:
引理 ker_eq_top_of_isEmpty
  条件: (f : X.态射 Y) [是空 X]
  结论: f.ker = ⊤
  证明: top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ => by simpa using Subsingleton.elim _ _)

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, le_ofIdeals_iff, le_ofIdeals_iff.mpr, top_le_iff, top_le_iff.mp
-/
lemma ker_eq_top_of_isEmpty (f : X.Hom Y) [IsEmpty X] : f.ker = ⊤ :=
  top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ => by simpa using Subsingleton.elim _ _)

@[simp]
/--
lemma `Hom.ker_eq_bot_of_isIso` / 引理 `Hom.ker_eq_bot_of_isIso`

English:
lemma Hom.ker_eq_bot_of_isIso
  given: (f : X ⟶ Y) [IsIso f]
  statement: f.ker = ⊥
  proof: by
  ext U
  simp [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f.app U)).1]

中文:
引理 态射.ker_eq_bot_of_isIso
  条件: (f : X ⟶ Y) [是同构 f]
  结论: f.ker = ⊥
  证明: by
  ext U
  simp [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f.app U)).1]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.bijective_of_isIso, bijective_of_isIso, f.app, map_eq_zero_iff
-/
lemma Hom.ker_eq_bot_of_isIso (f : X ⟶ Y) [IsIso f] : f.ker = ⊥ := by
  ext U
  simp [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f.app U)).1]

/--
lemma `Hom.ker_comp_of_isIso` / 引理 `Hom.ker_comp_of_isIso`

English:
lemma Hom.ker_comp_of_isIso
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  statement: (f ≫ g).ker = g.ker
  proof: (f.le_ker_comp g).antisymm' (((inv f).le_ker_comp _).trans (by simp))

中文:
引理 态射.ker_comp_of_isIso
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [是同构 f]
  结论: (f ≫ g).ker = g.ker
  证明: (f.le_ker_comp g).antisymm' (((inv f).le_ker_comp _).trans (by simp))

Depends on / 依赖: antisymm, f.le_ker_comp, le_ker_comp
-/
lemma Hom.ker_comp_of_isIso (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : (f ≫ g).ker = g.ker :=
  (f.le_ker_comp g).antisymm' (((inv f).le_ker_comp _).trans (by simp))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ker_of_isAffine` / 引理 `ker_of_isAffine`

English:
lemma ker_of_isAffine
  given: {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
  proof: by
  refine (le_of_isAffine ((f.ideal_ker_le _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U => ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual

中文:
引理 ker_of_isAffine
  条件: {X Y : 概形} (f : X ⟶ Y) [是仿射 Y]
  证明: by
  refine (le_of_isAffine ((f.ideal_ker_le _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U => ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, Ideal.map_le_iff_le_comap, RingHom, RingHom.comap_ker, antisymm, comap_ker, contextual, f.ideal_ker_le, f.naturality, homOfLE_leOfHom, hom_comp, ideal_ker_le, le_ofIdeals_iff, le_ofIdeals_iff.mpr, le_of_isAffine, map_le_iff_le_comap, naturality, ofIdealTop_ideal
-/
lemma ker_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    f.ker = ofIdealTop (RingHom.ker f.appTop.hom) := by
  refine (le_of_isAffine ((f.ideal_ker_le _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U => ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual

/--
lemma `Hom.range_subset_ker_support` / 引理 `Hom.range_subset_ker_support`

English:
lemma Hom.range_subset_ker_support
  given: (f : X ⟶ Y)
  proof: by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ((coe_support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x in f ⁻¹ᵁ Y

中文:
引理 态射.range_subset_ker_support
  条件: (f : X ⟶ Y)
  证明: by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ((coe_support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x in f ⁻¹ᵁ Y

Depends on / 依赖: RingHom, RingHom.mem_ker.mp, Scheme, Scheme.basicOpen_zero, Scheme.mem_zeroLocus_iff, Scheme.preimage_basicOpen, Set.mem_univ, SetLike, SetLike.mem_coe, Y.basicOpen, Y.isBasis_affineOpens.exists_subset_of_mem_open, basicOpen, basicOpen_zero, coe_support_inter, exists_subset_of_mem_open, f.ideal_ker_le, f.ker, ideal_ker_le, isBasis_affineOpens, isOpen_univ
-/
lemma Hom.range_subset_ker_support (f : X ⟶ Y) :
    Set.range f subseteq f.ker.support := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ((coe_support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x in f ⁻¹ᵁ Y.basicOpen s := hxs
  rwa [Scheme.preimage_basicOpen, RingHom.mem_ker.mp (f.ideal_ker_le _ hs),
    Scheme.basicOpen_zero] at this

/--
lemma `Hom.ker_eq_top_iff_isEmpty` / 引理 `Hom.ker_eq_top_iff_isEmpty`

English:
lemma Hom.ker_eq_top_iff_isEmpty
  given: (f : X.Hom Y)
  statement: f.ker = ⊤ ↔ IsEmpty X
  proof: ⟨fun H => by simpa [H] using f.range_subset_ker_support, fun _ => ker_eq_top_of_isEmpty f⟩

中文:
引理 态射.ker_eq_top_iff_isEmpty
  条件: (f : X.态射 Y)
  结论: f.ker = ⊤ ↔ 是空 X
  证明: ⟨fun H => by simpa [H] using f.range_subset_ker_support, fun _ => ker_eq_top_of_isEmpty f⟩

Depends on / 依赖: f.range_subset_ker_support, ker_eq_top_of_isEmpty, range_subset_ker_support
-/
lemma Hom.ker_eq_top_iff_isEmpty (f : X.Hom Y) : f.ker = ⊤ ↔ IsEmpty X :=
  ⟨fun H => by simpa [H] using f.range_subset_ker_support, fun _ => ker_eq_top_of_isEmpty f⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Hom.iInf_ker_openCover_map_comp_apply` / 引理 `Hom.iInf_ker_openCover_map_comp_apply`

English:
lemma Hom.iInf_ker_openCover_map_comp_apply
  proof: by
  refine le_antisymm ?_ (le_iInf fun i => (𝒰.f i).le_ker_comp f U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, map_zero, exists_and_left]
  refine ⟨𝒰.f i ''ᵁ 𝒰.f i ⁻¹ᵁ f 

中文:
引理 态射.iInf_ker_openCover_map_comp_apply
  证明: by
  refine le_antisymm ?_ (le_iInf fun i => (𝒰.f i).le_ker_comp f U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, map_zero, exists_and_left]
  refine ⟨𝒰.f i ''ᵁ 𝒰.f i ⁻¹ᵁ f 

Depends on / 依赖: Hom.ker_apply, IsSheaf, Iso.commRingCatIsoToRingEquiv_t, RingEquiv, RingEquiv.coe_toRingHom, RingHom, RingHom.mem_ker, Set.image_preimage_subset, X.IsSheaf.section_ext, appIso, coe_toRingHom, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.injective, commRingCatIsoToRingEquiv_t, exists_and_left, exists_eq, homOfLE_leOfHom, image_preimage_subset, injective, ker_apply
-/
lemma Hom.iInf_ker_openCover_map_comp_apply
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) (U : Y.affineOpens) :
    ⨅ i, (𝒰.f i ≫ f).ker.ideal U = f.ker.ideal U := by
  refine le_antisymm ?_ (le_iInf fun i => (𝒰.f i).le_ker_comp f U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, map_zero, exists_and_left]
  refine ⟨𝒰.f i ''ᵁ 𝒰.f i ⁻¹ᵁ f ⁻¹ᵁ U.1, ⟨_, hxU, rfl⟩,
    Set.image_preimage_subset (𝒰.f i) (f ⁻¹ᵁ U), ?_⟩
  apply ((𝒰.f i).appIso _).commRingCatIsoToRingEquiv.injective
  rw [map_zero]; rw [← RingEquiv.coe_toRingHom]; rw [Iso.commRingCatIsoToRingEquiv_toRingHom]; rw [Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  simpa [Scheme.Hom.appLE] using! ideal_ker_le _ _ (Ideal.mem_iInf.mp hs i)

/--
lemma `Hom.iInf_ker_openCover_map_comp` / 引理 `Hom.iInf_ker_openCover_map_comp`

English:
lemma Hom.iInf_ker_openCover_map_comp
  given: (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover)
  proof: by
  refine le_antisymm ?_ (le_iInf fun i => (𝒰.f i).le_ker_comp f)
  refine iInf_le_iff.mpr fun I hI U => ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰]; rw [le_iInf_iff]
  exact fun i => hI i U

中文:
引理 态射.iInf_ker_openCover_map_comp
  条件: (f : X ⟶ Y) [拟紧 f] (𝒰 : X.OpenCover)
  证明: by
  refine le_antisymm ?_ (le_iInf fun i => (𝒰.f i).le_ker_comp f)
  refine iInf_le_iff.mpr fun I hI U => ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰]; rw [le_iInf_iff]
  exact fun i => hI i U

Depends on / 依赖: f.iInf_ker_openCover_map_comp_apply, iInf_ker_openCover_map_comp_apply, iInf_le_iff, iInf_le_iff.mpr, le_antisymm, le_iInf, le_iInf_iff, le_ker_comp
-/
lemma Hom.iInf_ker_openCover_map_comp (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover) :
    ⨅ i, (𝒰.f i ≫ f).ker = f.ker := by
  refine le_antisymm ?_ (le_iInf fun i => (𝒰.f i).le_ker_comp f)
  refine iInf_le_iff.mpr fun I hI U => ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰]; rw [le_iInf_iff]
  exact fun i => hI i U

/--
lemma `Hom.iUnion_support_ker_openCover_map_comp` / 引理 `Hom.iUnion_support_ker_openCover_map_comp`

English:
lemma Hom.iUnion_support_ker_openCover_map_comp
  proof: by
  cases isEmpty_or_nonempty 𝒰.I₀
  · have : IsEmpty X := Function.isEmpty 𝒰.idx
    simp [ker_eq_top_of_isEmpty]
  suffices forall U : Y.affineOpens,
      (⋃ i, (𝒰.f i ≫ f).ker.support) inter U = (f.ker.support inter U : Set Y) by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis

中文:
引理 态射.iUnion_support_ker_openCover_map_comp
  证明: by
  cases isEmpty_or_nonempty 𝒰.I₀
  · have : IsEmpty X := Function.isEmpty 𝒰.idx
    simp [ker_eq_top_of_isEmpty]
  suffices forall U : Y.affineOpens,
      (⋃ i, (𝒰.f i ≫ f).ker.support) inter U = (f.ker.support inter U : Set Y) by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis

Depends on / 依赖: Function, Function.isEmpty, IsEmpty, Scheme, Scheme.zeroLocus_iI, Set.iUnion_inter, Set.mem_univ, Y.affineOpens, Y.isBasis_affineOpens.exists_subset_of_mem_open, affineOpens, coe_support_inter, exists_subset_of_mem_open, f.iInf_ker_openCover_map_comp_apply, f.ker.support, iInf_ker_openCover_map_comp_apply, iUnion_inter, isBasis_affineOpens, isEmpty, isEmpty_or_nonempty, isOpen_univ
-/
lemma Hom.iUnion_support_ker_openCover_map_comp
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) [Finite 𝒰.I₀] :
    ⋃ i, ((𝒰.f i ≫ f).ker.support : Set Y) = f.ker.support := by
  cases isEmpty_or_nonempty 𝒰.I₀
  · have : IsEmpty X := Function.isEmpty 𝒰.idx
    simp [ker_eq_top_of_isEmpty]
  suffices forall U : Y.affineOpens,
      (⋃ i, (𝒰.f i ≫ f).ker.support) inter U = (f.ker.support inter U : Set Y) by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    simpa [hxU] using congr(x in $(this ⟨U, hU⟩))
  intro U
  simp only [Set.iUnion_inter, coe_support_inter, ← f.iInf_ker_openCover_map_comp_apply 𝒰,
    Scheme.zeroLocus_iInf_of_nonempty]

/--
lemma `ker_morphismRestrict_ideal` / 引理 `ker_morphismRestrict_ideal`

English:
lemma ker_morphismRestrict_ideal
  statement: (f : X.Hom Y) [QuasiCompact f]
  proof: by
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).1

中文:
引理 ker_morphismRestrict_ideal
  结论: (f : X.态射 Y) [拟紧 f]
  证明: by
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).1

Depends on / 依赖: ConcreteCategory, ConcreteCategory.bijective_of_isIso, Scheme, Scheme.Hom.appLE, X.presheaf.map, bijective_of_isIso, eqToHom, image_morphismRestrict_preimage, map_eq_zero_iff, presheaf
-/
lemma ker_morphismRestrict_ideal (f : X.Hom Y) [QuasiCompact f]
    (U : Y.Opens) (V : U.toScheme.affineOpens) :
    (f ∣_ U).ker.ideal V = f.ker.ideal ⟨U.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩ := by
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).1

/--
lemma `ker_ideal_of_isPullback_of_isOpenImmersion` / 引理 `ker_ideal_of_isPullback_of_isOpenImmersion`

English:
lemma ker_ideal_of_isPullback_of_isOpenImmersion
  statement: {X Y U V : Scheme.{u}}
  proof: by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback H inferInstance
  ext x
  have : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
  let e : Γ(X, 

中文:
引理 ker_ideal_of_isPullback_of_isOpenImmersion
  结论: {X Y U V : 概形.{u}}
  证明: by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback H inferInstance
  ext x
  have : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
  let e : Γ(X, 

Depends on / 依赖: Category, Category.assoc, H.flip, IsOpenImmersion, IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback, Iso.eq_comp_inv, Iso.inv_comp_eq, MorphismProperty, MorphismProperty.of_isPullback, QuasiCompact, X.presheaf.mapIso, appIso, e.inv, eqToIso, eq_comp_inv, f.app, iU.appIso, iV.appIso, image_preimage_eq_preimage_image_of_isPullback, inv_comp_eq
-/
lemma ker_ideal_of_isPullback_of_isOpenImmersion {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV]
    [QuasiCompact f] (H : IsPullback f' iU iV f) (W) :
    f'.ker.ideal W =
      (f.ker.ideal ⟨iV ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).comap (iV.appIso W).inv.hom := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback H inferInstance
  ext x
  have : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
  let e : Γ(X, f ⁻¹ᵁ iV ''ᵁ W) ≅ Γ(U, f' ⁻¹ᵁ W) :=
    X.presheaf.mapIso (eqToIso this).op ≪≫ iU.appIso _
  have : (iV.appIso W).inv ≫ f.app _ = f'.app W ≫ e.inv := by
    rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]
    simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, e, Scheme.Hom.appLE_comp_appLE, H.w]
  simp only [Scheme.Hom.ker_apply, RingHom.mem_ker, Ideal.mem_comap, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, this]
  simpa using (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv).1).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Hom.support_ker` / 引理 `Hom.support_ker`

English:
lemma Hom.support_ker
  given: (f : X ⟶ Y) [QuasiCompact f]
  proof: by
  apply subset_antisymm
  · wlog hY : exists S, Y = Spec S
    · intro x hx
      let 𝒰 := Y.affineCover
      obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
      have inst : QuasiCompact (𝒰.pullbackHom f i) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      have := this (𝒰.pullbackHom f i) ⟨

中文:
引理 态射.support_ker
  条件: (f : X ⟶ Y) [拟紧 f]
  证明: by
  apply subset_antisymm
  · wlog hY : exists S, Y = Spec S
    · intro x hx
      let 𝒰 := Y.affineCover
      obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
      have inst : QuasiCompact (𝒰.pullbackHom f i) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      have := this (𝒰.pullbackHom f i) ⟨

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, QuasiCompact, Set.mem_image_of_mem, Set.mem_univ, Set.range_comp, TopCat, TopCat.coe_comp, Y.affineCover, affineCover, coe_comp, coe_support_inter, continuous, exists_eq, image_closure_subset_closure_image, isAffineOpen_top, mem_image_of_mem, mem_univ, pullbackHom, pullback_snd
-/
lemma Hom.support_ker (f : X ⟶ Y) [QuasiCompact f] :
    f.ker.support = closure (Set.range f) := by
  apply subset_antisymm
  · wlog hY : exists S, Y = Spec S
    · intro x hx
      let 𝒰 := Y.affineCover
      obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
      have inst : QuasiCompact (𝒰.pullbackHom f i) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      have := this (𝒰.pullbackHom f i) ⟨_, rfl⟩
        ((coe_support_inter _ ⟨⊤, isAffineOpen_top _⟩).ge ⟨?_, Set.mem_univ x⟩).1
      · have := image_closure_subset_closure_image (f := 𝒰.f i)
          (𝒰.f i).continuous (Set.mem_image_of_mem _ this)
        rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [𝒰.pullbackHom_map] at this
        exact closure_mono (Set.range_comp_subset_range _ _) this
      · rw [← (𝒰.f i).isOpenEmbedding.injective.mem_set_image, Scheme.image_zeroLocus,
          ker_ideal_of_isPullback_of_isOpenImmersion f (𝒰.pullbackHom f i)
            ((𝒰.pullback₁ f).f i) (𝒰.f i),
          Ideal.coe_comap, Set.image_preimage_eq]
        · exact ⟨((coe_support_inter _ _).le ⟨hx, by simp⟩).1, ⟨_, rfl⟩⟩
        · exact (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso ⊤).inv).2
        · exact (IsPullback.of_hasPullback _ _).flip
    obtain ⟨S, rfl⟩ := hY
    wlog hX : exists R, X = Spec R generalizing X S
    · intro x hx
      have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
      let 𝒰 := X.affineCover.finiteSubcover
      obtain ⟨_, ⟨i, rfl⟩, hx⟩ := (f.iUnion_support_ker_openCover_map_comp 𝒰).ge hx
      have inst : QuasiCompact (𝒰.f i ≫ f) := HasAffineProperty.iff_of_isAffine.mpr
        (inferInstanceAs <| CompactSpace (Spec _))
      exact closure_mono (Set.range_comp_subset_range _ _) (this S (𝒰.f i ≫ f) ⟨_, rfl⟩ hx)
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    rw [ker_of_isAffine]; rw [coe_support_ofIdealTop]; rw [Spec_zeroLocus]; rw [← Ideal.coe_comap]; rw [RingHom.comap_ker]; rw [← PrimeSpectrum.closure_range_comap]; rw [← CommRingCat.hom_comp]; rw [← Scheme.ΓSpecIso_inv_naturality]
    simp only [CommRingCat.hom_comp, PrimeSpectrum.comap_comp]
    exact closure_mono (Set.range_comp_subset_range _ (Spec.map φ))
  · rw [(support _).isClosed.closure_subset_iff]
    exact f.range_subset_ker_support

/-- The functor taking a morphism into `Y` to its kernel as an ideal sheaf on `Y`. -/
@[simps]
/--
Definition of `kerFunctor` / `kerFunctor` 的定义

English:
definition kerFunctor
  signature: (Y : Scheme.{u})
  body: f.unop.hom.ker
map {f g} hfg := homOfLE by simpa only [Functor.id_obj, Functor.const_obj_obj,
    OrderDual.toDual_le_toDual, ← Over.w hfg.unop] using hfg.unop.left.le_ker_comp f.unop.hom
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

中文:
定义 kerFunctor
  签名: (Y : 概形.{u})
  定义体: f.unop.hom.ker
map {f g} hfg := homOfLE by simpa only [Functor.id_obj, Functor.const_obj_obj,
    OrderDual.toDual_le_toDual, ← Over.w hfg.unop] using hfg.unop.left.le_ker_comp f.unop.hom
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

Depends on / 依赖: f.unop.hom.ker
-/
def kerFunctor (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ IdealSheafData Y where
  obj f := f.unop.hom.ker
map {f g} hfg := homOfLE by simpa only [Functor.id_obj, Functor.const_obj_obj,
    OrderDual.toDual_le_toDual, ← Over.w hfg.unop] using hfg.unop.left.le_ker_comp f.unop.hom
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable (X) in
@[simp]
/--
lemma `ker_toSpecΓ` / 引理 `ker_toSpecΓ`

English:
lemma ker_toSpecΓ
  given: [CompactSpace X]
  statement: X.toSpecΓ.ker = ⊥
  proof: by
  apply IdealSheafData.ext_of_isAffine
  simpa using! RingHom.ker_coe_equiv (ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv

中文:
引理 ker_toSpecΓ
  条件: [紧空间 X]
  结论: X.toSpecΓ.ker = ⊥
  证明: by
  apply IdealSheafData.ext_of_isAffine
  simpa using! RingHom.ker_coe_equiv (ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv

Depends on / 依赖: IdealSheafData, IdealSheafData.ext_of_isAffine, RingHom, RingHom.ker_coe_equiv, commRingCatIsoToRingEquiv, ext_of_isAffine, ker_coe_equiv
-/
lemma ker_toSpecΓ [CompactSpace X] : X.toSpecΓ.ker = ⊥ := by
  apply IdealSheafData.ext_of_isAffine
  simpa using! RingHom.ker_coe_equiv (ΓSpecIso Γ(X, ⊤)).commRingCatIsoToRingEquiv

end ker

end Scheme

end AlgebraicGeometry
