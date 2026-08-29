/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Geometry.Convex.Cone.Basic


/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that, as a set, a pointed cone is a convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

variable {R E F G : Type*}

local notation3 "R>=0" => {c : R // 0 <= c}

/--
Definition of `PointedCone` / `PointedCone` 的定义

English:
abbreviation PointedCone
  signature: (R E)
  body: Submodule {c : R // 0 <= c} E

中文:
缩写 PointedCone
  签名: (R E)
  定义体: Submodule {c : R // 0 <= c} E

Depends on / 依赖: Submodule
-/
abbrev PointedCone (R E)
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] :=
  Submodule {c : R // 0 <= c} E

namespace PointedCone

open Function Submodule Pointwise

open scoped Pointwise

section Submodule

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C : PointedCone R E}

/--
Definition of `ofSubmodule` / `ofSubmodule` 的定义

English:
abbreviation ofSubmodule
  signature: (S : Submodule R E)
  body: S.restrictScalars _

中文:
缩写 ofSubmodule
  签名: (S : 子模 R E)
  定义体: S.restrictScalars _
-/
@[coe] abbrev ofSubmodule (S : Submodule R E) : PointedCone R E := S.restrictScalars _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Submodule R E) (PointedCone R E)
  body: ⟨ofSubmodule⟩

中文:
实例 :
  签名: Coe (子模 R E) (PointedCone R E)
  定义体: ⟨ofSubmodule⟩

Depends on / 依赖: ofSubmodule
-/
instance : Coe (Submodule R E) (PointedCone R E) := ⟨ofSubmodule⟩

/--
lemma `coe_ofSubmodule` / 引理 `coe_ofSubmodule`

English:
lemma coe_ofSubmodule
  given: (S : Submodule R E)
  statement: (ofSubmodule S : Set E) = S
  proof: rfl

中文:
引理 coe_ofSubmodule
  条件: (S : 子模 R E)
  结论: (ofSubmodule S : 集合 E) = S
  证明: rfl
-/
@[simp] lemma coe_ofSubmodule (S : Submodule R E) : (ofSubmodule S : Set E) = S := rfl

/--
lemma `mem_ofSubmodule_iff` / 引理 `mem_ofSubmodule_iff`

English:
lemma mem_ofSubmodule_iff
  given: {S : Submodule R E} {x : E}
  statement: x in (S : PointedCone R E) ↔ x in S
  proof: .rfl

中文:
引理 mem_ofSubmodule_iff
  条件: {S : 子模 R E} {x : E}
  结论: x in (S : PointedCone R E) ↔ x in S
  证明: .rfl
-/
lemma mem_ofSubmodule_iff {S : Submodule R E} {x : E} : x in (S : PointedCone R E) ↔ x in S := .rfl

/--
lemma `ofSubmodule_inj` / 引理 `ofSubmodule_inj`

English:
lemma ofSubmodule_inj
  given: {S T : Submodule R E}
  statement: ofSubmodule S = ofSubmodule T ↔ S = T
  proof: restrictScalars_inj ..

中文:
引理 ofSubmodule_inj
  条件: {S T : 子模 R E}
  结论: ofSubmodule S = ofSubmodule T ↔ S = T
  证明: restrictScalars_inj ..

Depends on / 依赖: restrictScalars_inj
-/
lemma ofSubmodule_inj {S T : Submodule R E} : ofSubmodule S = ofSubmodule T ↔ S = T :=
  restrictScalars_inj ..

/--
lemma `ofSubmodule_le_ofSubmodule` / 引理 `ofSubmodule_le_ofSubmodule`

English:
lemma ofSubmodule_le_ofSubmodule
  given: {S T : Submodule R E}
  statement: ofSubmodule S <= ofSubmodule T ↔ S <= T
  proof: .rfl

中文:
引理 ofSubmodule_le_ofSubmodule
  条件: {S T : 子模 R E}
  结论: ofSubmodule S <= ofSubmodule T ↔ S <= T
  证明: .rfl
-/
lemma ofSubmodule_le_ofSubmodule {S T : Submodule R E} : ofSubmodule S <= ofSubmodule T ↔ S <= T :=
  .rfl

/--
lemma `ofSubmodule_lt_ofSubmodule` / 引理 `ofSubmodule_lt_ofSubmodule`

English:
lemma ofSubmodule_lt_ofSubmodule
  given: {S T : Submodule R E}
  statement: ofSubmodule S < ofSubmodule T ↔ S < T
  proof: .rfl

中文:
引理 ofSubmodule_lt_ofSubmodule
  条件: {S T : 子模 R E}
  结论: ofSubmodule S < ofSubmodule T ↔ S < T
  证明: .rfl
-/
lemma ofSubmodule_lt_ofSubmodule {S T : Submodule R E} : ofSubmodule S < ofSubmodule T ↔ S < T :=
  .rfl

/--
Definition of `ofSubmoduleEmbedding` / `ofSubmoduleEmbedding` 的定义

English:
abbreviation ofSubmoduleEmbedding
  signature: : Submodule R E ↪o PointedCone R E
  body: restrictScalarsEmbedding ..

中文:
缩写 ofSubmoduleEmbedding
  签名: : 子模 R E ↪o PointedCone R E
  定义体: restrictScalarsEmbedding ..

Depends on / 依赖: restrictScalarsEmbedding
-/
abbrev ofSubmoduleEmbedding : Submodule R E ↪o PointedCone R E :=
  restrictScalarsEmbedding ..

/--
Definition of `ofSubmoduleLatticeHom` / `ofSubmoduleLatticeHom` 的定义

English:
abbreviation ofSubmoduleLatticeHom
  signature: : CompleteLatticeHom (Submodule R E) (PointedCone R E)
  body: restrictScalarsLatticeHom ..

中文:
缩写 ofSubmoduleLatticeHom
  签名: : 完备格态射 (子模 R E) (PointedCone R E)
  定义体: restrictScalarsLatticeHom ..

Depends on / 依赖: restrictScalarsLatticeHom
-/
abbrev ofSubmoduleLatticeHom : CompleteLatticeHom (Submodule R E) (PointedCone R E) :=
  restrictScalarsLatticeHom ..

/--
lemma `ofSubmodule_inf` / 引理 `ofSubmodule_inf`

English:
lemma ofSubmodule_inf
  given: (S T : Submodule R E)
  statement: S ⊓ T = (S ⊓ T : PointedCone R E)
  proof: restrictScalars_inf _ _ _

中文:
引理 ofSubmodule_inf
  条件: (S T : 子模 R E)
  结论: S ⊓ T = (S ⊓ T : PointedCone R E)
  证明: restrictScalars_inf _ _ _

Depends on / 依赖: restrictScalars_inf
-/
lemma ofSubmodule_inf (S T : Submodule R E) : S ⊓ T = (S ⊓ T : PointedCone R E) :=
  restrictScalars_inf _ _ _

/--
lemma `ofSubmodule_sup` / 引理 `ofSubmodule_sup`

English:
lemma ofSubmodule_sup
  given: (S T : Submodule R E)
  statement: S ⊔ T = (S ⊔ T : PointedCone R E)
  proof: restrictScalars_sup _ _ _

中文:
引理 ofSubmodule_sup
  条件: (S T : 子模 R E)
  结论: S ⊔ T = (S ⊔ T : PointedCone R E)
  证明: restrictScalars_sup _ _ _

Depends on / 依赖: restrictScalars_sup
-/
lemma ofSubmodule_sup (S T : Submodule R E) : S ⊔ T = (S ⊔ T : PointedCone R E) :=
  restrictScalars_sup _ _ _

/--
lemma `ofSubmodule_sInf` / 引理 `ofSubmodule_sInf`

English:
lemma ofSubmodule_sInf
  given: (s : Set (Submodule R E))
  statement: sInf s = sInf (ofSubmodule '' s)
  proof: ofSubmoduleLatticeHom.map_sInf' s

中文:
引理 ofSubmodule_sInf
  条件: (s : 集合 (子模 R E))
  结论: sInf s = sInf (ofSubmodule '' s)
  证明: ofSubmoduleLatticeHom.map_sInf' s

Depends on / 依赖: map_sInf, ofSubmoduleLatticeHom, ofSubmoduleLatticeHom.map_sInf
-/
lemma ofSubmodule_sInf (s : Set (Submodule R E)) : sInf s = sInf (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sInf' s

/--
lemma `ofSubmodule_iInf` / 引理 `ofSubmodule_iInf`

English:
lemma ofSubmodule_iInf
  given: (s : Set (Submodule R E))
  statement: ⨅ S in s, S = ⨅ S in s, (S : PointedCone R E)
  proof: by
  rw [← sInf_eq_iInf]; rw [ofSubmodule_sInf]; rw [sInf_eq_iInf]; rw [iInf_image]

中文:
引理 ofSubmodule_iInf
  条件: (s : 集合 (子模 R E))
  结论: ⨅ S in s, S = ⨅ S in s, (S : PointedCone R E)
  证明: by
  rw [← sInf_eq_iInf]; rw [ofSubmodule_sInf]; rw [sInf_eq_iInf]; rw [iInf_image]

Depends on / 依赖: iInf_image, ofSubmodule_sInf, sInf_eq_iInf
-/
lemma ofSubmodule_iInf (s : Set (Submodule R E)) : ⨅ S in s, S = ⨅ S in s, (S : PointedCone R E) := by
  rw [← sInf_eq_iInf]; rw [ofSubmodule_sInf]; rw [sInf_eq_iInf]; rw [iInf_image]

/--
lemma `ofSubmodule_sSup` / 引理 `ofSubmodule_sSup`

English:
lemma ofSubmodule_sSup
  given: (s : Set (Submodule R E))
  statement: sSup s = sSup (ofSubmodule '' s)
  proof: ofSubmoduleLatticeHom.map_sSup' s

中文:
引理 ofSubmodule_sSup
  条件: (s : 集合 (子模 R E))
  结论: sSup s = sSup (ofSubmodule '' s)
  证明: ofSubmoduleLatticeHom.map_sSup' s

Depends on / 依赖: map_sSup, ofSubmoduleLatticeHom, ofSubmoduleLatticeHom.map_sSup
-/
lemma ofSubmodule_sSup (s : Set (Submodule R E)) : sSup s = sSup (ofSubmodule '' s) :=
  ofSubmoduleLatticeHom.map_sSup' s

/--
lemma `ofSubmodule_iSup` / 引理 `ofSubmodule_iSup`

English:
lemma ofSubmodule_iSup
  given: (s : Set (Submodule R E))
  statement: ⨆ S in s, S = ⨆ S in s, (S : PointedCone R E)
  proof: by
  rw [← sSup_eq_iSup]; rw [ofSubmodule_sSup]; rw [sSup_eq_iSup]; rw [iSup_image]

中文:
引理 ofSubmodule_iSup
  条件: (s : 集合 (子模 R E))
  结论: ⨆ S in s, S = ⨆ S in s, (S : PointedCone R E)
  证明: by
  rw [← sSup_eq_iSup]; rw [ofSubmodule_sSup]; rw [sSup_eq_iSup]; rw [iSup_image]

Depends on / 依赖: iSup_image, ofSubmodule_sSup, sSup_eq_iSup
-/
lemma ofSubmodule_iSup (s : Set (Submodule R E)) : ⨆ S in s, S = ⨆ S in s, (S : PointedCone R E) := by
  rw [← sSup_eq_iSup]; rw [ofSubmodule_sSup]; rw [sSup_eq_iSup]; rw [iSup_image]

variable {R E : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/--
lemma `neg_ofSubmodule` / 引理 `neg_ofSubmodule`

English:
lemma neg_ofSubmodule
  given: (S : Submodule R E)
  statement: -(ofSubmodule S) = ofSubmodule (-S)
  proof: neg_restrictScalars S

中文:
引理 neg_ofSubmodule
  条件: (S : 子模 R E)
  结论: -(ofSubmodule S) = ofSubmodule (-S)
  证明: neg_restrictScalars S

Depends on / 依赖: neg_restrictScalars
-/
lemma neg_ofSubmodule (S : Submodule R E) : -(ofSubmodule S) = ofSubmodule (-S) :=
  neg_restrictScalars S

end Submodule

section ConvexCone

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C C₁ C₂ : PointedCone R E} {x : E} {r : R}

/-- Every pointed cone is a convex cone. -/
@[coe]
/--
Definition of `toConvexCone` / `toConvexCone` 的定义

English:
definition toConvexCone
  signature: (C : PointedCone R E)
  body: C
  smul_mem' c hc _ hx := C.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := C.add_mem hx hy

中文:
定义 toConvexCone
  签名: (C : PointedCone R E)
  定义体: C
  smul_mem' c hc _ hx := C.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := C.add_mem hx hy
-/
def toConvexCone (C : PointedCone R E) : ConvexCone R E where
  carrier := C
  smul_mem' c hc _ hx := C.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' _ hx _ hy := C.add_mem hx hy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (PointedCone R E) (ConvexCone R E)
  body: toConvexCone

中文:
实例 :
  签名: Coe (PointedCone R E) (余nvexCone R E)
  定义体: toConvexCone

Depends on / 依赖: toConvexCone
-/
instance : Coe (PointedCone R E) (ConvexCone R E) where
  coe := toConvexCone

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toConvexCone_injective` / 定理 `toConvexCone_injective`

English:
theorem toConvexCone_injective
  statement: Injective ((↑) : PointedCone R E -> ConvexCone R E)
  proof: fun _ _ => by simp [toConvexCone]

中文:
定理 toConvexCone_injective
  结论: 单射 ((↑) : PointedCone R E -> 余nvexCone R E)
  证明: fun _ _ => by simp [toConvexCone]

Depends on / 依赖: toConvexCone
-/
theorem toConvexCone_injective : Injective ((↑) : PointedCone R E -> ConvexCone R E) :=
  fun _ _ => by simp [toConvexCone]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pointed_toConvexCone` / 定理 `pointed_toConvexCone`

English:
theorem pointed_toConvexCone
  given: (C : PointedCone R E)
  statement: (C : ConvexCone R E).Pointed
  proof: by
  simp [toConvexCone, ConvexCone.Pointed]

中文:
定理 pointed_toConvexCone
  条件: (C : PointedCone R E)
  结论: (C : 余nvexCone R E).Pointed
  证明: by
  simp [toConvexCone, ConvexCone.Pointed]

Depends on / 依赖: ConvexCone, ConvexCone.Pointed, Pointed, toConvexCone
-/
theorem pointed_toConvexCone (C : PointedCone R E) : (C : ConvexCone R E).Pointed := by
  simp [toConvexCone, ConvexCone.Pointed]

/--
lemma `mem_toConvexCone` / 引理 `mem_toConvexCone`

English:
lemma mem_toConvexCone
  statement: x in C.toConvexCone ↔ x in C
  proof: .rfl

中文:
引理 mem_toConvexCone
  结论: x in C.toConvexCone ↔ x in C
  证明: .rfl
-/
@[simp] lemma mem_toConvexCone : x in C.toConvexCone ↔ x in C := .rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (h : forall x, x in C₁ ↔ x in C₂)
  statement: C₁ = C₂
  proof: SetLike.ext h

中文:
引理 ext
  条件: (h : 对任意 x, x in C₁ ↔ x in C₂)
  结论: C₁ = C₂
  证明: SetLike.ext h
-/
@[ext] lemma ext (h : forall x, x in C₁ ↔ x in C₂) : C₁ = C₂ := SetLike.ext h

/--
lemma `convex` / 引理 `convex`

English:
lemma convex
  given: (C : PointedCone R E)
  statement: Convex R (C : Set E)
  proof: C.toConvexCone.convex

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 <= r) (hx : x in C) : r • x in C :=
  C.smul_mem ⟨r, hr⟩ hx

中文:
引理 convex
  条件: (C : PointedCone R E)
  结论: 凸 R (C : 集合 E)
  证明: C.toConvexCone.convex

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 <= r) (hx : x in C) : r • x in C :=
  C.smul_mem ⟨r, hr⟩ hx

Depends on / 依赖: C.toConvexCone.convex, convex, toConvexCone
-/
lemma convex (C : PointedCone R E) : Convex R (C : Set E) := C.toConvexCone.convex

@[aesop 90% (rule_sets := [SetLike])]
nonrec lemma smul_mem (C : PointedCone R E) (hr : 0 <= r) (hx : x in C) : r • x in C :=
  C.smul_mem ⟨r, hr⟩ hx

/--
lemma `smul_mem_iff` / 引理 `smul_mem_iff`

English:
lemma smul_mem_iff
  statement: {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc).le h, C.smul_mem hc.le⟩

中文:
引理 smul_mem_iff
  结论: {𝕜 M : 类型} [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc).le h, C.smul_mem hc.le⟩

Depends on / 依赖: C.smul_mem, hc.le, hc.ne, inv_pos, smul_mem
-/
lemma smul_mem_iff {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid M] [Module 𝕜 M] (C : PointedCone 𝕜 M)
    {c : 𝕜} (hc : 0 < c) {x : M} : c • x in C ↔ x in C :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc).le h, C.smul_mem hc.le⟩

/--
Definition of `_root_.ConvexCone.toPointedCone` / `_root_.ConvexCone.toPointedCone` 的定义

English:
definition _root_.ConvexCone.toPointedCone
  signature: (C : ConvexCone R E) (hC : C.Pointed)
  body: C
  add_mem' hx hy := C.add_mem hx hy
  zero_mem' := hC
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hC
      convert! hC
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert! hpo

中文:
定义 _root_.余nvexCone.toPointedCone
  签名: (C : 余nvexCone R E) (hC : C.Pointed)
  定义体: C
  add_mem' hx hy := C.add_mem hx hy
  zero_mem' := hC
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hC
      convert! hC
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert! hpo

Depends on / 依赖: Matrix, Matrix.toLin, _mul
-/
def _root_.ConvexCone.toPointedCone (C : ConvexCone R E) (hC : C.Pointed) : PointedCone R E where
  carrier := C
  add_mem' hx hy := C.add_mem hx hy
  zero_mem' := hC
  smul_mem' := fun ⟨c, hc⟩ x hx => by
    simp_rw [SetLike.mem_coe]
    rcases eq_or_lt_of_le hc with hzero | hpos
    · unfold ConvexCone.Pointed at hC
      convert! hC
      simp [← hzero]
    · apply ConvexCone.smul_mem
      · convert! hpos
      · exact hx

@[simp]
/--
lemma `_root_.ConvexCone.mem_toPointedCone` / 引理 `_root_.ConvexCone.mem_toPointedCone`

English:
lemma _root_.ConvexCone.mem_toPointedCone
  given: {C : ConvexCone R E} (hC : C.Pointed) (x : E)
  proof: Iff.rfl

@[simp, norm_cast]

中文:
引理 _root_.余nvexCone.mem_toPointedCone
  条件: {C : 余nvexCone R E} (hC : C.Pointed) (x : E)
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl, Matrix, Matrix.toLin, _one
-/
lemma _root_.ConvexCone.mem_toPointedCone {C : ConvexCone R E} (hC : C.Pointed) (x : E) :
    x in C.toPointedCone hC ↔ x in C :=
  Iff.rfl

@[simp, norm_cast]
/--
lemma `_root_.ConvexCone.coe_toPointedCone` / 引理 `_root_.ConvexCone.coe_toPointedCone`

English:
lemma _root_.ConvexCone.coe_toPointedCone
  given: (C : ConvexCone R E) (hC : C.Pointed)
  proof: rfl

@[simp]

中文:
引理 _root_.余nvexCone.coe_toPointedCone
  条件: (C : 余nvexCone R E) (hC : C.Pointed)
  证明: rfl

@[simp]
-/
lemma _root_.ConvexCone.coe_toPointedCone (C : ConvexCone R E) (hC : C.Pointed) :
    C.toPointedCone hC = C :=
  rfl

@[simp]
/--
lemma `_root_.ConvexCone.toPointedCone_top` / 引理 `_root_.ConvexCone.toPointedCone_top`

English:
lemma _root_.ConvexCone.toPointedCone_top
  statement: (⊤ : ConvexCone R E).toPointedCone trivial = ⊤
  proof: rfl

中文:
引理 _root_.余nvexCone.toPointedCone_top
  结论: (⊤ : 余nvexCone R E).toPointedCone trivial = ⊤
  证明: rfl
-/
lemma _root_.ConvexCone.toPointedCone_top : (⊤ : ConvexCone R E).toPointedCone trivial = ⊤ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (ConvexCone R E) (PointedCone R E) (↑) ConvexCone.Pointed
  body: ⟨C.toPointedCone hC, rfl⟩

中文:
实例 :
  签名: CanLift (余nvexCone R E) (PointedCone R E) (↑) 余nvexCone.Pointed
  定义体: ⟨C.toPointedCone hC, rfl⟩

Depends on / 依赖: C.toPointedCone, toPointedCone
-/
instance : CanLift (ConvexCone R E) (PointedCone R E) (↑) ConvexCone.Pointed where
  prf C hC := ⟨C.toPointedCone hC, rfl⟩

end ConvexCone

section Definitions

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]
variable {C : PointedCone R E} {x : E}

/-- Construct a pointed cone from closure under two-element conical combinations.
I.e., a nonempty set closed under two-element conical combinations is a pointed cone. -/
@[simps!]
/--
Definition of `ofConeComb` / `ofConeComb` 的定义

English:
definition ofConeComb
  signature: (C : Set E) (nonempty : C.Nonempty)
  body: .ofLinearComb C nonempty fun x hx y hy ⟨a, ha⟩ ⟨b, hb⟩ => coneComb x hx y hy a ha b hb

中文:
定义 ofConeComb
  签名: (C : 集合 E) (nonempty : C.非空)
  定义体: .ofLinearComb C nonempty fun x hx y hy ⟨a, ha⟩ ⟨b, hb⟩ => coneComb x hx y hy a ha b hb

Depends on / 依赖: coneComb, nonempty, ofLinearComb
-/
def ofConeComb (C : Set E) (nonempty : C.Nonempty)
    (coneComb : forall x in C, forall y in C, forall a : R, 0 <= a -> forall b : R, 0 <= b -> a • x + b • y in C) :
    PointedCone R E :=
  .ofLinearComb C nonempty fun x hx y hy ⟨a, ha⟩ ⟨b, hb⟩ => coneComb x hx y hy a ha b hb

variable (R) in
/--
Definition of `hull` / `hull` 的定义

English:
abbreviation hull
  signature: (s : Set E)
  body: span R>=0 s

中文:
缩写 hull
  签名: (s : 集合 E)
  定义体: span R>=0 s
-/
abbrev hull (s : Set E) : PointedCone R E := span R>=0 s

/--
lemma `subset_hull` / 引理 `subset_hull`

English:
lemma subset_hull
  given: {s : Set E}
  statement: s subseteq PointedCone.hull R s
  proof: subset_span

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias subset_span := subset_hull

中文:
引理 subset_hull
  条件: {s : 集合 E}
  结论: s subseteq PointedCone.hull R s
  证明: subset_span

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias subset_span := subset_hull

Depends on / 依赖: subset_span
-/
lemma subset_hull {s : Set E} : s subseteq PointedCone.hull R s := subset_span

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias subset_span := subset_hull

variable (R) in
/--
lemma `hull_le_span` / 引理 `hull_le_span`

English:
lemma hull_le_span
  given: (s : Set E)
  statement: hull R s <= span R s
  proof: span_le_restrictScalars R>=0 R s

中文:
引理 hull_le_span
  条件: (s : 集合 E)
  结论: hull R s <= span R s
  证明: span_le_restrictScalars R>=0 R s

Depends on / 依赖: span_le_restrictScalars
-/
lemma hull_le_span (s : Set E) : hull R s <= span R s := span_le_restrictScalars R>=0 R s

/--
lemma `mem_hull_set` / 引理 `mem_hull_set`

English:
lemma mem_hull_set
  given: {s : Set E}
  statement: x in hull R s ↔
  proof: by
  rw [mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y => (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y => ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩

@[deprecated "`PointedCone.span` was renamed to

中文:
引理 mem_hull_set
  条件: {s : 集合 E}
  结论: x in hull R s ↔
  证明: by
  rw [mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y => (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y => ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩

@[deprecated "`PointedCone.span` was renamed to

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_inj, c.support, mem_span_set, support, val_inj
-/
lemma mem_hull_set {s : Set E} : x in hull R s ↔
      exists c : E ->₀ R, ↑c.support subseteq s ∧ (forall y, 0 <= c y) ∧ c.sum (fun m r => r • m) = x := by
  rw [mem_span_set]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.support, Subtype.val ∘ c, by simp [← Subtype.val_inj]⟩, hc, fun y => (c y).2, rfl⟩
  · rintro ⟨c, hc, hc₀, rfl⟩
    exact ⟨⟨c.support, fun y => ⟨c y, hc₀ _⟩, by simp⟩, hc, rfl⟩

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias mem_span_set := mem_hull_set

end Definitions

section Maps

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]
variable [AddCommMonoid G] [Module R G]

/-!

## Maps between pointed cones

There is already a definition of maps between submodules, `Submodule.map`. In our case, these maps
are induced from linear maps between the ambient modules that are linear over nonnegative scalars.
Such maps are unlikely to be of any use in practice. So, we construct some API to define maps
between pointed cones induced from linear maps between the ambient modules that are linear over
*all* scalars.

-/

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : E ->ₗ[R] F) (C : PointedCone R E)
  body: Submodule.map (f : E ->ₗ[R>=0] F) C

@[simp, norm_cast]

中文:
定义 map
  签名: (f : E ->ₗ[R] F) (C : PointedCone R E)
  定义体: Submodule.map (f : E ->ₗ[R>=0] F) C

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.map
-/
def map (f : E ->ₗ[R] F) (C : PointedCone R E) : PointedCone R F :=
  Submodule.map (f : E ->ₗ[R>=0] F) C

@[simp, norm_cast]
/--
theorem `toConvexCone_map` / 定理 `toConvexCone_map`

English:
theorem toConvexCone_map
  given: (C : PointedCone R E) (f : E ->ₗ[R] F)
  proof: rfl

@[simp, norm_cast]

中文:
定理 toConvexCone_map
  条件: (C : PointedCone R E) (f : E ->ₗ[R] F)
  证明: rfl

@[simp, norm_cast]
-/
theorem toConvexCone_map (C : PointedCone R E) (f : E ->ₗ[R] F) :
    (C.map f : ConvexCone R F) = (C : ConvexCone R E).map f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (C : PointedCone R E) (f : E ->ₗ[R] F)
  statement: (C.map f : Set F) = f '' C
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (C : PointedCone R E) (f : E ->ₗ[R] F)
  结论: (C.map f : 集合 F) = f '' C
  证明: rfl

@[simp]
-/
theorem coe_map (C : PointedCone R E) (f : E ->ₗ[R] F) : (C.map f : Set F) = f '' C :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : E ->ₗ[R] F} {C : PointedCone R E} {y : F}
  statement: y in C.map f ↔ exists x in C, f x = y
  proof: Iff.rfl

中文:
定理 mem_map
  条件: {f : E ->ₗ[R] F} {C : PointedCone R E} {y : F}
  结论: y in C.map f ↔ 存在 x in C, f x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : E ->ₗ[R] F} {C : PointedCone R E} {y : F} : y in C.map f ↔ exists x in C, f x = y :=
  Iff.rfl

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R E)
  proof: SetLike.coe_injective Set.image_image g f C

@[simp]

中文:
定理 map_map
  条件: (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R E)
  证明: SetLike.coe_injective Set.image_image g f C

@[simp]

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R E) :
    (C.map f).map g = C.map (g.comp f) :=
SetLike.coe_injective Set.image_image g f C

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (C : PointedCone R E)
  statement: C.map LinearMap.id = C
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  条件: (C : PointedCone R E)
  结论: C.map 线性映射.id = C
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (C : PointedCone R E) : C.map LinearMap.id = C :=
SetLike.coe_injective Set.image_id _

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : E ->ₗ[R] F) (C : PointedCone R F)
  body: Submodule.comap (f : E ->ₗ[R>=0] F) C

@[simp, norm_cast]

中文:
定义 comap
  签名: (f : E ->ₗ[R] F) (C : PointedCone R F)
  定义体: Submodule.comap (f : E ->ₗ[R>=0] F) C

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.comap
-/
def comap (f : E ->ₗ[R] F) (C : PointedCone R F) : PointedCone R E :=
  Submodule.comap (f : E ->ₗ[R>=0] F) C

@[simp, norm_cast]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (f : E ->ₗ[R] F) (C : PointedCone R F)
  statement: (C.comap f : Set E) = f ⁻¹' C
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (f : E ->ₗ[R] F) (C : PointedCone R F)
  结论: (C.comap f : 集合 E) = f ⁻¹' C
  证明: rfl

@[simp]
-/
theorem coe_comap (f : E ->ₗ[R] F) (C : PointedCone R F) : (C.comap f : Set E) = f ⁻¹' C :=
  rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (C : PointedCone R E)
  statement: C.comap LinearMap.id = C
  proof: rfl

中文:
定理 comap_id
  条件: (C : PointedCone R E)
  结论: C.comap 线性映射.id = C
  证明: rfl
-/
theorem comap_id (C : PointedCone R E) : C.comap LinearMap.id = C :=
  rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R G)
  proof: rfl

@[simp]

中文:
定理 comap_comap
  条件: (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R G)
  证明: rfl

@[simp]
-/
theorem comap_comap (g : F ->ₗ[R] G) (f : E ->ₗ[R] F) (C : PointedCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {f : E ->ₗ[R] F} {C : PointedCone R F} {x : E}
  statement: x in C.comap f ↔ f x in C
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {f : E ->ₗ[R] F} {C : PointedCone R F} {x : E}
  结论: x in C.comap f ↔ f x in C
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {f : E ->ₗ[R] F} {C : PointedCone R F} {x : E} : x in C.comap f ↔ f x in C :=
  Iff.rfl

end Maps

section PositiveCone

variable (R E)
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]

/-- The positive cone is the pointed cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
/--
Definition of `positive` / `positive` 的定义

English:
definition positive
  signature: : PointedCone R E where
  body: AddSubmonoid.nonneg E
  smul_mem' c _ hx := by simpa using smul_nonneg c.property hx

@[simp]

中文:
定义 positive
  签名: : PointedCone R E where
  定义体: AddSubmonoid.nonneg E
  smul_mem' c _ hx := by simpa using smul_nonneg c.property hx

@[simp]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.nonneg, nonneg
-/
def positive : PointedCone R E where
  __ := AddSubmonoid.nonneg E
  smul_mem' c _ hx := by simpa using smul_nonneg c.property hx

@[simp]
/--
theorem `mem_positive` / 定理 `mem_positive`

English:
theorem mem_positive
  given: {x : E}
  statement: x in positive R E ↔ 0 <= x
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_positive
  条件: {x : E}
  结论: x in positive R E ↔ 0 <= x
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_positive {x : E} : x in positive R E ↔ 0 <= x :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `toConvexCone_positive` / 定理 `toConvexCone_positive`

English:
theorem toConvexCone_positive
  statement: ↑(positive R E) = ConvexCone.positive R E
  proof: rfl

中文:
定理 toConvexCone_positive
  结论: ↑(positive R E) = 余nvexCone.positive R E
  证明: rfl
-/
theorem toConvexCone_positive : ↑(positive R E) = ConvexCone.positive R E :=
  rfl

end PositiveCone

section AddCommGroup

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/--
lemma `sup_inf_assoc_of_le_submodule` / 引理 `sup_inf_assoc_of_le_submodule`

English:
lemma sup_inf_assoc_of_le_submodule
  statement: {C : PointedCone R E} (D : PointedCone R E)
  proof: sup_inf_assoc_of_le_of_neg_le _ hCS (by simpa [Submodule.neg_le])

中文:
引理 sup_inf_assoc_of_le_submodule
  结论: {C : PointedCone R E} (D : PointedCone R E)
  证明: sup_inf_assoc_of_le_of_neg_le _ hCS (by simpa [Submodule.neg_le])

Depends on / 依赖: Submodule, Submodule.neg_le, neg_le, sup_inf_assoc_of_le_of_neg_le
-/
lemma sup_inf_assoc_of_le_submodule {C : PointedCone R E} (D : PointedCone R E)
    {S : Submodule R E} (hCS : C <= S) : (C ⊔ D) ⊓ S = C ⊔ (D ⊓ S) :=
  sup_inf_assoc_of_le_of_neg_le _ hCS (by simpa [Submodule.neg_le])

/--
lemma `inf_sup_assoc_of_le_of_submodule_le` / 引理 `inf_sup_assoc_of_le_of_submodule_le`

English:
lemma inf_sup_assoc_of_le_of_submodule_le
  statement: {C : PointedCone R E} (D : PointedCone R E)
  proof: inf_sup_assoc_of_le_of_neg_le _ hSC (by simpa [Submodule.neg_le])

中文:
引理 inf_sup_assoc_of_le_of_submodule_le
  结论: {C : PointedCone R E} (D : PointedCone R E)
  证明: inf_sup_assoc_of_le_of_neg_le _ hSC (by simpa [Submodule.neg_le])

Depends on / 依赖: Submodule, Submodule.neg_le, inf_sup_assoc_of_le_of_neg_le, neg_le
-/
lemma inf_sup_assoc_of_le_of_submodule_le {C : PointedCone R E} (D : PointedCone R E)
    {S : Submodule R E} (hSC : S <= C) : (C ⊓ D) ⊔ S = C ⊓ (D ⊔ S) :=
  inf_sup_assoc_of_le_of_neg_le _ hSC (by simpa [Submodule.neg_le])

end AddCommGroup

section OrderedAddCommGroup

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module R E]

/--
lemma `to_isOrderedModule` / 引理 `to_isOrderedModule`

English:
lemma to_isOrderedModule
  given: (C : PointedCone R E) (h : forall x y : E, x <= y ↔ y - x in C)
  proof: .of_smul_nonneg by simp +contextual [h, C.smul_mem]

中文:
引理 to_isOrderedModule
  条件: (C : PointedCone R E) (h : 对任意 x y : E, x <= y ↔ y - x in C)
  证明: .of_smul_nonneg by simp +contextual [h, C.smul_mem]

Depends on / 依赖: C.smul_mem, contextual, of_smul_nonneg, smul_mem
-/
lemma to_isOrderedModule (C : PointedCone R E) (h : forall x y : E, x <= y ↔ y - x in C) :
IsOrderedModule R E := .of_smul_nonneg by simp +contextual [h, C.smul_mem]

end OrderedAddCommGroup

section Lineal

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/-- The lineality space of a cone `C` is the submodule given by `C ⊓ -C`. -/
@[simps!]
/--
Definition of `lineal` / `lineal` 的定义

English:
definition lineal
  signature: (C : PointedCone R E)
  body: C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 <= r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
· have hr := le_of_lt neg_pos_of_neg lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

中文:
定义 lineal
  签名: (C : PointedCone R E)
  定义体: C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 <= r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
· have hr := le_of_lt neg_pos_of_neg lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

Depends on / 依赖: C.support, support
-/
def lineal (C : PointedCone R E) : Submodule R E where
  __ := C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 <= r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
· have hr := le_of_lt neg_pos_of_neg lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

/--
lemma `ofSubmodule_lineal` / 引理 `ofSubmodule_lineal`

English:
lemma ofSubmodule_lineal
  given: (C : PointedCone R E)
  statement: C.lineal = C ⊓ -C
  proof: rfl

中文:
引理 ofSubmodule_lineal
  条件: (C : PointedCone R E)
  结论: C.lineal = C ⊓ -C
  证明: rfl
-/
@[simp] lemma ofSubmodule_lineal (C : PointedCone R E) : C.lineal = C ⊓ -C := rfl

/--
lemma `mem_lineal` / 引理 `mem_lineal`

English:
lemma mem_lineal
  given: {C : PointedCone R E} {x : E}
  statement: x in C.lineal ↔ x in C ∧ -x in C
  proof: .rfl

中文:
引理 mem_lineal
  条件: {C : PointedCone R E} {x : E}
  结论: x in C.lineal ↔ x in C ∧ -x in C
  证明: .rfl
-/
@[simp] lemma mem_lineal {C : PointedCone R E} {x : E} : x in C.lineal ↔ x in C ∧ -x in C := .rfl

/--
theorem `support_eq` / 定理 `support_eq`

English:
theorem support_eq
  given: (C : PointedCone R E)
  statement: C.support = C.lineal.toAddSubgroup
  proof: rfl

中文:
定理 support_eq
  条件: (C : PointedCone R E)
  结论: C.support = C.lineal.toAddSubgroup
  证明: rfl
-/
@[simp] theorem support_eq (C : PointedCone R E) : C.support = C.lineal.toAddSubgroup := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `gc_ofSubmodule_lineal` / 定理 `gc_ofSubmodule_lineal`

English:
theorem gc_ofSubmodule_lineal
  proof: fun _ _ => ⟨fun _ _ => by aesop, fun h _ hx => (h hx).1⟩

中文:
定理 gc_ofSubmodule_lineal
  证明: fun _ _ => ⟨fun _ _ => by aesop, fun h _ hx => (h hx).1⟩

Depends on / 依赖: Submodule, lineal, ofSubmodule
-/
theorem gc_ofSubmodule_lineal :
    GaloisConnection (α := Submodule R E) ofSubmodule lineal :=
  fun _ _ => ⟨fun _ _ => by aesop, fun h _ hx => (h hx).1⟩

/--
lemma `lineal_le` / 引理 `lineal_le`

English:
lemma lineal_le
  given: (C : PointedCone R E)
  statement: C.lineal <= C
  proof: gc_ofSubmodule_lineal.l_u_le C

中文:
引理 lineal_le
  条件: (C : PointedCone R E)
  结论: C.lineal <= C
  证明: gc_ofSubmodule_lineal.l_u_le C

Depends on / 依赖: gc_ofSubmodule_lineal, gc_ofSubmodule_lineal.l_u_le, l_u_le
-/
lemma lineal_le (C : PointedCone R E) : C.lineal <= C := gc_ofSubmodule_lineal.l_u_le C

/--
theorem `lineal_eq_sSup` / 定理 `lineal_eq_sSup`

English:
theorem lineal_eq_sSup
  given: (C : PointedCone R E)
  statement: C.lineal = sSup {S : Submodule R E | S <= C}
  proof: by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

中文:
定理 lineal_eq_sSup
  条件: (C : PointedCone R E)
  结论: C.lineal = sSup {S : 子模 R E | S <= C}
  证明: by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

Depends on / 依赖: Iic_def, Set.Iic_def, csSup_Iic, gc_ofSubmodule_lineal, gc_ofSubmodule_lineal.le_iff_le, le_iff_le, simp_rw
-/
theorem lineal_eq_sSup (C : PointedCone R E) : C.lineal = sSup {S : Submodule R E | S <= C} := by
  simp_rw [gc_ofSubmodule_lineal.le_iff_le, Set.Iic_def, csSup_Iic]

end Lineal

section Salient

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E] [Module R E]

/--
lemma `salient_iff_inter_neg_eq_singleton` / 引理 `salient_iff_inter_neg_eq_singleton`

English:
lemma salient_iff_inter_neg_eq_singleton
  given: (C : PointedCone R E)
  proof: by
  simp [ConvexCone.Salient, Set.eq_singleton_iff_unique_mem, not_imp_not]

中文:
引理 salient_iff_inter_neg_eq_singleton
  条件: (C : PointedCone R E)
  证明: by
  simp [ConvexCone.Salient, Set.eq_singleton_iff_unique_mem, not_imp_not]

Depends on / 依赖: ConvexCone, ConvexCone.Salient, Salient, Set.eq_singleton_iff_unique_mem, eq_singleton_iff_unique_mem, not_imp_not
-/
lemma salient_iff_inter_neg_eq_singleton (C : PointedCone R E) :
    (C : ConvexCone R E).Salient ↔ (C inter -C : Set E) = {0} := by
  simp [ConvexCone.Salient, Set.eq_singleton_iff_unique_mem, not_imp_not]

end Salient

end PointedCone
