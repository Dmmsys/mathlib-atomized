/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Andrew Yang,
  Johannes Hölzl, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.Hom.CompleteLattice

/-!

# Restriction of scalars for submodules

If semiring `S` acts on a semiring `R` and `M` is a module over both (compatibly with this action)
then we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `R`. We call
this restriction of scalars for submodules.

## Main definitions:
* `Submodule.restrictScalars`: regard an `R`-submodule as an `S`-submodule if `S` acts on `R`

-/

@[expose] public section

namespace Submodule

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (V : Submodule R M)
  body: V
  zero_mem' := V.zero_mem
  smul_mem' c _ h := V.smul_of_tower_mem c h
  add_mem' hx hy := V.add_mem hx hy

@[simp]

中文:
定义 restrictScalars
  签名: (V : 子模 R M)
  定义体: V
  zero_mem' := V.zero_mem
  smul_mem' c _ h := V.smul_of_tower_mem c h
  add_mem' hx hy := V.add_mem hx hy

@[simp]
-/
def restrictScalars (V : Submodule R M) : Submodule S M where
  carrier := V
  zero_mem' := V.zero_mem
  smul_mem' c _ h := V.smul_of_tower_mem c h
  add_mem' hx hy := V.add_mem hx hy

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (V : Submodule R M)
  statement: (V.restrictScalars S : Set M) = V
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: (V : 子模 R M)
  结论: (V.restrictScalars S : 集合 M) = V
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars (V : Submodule R M) : (V.restrictScalars S : Set M) = V :=
  rfl

@[simp]
/--
theorem `toAddSubmonoid_restrictScalars` / 定理 `toAddSubmonoid_restrictScalars`

English:
theorem toAddSubmonoid_restrictScalars
  given: (V : Submodule R M)
  proof: rfl

@[simp]

中文:
定理 toAddSubmonoid_restrictScalars
  条件: (V : 子模 R M)
  证明: rfl

@[simp]
-/
theorem toAddSubmonoid_restrictScalars (V : Submodule R M) :
    (V.restrictScalars S).toAddSubmonoid = V.toAddSubmonoid :=
  rfl

@[simp]
/--
theorem `restrictScalars_mem` / 定理 `restrictScalars_mem`

English:
theorem restrictScalars_mem
  given: (V : Submodule R M) (m : M)
  statement: m in V.restrictScalars S ↔ m in V
  proof: Iff.refl _

@[simp]

中文:
定理 restrictScalars_mem
  条件: (V : 子模 R M) (m : M)
  结论: m in V.restrictScalars S ↔ m in V
  证明: Iff.refl _

@[simp]

Depends on / 依赖: Iff.refl
-/
theorem restrictScalars_mem (V : Submodule R M) (m : M) : m in V.restrictScalars S ↔ m in V :=
  Iff.refl _

@[simp]
/--
theorem `restrictScalars_self` / 定理 `restrictScalars_self`

English:
theorem restrictScalars_self
  given: (V : Submodule R M)
  statement: V.restrictScalars R = V
  proof: SetLike.coe_injective rfl

中文:
定理 restrictScalars_self
  条件: (V : 子模 R M)
  结论: V.restrictScalars R = V
  证明: SetLike.coe_injective rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem restrictScalars_self (V : Submodule R M) : V.restrictScalars R = V :=
  SetLike.coe_injective rfl

/--
theorem `restrictScalars_restrictScalars` / 定理 `restrictScalars_restrictScalars`

English:
theorem restrictScalars_restrictScalars
  proof: rfl

中文:
定理 restrictScalars_restrictScalars
  证明: rfl
-/
@[simp] theorem restrictScalars_restrictScalars
    (T : Type*) [Semiring T] [SMul T R] [SMul S T]
    [Module T M] [IsScalarTower S T M] [IsScalarTower T R M]
    (V : Submodule R M) :
    (V.restrictScalars T).restrictScalars S = V.restrictScalars S :=
  rfl

variable (R M)

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h =>
ext Set.ext_iff.1 (SetLike.ext'_iff.1 h :)

@[simp]

中文:
定理 restrictScalars_injective
  证明: fun _ _ h =>
ext Set.ext_iff.1 (SetLike.ext'_iff.1 h :)

@[simp]
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars S : Submodule R M -> Submodule S M) := fun _ _ h =>
ext Set.ext_iff.1 (SetLike.ext'_iff.1 h :)

@[simp]
/--
theorem `restrictScalars_inj` / 定理 `restrictScalars_inj`

English:
theorem restrictScalars_inj
  given: {V₁ V₂ : Submodule R M}
  proof: (restrictScalars_injective S _ _).eq_iff

中文:
定理 restrictScalars_inj
  条件: {V₁ V₂ : 子模 R M}
  证明: (restrictScalars_injective S _ _).eq_iff

Depends on / 依赖: eq_iff, restrictScalars_injective
-/
theorem restrictScalars_inj {V₁ V₂ : Submodule R M} :
    restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂ :=
  (restrictScalars_injective S _ _).eq_iff

/--
Instance `restrictScalars.origModule` / 实例 `restrictScalars.origModule`

English:
instance restrictScalars.origModule
  signature: (p : Submodule R M)
  body: inferInstanceAs Module R p

中文:
实例 restrictScalars.origModule
  签名: (p : 子模 R M)
  定义体: inferInstanceAs Module R p

Depends on / 依赖: Module
-/
instance restrictScalars.origModule (p : Submodule R M) : Module R (p.restrictScalars S) :=
inferInstanceAs Module R p

/--
Instance `restrictScalars.isScalarTower` / 实例 `restrictScalars.isScalarTower`

English:
instance restrictScalars.isScalarTower
  signature: (p : Submodule R M)
  body: Subtype.ext smul_assoc r s (x : M)

中文:
实例 restrictScalars.isScalarTower
  签名: (p : 子模 R M)
  定义体: Subtype.ext smul_assoc r s (x : M)

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance restrictScalars.isScalarTower (p : Submodule R M) :
    IsScalarTower S R (p.restrictScalars S) where
smul_assoc r s x := Subtype.ext smul_assoc r s (x : M)

variable {R M} in
/--
lemma `restrictScalars_le` / 引理 `restrictScalars_le`

English:
lemma restrictScalars_le
  given: {s t : Submodule R M}
  proof: Iff.rfl

中文:
引理 restrictScalars_le
  条件: {s t : 子模 R M}
  证明: Iff.rfl
-/
@[gcongr, simp] lemma restrictScalars_le {s t : Submodule R M} :
    s.restrictScalars S <= t.restrictScalars S ↔ s <= t :=
  Iff.rfl

variable {R M} in
/--
lemma `restrictScalars_lt` / 引理 `restrictScalars_lt`

English:
lemma restrictScalars_lt
  given: {s t : Submodule R M}
  proof: Iff.rfl

中文:
引理 restrictScalars_lt
  条件: {s t : 子模 R M}
  证明: Iff.rfl
-/
@[gcongr, simp] lemma restrictScalars_lt {s t : Submodule R M} :
    s.restrictScalars S < t.restrictScalars S ↔ s < t :=
  Iff.rfl

/-- `restrictScalars S` is an embedding of the lattice of `R`-submodules into
the lattice of `S`-submodules. -/
@[simps]
/--
Definition of `restrictScalarsEmbedding` / `restrictScalarsEmbedding` 的定义

English:
definition restrictScalarsEmbedding
  signature: : Submodule R M ↪o Submodule S M where
  body: restrictScalars S
  inj' := restrictScalars_injective S R M
  map_rel_iff' := restrictScalars_le S

@[mono]

中文:
定义 restrictScalarsEmbedding
  签名: : 子模 R M ↪o 子模 S M where
  定义体: restrictScalars S
  inj' := restrictScalars_injective S R M
  map_rel_iff' := restrictScalars_le S

@[mono]

Depends on / 依赖: restrictScalars
-/
def restrictScalarsEmbedding : Submodule R M ↪o Submodule S M where
  toFun := restrictScalars S
  inj' := restrictScalars_injective S R M
  map_rel_iff' := restrictScalars_le S

@[mono]
/--
lemma `restrictScalars_monotone` / 引理 `restrictScalars_monotone`

English:
lemma restrictScalars_monotone
  statement: Monotone (restrictScalars S : Submodule R M -> Submodule S M)
  proof: (restrictScalarsEmbedding S R M).monotone

中文:
引理 restrictScalars_monotone
  结论: 递增 (restrictScalars S : 子模 R M -> 子模 S M)
  证明: (restrictScalarsEmbedding S R M).monotone

Depends on / 依赖: monotone, restrictScalarsEmbedding
-/
lemma restrictScalars_monotone : Monotone (restrictScalars S : Submodule R M -> Submodule S M) :=
  (restrictScalarsEmbedding S R M).monotone

variable {R M} in
/--
lemma `restrictScalars_mono` / 引理 `restrictScalars_mono`

English:
lemma restrictScalars_mono
  given: {s t : Submodule R M} (hst : s <= t)
  proof: restrictScalars_monotone S R M hst

中文:
引理 restrictScalars_mono
  条件: {s t : 子模 R M} (hst : s <= t)
  证明: restrictScalars_monotone S R M hst

Depends on / 依赖: restrictScalars_monotone
-/
lemma restrictScalars_mono {s t : Submodule R M} (hst : s <= t) :
    s.restrictScalars S <= t.restrictScalars S := restrictScalars_monotone S R M hst

/-- Turning `p : Submodule R M` into an `S`-submodule gives the same module structure
as turning it into a type and adding a module structure. -/
@[simps +simpRhs]
/--
Definition of `restrictScalarsEquiv` / `restrictScalarsEquiv` 的定义

English:
definition restrictScalarsEquiv
  signature: (p : Submodule R M)
  body: { AddEquiv.refl p with
    map_smul' := fun _ _ => rfl }

@[simp]

中文:
定义 restrictScalarsEquiv
  签名: (p : 子模 R M)
  定义体: { AddEquiv.refl p with
    map_smul' := fun _ _ => rfl }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.refl, map_smul
-/
def restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p :=
  { AddEquiv.refl p with
    map_smul' := fun _ _ => rfl }

@[simp]
/--
theorem `restrictScalars_bot` / 定理 `restrictScalars_bot`

English:
theorem restrictScalars_bot
  statement: restrictScalars S (⊥ : Submodule R M) = ⊥
  proof: rfl

@[simp]

中文:
定理 restrictScalars_bot
  结论: restrictScalars S (⊥ : 子模 R M) = ⊥
  证明: rfl

@[simp]
-/
theorem restrictScalars_bot : restrictScalars S (⊥ : Submodule R M) = ⊥ :=
  rfl

@[simp]
/--
theorem `restrictScalars_eq_bot_iff` / 定理 `restrictScalars_eq_bot_iff`

English:
theorem restrictScalars_eq_bot_iff
  given: {p : Submodule R M}
  statement: restrictScalars S p = ⊥ ↔ p = ⊥
  proof: by
  simp [SetLike.ext_iff]

@[simp]

中文:
定理 restrictScalars_eq_bot_iff
  条件: {p : 子模 R M}
  结论: restrictScalars S p = ⊥ ↔ p = ⊥
  证明: by
  simp [SetLike.ext_iff]

@[simp]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem restrictScalars_eq_bot_iff {p : Submodule R M} : restrictScalars S p = ⊥ ↔ p = ⊥ := by
  simp [SetLike.ext_iff]

@[simp]
/--
theorem `restrictScalars_top` / 定理 `restrictScalars_top`

English:
theorem restrictScalars_top
  statement: restrictScalars S (⊤ : Submodule R M) = ⊤
  proof: rfl

@[simp]

中文:
定理 restrictScalars_top
  结论: restrictScalars S (⊤ : 子模 R M) = ⊤
  证明: rfl

@[simp]
-/
theorem restrictScalars_top : restrictScalars S (⊤ : Submodule R M) = ⊤ :=
  rfl

@[simp]
/--
theorem `restrictScalars_eq_top_iff` / 定理 `restrictScalars_eq_top_iff`

English:
theorem restrictScalars_eq_top_iff
  given: {p : Submodule R M}
  statement: restrictScalars S p = ⊤ ↔ p = ⊤
  proof: by
  simp [SetLike.ext_iff]

中文:
定理 restrictScalars_eq_top_iff
  条件: {p : 子模 R M}
  结论: restrictScalars S p = ⊤ ↔ p = ⊤
  证明: by
  simp [SetLike.ext_iff]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem restrictScalars_eq_top_iff {p : Submodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤ := by
  simp [SetLike.ext_iff]

variable {R M}

@[simp]
/--
lemma `restrictScalars_sInf` / 引理 `restrictScalars_sInf`

English:
lemma restrictScalars_sInf
  given: (s : Set (Submodule R M))
  proof: by
  ext; simp

中文:
引理 restrictScalars_sInf
  条件: (s : 集合 (子模 R M))
  证明: by
  ext; simp
-/
lemma restrictScalars_sInf (s : Set (Submodule R M)) :
    (sInf s).restrictScalars S = sInf (restrictScalars S '' s) := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `restrictScalars_sSup` / 引理 `restrictScalars_sSup`

English:
lemma restrictScalars_sSup
  given: (s : Set (Submodule R M))
  proof: by
  simp [← toAddSubmonoid_inj, toAddSubmonoid_sSup, ← Set.image_comp]

中文:
引理 restrictScalars_sSup
  条件: (s : 集合 (子模 R M))
  证明: by
  simp [← toAddSubmonoid_inj, toAddSubmonoid_sSup, ← Set.image_comp]

Depends on / 依赖: Set.image_comp, image_comp, toAddSubmonoid_inj, toAddSubmonoid_sSup
-/
lemma restrictScalars_sSup (s : Set (Submodule R M)) :
    (sSup s).restrictScalars S = sSup (restrictScalars S '' s) := by
  simp [← toAddSubmonoid_inj, toAddSubmonoid_sSup, ← Set.image_comp]

variable (R M) in
/--
Definition of `restrictScalarsLatticeHom` / `restrictScalarsLatticeHom` 的定义

English:
definition restrictScalarsLatticeHom
  signature: : CompleteLatticeHom (Submodule R M) (Submodule S M) where
  body: restrictScalars S
  map_sInf' := restrictScalars_sInf S
  map_sSup' := restrictScalars_sSup S

@[simp]

中文:
定义 restrictScalarsLatticeHom
  签名: : 完备格态射 (子模 R M) (子模 S M) where
  定义体: restrictScalars S
  map_sInf' := restrictScalars_sInf S
  map_sSup' := restrictScalars_sSup S

@[simp]

Depends on / 依赖: restrictScalars
-/
def restrictScalarsLatticeHom : CompleteLatticeHom (Submodule R M) (Submodule S M) where
  toFun := restrictScalars S
  map_sInf' := restrictScalars_sInf S
  map_sSup' := restrictScalars_sSup S

@[simp]
/--
lemma `restrictScalars_iInf` / 引理 `restrictScalars_iInf`

English:
lemma restrictScalars_iInf
  given: {ι : Sort*} (s : ι -> Submodule R M)
  proof: by
  ext; simp

@[simp]

中文:
引理 restrictScalars_iInf
  条件: {ι : 类型层*} (s : ι -> 子模 R M)
  证明: by
  ext; simp

@[simp]
-/
lemma restrictScalars_iInf {ι : Sort*} (s : ι -> Submodule R M) :
    (iInf s).restrictScalars S = ⨅ i, restrictScalars S (s i) := by
  ext; simp

@[simp]
/--
lemma `restrictScalars_iSup` / 引理 `restrictScalars_iSup`

English:
lemma restrictScalars_iSup
  given: {ι : Sort*} (s : ι -> Submodule R M)
  proof: map_iSup (restrictScalarsLatticeHom S R M) s

@[simp]

中文:
引理 restrictScalars_iSup
  条件: {ι : 类型层*} (s : ι -> 子模 R M)
  证明: map_iSup (restrictScalarsLatticeHom S R M) s

@[simp]

Depends on / 依赖: map_iSup, restrictScalarsLatticeHom
-/
lemma restrictScalars_iSup {ι : Sort*} (s : ι -> Submodule R M) :
    (iSup s).restrictScalars S = ⨆ i, restrictScalars S (s i) :=
  map_iSup (restrictScalarsLatticeHom S R M) s

@[simp]
/--
lemma `restrictScalars_inf` / 引理 `restrictScalars_inf`

English:
lemma restrictScalars_inf
  given: (s t : Submodule R M)
  proof: by
  ext x; simp

@[simp]

中文:
引理 restrictScalars_inf
  条件: (s t : 子模 R M)
  证明: by
  ext x; simp

@[simp]
-/
lemma restrictScalars_inf (s t : Submodule R M) :
    (s ⊓ t).restrictScalars S = s.restrictScalars S ⊓ t.restrictScalars S := by
  ext x; simp

@[simp]
/--
lemma `restrictScalars_sup` / 引理 `restrictScalars_sup`

English:
lemma restrictScalars_sup
  given: (s t : Submodule R M)
  proof: by
  simpa [Set.image_insert_eq] using restrictScalars_sSup S (s := {s, t})

@[simp]

中文:
引理 restrictScalars_sup
  条件: (s t : 子模 R M)
  证明: by
  simpa [Set.image_insert_eq] using restrictScalars_sSup S (s := {s, t})

@[simp]

Depends on / 依赖: Set.image_insert_eq, image_insert_eq, restrictScalars_sSup
-/
lemma restrictScalars_sup (s t : Submodule R M) :
    (s ⊔ t).restrictScalars S = s.restrictScalars S ⊔ t.restrictScalars S := by
  simpa [Set.image_insert_eq] using restrictScalars_sSup S (s := {s, t})

@[simp]
/--
lemma `toIntSubmodule_toAddSubgroup` / 引理 `toIntSubmodule_toAddSubgroup`

English:
lemma toIntSubmodule_toAddSubgroup
  statement: {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  proof: rfl

@[simp]

中文:
引理 to整数Submodule_toAddSubgroup
  结论: {R M : 类型} [环 R] [加法交换群 M] [模 R M]
  证明: rfl

@[simp]
-/
lemma toIntSubmodule_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    N.toAddSubgroup.toIntSubmodule = N.restrictScalars Int := rfl

@[simp]
/--
theorem `codisjoint_restrictScalars_iff` / 定理 `codisjoint_restrictScalars_iff`

English:
theorem codisjoint_restrictScalars_iff
  given: {s t : Submodule R M}
  proof: by
  simp [codisjoint_iff, ← restrictScalars_sup]

@[simp]

中文:
定理 codisjoint_restrictScalars_iff
  条件: {s t : 子模 R M}
  证明: by
  simp [codisjoint_iff, ← restrictScalars_sup]

@[simp]

Depends on / 依赖: codisjoint_iff, restrictScalars_sup
-/
theorem codisjoint_restrictScalars_iff {s t : Submodule R M} :
    Codisjoint (s.restrictScalars S) (t.restrictScalars S) ↔ Codisjoint s t := by
  simp [codisjoint_iff, ← restrictScalars_sup]

@[simp]
/--
theorem `disjoint_restrictScalars_iff` / 定理 `disjoint_restrictScalars_iff`

English:
theorem disjoint_restrictScalars_iff
  given: {s t : Submodule R M}
  proof: by
  simp [disjoint_def]

@[simp]

中文:
定理 disjoint_restrictScalars_iff
  条件: {s t : 子模 R M}
  证明: by
  simp [disjoint_def]

@[simp]

Depends on / 依赖: disjoint_def
-/
theorem disjoint_restrictScalars_iff {s t : Submodule R M} :
    Disjoint (s.restrictScalars S) (t.restrictScalars S) ↔ Disjoint s t := by
  simp [disjoint_def]

@[simp]
/--
theorem `isCompl_restrictScalars_iff` / 定理 `isCompl_restrictScalars_iff`

English:
theorem isCompl_restrictScalars_iff
  given: {s t : Submodule R M}
  proof: by
  simp [isCompl_iff]

中文:
定理 isCompl_restrictScalars_iff
  条件: {s t : 子模 R M}
  证明: by
  simp [isCompl_iff]

Depends on / 依赖: isCompl_iff
-/
theorem isCompl_restrictScalars_iff {s t : Submodule R M} :
    IsCompl (s.restrictScalars S) (t.restrictScalars S) ↔ IsCompl s t := by
  simp [isCompl_iff]

end Submodule
