/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

/-!
# Helper structure in order to construct pairings

In this file, we introduce a helper structure `Subcomplex.PairingCore`
in order to construct a pairing for a subcomplex of a simplicial set.
The main difference with `Subcomplex.Pairing` are that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (II) and (I) simplices in such a way that, *definitionally*,
their dimensions are respectively `dim s` or `dim s + 1` for `s : ι`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/--
Definition of `PairingCore` / `PairingCore` 的定义

English:
structure PairingCore
  parameters: where
  axioms and operations (12):
    - ι : Type v
    - dim((s : ι)) : Nat
    - simplex((s : ι)) : X _⦋dim s + 1⦌
    - index((s : ι)) : Fin (dim s + 2)
    - nonDegenerate₁((s : ι)) : simplex s in X.nonDegenerate _
    - nonDegenerate₂((s : ι)) : X.δ (index s) (simplex s) in X.nonDegenerate _
    - notMem₁((s : ι)) : simplex s ∉ A.obj _
    - notMem₂((s : ι)) : X.δ (index s) (simplex s) ∉ A.obj _
    - injective_type₁'({s t : ι} (h : S.mk (simplex s) = S.mk (simplex t))) : s = t
    - injective_type₂'({s t : ι} (h : S.mk (X.δ (index s) (simplex s)) = S.mk (X.δ (index t) (simplex t)))) : s = t
    - type₁_ne_type₂'((s t : ι)) : S.mk (simplex s) != S.mk (X.δ (index t) (simplex t))
    - surjective'((x : A.N)) : exists (s : ι), x.toS = S.mk (simplex s) ∨ x.toS = S.mk (X.δ (index s) (simplex s))

中文:
结构 PairingCore
  参数: where
  公理与运算 (12 个):
    - ι : 类型v
    - dim((s : ι)) : 自然数
    - simplex((s : ι)) : X _⦋dim s + 1⦌
    - index((s : ι)) : 有限集 (dim s + 2)
    - nonDegenerate₁((s : ι)) : simplex s in X.nonDegenerate _
    - nonDegenerate₂((s : ι)) : X.δ (index s) (simplex s) in X.nonDegenerate _
    - notMem₁((s : ι)) : simplex s ∉ A.obj _
    - notMem₂((s : ι)) : X.δ (index s) (simplex s) ∉ A.obj _
    - injective_type₁'({s t : ι} (h : S.mk (simplex s) = S.mk (simplex t))) : s = t
    - injective_type₂'({s t : ι} (h : S.mk (X.δ (index s) (simplex s)) = S.mk (X.δ (index t) (simplex t)))) : s = t
    - type₁_ne_type₂'((s t : ι)) : S.mk (simplex s) != S.mk (X.δ (index t) (simplex t))
    - surjective'((x : A.N)) : 存在 (s : ι), x.toS = S.mk (simplex s) ∨ x.toS = S.mk (X.δ (index s) (simplex s))
-/
structure PairingCore where
  /-- the index type -/
  ι : Type v
  /-- the dimension of each type (II) simplex -/
  dim (s : ι) : Nat
  /-- the family of type (I) simplices -/
  simplex (s : ι) : X _⦋dim s + 1⦌
  /-- the corresponding type (II) simplex is the `1`-codimensional
    face given by this index -/
  index (s : ι) : Fin (dim s + 2)
  nonDegenerate₁ (s : ι) : simplex s in X.nonDegenerate _
  nonDegenerate₂ (s : ι) : X.δ (index s) (simplex s) in X.nonDegenerate _
  notMem₁ (s : ι) : simplex s ∉ A.obj _
  notMem₂ (s : ι) : X.δ (index s) (simplex s) ∉ A.obj _
  injective_type₁' {s t : ι} (h : S.mk (simplex s) = S.mk (simplex t)) : s = t
  injective_type₂' {s t : ι}
    (h : S.mk (X.δ (index s) (simplex s)) = S.mk (X.δ (index t) (simplex t))) : s = t
  type₁_ne_type₂' (s t : ι) : S.mk (simplex s) != S.mk (X.δ (index t) (simplex t))
  surjective' (x : A.N) :
    exists (s : ι), x.toS = S.mk (simplex s) ∨ x.toS = S.mk (X.δ (index s) (simplex s))

variable {A}

/--
Definition of `Pairing.pairingCore` / `Pairing.pairingCore` 的定义

English:
definition Pairing.pairingCore
  signature: (P : A.Pairing) [P.IsProper]
  body: P.II
  dim s := s.val.dim
  simplex s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).simplex
  index s := (P.isUniquelyCodimOneFace s).index rfl
  nonDegenerate₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).nonDegenerate
  nonDegenerate₂ s := by
    rw [(P.isUniquelyCodimOn

中文:
定义 Pairing.pairingCore
  签名: (P : A.Pairing) [P.是真]
  定义体: P.II
  dim s := s.val.dim
  simplex s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).simplex
  index s := (P.isUniquelyCodimOneFace s).index rfl
  nonDegenerate₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).nonDegenerate
  nonDegenerate₂ s := by
    rw [(P.isUniquelyCodimOn

Depends on / 依赖: P.II
-/
noncomputable def Pairing.pairingCore (P : A.Pairing) [P.IsProper] :
    A.PairingCore where
  ι := P.II
  dim s := s.val.dim
  simplex s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).simplex
  index s := (P.isUniquelyCodimOneFace s).index rfl
  nonDegenerate₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).nonDegenerate
  nonDegenerate₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.nonDegenerate
  notMem₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).notMem
  notMem₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.notMem
  injective_type₁' {s t} _ := by
    apply P.p.injective
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff,
      ← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      ← (P.p t).val.cast_eq_self (P.isUniquelyCodimOneFace t).dim_eq]
  injective_type₂' {s t} h := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]; rw [(P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff]
  type₁_ne_type₂' s t h := (P.ne (P.p s) t) (by
    rw [(P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      N.ext_iff, SSet.N.ext_iff])
  surjective' x := by
    obtain ⟨s, rfl | rfl⟩ := P.exists_or x
    · refine ⟨s, Or.inr ?_⟩
      simp [(P.isUniquelyCodimOneFace s).δ_index]
    · refine ⟨s, Or.inl ?_⟩
      nth_rw 1 [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq]
      rfl

namespace PairingCore

variable (h : A.PairingCore)

/-- The type (I) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`. -/
@[simps!]
/--
Definition of `type₁` / `type₁` 的定义

English:
definition type₁
  signature: (s : h.ι)
  body: Subcomplex.N.mk (h.simplex s) (h.nonDegenerate₁ s) (h.notMem₁ s)

中文:
定义 type₁
  签名: (s : h.ι)
  定义体: Subcomplex.N.mk (h.simplex s) (h.nonDegenerate₁ s) (h.notMem₁ s)

Depends on / 依赖: Subcomplex, Subcomplex.N.mk, h.nonDegenerate, h.notMem, h.simplex, simplex
-/
def type₁ (s : h.ι) : A.N :=
  Subcomplex.N.mk (h.simplex s) (h.nonDegenerate₁ s) (h.notMem₁ s)

/-- The type (II) simplices of `h : A.PairingCore`, as a family indexed by `h.ι`. -/
@[simps!]
/--
Definition of `type₂` / `type₂` 的定义

English:
definition type₂
  signature: (s : h.ι)
  body: Subcomplex.N.mk (X.δ (h.index s) (h.simplex s)) (h.nonDegenerate₂ s)
    (h.notMem₂ s)

中文:
定义 type₂
  签名: (s : h.ι)
  定义体: Subcomplex.N.mk (X.δ (h.index s) (h.simplex s)) (h.nonDegenerate₂ s)
    (h.notMem₂ s)

Depends on / 依赖: Subcomplex, Subcomplex.N.mk, h.index, h.nonDegenerate, h.notMem, h.simplex, simplex
-/
def type₂ (s : h.ι) : A.N :=
  Subcomplex.N.mk (X.δ (h.index s) (h.simplex s)) (h.nonDegenerate₂ s)
    (h.notMem₂ s)

/--
lemma `injective_type₁` / 引理 `injective_type₁`

English:
lemma injective_type₁
  statement: Function.Injective h.type₁
  proof: fun _ _ hst => h.injective_type₁' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

中文:
引理 injective_type₁
  结论: 函数.单射 h.type₁
  证明: fun _ _ hst => h.injective_type₁' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

Depends on / 依赖: SSet.N.ext_iff, Subcomplex, Subcomplex.N.ext_iff, ext_iff, h.injective_type
-/
lemma injective_type₁ : Function.Injective h.type₁ :=
  fun _ _ hst => h.injective_type₁' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

/--
lemma `injective_type₂` / 引理 `injective_type₂`

English:
lemma injective_type₂
  statement: Function.Injective h.type₂
  proof: fun s t hst => h.injective_type₂' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

中文:
引理 injective_type₂
  结论: 函数.单射 h.type₂
  证明: fun s t hst => h.injective_type₂' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

Depends on / 依赖: SSet.N.ext_iff, Subcomplex, Subcomplex.N.ext_iff, ext_iff, h.injective_type
-/
lemma injective_type₂ : Function.Injective h.type₂ :=
  fun s t hst => h.injective_type₂' (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

/--
lemma `type₁_ne_type₂` / 引理 `type₁_ne_type₂`

English:
lemma type₁_ne_type₂
  given: (s t : h.ι)
  statement: h.type₁ s != h.type₂ t
  proof: by
  simpa only [ne_eq, N.ext_iff, SSet.N.ext_iff] using! h.type₁_ne_type₂' s t

中文:
引理 type₁_ne_type₂
  条件: (s t : h.ι)
  结论: h.type₁ s != h.type₂ t
  证明: by
  simpa only [ne_eq, N.ext_iff, SSet.N.ext_iff] using! h.type₁_ne_type₂' s t

Depends on / 依赖: N.ext_iff, SSet.N.ext_iff, ext_iff, h.type, ne_eq
-/
lemma type₁_ne_type₂ (s t : h.ι) : h.type₁ s != h.type₂ t := by
  simpa only [ne_eq, N.ext_iff, SSet.N.ext_iff] using! h.type₁_ne_type₂' s t

/--
lemma `surjective` / 引理 `surjective`

English:
lemma surjective
  given: (x : A.N)
  proof: by
  obtain ⟨s, _ | _⟩ := h.surjective' x
  · exact ⟨s, Or.inl (by rwa [N.ext_iff, SSet.N.ext_iff])⟩
  · exact ⟨s, Or.inr (by rwa [N.ext_iff, SSet.N.ext_iff])⟩

中文:
引理 surjective
  条件: (x : A.N)
  证明: by
  obtain ⟨s, _ | _⟩ := h.surjective' x
  · exact ⟨s, Or.inl (by rwa [N.ext_iff, SSet.N.ext_iff])⟩
  · exact ⟨s, Or.inr (by rwa [N.ext_iff, SSet.N.ext_iff])⟩

Depends on / 依赖: N.ext_iff, Or.inl, Or.inr, SSet.N.ext_iff, ext_iff, h.surjective, surjective
-/
lemma surjective (x : A.N) :
    exists (s : h.ι), x = h.type₁ s ∨ x = h.type₂ s := by
  obtain ⟨s, _ | _⟩ := h.surjective' x
  · exact ⟨s, Or.inl (by rwa [N.ext_iff, SSet.N.ext_iff])⟩
  · exact ⟨s, Or.inr (by rwa [N.ext_iff, SSet.N.ext_iff])⟩

/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: : Set A.N
  body: Set.range h.type₁

中文:
定义 I
  签名: : 集合 A.N
  定义体: Set.range h.type₁

Depends on / 依赖: Set.range, h.type
-/
def I : Set A.N := Set.range h.type₁

/--
Definition of `II` / `II` 的定义

English:
definition II
  signature: : Set A.N
  body: Set.range h.type₂

中文:
定义 II
  签名: : 集合 A.N
  定义体: Set.range h.type₂

Depends on / 依赖: Set.range, h.type
-/
def II : Set A.N := Set.range h.type₂

/-- The bijection `h.ι ≃ h.I` when `h : A.PairingCore`. -/
@[simps! apply_coe]
/--
Definition of `equivI` / `equivI` 的定义

English:
definition equivI
  signature: : h.ι ≃ h.I
  body: Equiv.ofInjective _ h.injective_type₁

中文:
定义 equivI
  签名: : h.ι ≃ h.I
  定义体: Equiv.ofInjective _ h.injective_type₁

Depends on / 依赖: Equiv.ofInjective, h.injective_type, ofInjective
-/
noncomputable def equivI : h.ι ≃ h.I := Equiv.ofInjective _ h.injective_type₁

/-- The bijection `h.ι ≃ h.II` when `h : A.PairingCore`. -/
@[simps! apply_coe]
/--
Definition of `equivII` / `equivII` 的定义

English:
definition equivII
  signature: : h.ι ≃ h.II
  body: Equiv.ofInjective _ h.injective_type₂

中文:
定义 equivII
  签名: : h.ι ≃ h.II
  定义体: Equiv.ofInjective _ h.injective_type₂

Depends on / 依赖: Equiv.ofInjective, h.injective_type, ofInjective
-/
noncomputable def equivII : h.ι ≃ h.II := Equiv.ofInjective _ h.injective_type₂

/-- The pairing induced by `h : A.PairingCore`. -/
@[simps I II]
/--
Definition of `pairing` / `pairing` 的定义

English:
definition pairing
  signature: : A.Pairing where
  body: h.I
  II := h.II
  inter := by
    ext s
    simp only [I, II, Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, forall_exists_index]
    rintro t rfl s
    exact (h.type₁_ne_type₂ t s).symm
  union := by
    ext s
    have := h.surjective s
    simp on

中文:
定义 pairing
  签名: : A.Pairing where
  定义体: h.I
  II := h.II
  inter := by
    ext s
    simp only [I, II, Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, forall_exists_index]
    rintro t rfl s
    exact (h.type₁_ne_type₂ t s).symm
  union := by
    ext s
    have := h.surjective s
    simp on
-/
noncomputable def pairing : A.Pairing where
  I := h.I
  II := h.II
  inter := by
    ext s
    simp only [I, II, Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, forall_exists_index]
    rintro t rfl s
    exact (h.type₁_ne_type₂ t s).symm
  union := by
    ext s
    have := h.surjective s
    simp only [I, II, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    aesop
  p := h.equivII.symm.trans h.equivI

@[simp]
/--
lemma `pairing_p_equivII` / 引理 `pairing_p_equivII`

English:
lemma pairing_p_equivII
  given: (x : h.ι)
  proof: by
  simp [pairing]

@[simp]

中文:
引理 pairing_p_equivII
  条件: (x : h.ι)
  证明: by
  simp [pairing]

@[simp]

Depends on / 依赖: equivI, equivII, h.II, h.equivI, h.equivII, h.pairing.p, pairing
-/
lemma pairing_p_equivII (x : h.ι) :
    DFunLike.coe (F := h.II ≃ h.I) h.pairing.p (h.equivII x) = h.equivI x := by
  simp [pairing]

@[simp]
/--
lemma `pairing_p_symm_equivI` / 引理 `pairing_p_symm_equivI`

English:
lemma pairing_p_symm_equivI
  given: (x : h.ι)
  proof: by
  simp [pairing]

中文:
引理 pairing_p_symm_equivI
  条件: (x : h.ι)
  证明: by
  simp [pairing]

Depends on / 依赖: equivI, equivII, h.II, h.equivI, h.equivII, h.pairing.p.symm, pairing
-/
lemma pairing_p_symm_equivI (x : h.ι) :
    DFunLike.coe (F := h.I ≃ h.II) h.pairing.p.symm (h.equivI x) = h.equivII x := by
  simp [pairing]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `type₁_pairing` / 引理 `type₁_pairing`

English:
lemma type₁_pairing
  given: (x : h.ι)
  proof: by
  simp +instances

中文:
引理 type₁_pairing
  条件: (x : h.ι)
  证明: by
  simp +instances

Depends on / 依赖: instances
-/
lemma type₁_pairing (x : h.ι) :
    h.type₁ x = h.pairing.p (h.equivII x) := by
  simp +instances

/--
Definition of `IsProper` / `IsProper` 的定义

English:
class IsProper
  parameters: : Prop where
  axioms and operations (1):
    - isUniquelyCodimOneFace((s : h.ι)) : S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS

中文:
类 是真
  参数: : 命题 where
  公理与运算 (1 个):
    - isUniquelyCodimOneFace((s : h.ι)) : S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS
-/
class IsProper : Prop where
  isUniquelyCodimOneFace (s : h.ι) :
    S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS

/--
lemma `isUniquelyCodimOneFace` / 引理 `isUniquelyCodimOneFace`

English:
lemma isUniquelyCodimOneFace
  given: [h.IsProper] (s : h.ι)
  proof: IsProper.isUniquelyCodimOneFace _

中文:
引理 isUniquelyCodimOneFace
  条件: [h.是真] (s : h.ι)
  证明: IsProper.isUniquelyCodimOneFace _

Depends on / 依赖: IsProper, IsProper.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
lemma isUniquelyCodimOneFace [h.IsProper] (s : h.ι) :
    S.IsUniquelyCodimOneFace (h.type₂ s).toS (h.type₁ s).toS :=
  IsProper.isUniquelyCodimOneFace _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Nonsingular]
  signature: : h.IsProper where
  body: (S.IsUniquelyCodimOneFace.iff _ _).2
      (existsUnique_of_exists_of_unique ⟨_, rfl⟩
        (fun _ _ hi hj => Nonsingular.δ_injective _
          (h.nonDegenerate₁ s) _ _ (hi.trans hj.symm)))

中文:
实例 [X.非奇异]
  签名: : h.是真 where
  定义体: (S.IsUniquelyCodimOneFace.iff _ _).2
      (existsUnique_of_exists_of_unique ⟨_, rfl⟩
        (fun _ _ hi hj => Nonsingular.δ_injective _
          (h.nonDegenerate₁ s) _ _ (hi.trans hj.symm)))

Depends on / 依赖: IsUniquelyCodimOneFace, Nonsingular, S.IsUniquelyCodimOneFace.iff, existsUnique_of_exists_of_unique, h.nonDegenerate, hi.trans, hj.symm
-/
instance [X.Nonsingular] : h.IsProper where
  isUniquelyCodimOneFace s :=
    (S.IsUniquelyCodimOneFace.iff _ _).2
      (existsUnique_of_exists_of_unique ⟨_, rfl⟩
        (fun _ _ hi hj => Nonsingular.δ_injective _
          (h.nonDegenerate₁ s) _ _ (hi.trans hj.symm)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h.IsProper]
  signature: : h.pairing.IsProper where
  body: by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    simpa using h.isUniquelyCodimOneFace s

中文:
实例 [h.是真]
  签名: : h.pairing.是真 where
  定义体: by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    simpa using h.isUniquelyCodimOneFace s

Depends on / 依赖: equivII, h.equivII.surjective, h.isUniquelyCodimOneFace, isUniquelyCodimOneFace, surjective
-/
instance [h.IsProper] : h.pairing.IsProper where
  isUniquelyCodimOneFace x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    simpa using h.isUniquelyCodimOneFace s

/--
lemma `isProper_pairing_iff` / 引理 `isProper_pairing_iff`

English:
lemma isProper_pairing_iff
  proof: by
  refine ⟨fun _ => ⟨fun s => ?_⟩, fun _ => inferInstance⟩
  simpa [type₁_pairing] using h.pairing.isUniquelyCodimOneFace (h.equivII s)

中文:
引理 isProper_pairing_iff
  证明: by
  refine ⟨fun _ => ⟨fun s => ?_⟩, fun _ => inferInstance⟩
  simpa [type₁_pairing] using h.pairing.isUniquelyCodimOneFace (h.equivII s)

Depends on / 依赖: equivII, h.equivII, h.pairing.isUniquelyCodimOneFace, isUniquelyCodimOneFace, pairing
-/
lemma isProper_pairing_iff :
    h.pairing.IsProper ↔ h.IsProper := by
  refine ⟨fun _ => ⟨fun s => ?_⟩, fun _ => inferInstance⟩
  simpa [type₁_pairing] using h.pairing.isUniquelyCodimOneFace (h.equivII s)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `isUniquelyCodimOneFace_index` / 引理 `isUniquelyCodimOneFace_index`

English:
lemma isUniquelyCodimOneFace_index
  given: [h.IsProper] (s : h.ι)
  proof: by
  symm
  simp [← (h.isUniquelyCodimOneFace s).δ_eq_iff]

中文:
引理 isUniquelyCodimOneFace_index
  条件: [h.是真] (s : h.ι)
  证明: by
  symm
  simp [← (h.isUniquelyCodimOneFace s).δ_eq_iff]

Depends on / 依赖: h.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
lemma isUniquelyCodimOneFace_index [h.IsProper] (s : h.ι) :
    (h.isUniquelyCodimOneFace s).index rfl = h.index s := by
  symm
  simp [← (h.isUniquelyCodimOneFace s).δ_eq_iff]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isUniquelyCodimOneFace_index_coe` / 引理 `isUniquelyCodimOneFace_index_coe`

English:
lemma isUniquelyCodimOneFace_index_coe
  proof: by
  subst hd
  simp

中文:
引理 isUniquelyCodimOneFace_index_coe
  证明: by
  subst hd
  simp
-/
lemma isUniquelyCodimOneFace_index_coe
    [h.IsProper] (s : h.ι) {d : Nat} (hd : h.dim s = d) :
    ((h.isUniquelyCodimOneFace s).index hd).val = (h.index s).val := by
  subst hd
  simp

/--
Definition of `IsInner` / `IsInner` 的定义

English:
class IsInner
  parameters: where
  axioms and operations (2):
    - ne_zero((s : h.ι)) : h.index s != 0
    - ne_last((s : h.ι)) : h.index s != Fin.last _

中文:
类 是内积
  参数: where
  公理与运算 (2 个):
    - ne_zero((s : h.ι)) : h.index s != 0
    - ne_last((s : h.ι)) : h.index s != 有限集.last _
-/
class IsInner where
  ne_zero (s : h.ι) : h.index s != 0
  ne_last (s : h.ι) : h.index s != Fin.last _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h.IsInner]
  signature: [h.IsProper]
  body: by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_zero s
  ne_last x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_last s

中文:
实例 [h.是内积]
  签名: [h.是真]
  定义体: by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_zero s
  ne_last x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_last s

Depends on / 依赖: IsInner, IsInner.ne_last, IsInner.ne_zero, equivII, h.equivII.surjective, ne_last, ne_zero, surjective
-/
instance [h.IsInner] [h.IsProper] : h.pairing.IsInner where
  ne_zero x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_zero s
  ne_last x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsInner.ne_last s

/--
Definition of `AncestralRel` / `AncestralRel` 的定义

English:
definition AncestralRel
  signature: (s t : h.ι)
  body: s != t ∧ h.type₂ s < h.type₁ t

中文:
定义 AncestralRel
  签名: (s t : h.ι)
  定义体: s != t ∧ h.type₂ s < h.type₁ t

Depends on / 依赖: h.type
-/
def AncestralRel (s t : h.ι) : Prop :=
  s != t ∧ h.type₂ s < h.type₁ t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ancestralRel_iff` / 引理 `ancestralRel_iff`

English:
lemma ancestralRel_iff
  given: (s t : h.ι)
  proof: by
  simp [AncestralRel, Pairing.AncestralRel]

中文:
引理 ancestralRel_iff
  条件: (s t : h.ι)
  证明: by
  simp [AncestralRel, Pairing.AncestralRel]

Depends on / 依赖: AncestralRel, Pairing, Pairing.AncestralRel
-/
lemma ancestralRel_iff (s t : h.ι) :
    h.AncestralRel s t ↔ h.pairing.AncestralRel (h.equivII s) (h.equivII t) := by
  simp [AncestralRel, Pairing.AncestralRel]

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
class IsRegular
  parameters: (h : A.PairingCore)
  extends: h.IsProper
  axioms and operations (1):
    - wf((h)) : WellFounded h.AncestralRel

中文:
类 是正则
  参数: (h : A.PairingCore)
  继承: h.是真
  公理与运算 (1 个):
    - wf((h)) : 良基 h.AncestralRel
-/
class IsRegular (h : A.PairingCore) extends h.IsProper where
  wf (h) : WellFounded h.AncestralRel

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h.IsRegular]
  signature: : h.pairing.IsRegular where
  body: by
    have := IsRegular.wf h
    rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
    exact ⟨fun ⟨f, hf⟩ => this.false
      ⟨fun n => h.equivII.symm (f n), fun n => by simpa [ancestralRel_iff] using hf n⟩⟩

中文:
实例 [h.是正则]
  签名: : h.pairing.是正则 where
  定义体: by
    have := IsRegular.wf h
    rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
    exact ⟨fun ⟨f, hf⟩ => this.false
      ⟨fun n => h.equivII.symm (f n), fun n => by simpa [ancestralRel_iff] using hf n⟩⟩

Depends on / 依赖: IsRegular, IsRegular.wf, ancestralRel_iff, equivII, h.equivII.symm, this.false, wellFounded_iff_isEmpty_descending_chain
-/
instance [h.IsRegular] : h.pairing.IsRegular where
  wf := by
    have := IsRegular.wf h
    rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
    exact ⟨fun ⟨f, hf⟩ => this.false
      ⟨fun n => h.equivII.symm (f n), fun n => by simpa [ancestralRel_iff] using hf n⟩⟩

/--
lemma `isRegular_pairing_iff` / 引理 `isRegular_pairing_iff`

English:
lemma isRegular_pairing_iff
  given: (h : A.PairingCore)
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : h.IsProper := by
    rw [← isProper_pairing_iff]
    infer_instance
  constructor
  have := h.pairing.wf
  rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
  exact ⟨fun ⟨f, hf⟩ => this.false
    ⟨fun n => h.equivII (f n), fun n => by 

中文:
引理 isRegular_pairing_iff
  条件: (h : A.PairingCore)
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : h.IsProper := by
    rw [← isProper_pairing_iff]
    infer_instance
  constructor
  have := h.pairing.wf
  rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
  exact ⟨fun ⟨f, hf⟩ => this.false
    ⟨fun n => h.equivII (f n), fun n => by 

Depends on / 依赖: IsProper, ancestralRel_iff, equivII, h.IsProper, h.equivII, h.pairing.wf, infer_instance, isProper_pairing_iff, pairing, this.false, wellFounded_iff_isEmpty_descending_chain
-/
lemma isRegular_pairing_iff (h : A.PairingCore) :
    h.pairing.IsRegular ↔ h.IsRegular := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : h.IsProper := by
    rw [← isProper_pairing_iff]
    infer_instance
  constructor
  have := h.pairing.wf
  rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
  exact ⟨fun ⟨f, hf⟩ => this.false
    ⟨fun n => h.equivII (f n), fun n => by simpa [ancestralRel_iff] using hf n⟩⟩

end PairingCore

end SSet.Subcomplex
