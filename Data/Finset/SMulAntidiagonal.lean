/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.SMulAntidiagonal

/-!
# Antidiagonal for scalar multiplication as a `Finset`.

Given sets `G` and `P`, with an action of `G` on `P`, we construct, for any element `a` in `P`,
the `Finset` of all pairs of an element in `s` and an element in `t` that scalar-multiply to `a`,
assuming that set is finite.

## Definitions
* Finset.SMulAntidiagonal : Finset antidiagonal for PWO inputs.
* Finset.VAddAntidiagonal : Finset antidiagonal for PWO inputs.

-/

@[expose] public section

variable {G P : Type*}

open scoped Pointwise

namespace Set

@[to_additive]
/--
theorem `IsPWO.smul` / 定理 `IsPWO.smul`

English:
theorem IsPWO.smul
  statement: [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
  proof: by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.smul monotone_snd)

@[to_additive]

中文:
定理 IsPWO.smul
  结论: [预序 G] [预序 P] [标量乘法 G P] [是OrderedSMul G P]
  证明: by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.smul monotone_snd)

@[to_additive]

Depends on / 依赖: hs.prod, image_of_monotone, image_smul_prod, monotone_fst, monotone_fst.smul, monotone_snd
-/
theorem IsPWO.smul [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s • t) := by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.smul monotone_snd)

@[to_additive]
/--
theorem `IsWF.smul` / 定理 `IsWF.smul`

English:
theorem IsWF.smul
  statement: [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P] {s : Set G}
  proof: (hs.isPWO.smul ht.isPWO).isWF

@[to_additive]

中文:
定理 IsWF.smul
  结论: [线性序 G] [线性序 P] [标量乘法 G P] [是OrderedSMul G P] {s : 集合 G}
  证明: (hs.isPWO.smul ht.isPWO).isWF

@[to_additive]

Depends on / 依赖: hs.isPWO.smul, ht.isPWO
-/
theorem IsWF.smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) : IsWF (s • t) :=
  (hs.isPWO.smul ht.isPWO).isWF

@[to_additive]
/--
theorem `IsWF.min_smul` / 定理 `IsWF.min_smul`

English:
theorem IsWF.min_smul
  statement: [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P]
  proof: by
  refine le_antisymm (IsWF.min_le _ _ (mem_smul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact IsOrderedSMul.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

中文:
定理 IsWF.min_smul
  结论: [线性序 G] [线性序 P] [标量乘法 G P] [是OrderedSMul G P]
  证明: by
  refine le_antisymm (IsWF.min_le _ _ (mem_smul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact IsOrderedSMul.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

Depends on / 依赖: IsOrderedSMul, IsOrderedSMul.smul_le_smul, IsWF.le_min_iff, IsWF.min_le, hs.min_le, hs.min_mem, ht.min_le, ht.min_mem, le_antisymm, le_min_iff, mem_smul, min_le, min_mem, smul_le_smul
-/
theorem IsWF.min_smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.smul ht).min (hsn.smul htn) = hs.min hsn • ht.min htn := by
  refine le_antisymm (IsWF.min_le _ _ (mem_smul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact IsOrderedSMul.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

section

open Set

variable [SMul G P]

/-- `Finset.SMulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose scalar multiplication yields `a`, but its construction requires a proof that
the set-theoretic antidiagonal is finite. -/
@[to_additive /-- `Finset.VAddAntidiagonal hs ht a` is the set of all pairs of an element in `s`
and an element in `t` whose vector addition yields `a`, but its construction requires proofs that
`s` and `t` are well-ordered. -/]
/--
Definition of `SMulAntidiagonal` / `SMulAntidiagonal` 的定义

English:
definition SMulAntidiagonal
  signature: {s : Set G}
  body: h.toFinset

@[to_additive (attr := simp)]

中文:
定义 SMulAntidiagonal
  签名: {s : 集合 G}
  定义体: h.toFinset

@[to_additive (attr := simp)]

Depends on / 依赖: h.toFinset, toFinset
-/
noncomputable def SMulAntidiagonal {s : Set G}
    {t : Set P} (a : P) (h : (s.smulAntidiagonal t a).Finite) : Finset (G × P) :=
  h.toFinset

@[to_additive (attr := simp)]
/--
theorem `mem_smulAntidiagonal` / 定理 `mem_smulAntidiagonal`

English:
theorem mem_smulAntidiagonal
  statement: {s : Set G}
  proof: by
  simp only [SMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]

中文:
定理 mem_smulAntidiagonal
  结论: {s : 集合 G}
  证明: by
  simp only [SMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]

Depends on / 依赖: Finite, SMulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_sep_iff, mem_sep_iff, mem_toFinset
-/
theorem mem_smulAntidiagonal {s : Set G}
    {t : Set P} (a : P) (h : (s.smulAntidiagonal t a).Finite) {x : G × P} :
    x in SMulAntidiagonal a h ↔ x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a := by
  simp only [SMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]
/--
theorem `smulAntidiagonal_mono_left` / 定理 `smulAntidiagonal_mono_left`

English:
theorem smulAntidiagonal_mono_left
  statement: {s u : Set G} {t : Set P} (a : P) (h : u subseteq s)
  proof: Set.Finite.toFinset_mono Set.smulAntidiagonal_mono_left h

@[to_additive]

中文:
定理 smulAntidiagonal_mono_left
  结论: {s u : 集合 G} {t : 集合 P} (a : P) (h : u subseteq s)
  证明: Set.Finite.toFinset_mono Set.smulAntidiagonal_mono_left h

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.toFinset_mono, Set.smulAntidiagonal_mono_left, smulAntidiagonal_mono_left, toFinset_mono
-/
theorem smulAntidiagonal_mono_left {s u : Set G} {t : Set P} (a : P) (h : u subseteq s)
    (hst : (s.smulAntidiagonal t a).Finite) (hut : (u.smulAntidiagonal t a).Finite) :
    SMulAntidiagonal a hut subseteq SMulAntidiagonal a hst :=
Set.Finite.toFinset_mono Set.smulAntidiagonal_mono_left h

@[to_additive]
/--
theorem `smulAntidiagonal_mono_right` / 定理 `smulAntidiagonal_mono_right`

English:
theorem smulAntidiagonal_mono_right
  statement: {s : Set G}
  proof: Set.Finite.toFinset_mono Set.smulAntidiagonal_mono_right h

@[to_additive]

中文:
定理 smulAntidiagonal_mono_right
  结论: {s : 集合 G}
  证明: Set.Finite.toFinset_mono Set.smulAntidiagonal_mono_right h

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.toFinset_mono, Set.smulAntidiagonal_mono_right, smulAntidiagonal_mono_right, toFinset_mono
-/
theorem smulAntidiagonal_mono_right {s : Set G}
    {t v : Set P} (a : P) (hst : (s.smulAntidiagonal t a).Finite)
    (hsv : (s.smulAntidiagonal v a).Finite) (h : v subseteq t) :
    SMulAntidiagonal a hsv subseteq SMulAntidiagonal a hst :=
Set.Finite.toFinset_mono Set.smulAntidiagonal_mono_right h

@[to_additive]
/--
theorem `support_smulAntidiagonal_subset_smul` / 定理 `support_smulAntidiagonal_subset_smul`

English:
theorem support_smulAntidiagonal_subset_smul
  statement: {s : Set G}
  proof: by
  grind [mem_smul, mem_smulAntidiagonal]

中文:
定理 support_smulAntidiagonal_subset_smul
  结论: {s : 集合 G}
  证明: by
  grind [mem_smul, mem_smulAntidiagonal]

Depends on / 依赖: mem_smul, mem_smulAntidiagonal
-/
theorem support_smulAntidiagonal_subset_smul {s : Set G}
    {t : Set P} (hst : forall a, (s.smulAntidiagonal t a).Finite) :
    { a | (SMulAntidiagonal a (hst a)).Nonempty } subseteq (s • t) := by
  grind [mem_smul, mem_smulAntidiagonal]

variable [PartialOrder G] [PartialOrder P] [IsOrderedCancelSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) {u : Set G} {hu : u.IsPWO} {v : Set P}
    {hv : v.IsPWO} {x : G × P}

@[to_additive]
/--
theorem `isPWO_support_smulAntidiagonal` / 定理 `isPWO_support_smulAntidiagonal`

English:
theorem isPWO_support_smulAntidiagonal
  proof: (hs.smul ht).mono
    (support_smulAntidiagonal_subset_smul (fun a => (Set.SMulAntidiagonal.finite_of_isPWO hs ht a)))

中文:
定理 isPWO_support_smulAntidiagonal
  证明: (hs.smul ht).mono
    (support_smulAntidiagonal_subset_smul (fun a => (Set.SMulAntidiagonal.finite_of_isPWO hs ht a)))

Depends on / 依赖: SMulAntidiagonal, Set.SMulAntidiagonal.finite_of_isPWO, finite_of_isPWO, hs.smul, support_smulAntidiagonal_subset_smul
-/
theorem isPWO_support_smulAntidiagonal :
    { a | (SMulAntidiagonal a (Set.SMulAntidiagonal.finite_of_isPWO hs ht a)).Nonempty }.IsPWO :=
  (hs.smul ht).mono
    (support_smulAntidiagonal_subset_smul (fun a => (Set.SMulAntidiagonal.finite_of_isPWO hs ht a)))

end

@[to_additive]
/--
theorem `smulAntidiagonal_min_smul_min` / 定理 `smulAntidiagonal_min_smul_min`

English:
theorem smulAntidiagonal_min_smul_min
  statement: [LinearOrder G] [LinearOrder P] [SMul G P]
  proof: by
  ext ⟨a, b⟩
  simp only [mem_smulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, IsCancelSMul.left_canc

中文:
定理 smulAntidiagonal_min_smul_min
  结论: [线性序 G] [线性序 P] [标量乘法 G P]
  证明: by
  ext ⟨a, b⟩
  simp only [mem_smulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, IsCancelSMul.left_canc

Depends on / 依赖: IsCancelSMul, IsCancelSMul.left_cancel, Prod.ext_iff, SMul.smul_lt_smul_of_lt_of_le, eq_of_not_lt, ext_iff, hs.min_le, hs.min_mem, ht.min_le, ht.min_mem, left_cancel, mem_singleton, mem_smulAntidiagonal, min_le, min_mem, smul_lt_smul_of_lt_of_le
-/
theorem smulAntidiagonal_min_smul_min [LinearOrder G] [LinearOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty)
    (hnt : t.Nonempty) :
    SMulAntidiagonal (hs.min hns • ht.min hnt)
      (Set.SMulAntidiagonal.finite_of_isPWO hs.isPWO ht.isPWO (hs.min hns • ht.min hnt)) =
      {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_smulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, IsCancelSMul.left_cancel _ _ _ hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset
