/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!

# Integer elements of a localized module

This is a mirror of the corresponding notion for localizations of rings.

## Main definitions

* `IsLocalizedModule.IsInteger` is a predicate stating that `m : M'` is in the image of `M`

## Implementation details

After `IsLocalizedModule` and `IsLocalization` are unified, the two `IsInteger` predicates
can be unified.

-/

@[expose] public section


variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M ->ₗ[R] M')

open Function

namespace IsLocalizedModule

/--
Definition of `IsInteger` / `IsInteger` 的定义

English:
definition IsInteger
  signature: (x : M')
  body: x in LinearMap.range f

中文:
定义 Is整数eger
  签名: (x : M')
  定义体: x in LinearMap.range f

Depends on / 依赖: LinearMap, LinearMap.range
-/
def IsInteger (x : M') : Prop :=
  x in LinearMap.range f

/--
lemma `isInteger_zero` / 引理 `isInteger_zero`

English:
lemma isInteger_zero
  statement: IsInteger f (0 : M')
  proof: Submodule.zero_mem _

中文:
引理 is整数eger_zero
  结论: Is整数eger f (0 : M')
  证明: Submodule.zero_mem _

Depends on / 依赖: Submodule, Submodule.zero_mem, zero_mem
-/
lemma isInteger_zero : IsInteger f (0 : M') :=
  Submodule.zero_mem _

/--
theorem `isInteger_add` / 定理 `isInteger_add`

English:
theorem isInteger_add
  given: {x y : M'} (hx : IsInteger f x) (hy : IsInteger f y)
  statement: IsInteger f (x + y)
  proof: Submodule.add_mem _ hx hy

中文:
定理 is整数eger_add
  条件: {x y : M'} (hx : Is整数eger f x) (hy : Is整数eger f y)
  结论: Is整数eger f (x + y)
  证明: Submodule.add_mem _ hx hy

Depends on / 依赖: Submodule, Submodule.add_mem, add_mem
-/
theorem isInteger_add {x y : M'} (hx : IsInteger f x) (hy : IsInteger f y) : IsInteger f (x + y) :=
  Submodule.add_mem _ hx hy

/--
theorem `isInteger_smul` / 定理 `isInteger_smul`

English:
theorem isInteger_smul
  given: {a : R} {x : M'} (hx : IsInteger f x)
  statement: IsInteger f (a • x)
  proof: by
  rcases hx with ⟨x', hx⟩
  use a • x'
  rw [← hx]; rw [LinearMapClass.map_smul]

中文:
定理 is整数eger_smul
  条件: {a : R} {x : M'} (hx : Is整数eger f x)
  结论: Is整数eger f (a • x)
  证明: by
  rcases hx with ⟨x', hx⟩
  use a • x'
  rw [← hx]; rw [LinearMapClass.map_smul]

Depends on / 依赖: LinearMapClass, LinearMapClass.map_smul, map_smul
-/
theorem isInteger_smul {a : R} {x : M'} (hx : IsInteger f x) : IsInteger f (a • x) := by
  rcases hx with ⟨x', hx⟩
  use a • x'
  rw [← hx]; rw [LinearMapClass.map_smul]

variable (S)
variable [IsLocalizedModule S f]

/--
theorem `exists_integer_multiple` / 定理 `exists_integer_multiple`

English:
theorem exists_integer_multiple
  given: (x : M')
  statement: exists a : S, IsInteger f (a.val • x)
  proof: let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

中文:
定理 存在_integer_multiple
  条件: (x : M')
  结论: 存在 a : S, Is整数eger f (a.val • x)
  证明: let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.surj, Set.mem_range.mpr, h.symm, mem_range
-/
theorem exists_integer_multiple (x : M') : exists a : S, IsInteger f (a.val • x) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/--
theorem `exist_integer_multiples` / 定理 `exist_integer_multiples`

English:
theorem exist_integer_multiples
  given: {ι : Type*} (s : Finset ι) (g : ι -> M')
  proof: by
  classical
  choose sec hsec using (fun i => IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i in s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j in s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finsetProd]
    rw [← hsec]; rw [← mul_smul]; rw [Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finsetProd, mul_comm]
    rw [← Finset.prod_insert (f := fun i => ((sec i).snd).val) (s.notMem_erase i)]; rw [Finset.insert_erase hi]

中文:
定理 exist_integer_multiples
  条件: {ι : 类型} (s : 有限集 ι) (g : ι -> M')
  证明: by
  classical
  choose sec hsec using (fun i => IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i in s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j in s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finsetProd]
    rw [← hsec]; rw [← mul_smul]; rw [Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finsetProd, mul_comm]
    rw [← Finset.prod_insert (f := fun i => ((sec i).snd).val) (s.notMem_erase i)]; rw [Finset.insert_erase hi]

Depends on / 依赖: Finset, Finset.insert_erase, Finset.prod_insert, IsLocalizedModule, IsLocalizedModule.surj, LinearMap, LinearMap.map_smul_of_tower, Submonoid, Submonoid.coe_finsetProd, Submonoid.coe_mul, Submonoid.smul_def, classical, coe_finsetProd, coe_mul, insert_erase, map_smul_of_tower, mul_comm, mul_smul, notMem_erase, prod_insert
-/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι -> M') :
    exists b : S, forall i in s, IsInteger f (b.val • g i) := by
  classical
  choose sec hsec using (fun i => IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i in s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j in s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finsetProd]
    rw [← hsec]; rw [← mul_smul]; rw [Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finsetProd, mul_comm]
    rw [← Finset.prod_insert (f := fun i => ((sec i).snd).val) (s.notMem_erase i)]; rw [Finset.insert_erase hi]

/--
theorem `exist_integer_multiples_of_finite` / 定理 `exist_integer_multiples_of_finite`

English:
theorem exist_integer_multiples_of_finite
  given: {ι : Type*} [Finite ι] (g : ι -> M')
  proof: by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

中文:
定理 exist_integer_multiples_of_finite
  条件: {ι : 类型} [有限 ι] (g : ι -> M')
  证明: by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ, exist_integer_multiples, mem_univ, nonempty_fintype
-/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι -> M') :
    exists b : S, forall i, IsInteger f ((b : R) • g i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/--
theorem `exist_integer_multiples_of_finset` / 定理 `exist_integer_multiples_of_finset`

English:
theorem exist_integer_multiples_of_finset
  given: (s : Finset M')
  proof: exist_integer_multiples S f s id

中文:
定理 exist_integer_multiples_of_finset
  条件: (s : 有限集 M')
  证明: exist_integer_multiples S f s id

Depends on / 依赖: exist_integer_multiples
-/
theorem exist_integer_multiples_of_finset (s : Finset M') :
    exists b : S, forall a in s, IsInteger f ((b : R) • a) :=
  exist_integer_multiples S f s id

/--
Definition of `commonDenom` / `commonDenom` 的定义

English:
definition commonDenom
  signature: {ι : Type*} (s : Finset ι) (g : ι -> M')
  body: (exist_integer_multiples S f s g).choose

中文:
定义 commonDenom
  签名: {ι : 类型} (s : 有限集 ι) (g : ι -> M')
  定义体: (exist_integer_multiples S f s g).choose

Depends on / 依赖: exist_integer_multiples
-/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (g : ι -> M') : S :=
  (exist_integer_multiples S f s g).choose

/--
Definition of `integerMultiple` / `integerMultiple` 的定义

English:
definition integerMultiple
  signature: {ι : Type*} (s : Finset ι) (g : ι -> M') (i : s)
  body: ((exist_integer_multiples S f s g).choose_spec i i.prop).choose

@[simp]

中文:
定义 integerMultiple
  签名: {ι : 类型} (s : 有限集 ι) (g : ι -> M') (i : s)
  定义体: ((exist_integer_multiples S f s g).choose_spec i i.prop).choose

@[simp]

Depends on / 依赖: choose_spec, exist_integer_multiples, i.prop
-/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (g : ι -> M') (i : s) : M :=
  ((exist_integer_multiples S f s g).choose_spec i i.prop).choose

@[simp]
/--
theorem `map_integerMultiple` / 定理 `map_integerMultiple`

English:
theorem map_integerMultiple
  given: {ι : Type*} (s : Finset ι) (g : ι -> M') (i : s)
  proof: ((exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec

中文:
定理 map_integerMultiple
  条件: {ι : 类型} (s : 有限集 ι) (g : ι -> M') (i : s)
  证明: ((exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec

Depends on / 依赖: choose_spec, exist_integer_multiples, i.prop
-/
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (g : ι -> M') (i : s) :
    f (integerMultiple S f s g i) = commonDenom S f s g • g i :=
  ((exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec

/--
Definition of `commonDenomOfFinset` / `commonDenomOfFinset` 的定义

English:
definition commonDenomOfFinset
  signature: (s : Finset M')
  body: commonDenom S f s id

中文:
定义 commonDenomOfFinset
  签名: (s : 有限集 M')
  定义体: commonDenom S f s id

Depends on / 依赖: commonDenom
-/
noncomputable def commonDenomOfFinset (s : Finset M') : S :=
  commonDenom S f s id

/--
Definition of `finsetIntegerMultiple` / `finsetIntegerMultiple` 的定义

English:
definition finsetIntegerMultiple
  signature: [DecidableEq M] (s : Finset M')
  body: s.attach.image fun t => integerMultiple S f s id t

中文:
定义 finset整数egerMultiple
  签名: [DecidableEq M] (s : 有限集 M')
  定义体: s.attach.image fun t => integerMultiple S f s id t

Depends on / 依赖: attach, integerMultiple, s.attach.image
-/
noncomputable def finsetIntegerMultiple [DecidableEq M] (s : Finset M') : Finset M :=
  s.attach.image fun t => integerMultiple S f s id t

open scoped Pointwise

/--
theorem `finsetIntegerMultiple_image` / 定理 `finsetIntegerMultiple_image`

English:
theorem finsetIntegerMultiple_image
  given: [DecidableEq M] (s : Finset M')
  proof: by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple S f s id _⟩

中文:
定理 finset整数egerMultiple_image
  条件: [DecidableEq M] (s : 有限集 M')
  证明: by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple S f s id _⟩

Depends on / 依赖: Finset, Finset.coe_image, Set.mem_image_of_mem, coe_image, commonDenom, finsetIntegerMultiple, map_integerMultiple, mem_attach, mem_image_of_mem, s.mem_attach, x.prop
-/
theorem finsetIntegerMultiple_image [DecidableEq M] (s : Finset M') :
    f '' finsetIntegerMultiple S f s = commonDenomOfFinset S f s • (s : Set M') := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple S f s id _⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smul_mem_finsetIntegerMultiple_span` / 定理 `smul_mem_finsetIntegerMultiple_span`

English:
theorem smul_mem_finsetIntegerMultiple_span
  statement: [DecidableEq M] (x : M) (s : Finset M')
  proof: by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : y • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ in y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  rw [hx₁]; rw [← f.map_smul]; rw [← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert!
    (Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem a hx'
      using 1
  convert! ha.symm using 1
  simp only [Submonoid.smul_def, ← smul_smul]

中文:
定理 smul_mem_finset整数egerMultiple_span
  结论: [DecidableEq M] (x : M) (s : 有限集 M')
  证明: by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : y • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ in y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  rw [hx₁]; rw [← f.map_smul]; rw [← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert!
    (Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem a hx'
      using 1
  convert! ha.symm using 1
  simp only [Submonoid.smul_def, ← smul_smul]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.commonDenomOfFinset, IsLocalizedModule.eq_iff_exists, IsLocalizedModule.finsetIntegerMultiple_image, Set.smul_mem_smul_set, Submodule, Submodule.map_span, Submodule.sp, Submodule.span, Submodule.span_smul, commonDenomOfFinset, convert, eq_iff_exists, f.map_smul, finsetIntegerMultiple_image, map_smul, map_span, replace, smul_mem_smul_set, span_smul
-/
theorem smul_mem_finsetIntegerMultiple_span [DecidableEq M] (x : M) (s : Finset M')
    (hx : f x in Submodule.span R s) :
    exists (m : S), m • x in Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s) := by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : y • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ in y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  rw [hx₁]; rw [← f.map_smul]; rw [← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert!
    (Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem a hx'
      using 1
  convert! ha.symm using 1
  simp only [Submonoid.smul_def, ← smul_smul]

end IsLocalizedModule
