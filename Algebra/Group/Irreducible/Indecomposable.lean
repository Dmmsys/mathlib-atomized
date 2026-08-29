/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Indecomposable elements of monoids
-/

@[expose] public section

open Set

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

/-- Given a family of elements of a monoid, a member is said to be indecomposable if it cannot be
written as a product of two others in a non-trivial way. -/
@[to_additive (attr := simp) /-- Given a family of elements of an additive monoid, a member is said
to be indecomposable if it cannot be written as a sum of two others in a non-trivial way.-/]
/--
Definition of `IsMulIndecomposable` / `IsMulIndecomposable` 的定义

English:
definition IsMulIndecomposable
  signature: (v : ι -> M) (s : Set ι) (i : ι)
  body: i in s ∧ forallᵉ (j in s) (k in s), v i = v j * v k -> v j = 1 ∨ v k = 1

@[to_additive]

中文:
定义 IsMulIndecomposable
  签名: (v : ι -> M) (s : 集合 ι) (i : ι)
  定义体: i in s ∧ forallᵉ (j in s) (k in s), v i = v j * v k -> v j = 1 ∨ v k = 1

@[to_additive]
-/
def IsMulIndecomposable (v : ι -> M) (s : Set ι) (i : ι) : Prop :=
  i in s ∧ forallᵉ (j in s) (k in s), v i = v j * v k -> v j = 1 ∨ v k = 1

@[to_additive]
/--
lemma `IsMulIndecomposable.subset` / 引理 `IsMulIndecomposable.subset`

English:
lemma IsMulIndecomposable.subset
  given: (v : ι -> M) (s : Set ι)
  proof: by
  aesop

@[to_additive]

中文:
引理 IsMulIndecomposable.subset
  条件: (v : ι -> M) (s : 集合 ι)
  证明: by
  aesop

@[to_additive]
-/
protected lemma IsMulIndecomposable.subset (v : ι -> M) (s : Set ι) :
    {i | IsMulIndecomposable v s i} subseteq s := by
  aesop

@[to_additive]
/--
lemma `isMulIndecomposable_id_univ` / 引理 `isMulIndecomposable_id_univ`

English:
lemma isMulIndecomposable_id_univ
  given: [Subsingleton Mˣ] {x : M} (hx : x != 1)
  proof: ⟨fun h => ⟨by simpa, by simpa using h⟩, fun h => by simpa using h.isUnit_or_isUnit⟩

中文:
引理 isMulIndecomposable_id_univ
  条件: [子单例 Mˣ] {x : M} (hx : x != 1)
  证明: ⟨fun h => ⟨by simpa, by simpa using h⟩, fun h => by simpa using h.isUnit_or_isUnit⟩

Depends on / 依赖: h.isUnit_or_isUnit, isUnit_or_isUnit
-/
lemma isMulIndecomposable_id_univ [Subsingleton Mˣ] {x : M} (hx : x != 1) :
    IsMulIndecomposable id univ x ↔ Irreducible x :=
  ⟨fun h => ⟨by simpa, by simpa using h⟩, fun h => by simpa using h.isUnit_or_isUnit⟩

/-- The "base" of a set of points of a monoid relative to a morphism `f`. -/
@[to_additive /-- The "base" of `v` relative to a morphism `f`.

In the case that `v` is the set of roots of a crystallographic root system, and `S = ℚ`, this is the
base of the root system associated to `f`. -/]
/--
Definition of `IsMulIndecomposable.baseOf` / `IsMulIndecomposable.baseOf` 的定义

English:
definition IsMulIndecomposable.baseOf
  signature: [Monoid S] (v : ι -> M) (f : M ->* S)
  body: {j | IsMulIndecomposable v {i | 1 < f (v i)} j}

@[to_additive]

中文:
定义 IsMulIndecomposable.baseOf
  签名: [幺半群 S] (v : ι -> M) (f : M ->* S)
  定义体: {j | IsMulIndecomposable v {i | 1 < f (v i)} j}

@[to_additive]

Depends on / 依赖: IsMulIndecomposable
-/
def IsMulIndecomposable.baseOf [Monoid S] (v : ι -> M) (f : M ->* S) : Set ι :=
  {j | IsMulIndecomposable v {i | 1 < f (v i)} j}

@[to_additive]
/--
lemma `IsMulIndecomposable.baseOf_subset_one_lt` / 引理 `IsMulIndecomposable.baseOf_subset_one_lt`

English:
lemma IsMulIndecomposable.baseOf_subset_one_lt
  given: [Monoid S] (v : ι -> M) (f : M ->* S)
  proof: IsMulIndecomposable.subset _ _

@[to_additive]

中文:
引理 IsMulIndecomposable.baseOf_subset_one_lt
  条件: [幺半群 S] (v : ι -> M) (f : M ->* S)
  证明: IsMulIndecomposable.subset _ _

@[to_additive]

Depends on / 依赖: IsMulIndecomposable, IsMulIndecomposable.subset, subset
-/
lemma IsMulIndecomposable.baseOf_subset_one_lt [Monoid S] (v : ι -> M) (f : M ->* S) :
    IsMulIndecomposable.baseOf v f subseteq {i | 1 < f (v i)} :=
  IsMulIndecomposable.subset _ _

@[to_additive]
/--
lemma `IsMulIndecomposable.image_baseOf_inv_comp_eq` / 引理 `IsMulIndecomposable.image_baseOf_inv_comp_eq`

English:
lemma IsMulIndecomposable.image_baseOf_inv_comp_eq
  statement: [InvolutiveInv ι]
  proof: by
  suffices forall (f : G ->* S),
      v '' baseOf v (invMonoidHom.comp f) subseteq (invMonoidHom ∘ v) '' baseOf v f by
    apply subset_antisymm (this f)
replace this := image_mono (f := invMonoidHom) this (invMonoidHom.comp f)
    rw [← MonoidHom.comp_assoc]; rw [invMonoidHom_comp_invMonoidHom]; rw [MonoidHom.id_comp]; rw [image_comp]; rw [← image_comp invMonoidHom invMonoidHom]; rw [← MonoidHom.coe_comp]; rw [invMonoidHom_comp_invMonoidHom]; rw [← image_comp] at this
    simpa using this
  clear f
  rintro f g ⟨i, ⟨hi, hi'⟩, rfl⟩
  refine ⟨i⁻¹, ⟨by simpa [hv_inv] using hi, fun j hj k hk hi => ?_⟩, by simp [hv_inv]⟩
  replace hi : v i = v j⁻¹ * v k⁻¹ := by
    rwa [hv_inv, inv_eq_iff_eq_inv, mul_inv, ← hv_inv, ← hv_inv] at hi
  specialize hi' j⁻¹ (by simpa [hv_inv]) k⁻¹ (by simpa [hv_inv]) hi
  aesop

中文:
引理 IsMulIndecomposable.image_baseOf_inv_comp_eq
  结论: [InvolutiveInv ι]
  证明: by
  suffices forall (f : G ->* S),
      v '' baseOf v (invMonoidHom.comp f) subseteq (invMonoidHom ∘ v) '' baseOf v f by
    apply subset_antisymm (this f)
replace this := image_mono (f := invMonoidHom) this (invMonoidHom.comp f)
    rw [← MonoidHom.comp_assoc]; rw [invMonoidHom_comp_invMonoidHom]; rw [MonoidHom.id_comp]; rw [image_comp]; rw [← image_comp invMonoidHom invMonoidHom]; rw [← MonoidHom.coe_comp]; rw [invMonoidHom_comp_invMonoidHom]; rw [← image_comp] at this
    simpa using this
  clear f
  rintro f g ⟨i, ⟨hi, hi'⟩, rfl⟩
  refine ⟨i⁻¹, ⟨by simpa [hv_inv] using hi, fun j hj k hk hi => ?_⟩, by simp [hv_inv]⟩
  replace hi : v i = v j⁻¹ * v k⁻¹ := by
    rwa [hv_inv, inv_eq_iff_eq_inv, mul_inv, ← hv_inv, ← hv_inv] at hi
  specialize hi' j⁻¹ (by simpa [hv_inv]) k⁻¹ (by simpa [hv_inv]) hi
  aesop

Depends on / 依赖: MonoidHom, MonoidHom.coe_comp, MonoidHom.comp_assoc, MonoidHom.id_comp, baseOf, coe_comp, comp_assoc, id_comp, image_comp, image_mono, invMonoidHom, invMonoidHom.comp, invMonoidHom_comp_invMonoidHom, replace, subset_antisymm, subseteq
-/
lemma IsMulIndecomposable.image_baseOf_inv_comp_eq [InvolutiveInv ι]
    [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹)
    (f : G ->* S) :
    v '' baseOf v (invMonoidHom.comp f) = (invMonoidHom ∘ v) '' baseOf v f := by
  suffices forall (f : G ->* S),
      v '' baseOf v (invMonoidHom.comp f) subseteq (invMonoidHom ∘ v) '' baseOf v f by
    apply subset_antisymm (this f)
replace this := image_mono (f := invMonoidHom) this (invMonoidHom.comp f)
    rw [← MonoidHom.comp_assoc]; rw [invMonoidHom_comp_invMonoidHom]; rw [MonoidHom.id_comp]; rw [image_comp]; rw [← image_comp invMonoidHom invMonoidHom]; rw [← MonoidHom.coe_comp]; rw [invMonoidHom_comp_invMonoidHom]; rw [← image_comp] at this
    simpa using this
  clear f
  rintro f g ⟨i, ⟨hi, hi'⟩, rfl⟩
  refine ⟨i⁻¹, ⟨by simpa [hv_inv] using hi, fun j hj k hk hi => ?_⟩, by simp [hv_inv]⟩
  replace hi : v i = v j⁻¹ * v k⁻¹ := by
    rwa [hv_inv, inv_eq_iff_eq_inv, mul_inv, ← hv_inv, ← hv_inv] at hi
  specialize hi' j⁻¹ (by simpa [hv_inv]) k⁻¹ (by simpa [hv_inv]) hi
  aesop

/-- Given a finite family of points `v` in a monoid `M`, together with a morphism into a
linearly-ordered monoid `f : M →* S`, the submonoid generated by those points of `v` which lie in
the "half space" where `f > 1` is generated by the subset of such points which are indecomposable
with respect to points in this half space. -/
@[to_additive /-- Given a finite family of points `v` in an additive monoid `M`, together with a
morphism into a linearly-ordered additive monoid `f : M →+ S`, the submonoid generated by those
points of `v` which lie in the half space where `f > 0` is generated by the subset of such points
which are indecomposable with respect to points in this half space.

If `v` is the set of roots of a crystallographic root system and `S = ℚ`, then this is
[serre1965](Ch. V, §9, Lemma 2) and it may be used to prove that the root system has a base. -/]
/--
lemma `Submonoid.closure_image_isMulIndecomposable_baseOf` / 引理 `Submonoid.closure_image_isMulIndecomposable_baseOf`

English:
lemma Submonoid.closure_image_isMulIndecomposable_baseOf
  statement: [Finite ι]
  proof: by
  refine le_antisymm (closure_mono (image_mono <| IsMulIndecomposable.baseOf_subset_one_lt v f))
    (closure_le.mpr ?_)
  rintro - ⟨i, hi : 1 < f (v i), rfl⟩
  by_contra hi'
  let t : Set ι := {i | IsMulIndecomposable v {j | 1 < f (v j)} i}
  let s : Set ι := {j | 1 < f (v j) ∧ v j ∉ closure (v '' t)}
  have hne : s.Nonempty := ⟨i, hi, hi'⟩
  clear! i
  obtain ⟨i, hi⟩ := s.toFinite.exists_minimalFor (f ∘ v) s hne
  have ⟨(hi₀ : 1 < f (v i)), (hi₁ : v i ∉ _)⟩ : i in s := hi.prop
  have hi₂ (k : ι) (hk₀ : 1 < f (v k)) (hk₁ : f (v k) < f (v i)) : v k in closure (v '' t) := by
by_contra hk₂; exact not_le.mpr hk₁ hi.le_of_le ⟨hk₀, hk₂⟩ hk₁.le
have hi₃ : i ∉ t := by contrapose hi₁; exact subset_closure mem_image_of_mem v hi₁
  obtain ⟨j, k, hj, hk, hjk⟩ : exists (j k : ι) (hj : 1 < f (v j)) (hk : 1 < f (v k)),
      v i = v j * v k := by
    grind [IsMulIndecomposable]
have hj' : v j in closure (v '' t) := hi₂ j hj by aesop
have hk' : v k in closure (v '' t) := hi₂ k hk by aesop
  replace hjk : v i in closure (v '' t) := hjk ▸ mul_mem hj' hk'
  exact hi₁ hjk

@[to_additive]

中文:
引理 子幺半群.closure_image_isMulIndecomposable_baseOf
  结论: [有限 ι]
  证明: by
  refine le_antisymm (closure_mono (image_mono <| IsMulIndecomposable.baseOf_subset_one_lt v f))
    (closure_le.mpr ?_)
  rintro - ⟨i, hi : 1 < f (v i), rfl⟩
  by_contra hi'
  let t : Set ι := {i | IsMulIndecomposable v {j | 1 < f (v j)} i}
  let s : Set ι := {j | 1 < f (v j) ∧ v j ∉ closure (v '' t)}
  have hne : s.Nonempty := ⟨i, hi, hi'⟩
  clear! i
  obtain ⟨i, hi⟩ := s.toFinite.exists_minimalFor (f ∘ v) s hne
  have ⟨(hi₀ : 1 < f (v i)), (hi₁ : v i ∉ _)⟩ : i in s := hi.prop
  have hi₂ (k : ι) (hk₀ : 1 < f (v k)) (hk₁ : f (v k) < f (v i)) : v k in closure (v '' t) := by
by_contra hk₂; exact not_le.mpr hk₁ hi.le_of_le ⟨hk₀, hk₂⟩ hk₁.le
have hi₃ : i ∉ t := by contrapose hi₁; exact subset_closure mem_image_of_mem v hi₁
  obtain ⟨j, k, hj, hk, hjk⟩ : exists (j k : ι) (hj : 1 < f (v j)) (hk : 1 < f (v k)),
      v i = v j * v k := by
    grind [IsMulIndecomposable]
have hj' : v j in closure (v '' t) := hi₂ j hj by aesop
have hk' : v k in closure (v '' t) := hi₂ k hk by aesop
  replace hjk : v i in closure (v '' t) := hjk ▸ mul_mem hj' hk'
  exact hi₁ hjk

@[to_additive]

Depends on / 依赖: IsMulIndecomposable, IsMulIndecomposable.baseOf_subset_one_lt, Nonempty, baseOf_subset_one_lt, closure, closure_le, closure_le.mpr, closure_mono, exists_minimalFor, hi.prop, image_mono, le_antisymm, s.Nonempty, s.toFinite.exists_minimalFor, toFinite
-/
lemma Submonoid.closure_image_isMulIndecomposable_baseOf [Finite ι]
    [CommMonoid S] [IsOrderedCancelMonoid S]
    (v : ι -> M) (f : M ->* S) :
    closure (v '' IsMulIndecomposable.baseOf v f) = closure (v '' {i | 1 < f (v i)}) := by
  refine le_antisymm (closure_mono (image_mono <| IsMulIndecomposable.baseOf_subset_one_lt v f))
    (closure_le.mpr ?_)
  rintro - ⟨i, hi : 1 < f (v i), rfl⟩
  by_contra hi'
  let t : Set ι := {i | IsMulIndecomposable v {j | 1 < f (v j)} i}
  let s : Set ι := {j | 1 < f (v j) ∧ v j ∉ closure (v '' t)}
  have hne : s.Nonempty := ⟨i, hi, hi'⟩
  clear! i
  obtain ⟨i, hi⟩ := s.toFinite.exists_minimalFor (f ∘ v) s hne
  have ⟨(hi₀ : 1 < f (v i)), (hi₁ : v i ∉ _)⟩ : i in s := hi.prop
  have hi₂ (k : ι) (hk₀ : 1 < f (v k)) (hk₁ : f (v k) < f (v i)) : v k in closure (v '' t) := by
by_contra hk₂; exact not_le.mpr hk₁ hi.le_of_le ⟨hk₀, hk₂⟩ hk₁.le
have hi₃ : i ∉ t := by contrapose hi₁; exact subset_closure mem_image_of_mem v hi₁
  obtain ⟨j, k, hj, hk, hjk⟩ : exists (j k : ι) (hj : 1 < f (v j)) (hk : 1 < f (v k)),
      v i = v j * v k := by
    grind [IsMulIndecomposable]
have hj' : v j in closure (v '' t) := hi₂ j hj by aesop
have hk' : v k in closure (v '' t) := hi₂ k hk by aesop
  replace hjk : v i in closure (v '' t) := hjk ▸ mul_mem hj' hk'
  exact hi₁ hjk

@[to_additive]
/--
lemma `Subgroup.closure_image_isMulIndecomposable_baseOf` / 引理 `Subgroup.closure_image_isMulIndecomposable_baseOf`

English:
lemma Subgroup.closure_image_isMulIndecomposable_baseOf
  statement: [Finite ι] [InvolutiveInv ι]
  proof: by
  rw [← image_univ]
  refine le_antisymm (closure_mono (image_mono <| by simp)) ((closure_le _).mpr ?_)
  have : univ = {i | 1 < f (v i)} union {i | f (v i) < 1} := by ext i; simp [(hf i).symm]
  rw [this]; rw [image_union]; rw [union_subset_iff]
  refine ⟨le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f)), ?_⟩
  · simp [Submonoid.closure_image_isMulIndecomposable_baseOf]
  · let f' : G ->* S := invMonoidHom.comp f
    have h₁ : (invMonoidHom ∘ v) '' IsMulIndecomposable.baseOf v f' =
        v '' IsMulIndecomposable.baseOf v f := by
      rw [image_comp]; rw [IsMulIndecomposable.image_baseOf_inv_comp_eq v hv_inv f]; rw [image_comp]; rw [← image_comp]
      simp
    have h₂ : v '' {i | f (v i) < 1} = v '' {i | 1 < f' (v i)} := by simp [f']
    rw [h₂]; rw [← h₁]; rw [image_comp]; rw [coe_invMonoidHom]; rw [image_inv_eq_inv]; rw [closure_inv]
    refine le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f'))
    simp [Submonoid.closure_image_isMulIndecomposable_baseOf]

中文:
引理 子群.closure_image_isMulIndecomposable_baseOf
  结论: [有限 ι] [InvolutiveInv ι]
  证明: by
  rw [← image_univ]
  refine le_antisymm (closure_mono (image_mono <| by simp)) ((closure_le _).mpr ?_)
  have : univ = {i | 1 < f (v i)} union {i | f (v i) < 1} := by ext i; simp [(hf i).symm]
  rw [this]; rw [image_union]; rw [union_subset_iff]
  refine ⟨le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f)), ?_⟩
  · simp [Submonoid.closure_image_isMulIndecomposable_baseOf]
  · let f' : G ->* S := invMonoidHom.comp f
    have h₁ : (invMonoidHom ∘ v) '' IsMulIndecomposable.baseOf v f' =
        v '' IsMulIndecomposable.baseOf v f := by
      rw [image_comp]; rw [IsMulIndecomposable.image_baseOf_inv_comp_eq v hv_inv f]; rw [image_comp]; rw [← image_comp]
      simp
    have h₂ : v '' {i | f (v i) < 1} = v '' {i | 1 < f' (v i)} := by simp [f']
    rw [h₂]; rw [← h₁]; rw [image_comp]; rw [coe_invMonoidHom]; rw [image_inv_eq_inv]; rw [closure_inv]
    refine le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f'))
    simp [Submonoid.closure_image_isMulIndecomposable_baseOf]

Depends on / 依赖: IsMulIndecomposable, IsMulIndecomposable.baseOf, Submonoid, Submonoid.closure_image_isMulIndecomposable_baseOf, baseOf, closure_image_isMulIndecomposable_baseOf, closure_le, closure_mono, image_mono, image_union, image_univ, invMonoidHom, invMonoidHom.comp, le_antisymm, le_closure_toSubmonoid, le_trans, union_subset_iff
-/
lemma Subgroup.closure_image_isMulIndecomposable_baseOf [Finite ι] [InvolutiveInv ι]
    [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹)
    (f : G ->* S) (hf : forall i, f (v i) != 1) :
    closure (v '' IsMulIndecomposable.baseOf v f) = closure (range v) := by
  rw [← image_univ]
  refine le_antisymm (closure_mono (image_mono <| by simp)) ((closure_le _).mpr ?_)
  have : univ = {i | 1 < f (v i)} union {i | f (v i) < 1} := by ext i; simp [(hf i).symm]
  rw [this]; rw [image_union]; rw [union_subset_iff]
  refine ⟨le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f)), ?_⟩
  · simp [Submonoid.closure_image_isMulIndecomposable_baseOf]
  · let f' : G ->* S := invMonoidHom.comp f
    have h₁ : (invMonoidHom ∘ v) '' IsMulIndecomposable.baseOf v f' =
        v '' IsMulIndecomposable.baseOf v f := by
      rw [image_comp]; rw [IsMulIndecomposable.image_baseOf_inv_comp_eq v hv_inv f]; rw [image_comp]; rw [← image_comp]
      simp
    have h₂ : v '' {i | f (v i) < 1} = v '' {i | 1 < f' (v i)} := by simp [f']
    rw [h₂]; rw [← h₁]; rw [image_comp]; rw [coe_invMonoidHom]; rw [image_inv_eq_inv]; rw [closure_inv]
    refine le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f'))
    simp [Submonoid.closure_image_isMulIndecomposable_baseOf]

namespace IsMulIndecomposable

@[to_additive]
/--
lemma `pairwise_div_notMem_range` / 引理 `pairwise_div_notMem_range`

English:
lemma pairwise_div_notMem_range
  statement: [InvolutiveInv ι]
  proof: by
  have h_sub : s subseteq t := hst.trans (IsMulIndecomposable.subset _ _)
  intro i hi j hj hne
  by_contra! ⟨k, hk⟩
  rcases hv_t k with hk' | hk'
  · suffices ¬ IsMulIndecomposable v t i from this (hst hi)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ => ⟨k, hk', j, h_sub hj, by simp [hk]⟩
  · suffices ¬ IsMulIndecomposable v t j from this (hst hj)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ => ⟨k⁻¹, hk', i, h_sub hi, by simp [hv_inv, hk]⟩

@[to_additive]

中文:
引理 pairwise_div_notMem_range
  结论: [InvolutiveInv ι]
  证明: by
  have h_sub : s subseteq t := hst.trans (IsMulIndecomposable.subset _ _)
  intro i hi j hj hne
  by_contra! ⟨k, hk⟩
  rcases hv_t k with hk' | hk'
  · suffices ¬ IsMulIndecomposable v t i from this (hst hi)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ => ⟨k, hk', j, h_sub hj, by simp [hk]⟩
  · suffices ¬ IsMulIndecomposable v t j from this (hst hj)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ => ⟨k⁻¹, hk', i, h_sub hi, by simp [hv_inv, hk]⟩

@[to_additive]

Depends on / 依赖: IsMulIndecomposable, IsMulIndecomposable.subset, h_sub, hst.trans, hv_one, hv_t, imp_false, not_and, not_forall, not_not, or_self, subset, subseteq
-/
lemma pairwise_div_notMem_range [InvolutiveInv ι]
    (v : ι -> G)
    (hv_one : forall i, v i != 1)
    (hv_inv : forall i, v i⁻¹ = (v i)⁻¹)
    (s t : Set ι)
    (hst : s subseteq {i | IsMulIndecomposable v t i})
    (hv_t : forall i, i in t ∨ i⁻¹ in t) :
    s.Pairwise fun i j => v i / v j ∉ range v := by
  have h_sub : s subseteq t := hst.trans (IsMulIndecomposable.subset _ _)
  intro i hi j hj hne
  by_contra! ⟨k, hk⟩
  rcases hv_t k with hk' | hk'
  · suffices ¬ IsMulIndecomposable v t i from this (hst hi)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ => ⟨k, hk', j, h_sub hj, by simp [hk]⟩
  · suffices ¬ IsMulIndecomposable v t j from this (hst hj)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ => ⟨k⁻¹, hk', i, h_sub hi, by simp [hv_inv, hk]⟩

@[to_additive]
/--
lemma `pairwise_div_notMem_range'` / 引理 `pairwise_div_notMem_range'`

English:
lemma pairwise_div_notMem_range'
  statement: [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
  proof: by
  have hv_one : forall i, v i != 1 := fun i => by contrapose! hf; exact ⟨i, by simp [hf]⟩
  apply pairwise_div_notMem_range v hv_one hv_inv s {i | 1 < f (v i)} hst fun i => ?_
  simpa [hv_inv] using (hf i).symm

@[to_additive]

中文:
引理 pairwise_div_notMem_range'
  结论: [InvolutiveInv ι] [交换群 S] [是Ordered幺半群 S]
  证明: by
  have hv_one : forall i, v i != 1 := fun i => by contrapose! hf; exact ⟨i, by simp [hf]⟩
  apply pairwise_div_notMem_range v hv_one hv_inv s {i | 1 < f (v i)} hst fun i => ?_
  simpa [hv_inv] using (hf i).symm

@[to_additive]

Depends on / 依赖: contrapose, hv_inv, hv_one, pairwise_div_notMem_range
-/
lemma pairwise_div_notMem_range' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹)
    (f : G ->* S) (hf : forall i, f (v i) != 1)
    (s : Set ι) (hst : s subseteq {j | IsMulIndecomposable v {i | 1 < f (v i)} j}) :
    s.Pairwise fun i j => v i / v j ∉ range v := by
  have hv_one : forall i, v i != 1 := fun i => by contrapose! hf; exact ⟨i, by simp [hf]⟩
  apply pairwise_div_notMem_range v hv_one hv_inv s {i | 1 < f (v i)} hst fun i => ?_
  simpa [hv_inv] using (hf i).symm

@[to_additive]
/--
lemma `pairwise_baseOf_div_notMem` / 引理 `pairwise_baseOf_div_notMem`

English:
lemma pairwise_baseOf_div_notMem
  statement: [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
  proof: pairwise_div_notMem_range' v hv_inv f hf (baseOf v f) (.refl _)

中文:
引理 pairwise_baseOf_div_notMem
  结论: [InvolutiveInv ι] [交换群 S] [是Ordered幺半群 S]
  证明: pairwise_div_notMem_range' v hv_inv f hf (baseOf v f) (.refl _)

Depends on / 依赖: baseOf, hv_inv, pairwise_div_notMem_range
-/
lemma pairwise_baseOf_div_notMem [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G) (hv_inv : forall i, v i⁻¹ = (v i)⁻¹)
    (f : G ->* S) (hf : forall i, f (v i) != 1) :
    (baseOf v f).Pairwise fun i j => v i / v j ∉ range v :=
  pairwise_div_notMem_range' v hv_inv f hf (baseOf v f) (.refl _)

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[to_additive]
/--
lemma `mem_or_inv_mem_closure_baseOf` / 引理 `mem_or_inv_mem_closure_baseOf`

English:
lemma mem_or_inv_mem_closure_baseOf
  statement: [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
  proof: by
  rw [Submonoid.closure_image_isMulIndecomposable_baseOf v f]
  rcases lt_or_gt_of_ne hi with hj | hj
  · right
    exact Submonoid.subset_closure ⟨i⁻¹, by simpa [hi']⟩
  · left
    exact Submonoid.subset_closure ⟨i, by simpa⟩

中文:
引理 mem_or_inv_mem_closure_baseOf
  结论: [有限 ι] [InvolutiveInv ι] [交换群 S] [是Ordered幺半群 S]
  证明: by
  rw [Submonoid.closure_image_isMulIndecomposable_baseOf v f]
  rcases lt_or_gt_of_ne hi with hj | hj
  · right
    exact Submonoid.subset_closure ⟨i⁻¹, by simpa [hi']⟩
  · left
    exact Submonoid.subset_closure ⟨i, by simpa⟩

Depends on / 依赖: Submonoid, Submonoid.closure_image_isMulIndecomposable_baseOf, Submonoid.subset_closure, closure_image_isMulIndecomposable_baseOf, lt_or_gt_of_ne, subset_closure
-/
lemma mem_or_inv_mem_closure_baseOf [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G)
    (f : G ->* S) (i : ι) (hi : f (v i) != 1) (hi' : v i⁻¹ = (v i)⁻¹) :
     v i in Submonoid.closure (v '' baseOf v f) ∨
    (v i)⁻¹ in Submonoid.closure (v '' baseOf v f) := by
  rw [Submonoid.closure_image_isMulIndecomposable_baseOf v f]
  rcases lt_or_gt_of_ne hi with hj | hj
  · right
    exact Submonoid.subset_closure ⟨i⁻¹, by simpa [hi']⟩
  · left
    exact Submonoid.subset_closure ⟨i, by simpa⟩

end IsMulIndecomposable

@[to_additive]
/--
lemma `Submonoid.mem_closure_image_one_lt_iff` / 引理 `Submonoid.mem_closure_image_one_lt_iff`

English:
lemma Submonoid.mem_closure_image_one_lt_iff
  statement: [CommMonoid S] [IsOrderedCancelMonoid S]
  proof: by
refine ⟨fun hi => ?_, fun hi => subset_closure mem_image_of_mem v hi⟩
  suffices v i = 1 ∨ 1 < f (v i) from this.resolve_left hv_one
  refine closure_induction (by grind) (by simp) (fun x y _ _ hx hy => ?_) hi
  rcases hx with rfl | hx; · simpa
  rcases hy with rfl | hy; · right; simpa
  right
  simpa only [map_mul] using Left.one_lt_mul hx hy

@[to_additive]

中文:
引理 子幺半群.mem_closure_image_one_lt_iff
  结论: [交换幺半群 S] [是OrderedCancel幺半群 S]
  证明: by
refine ⟨fun hi => ?_, fun hi => subset_closure mem_image_of_mem v hi⟩
  suffices v i = 1 ∨ 1 < f (v i) from this.resolve_left hv_one
  refine closure_induction (by grind) (by simp) (fun x y _ _ hx hy => ?_) hi
  rcases hx with rfl | hx; · simpa
  rcases hy with rfl | hy; · right; simpa
  right
  simpa only [map_mul] using Left.one_lt_mul hx hy

@[to_additive]

Depends on / 依赖: Left.one_lt_mul, closure_induction, hv_one, map_mul, mem_image_of_mem, one_lt_mul, resolve_left, subset_closure, this.resolve_left
-/
lemma Submonoid.mem_closure_image_one_lt_iff [CommMonoid S] [IsOrderedCancelMonoid S]
    (v : ι -> M) (f : M ->* S) (i : ι) (hv_one : v i != 1) :
    v i in closure (v '' {i | 1 < f (v i)}) ↔ 1 < f (v i) := by
refine ⟨fun hi => ?_, fun hi => subset_closure mem_image_of_mem v hi⟩
  suffices v i = 1 ∨ 1 < f (v i) from this.resolve_left hv_one
  refine closure_induction (by grind) (by simp) (fun x y _ _ hx hy => ?_) hi
  rcases hx with rfl | hx; · simpa
  rcases hy with rfl | hy; · right; simpa
  right
  simpa only [map_mul] using Left.one_lt_mul hx hy

@[to_additive]
/--
lemma `Submonoid.apply_ne_one_of_mem_or_inv_mem_closure` / 引理 `Submonoid.apply_ne_one_of_mem_or_inv_mem_closure`

English:
lemma Submonoid.apply_ne_one_of_mem_or_inv_mem_closure
  proof: by
  wlog hi : v i in closure (v '' s)
  · rcases hsp with hi' | hi'; · contradiction
    simpa [hv_inv] using this v f s hf i⁻¹ (by simpa [hv_inv]) (by simp [hv_inv])
      (by left; simpa [hv_inv]) (by simpa [hv_inv])
  suffices v i != 1 -> 1 < f (v i) from (this hv_one).ne'
  refine closure_induction (by simp_all) (by simp) (fun x y _ _ hx hy _ => ?_) hi
  rcases eq_or_ne x 1 with rfl | hx'; · grind
  rcases eq_or_ne y 1 with rfl | hy'; · grind
  simpa using lt_mul_of_lt_of_one_lt (hx hx') (hy hy')

中文:
引理 子幺半群.apply_ne_one_of_mem_or_inv_mem_closure
  证明: by
  wlog hi : v i in closure (v '' s)
  · rcases hsp with hi' | hi'; · contradiction
    simpa [hv_inv] using this v f s hf i⁻¹ (by simpa [hv_inv]) (by simp [hv_inv])
      (by left; simpa [hv_inv]) (by simpa [hv_inv])
  suffices v i != 1 -> 1 < f (v i) from (this hv_one).ne'
  refine closure_induction (by simp_all) (by simp) (fun x y _ _ hx hy _ => ?_) hi
  rcases eq_or_ne x 1 with rfl | hx'; · grind
  rcases eq_or_ne y 1 with rfl | hy'; · grind
  simpa using lt_mul_of_lt_of_one_lt (hx hx') (hy hy')

Depends on / 依赖: closure, closure_induction, eq_or_ne, hv_inv, hv_one, lt_mul_of_lt_of_one_lt
-/
lemma Submonoid.apply_ne_one_of_mem_or_inv_mem_closure
    [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G)
    (f : G ->* S)
    (s : Set ι)
    (hf : forall i in s, 1 < f (v i))
    (i : ι) (hv_one : v i != 1) (hv_inv : v i⁻¹ = (v i)⁻¹)
    (hsp : v i in closure (v '' s) ∨ (v i)⁻¹ in closure (v '' s)) :
    f (v i) != 1 := by
  wlog hi : v i in closure (v '' s)
  · rcases hsp with hi' | hi'; · contradiction
    simpa [hv_inv] using this v f s hf i⁻¹ (by simpa [hv_inv]) (by simp [hv_inv])
      (by left; simpa [hv_inv]) (by simpa [hv_inv])
  suffices v i != 1 -> 1 < f (v i) from (this hv_one).ne'
  refine closure_induction (by simp_all) (by simp) (fun x y _ _ hx hy _ => ?_) hi
  rcases eq_or_ne x 1 with rfl | hx'; · grind
  rcases eq_or_ne y 1 with rfl | hy'; · grind
  simpa using lt_mul_of_lt_of_one_lt (hx hx') (hy hy')

open Submonoid in
@[to_additive]
/--
lemma `IsMulIndecomposable.apply_ne_one_iff_mem_closure` / 引理 `IsMulIndecomposable.apply_ne_one_iff_mem_closure`

English:
lemma IsMulIndecomposable.apply_ne_one_iff_mem_closure
  proof: ⟨fun h => mem_or_inv_mem_closure_baseOf v f i h hi',
    apply_ne_one_of_mem_or_inv_mem_closure v f (baseOf v f) (baseOf_subset_one_lt v f) i hi hi'⟩

中文:
引理 IsMulIndecomposable.apply_ne_one_iff_mem_closure
  证明: ⟨fun h => mem_or_inv_mem_closure_baseOf v f i h hi',
    apply_ne_one_of_mem_or_inv_mem_closure v f (baseOf v f) (baseOf_subset_one_lt v f) i hi hi'⟩

Depends on / 依赖: apply_ne_one_of_mem_or_inv_mem_closure, baseOf, baseOf_subset_one_lt, mem_or_inv_mem_closure_baseOf
-/
lemma IsMulIndecomposable.apply_ne_one_iff_mem_closure
    [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι -> G) (f : G ->* S) (i : ι) (hi : v i != 1) (hi' : v i⁻¹ = (v i)⁻¹) :
    f (v i) != 1 ↔ v i in closure (v '' baseOf v f) ∨ (v i)⁻¹ in closure (v '' baseOf v f) :=
  ⟨fun h => mem_or_inv_mem_closure_baseOf v f i h hi',
    apply_ne_one_of_mem_or_inv_mem_closure v f (baseOf v f) (baseOf_subset_one_lt v f) i hi hi'⟩
