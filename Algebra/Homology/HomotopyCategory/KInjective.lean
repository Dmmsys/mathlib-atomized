/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# K-injective cochain complexes

We define the notion of K-injective cochain complex in an abelian category,
and show that bounded below complexes of injective objects are K-injective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using an injective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex Preadditive

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `K`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `K`.)
/--
Definition of `IsKInjective` / `IsKInjective` 的定义

English:
class IsKInjective
  parameters: (L : CochainComplex C Int)
  axioms and operations (1):
    - nonempty_homotopy_zero({K : CochainComplex C Int} (f : K ⟶ L)) : K.Acyclic -> Nonempty (Homotopy f 0)

中文:
类 是KInjective
  参数: (L : 上链复形 C 整数)
  公理与运算 (1 个):
    - nonempty_homotopy_zero({K : 上链复形 C 整数} (f : K ⟶ L)) : K.非循环 -> 非空 (同伦 f 0)

Depends on / 依赖: IsKInjective, IsKInjective.nonempty_homotopy_zero, nonempty_homotopy_zero
-/
class IsKInjective (L : CochainComplex C Int) : Prop where
  nonempty_homotopy_zero {K : CochainComplex C Int} (f : K ⟶ L) :
    K.Acyclic -> Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from an acyclic
cochain complex to a K-injective cochain complex. -/
noncomputable irreducible_def IsKInjective.homotopyZero {K L : CochainComplex C Int} (f : K ⟶ L)
    (hK : K.Acyclic) [L.IsKInjective] :
    Homotopy f 0 :=
  (IsKInjective.nonempty_homotopy_zero f hK).some

/--
lemma `_root_.HomotopyEquiv.isKInjective` / 引理 `_root_.HomotopyEquiv.isKInjective`

English:
lemma _root_.HomotopyEquiv.isKInjective
  statement: {L₁ L₂ : CochainComplex C Int}
  proof: ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩

中文:
引理 _root_.同伦等价.isKInjective
  结论: {L₁ L₂ : 上链复形 C 整数}
  证明: ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩

Depends on / 依赖: HasHomology, HasHomology.mk, Homotopy, Homotopy.trans, IsKInjective, IsKInjective.homotopyZero, S.homologyData.unop, compLeft, compRight, e.hom, e.homotopyInvHomId.symm.compLeft, e.inv, homologyData, homotopyInvHomId, homotopyZero
-/
lemma _root_.HomotopyEquiv.isKInjective {L₁ L₂ : CochainComplex C Int}
    (e : HomotopyEquiv L₁ L₂)
    [L₁.IsKInjective] : L₂.IsKInjective where
  nonempty_homotopy_zero {K} f hK :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩

/--
lemma `isKInjective_of_iso` / 引理 `isKInjective_of_iso`

English:
lemma isKInjective_of_iso
  statement: {L₁ L₂ : CochainComplex C Int} (e : L₁ ≅ L₂)
  proof: (HomotopyEquiv.ofIso e).isKInjective

中文:
引理 isKInjective_of_iso
  结论: {L₁ L₂ : 上链复形 C 整数} (e : L₁ ≅ L₂)
  证明: (HomotopyEquiv.ofIso e).isKInjective

Depends on / 依赖: HomotopyEquiv, HomotopyEquiv.ofIso, isKInjective
-/
lemma isKInjective_of_iso {L₁ L₂ : CochainComplex C Int} (e : L₁ ≅ L₂)
    [L₁.IsKInjective] :
    L₂.IsKInjective :=
  (HomotopyEquiv.ofIso e).isKInjective

/--
lemma `isKInjective_iff_of_iso` / 引理 `isKInjective_iff_of_iso`

English:
lemma isKInjective_iff_of_iso
  given: {L₁ L₂ : CochainComplex C Int} (e : L₁ ≅ L₂)
  proof: ⟨fun _ => isKInjective_of_iso e, fun _ => isKInjective_of_iso e.symm⟩

中文:
引理 isKInjective_iff_of_iso
  条件: {L₁ L₂ : 上链复形 C 整数} (e : L₁ ≅ L₂)
  证明: ⟨fun _ => isKInjective_of_iso e, fun _ => isKInjective_of_iso e.symm⟩

Depends on / 依赖: e.symm, isKInjective_of_iso
-/
lemma isKInjective_iff_of_iso {L₁ L₂ : CochainComplex C Int} (e : L₁ ≅ L₂) :
    L₁.IsKInjective ↔ L₂.IsKInjective :=
  ⟨fun _ => isKInjective_of_iso e, fun _ => isKInjective_of_iso e.symm⟩

/--
lemma `isKInjective_iff_rightOrthogonal` / 引理 `isKInjective_iff_rightOrthogonal`

English:
lemma isKInjective_iff_rightOrthogonal
  given: (L : CochainComplex C Int)
  proof: by
  refine ⟨fun _ K f hK => ?_,
      fun hL => ⟨fun {K} f hK => ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK)]; rw [Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK]; rw [Functor.map_zero]

中文:
引理 isKInjective_iff_rightOrthogonal
  条件: (L : 上链复形 C 整数)
  证明: by
  refine ⟨fun _ K f hK => ?_,
      fun hL => ⟨fun {K} f hK => ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK)]; rw [Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK]; rw [Functor.map_zero]

Depends on / 依赖: Functor, Functor.map_zero, Homotop, HomotopyCategory, HomotopyCategory.eq_of_homotopy, HomotopyCategory.homotopyOfEq, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic, HomotopyCategory.quotient_obj_surjective, IsKInjective, IsKInjective.homotopyZero, eq_of_homotopy, homotopyOfEq, homotopyZero, map_surjective, map_zero, quotient, quotient_obj_mem_subcategoryAcyclic_iff_acyclic, quotient_obj_surjective
-/
lemma isKInjective_iff_rightOrthogonal (L : CochainComplex C Int) :
    L.IsKInjective ↔
      (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  refine ⟨fun _ K f hK => ?_,
      fun hL => ⟨fun {K} f hK => ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK)]; rw [Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK]; rw [Functor.map_zero]

/--
lemma `IsKInjective.rightOrthogonal` / 引理 `IsKInjective.rightOrthogonal`

English:
lemma IsKInjective.rightOrthogonal
  given: (L : CochainComplex C Int) [L.IsKInjective]
  proof: by
  rwa [← isKInjective_iff_rightOrthogonal]

中文:
引理 是KInjective.rightOrthogonal
  条件: (L : 上链复形 C 整数) [L.是KInjective]
  证明: by
  rwa [← isKInjective_iff_rightOrthogonal]

Depends on / 依赖: isKInjective_iff_rightOrthogonal
-/
lemma IsKInjective.rightOrthogonal (L : CochainComplex C Int) [L.IsKInjective] :
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  rwa [← isKInjective_iff_rightOrthogonal]

instance (L : CochainComplex C Int) [hL : L.IsKInjective] (n : Int) :
    (L⟦n⟧).IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal] at hL ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up Int)).commShiftIso n).symm.app L)
    ((HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.le_shift n _ hL)

/--
lemma `isKInjective_shift_iff` / 引理 `isKInjective_shift_iff`

English:
lemma isKInjective_shift_iff
  given: (L : CochainComplex C Int) (n : Int)
  proof: ⟨fun _ => isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ => inferInstance⟩

中文:
引理 isKInjective_shift_iff
  条件: (L : 上链复形 C 整数) (n : 整数)
  证明: ⟨fun _ => isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ => inferInstance⟩

Depends on / 依赖: isKInjective_of_iso, shiftEquiv, unitIso, unitIso.symm.app
-/
lemma isKInjective_shift_iff (L : CochainComplex C Int) (n : Int) :
    (L⟦n⟧).IsKInjective ↔ L.IsKInjective :=
  ⟨fun _ => isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ => inferInstance⟩

/--
lemma `isKInjective_of_injective_aux` / 引理 `isKInjective_of_injective_aux`

English:
lemma isKInjective_of_injective_aux
  statement: {K L : CochainComplex C Int}
  proof: by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : exists (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

中文:
引理 isKInjective_of_injective_aux
  结论: {K L : 上链复形 C 整数}
  证明: by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : exists (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

Depends on / 依赖: Category, Category.assoc, Cochain, Cochain.ofHom_v, HomologicalComplex, HomologicalComplex.d_comp_d_assoc, Int.negOnePow_zero, L.d_comp_d, add_comp, add_zero, comp_sub, comp_zero, d_comp_d, d_comp_d_assoc, f.comm, negOnePow_zero, neg_add_cancel, ofHom_v, one_smul, zero_add
-/
lemma isKInjective_of_injective_aux {K L : CochainComplex C Int}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : Int) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    exists (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : exists (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

open Cochain.InductionUp in
/--
lemma `isKInjective_of_injective` / 引理 `isKInjective_of_injective`

English:
lemma isKInjective_of_injective
  statement: (L : CochainComplex C Int) (d : Int)
  proof: by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : Nat) : Set (Cochain K L (-1)) :=
      Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp =>
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : Nat) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : Nat) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : Nat) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left]; rw [Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero]; rw [add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia)]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia)]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia)]; rw [limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia)]; rw [limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]

中文:
引理 isKInjective_of_injective
  结论: (L : 上链复形 C 整数) (d : 整数)
  证明: by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : Nat) : Set (Cochain K L (-1)) :=
      Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp =>
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : Nat) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : Nat) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : Nat) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left]; rw [Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero]; rw [add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia)]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia)]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia)]; rw [limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia)]; rw [limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]
-/
lemma isKInjective_of_injective (L : CochainComplex C Int) (d : Int)
    [L.IsStrictlyGE d] [forall (n : Int), Injective (L.X n)] :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : Nat) : Set (Cochain K L (-1)) :=
      Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp =>
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : Nat) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : Nat) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : Nat) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left]; rw [Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero]; rw [add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia)]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia)]; rw [δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia)]; rw [limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia)]; rw [limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]

instance (K : CochainComplex C Nat) [forall n, Injective (K.X n)] :
    IsKInjective (K.extend ComplexShape.embeddingUpNat) :=
  isKInjective_of_injective _ 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsKInjective.eq_δ_of_cocycle` / 引理 `IsKInjective.eq_δ_of_cocycle`

English:
lemma IsKInjective.eq_δ_of_cocycle
  statement: {K L : CochainComplex C Int} {n : Int}
  proof: by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.rightShift n 0 (zero_add n))
  rw [Cocycle.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero φ hK
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨n.negOnePow • Cochain.rightUnshift f m (by lia), ?_⟩
  apply (Cochain.rightShiftAddEquiv _ _ _ n 0 (by simp)).injective
  dsimp
  rw [← hφ]; rw [hf]; rw [δ_units_smul]; rw [Cochain.rightShift_units_smul]; rw [Cochain.δ_rightUnshift _ _ _ _ 0 (by simp)]
  simp [smul_smul]

中文:
引理 是KInjective.eq_δ_of_cocycle
  结论: {K L : 上链复形 C 整数} {n : 整数}
  证明: by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.rightShift n 0 (zero_add n))
  rw [Cocycle.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero φ hK
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨n.negOnePow • Cochain.rightUnshift f m (by lia), ?_⟩
  apply (Cochain.rightShiftAddEquiv _ _ _ n 0 (by simp)).injective
  dsimp
  rw [← hφ]; rw [hf]; rw [δ_units_smul]; rw [Cochain.rightShift_units_smul]; rw [Cochain.δ_rightUnshift _ _ _ _ 0 (by simp)]
  simp [smul_smul]

Depends on / 依赖: Cochain, Cochain.equivHomotopy, Cochain.ofHom_zero, Cochain.rightShiftAddEquiv, Cochain.rightShift_units_smul, Cochain.rightUnshift, Cocycle, Cocycle.equivHom, Cocycle.ext_iff, Int.reduceNeg, IsKInjective, IsKInjective.nonempty_homotopy_zero, add_zero, equivHom, equivHomotopy, ext_iff, injective, n.negOnePow, negOnePow, nonempty_homotopy_zero
-/
lemma IsKInjective.eq_δ_of_cocycle {K L : CochainComplex C Int} {n : Int}
    (z : Cocycle K L n) [L.IsKInjective] (hK : K.Acyclic) (m : Int) (hm : m + 1 = n) :
    exists (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.rightShift n 0 (zero_add n))
  rw [Cocycle.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero φ hK
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨n.negOnePow • Cochain.rightUnshift f m (by lia), ?_⟩
  apply (Cochain.rightShiftAddEquiv _ _ _ n 0 (by simp)).injective
  dsimp
  rw [← hφ]; rw [hf]; rw [δ_units_smul]; rw [Cochain.rightShift_units_smul]; rw [Cochain.δ_rightUnshift _ _ _ _ 0 (by simp)]
  simp [smul_smul]

/--
lemma `IsKInjective.eq_δ_of_cocycle'` / 引理 `IsKInjective.eq_δ_of_cocycle'`

English:
lemma IsKInjective.eq_δ_of_cocycle'
  statement: {K L : CochainComplex C Int} {n : Int}
  proof: by
  obtain ⟨β, hβ⟩ :=
    IsKInjective.eq_δ_of_cocycle (Cocycle.ofHom (𝟙 L)) hL (-1) (by simp)
  exact ⟨z.1.comp β (by lia), by simp [δ_comp z.1 β _ _ 0 _ hm rfl (by simp), hβ]⟩

中文:
引理 是KInjective.eq_δ_of_cocycle'
  结论: {K L : 上链复形 C 整数} {n : 整数}
  证明: by
  obtain ⟨β, hβ⟩ :=
    IsKInjective.eq_δ_of_cocycle (Cocycle.ofHom (𝟙 L)) hL (-1) (by simp)
  exact ⟨z.1.comp β (by lia), by simp [δ_comp z.1 β _ _ 0 _ hm rfl (by simp), hβ]⟩

Depends on / 依赖: Cocycle, Cocycle.ofHom, IsKInjective, IsKInjective.eq_
-/
lemma IsKInjective.eq_δ_of_cocycle' {K L : CochainComplex C Int} {n : Int}
    (z : Cocycle K L n) [L.IsKInjective] (hL : L.Acyclic) (m : Int) (hm : m + 1 = n) :
    exists (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨β, hβ⟩ :=
    IsKInjective.eq_δ_of_cocycle (Cocycle.ofHom (𝟙 L)) hL (-1) (by simp)
  exact ⟨z.1.comp β (by lia), by simp [δ_comp z.1 β _ _ 0 _ hm rfl (by simp), hβ]⟩

end CochainComplex
