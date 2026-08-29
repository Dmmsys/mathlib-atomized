/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Results about pointwise operations on sets and big operators.
-/

public section

namespace Set

open Function
open scoped Pointwise

variable {ι α β F : Type*} [FunLike F α β]

section Monoid

variable [Monoid α] [Monoid β] [MonoidHomClass F α β]

@[to_additive]
/--
theorem `image_list_prod` / 定理 `image_list_prod`

English:
theorem image_list_prod
  given: (f : F)

中文:
定理 image_list_prod
  条件: (f : F)
-/
theorem image_list_prod (f : F) :
    forall l : List (Set α), (f : α -> β) '' l.prod = (l.map fun s => f '' s).prod
| [] => image_one.trans congr_arg singleton (map_one f)
  | a :: as => by rw [List.map_cons, List.prod_cons, List.prod_cons, image_mul, image_list_prod _ _]

end Monoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

@[to_additive]
/--
theorem `image_multiset_prod` / 定理 `image_multiset_prod`

English:
theorem image_multiset_prod
  given: (f : F)
  proof: Quotient.ind by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      image_list_prod f

@[to_additive]

中文:
定理 image_multiset_prod
  条件: (f : F)
  证明: Quotient.ind by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      image_list_prod f

@[to_additive]

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, Quotient, Quotient.ind, image_list_prod, map_coe, prod_coe, quot_mk_to_coe
-/
theorem image_multiset_prod (f : F) :
    forall m : Multiset (Set α), (f : α -> β) '' m.prod = (m.map fun s => f '' s).prod :=
Quotient.ind by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      image_list_prod f

@[to_additive]
/--
theorem `image_finsetProd` / 定理 `image_finsetProd`

English:
theorem image_finsetProd
  given: (f : F) (m : Finset ι) (s : ι -> Set α)
  proof: (image_multiset_prod f _).trans congr_arg Multiset.prod Multiset.map_map _ _ _

@[deprecated (since := "2026-04-08")] alias image_finset_sum := image_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod := image_finsetProd

中文:
定理 image_finsetProd
  条件: (f : F) (m : 有限集 ι) (s : ι -> 集合 α)
  证明: (image_multiset_prod f _).trans congr_arg Multiset.prod Multiset.map_map _ _ _

@[deprecated (since := "2026-04-08")] alias image_finset_sum := image_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod := image_finsetProd

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.prod, congr_arg, image_multiset_prod, map_map
-/
theorem image_finsetProd (f : F) (m : Finset ι) (s : ι -> Set α) :
    ((f : α -> β) '' ∏ i in m, s i) = ∏ i in m, f '' s i :=
(image_multiset_prod f _).trans congr_arg Multiset.prod Multiset.map_map _ _ _

@[deprecated (since := "2026-04-08")] alias image_finset_sum := image_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod := image_finsetProd

/-- The n-ary version of `Set.mem_mul`. -/
@[to_additive /-- The n-ary version of `Set.mem_add`. -/]
/--
theorem `mem_finsetProd` / 定理 `mem_finsetProd`

English:
theorem mem_finsetProd
  given: (t : Finset ι) (f : ι -> Set α) (a : α)
  proof: by
  classical
    induction t using Finset.induction_on generalizing a with
    | empty =>
      simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h => ⟨fun _ => a, fun hi => False.elim (Finset.notMem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ => hf.symm⟩
    | insert i is hi ih => ?_
   

中文:
定理 mem_finsetProd
  条件: (t : 有限集 ι) (f : ι -> 集合 α) (a : α)
  证明: by
  classical
    induction t using Finset.induction_on generalizing a with
    | empty =>
      simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h => ⟨fun _ => a, fun hi => False.elim (Finset.notMem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ => hf.symm⟩
    | insert i is hi ih => ?_
   

Depends on / 依赖: False.elim, Finset, Finset.induction_on, Finset.mem_insert.mp, Finset.notMem_empty, Finset.prod_empty, Finset.prod_insert, Function, Function.update, Set.mem_mul, Set.mem_one, classical, generalizing, h.symm, hf.symm, induction_on, insert, mem_insert, mem_mul, mem_one
-/
theorem mem_finsetProd (t : Finset ι) (f : ι -> Set α) (a : α) :
    (a in ∏ i in t, f i) ↔ exists (g : ι -> α) (_ : forall {i}, i in t -> g i in f i), ∏ i in t, g i = a := by
  classical
    induction t using Finset.induction_on generalizing a with
    | empty =>
      simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h => ⟨fun _ => a, fun hi => False.elim (Finset.notMem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ => hf.symm⟩
    | insert i is hi ih => ?_
    rw [Finset.prod_insert hi]; rw [Set.mem_mul]
    simp_rw [Finset.prod_insert hi]
    simp_rw [ih]
    constructor
    · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨Function.update g i x, ?_, ?_⟩
      · intro j hj
        obtain rfl | hj := Finset.mem_insert.mp hj
        · rwa [Function.update_self]
        · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
          exact hg hj
      · rw [Finset.prod_update_of_notMem hi, Function.update_self]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g i, hg (is.mem_insert_self _), is.prod g,
        ⟨⟨g, fun hi => hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩⟩

@[deprecated (since := "2026-04-08")] alias mem_finset_sum := mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias mem_finset_prod := mem_finsetProd

@[to_additive]
/--
lemma `mem_pow_iff_prod` / 引理 `mem_pow_iff_prod`

English:
lemma mem_pow_iff_prod
  given: {n : Nat} {s : Set α} {a : α}
  proof: by
  simpa using mem_finsetProd (t := .univ) (f := fun _ : Fin n => s) _

中文:
引理 mem_pow_iff_prod
  条件: {n : 自然数} {s : 集合 α} {a : α}
  证明: by
  simpa using mem_finsetProd (t := .univ) (f := fun _ : Fin n => s) _

Depends on / 依赖: mem_finsetProd
-/
lemma mem_pow_iff_prod {n : Nat} {s : Set α} {a : α} :
    a in s ^ n ↔ exists f : Fin n -> α, (forall i, f i in s) ∧ ∏ i, f i = a := by
  simpa using mem_finsetProd (t := .univ) (f := fun _ : Fin n => s) _

/-- A version of `Set.mem_finsetProd` with a simpler RHS for products over a Fintype. -/
@[to_additive /-- A version of `Set.mem_finsetSum` with a simpler RHS for sums over a Fintype. -/]
/--
theorem `mem_fintype_prod` / 定理 `mem_fintype_prod`

English:
theorem mem_fintype_prod
  given: [Fintype ι] (f : ι -> Set α) (a : α)
  proof: by
  rw [mem_finsetProd]
  simp

中文:
定理 mem_fintype_prod
  条件: [有限类型 ι] (f : ι -> 集合 α) (a : α)
  证明: by
  rw [mem_finsetProd]
  simp

Depends on / 依赖: mem_finsetProd
-/
theorem mem_fintype_prod [Fintype ι] (f : ι -> Set α) (a : α) :
    (a in ∏ i, f i) ↔ exists (g : ι -> α) (_ : forall i, g i in f i), ∏ i, g i = a := by
  rw [mem_finsetProd]
  simp

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
/--
theorem `list_prod_mem_list_prod` / 定理 `list_prod_mem_list_prod`

English:
theorem list_prod_mem_list_prod
  given: (t : List ι) (f : ι -> Set α) (g : ι -> α) (hg : forall i in t, g i in f i)
  proof: by
  induction t with
  | nil => simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h List.mem_cons_self)
      (ih fun i hi => hg i <| List.mem_cons_of_mem _ hi)

中文:
定理 list_prod_mem_list_prod
  条件: (t : 列表 ι) (f : ι -> 集合 α) (g : ι -> α) (hg : 对任意 i in t, g i in f i)
  证明: by
  induction t with
  | nil => simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h List.mem_cons_self)
      (ih fun i hi => hg i <| List.mem_cons_of_mem _ hi)

Depends on / 依赖: List.map_cons, List.map_nil, List.mem_cons_of_mem, List.mem_cons_self, List.prod_cons, List.prod_nil, Set.mem_one, map_cons, map_nil, mem_cons_of_mem, mem_cons_self, mem_one, mul_mem_mul, prod_cons, prod_nil, simp_rw
-/
theorem list_prod_mem_list_prod (t : List ι) (f : ι -> Set α) (g : ι -> α) (hg : forall i in t, g i in f i) :
    (t.map g).prod in (t.map f).prod := by
  induction t with
  | nil => simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h List.mem_cons_self)
      (ih fun i hi => hg i <| List.mem_cons_of_mem _ hi)

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
/--
theorem `list_prod_subset_list_prod` / 定理 `list_prod_subset_list_prod`

English:
theorem list_prod_subset_list_prod
  given: (t : List ι) (f₁ f₂ : ι -> Set α) (hf : forall i in t, f₁ i subseteq f₂ i)
  proof: by
  induction t with
  | nil => rfl
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h List.mem_cons_self)
      (ih fun i hi => hf i <| List.mem_cons_of_mem _ hi)

@[to_additive]

中文:
定理 list_prod_subset_list_prod
  条件: (t : 列表 ι) (f₁ f₂ : ι -> 集合 α) (hf : 对任意 i in t, f₁ i subseteq f₂ i)
  证明: by
  induction t with
  | nil => rfl
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h List.mem_cons_self)
      (ih fun i hi => hf i <| List.mem_cons_of_mem _ hi)

@[to_additive]

Depends on / 依赖: List.map_cons, List.mem_cons_of_mem, List.mem_cons_self, List.prod_cons, map_cons, mem_cons_of_mem, mem_cons_self, mul_subset_mul, prod_cons, simp_rw
-/
theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι -> Set α) (hf : forall i in t, f₁ i subseteq f₂ i) :
    (t.map f₁).prod subseteq (t.map f₂).prod := by
  induction t with
  | nil => rfl
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h List.mem_cons_self)
      (ih fun i hi => hf i <| List.mem_cons_of_mem _ hi)

@[to_additive]
/--
theorem `list_prod_singleton` / 定理 `list_prod_singleton`

English:
theorem list_prod_singleton
  given: {M : Type*} [Monoid M] (s : List M)
  proof: (map_list_prod (singletonMonoidHom : M ->* Set M) _).symm

中文:
定理 list_prod_singleton
  条件: {M : 类型} [幺半群 M] (s : 列表 M)
  证明: (map_list_prod (singletonMonoidHom : M ->* Set M) _).symm

Depends on / 依赖: map_list_prod, singletonMonoidHom
-/
theorem list_prod_singleton {M : Type*} [Monoid M] (s : List M) :
    (s.map fun i => ({i} : Set M)).prod = {s.prod} :=
  (map_list_prod (singletonMonoidHom : M ->* Set M) _).symm

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
/--
theorem `multiset_prod_mem_multiset_prod` / 定理 `multiset_prod_mem_multiset_prod`

English:
theorem multiset_prod_mem_multiset_prod
  statement: (t : Multiset ι) (f : ι -> Set α) (g : ι -> α)
  proof: by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_mem_list_prod _ _ _ hg

中文:
定理 multiset_prod_mem_multiset_prod
  结论: (t : Multiset ι) (f : ι -> 集合 α) (g : ι -> α)
  证明: by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_mem_list_prod _ _ _ hg

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, Quotient, Quotient.inductionOn, inductionOn, list_prod_mem_list_prod, map_coe, prod_coe, quot_mk_to_coe, simp_rw
-/
theorem multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι -> Set α) (g : ι -> α)
    (hg : forall i in t, g i in f i) : (t.map g).prod in (t.map f).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_mem_list_prod _ _ _ hg

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
/--
theorem `multiset_prod_subset_multiset_prod` / 定理 `multiset_prod_subset_multiset_prod`

English:
theorem multiset_prod_subset_multiset_prod
  statement: (t : Multiset ι) (f₁ f₂ : ι -> Set α)
  proof: by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_subset_list_prod _ _ _ hf

@[to_additive]

中文:
定理 multiset_prod_subset_multiset_prod
  结论: (t : Multiset ι) (f₁ f₂ : ι -> 集合 α)
  证明: by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_subset_list_prod _ _ _ hf

@[to_additive]

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, Quotient, Quotient.inductionOn, inductionOn, list_prod_subset_list_prod, map_coe, prod_coe, quot_mk_to_coe, simp_rw
-/
theorem multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι -> Set α)
    (hf : forall i in t, f₁ i subseteq f₂ i) : (t.map f₁).prod subseteq (t.map f₂).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_subset_list_prod _ _ _ hf

@[to_additive]
/--
theorem `multiset_prod_singleton` / 定理 `multiset_prod_singleton`

English:
theorem multiset_prod_singleton
  given: {M : Type*} [CommMonoid M] (s : Multiset M)
  proof: (map_multiset_prod (singletonMonoidHom : M ->* Set M) _).symm

中文:
定理 multiset_prod_singleton
  条件: {M : 类型} [交换幺半群 M] (s : Multiset M)
  证明: (map_multiset_prod (singletonMonoidHom : M ->* Set M) _).symm

Depends on / 依赖: map_multiset_prod, singletonMonoidHom
-/
theorem multiset_prod_singleton {M : Type*} [CommMonoid M] (s : Multiset M) :
    (s.map fun i => ({i} : Set M)).prod = {s.prod} :=
  (map_multiset_prod (singletonMonoidHom : M ->* Set M) _).symm

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
/--
theorem `finsetProd_mem_finsetProd` / 定理 `finsetProd_mem_finsetProd`

English:
theorem finsetProd_mem_finsetProd
  statement: (t : Finset ι) (f : ι -> Set α) (g : ι -> α)
  proof: multiset_prod_mem_multiset_prod _ _ _ hg

@[deprecated (since := "2026-04-08")] alias finset_sum_mem_finset_sum := finsetSum_mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_mem_finset_prod := finsetProd_mem_finsetProd

中文:
定理 finsetProd_mem_finsetProd
  结论: (t : 有限集 ι) (f : ι -> 集合 α) (g : ι -> α)
  证明: multiset_prod_mem_multiset_prod _ _ _ hg

@[deprecated (since := "2026-04-08")] alias finset_sum_mem_finset_sum := finsetSum_mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_mem_finset_prod := finsetProd_mem_finsetProd

Depends on / 依赖: multiset_prod_mem_multiset_prod
-/
theorem finsetProd_mem_finsetProd (t : Finset ι) (f : ι -> Set α) (g : ι -> α)
    (hg : forall i in t, g i in f i) : (∏ i in t, g i) in ∏ i in t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg

@[deprecated (since := "2026-04-08")] alias finset_sum_mem_finset_sum := finsetSum_mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_mem_finset_prod := finsetProd_mem_finsetProd

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
/--
theorem `finsetProd_subset_finsetProd` / 定理 `finsetProd_subset_finsetProd`

English:
theorem finsetProd_subset_finsetProd
  statement: (t : Finset ι) (f₁ f₂ : ι -> Set α)
  proof: multiset_prod_subset_multiset_prod _ _ _ hf

@[deprecated (since := "2026-04-08")]
alias finset_sum_subset_finset_sum := finsetSum_subset_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_subset_finset_prod := finsetProd_subset_finsetProd

@[to_additive]

中文:
定理 finsetProd_subset_finsetProd
  结论: (t : 有限集 ι) (f₁ f₂ : ι -> 集合 α)
  证明: multiset_prod_subset_multiset_prod _ _ _ hf

@[deprecated (since := "2026-04-08")]
alias finset_sum_subset_finset_sum := finsetSum_subset_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_subset_finset_prod := finsetProd_subset_finsetProd

@[to_additive]

Depends on / 依赖: multiset_prod_subset_multiset_prod
-/
theorem finsetProd_subset_finsetProd (t : Finset ι) (f₁ f₂ : ι -> Set α)
    (hf : forall i in t, f₁ i subseteq f₂ i) : ∏ i in t, f₁ i subseteq ∏ i in t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf

@[deprecated (since := "2026-04-08")]
alias finset_sum_subset_finset_sum := finsetSum_subset_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_subset_finset_prod := finsetProd_subset_finsetProd

@[to_additive]
/--
theorem `finsetProd_singleton` / 定理 `finsetProd_singleton`

English:
theorem finsetProd_singleton
  given: {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι -> M)
  proof: (map_prod (singletonMonoidHom : M ->* Set M) _ _).symm

@[deprecated (since := "2026-04-08")] alias finset_sum_singleton := finsetSum_singleton

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_singleton := finsetProd_singleton

中文:
定理 finsetProd_singleton
  条件: {M ι : 类型} [交换幺半群 M] (s : 有限集 ι) (I : ι -> M)
  证明: (map_prod (singletonMonoidHom : M ->* Set M) _ _).symm

@[deprecated (since := "2026-04-08")] alias finset_sum_singleton := finsetSum_singleton

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_singleton := finsetProd_singleton

Depends on / 依赖: map_prod, singletonMonoidHom
-/
theorem finsetProd_singleton {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι -> M) :
    ∏ i in s, ({I i} : Set M) = {∏ i in s, I i} :=
  (map_prod (singletonMonoidHom : M ->* Set M) _ _).symm

@[deprecated (since := "2026-04-08")] alias finset_sum_singleton := finsetSum_singleton

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_singleton := finsetProd_singleton

/-- The n-ary version of `Set.image_mul_prod`. -/
@[to_additive /-- The n-ary version of `Set.add_image_prod`. -/]
/--
theorem `image_finsetProd_pi` / 定理 `image_finsetProd_pi`

English:
theorem image_finsetProd_pi
  given: (l : Finset ι) (S : ι -> Set α)
  proof: by
  ext
  simp_rw [mem_finsetProd, mem_image, mem_pi, exists_prop, Finset.mem_coe]

@[deprecated (since := "2026-04-08")] alias image_finset_sum_pi := image_finsetSum_pi

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod_pi := image_finsetProd_pi

中文:
定理 image_finsetProd_pi
  条件: (l : 有限集 ι) (S : ι -> 集合 α)
  证明: by
  ext
  simp_rw [mem_finsetProd, mem_image, mem_pi, exists_prop, Finset.mem_coe]

@[deprecated (since := "2026-04-08")] alias image_finset_sum_pi := image_finsetSum_pi

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod_pi := image_finsetProd_pi

Depends on / 依赖: Finset, Finset.mem_coe, exists_prop, mem_coe, mem_finsetProd, mem_image, mem_pi, simp_rw
-/
theorem image_finsetProd_pi (l : Finset ι) (S : ι -> Set α) :
    (fun f : ι -> α => ∏ i in l, f i) '' (l : Set ι).pi S = ∏ i in l, S i := by
  ext
  simp_rw [mem_finsetProd, mem_image, mem_pi, exists_prop, Finset.mem_coe]

@[deprecated (since := "2026-04-08")] alias image_finset_sum_pi := image_finsetSum_pi

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod_pi := image_finsetProd_pi

/-- A special case of `Set.image_finsetProd_pi` for `Finset.univ`. -/
@[to_additive /-- A special case of `Set.image_finsetSum_pi` for `Finset.univ`. -/]
/--
theorem `image_fintype_prod_pi` / 定理 `image_fintype_prod_pi`

English:
theorem image_fintype_prod_pi
  given: [Fintype ι] (S : ι -> Set α)
  proof: by
  simpa only [Finset.coe_univ] using image_finsetProd_pi Finset.univ S

中文:
定理 image_fintype_prod_pi
  条件: [有限类型 ι] (S : ι -> 集合 α)
  证明: by
  simpa only [Finset.coe_univ] using image_finsetProd_pi Finset.univ S

Depends on / 依赖: Finset, Finset.coe_univ, Finset.univ, coe_univ, image_finsetProd_pi
-/
theorem image_fintype_prod_pi [Fintype ι] (S : ι -> Set α) :
    (fun f : ι -> α => ∏ i, f i) '' univ.pi S = ∏ i, S i := by
  simpa only [Finset.coe_univ] using image_finsetProd_pi Finset.univ S

end CommMonoid

/-! TODO: define `decidable_mem_finsetProd` and `decidable_mem_finsetSum`. -/


end Set
