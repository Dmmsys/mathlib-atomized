/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Wojciech Nawrocki
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical of `R` to ideals of `R`,
by letting the nilradical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a ring, and `I` be a left ideal of `R`

* `Ideal.jacobson I` is the Jacobson radical, i.e. the infimum of all maximal ideals containing `I`.

* `Ideal.IsLocal I` is the proposition that the Jacobson radical of `I` is itself a maximal ideal

Furthermore when `I` is a two-sided ideal of `R`

* `TwoSidedIdeal.jacobson I` is the Jacobson radical as a two-sided ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the Jacobson of I

* `Ideal.isLocal_of_isMaximal_radical`: if the radical of I is maximal then so is the Jacobson
  radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/

@[expose] public section


universe u v

namespace Ideal

variable {R : Type u} {S : Type v}

section Jacobson

section Ring

variable [Ring R] [Ring S] {I : Ideal R}

/--
Definition of `jacobson` / `jacobson` 的定义

English:
definition jacobson
  signature: (I : Ideal R)
  body: sInf { J : Ideal R | I <= J ∧ IsMaximal J }

中文:
定义 jacobson
  签名: (I : Ideal R)
  定义体: sInf { J : Ideal R | I <= J ∧ IsMaximal J }

Depends on / 依赖: IsMaximal
-/
def jacobson (I : Ideal R) : Ideal R :=
  sInf { J : Ideal R | I <= J ∧ IsMaximal J }

/--
theorem `le_jacobson` / 定理 `le_jacobson`

English:
theorem le_jacobson
  statement: I <= jacobson I
  proof: fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx

@[simp]

中文:
定理 le_jacobson
  结论: I <= jacobson I
  证明: fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx

@[simp]

Depends on / 依赖: hJ.left, mem_sInf, mem_sInf.mpr
-/
theorem le_jacobson : I <= jacobson I := fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx

@[simp]
/--
theorem `jacobson_idem` / 定理 `jacobson_idem`

English:
theorem jacobson_idem
  statement: jacobson (jacobson I) = jacobson I
  proof: le_antisymm (sInf_le_sInf fun _ hJ => ⟨sInf_le hJ, hJ.2⟩) le_jacobson

@[simp]

中文:
定理 jacobson_idem
  结论: jacobson (jacobson I) = jacobson I
  证明: le_antisymm (sInf_le_sInf fun _ hJ => ⟨sInf_le hJ, hJ.2⟩) le_jacobson

@[simp]

Depends on / 依赖: le_antisymm, le_jacobson, sInf_le, sInf_le_sInf
-/
theorem jacobson_idem : jacobson (jacobson I) = jacobson I :=
  le_antisymm (sInf_le_sInf fun _ hJ => ⟨sInf_le hJ, hJ.2⟩) le_jacobson

@[simp]
/--
theorem `jacobson_top` / 定理 `jacobson_top`

English:
theorem jacobson_top
  statement: jacobson (⊤ : Ideal R) = ⊤
  proof: eq_top_iff.2 le_jacobson

中文:
定理 jacobson_top
  结论: jacobson (⊤ : Ideal R) = ⊤
  证明: eq_top_iff.2 le_jacobson

Depends on / 依赖: eq_top_iff, le_jacobson
-/
theorem jacobson_top : jacobson (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 le_jacobson

/--
theorem `jacobson_bot` / 定理 `jacobson_bot`

English:
theorem jacobson_bot
  statement: jacobson (⊥ : Ideal R) = Ring.jacobson R
  proof: by
  simp_rw [jacobson, Ring.jacobson, Module.jacobson, bot_le, true_and, isMaximal_def]

@[simp]

中文:
定理 jacobson_bot
  结论: jacobson (⊥ : Ideal R) = Ring.jacobson R
  证明: by
  simp_rw [jacobson, Ring.jacobson, Module.jacobson, bot_le, true_and, isMaximal_def]

@[simp]

Depends on / 依赖: Module, Module.jacobson, Ring.jacobson, bot_le, isMaximal_def, jacobson, simp_rw, true_and
-/
theorem jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobson R := by
  simp_rw [jacobson, Ring.jacobson, Module.jacobson, bot_le, true_and, isMaximal_def]

@[simp]
/--
theorem `jacobson_eq_top_iff` / 定理 `jacobson_eq_top_iff`

English:
theorem jacobson_eq_top_iff
  statement: jacobson I = ⊤ ↔ I = ⊤
  proof: ⟨fun H =>
    by_contradiction fun hi => let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1
        (lt_of_le_of_lt (show jacobson I <= M from sInf_le ⟨him, hm⟩) <|
          lt_top_iff_ne_top.2 hm.ne_top) H,
fun H => eq_top_iff.2 le_sInf fun _ ⟨hij, _⟩ => H ▸ hij⟩

中文:
定理 jacobson_eq_top_iff
  结论: jacobson I = ⊤ ↔ I = ⊤
  证明: ⟨fun H =>
    by_contradiction fun hi => let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1
        (lt_of_le_of_lt (show jacobson I <= M from sInf_le ⟨him, hm⟩) <|
          lt_top_iff_ne_top.2 hm.ne_top) H,
fun H => eq_top_iff.2 le_sInf fun _ ⟨hij, _⟩ => H ▸ hij⟩

Depends on / 依赖: by_contradiction, eq_top_iff, exists_le_maximal, hm.ne_top, jacobson, le_sInf, lt_of_le_of_lt, lt_top_iff_ne_top, ne_top, sInf_le
-/
theorem jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤ :=
  ⟨fun H =>
    by_contradiction fun hi => let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1
        (lt_of_le_of_lt (show jacobson I <= M from sInf_le ⟨him, hm⟩) <|
          lt_top_iff_ne_top.2 hm.ne_top) H,
fun H => eq_top_iff.2 le_sInf fun _ ⟨hij, _⟩ => H ▸ hij⟩

/--
theorem `jacobson_eq_bot` / 定理 `jacobson_eq_bot`

English:
theorem jacobson_eq_bot
  statement: jacobson I = ⊥ -> I = ⊥
  proof: fun h => eq_bot_iff.mpr (h ▸ le_jacobson)

中文:
定理 jacobson_eq_bot
  结论: jacobson I = ⊥ -> I = ⊥
  证明: fun h => eq_bot_iff.mpr (h ▸ le_jacobson)

Depends on / 依赖: eq_bot_iff, eq_bot_iff.mpr, le_jacobson
-/
theorem jacobson_eq_bot : jacobson I = ⊥ -> I = ⊥ := fun h => eq_bot_iff.mpr (h ▸ le_jacobson)

/--
theorem `jacobson_eq_self_of_isMaximal` / 定理 `jacobson_eq_self_of_isMaximal`

English:
theorem jacobson_eq_self_of_isMaximal
  given: [H : IsMaximal I]
  statement: I.jacobson = I
  proof: le_antisymm (sInf_le ⟨le_of_eq rfl, H⟩) le_jacobson

中文:
定理 jacobson_eq_self_of_isMaximal
  条件: [H : IsMaximal I]
  结论: I.jacobson = I
  证明: le_antisymm (sInf_le ⟨le_of_eq rfl, H⟩) le_jacobson

Depends on / 依赖: le_antisymm, le_jacobson, le_of_eq, sInf_le
-/
theorem jacobson_eq_self_of_isMaximal [H : IsMaximal I] : I.jacobson = I :=
  le_antisymm (sInf_le ⟨le_of_eq rfl, H⟩) le_jacobson

instance (priority := 100) jacobson.isMaximal [H : IsMaximal I] : IsMaximal (jacobson I) :=
  ⟨⟨fun htop => H.1.1 (jacobson_eq_top_iff.1 htop), fun _ hJ =>
    H.1.2 _ (lt_of_le_of_lt le_jacobson hJ)⟩⟩

/--
theorem `mem_jacobson_iff` / 定理 `mem_jacobson_iff`

English:
theorem mem_jacobson_iff
  given: {x : R}
  statement: x in jacobson I ↔ forall y, exists z, z * y * x + z - 1 in I
  proof: ⟨fun hx y =>
    by_cases
      (fun hxy : I ⊔ span {y * x + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton'.1 hq
        ⟨r, by
          rw [mul_assoc]; rw [← mul_add_one]; rw [hr]; rw [← hpq]; rw [← neg_sub]; 

中文:
定理 mem_jacobson_iff
  条件: {x : R}
  结论: x in jacobson I ↔ 对任意 y, 存在 z, z * y * x + z - 1 in I
  证明: ⟨fun hx y =>
    by_cases
      (fun hxy : I ⊔ span {y * x + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton'.1 hq
        ⟨r, by
          rw [mul_assoc]; rw [← mul_add_one]; rw [hr]; rw [← hpq]; rw [← neg_sub]; 

Depends on / 依赖: I.neg_mem, Submodule, Submodule.mem_sup, add_sub_cancel_right, eq_top_iff_, eq_top_iff_one, exists_le_maximal, le_sup_left, le_trans, mem_sInf, mem_span_singleton, mem_sup, mul_add_one, mul_assoc, neg_mem, neg_sub
-/
theorem mem_jacobson_iff {x : R} : x in jacobson I ↔ forall y, exists z, z * y * x + z - 1 in I :=
  ⟨fun hx y =>
    by_cases
      (fun hxy : I ⊔ span {y * x + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton'.1 hq
        ⟨r, by
          rw [mul_assoc]; rw [← mul_add_one]; rw [hr]; rw [← hpq]; rw [← neg_sub]; rw [add_sub_cancel_right]
          exact I.neg_mem hpi⟩)
      fun hxy : I ⊔ span {y * x + 1} != ⊤ => let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy
      suffices x ∉ M from (this <| mem_sInf.1 hx ⟨le_trans le_sup_left hm2, hm1⟩).elim
fun hxm => hm1.1.1 (eq_top_iff_one _).2 add_sub_cancel_left (y * x) 1 ▸
        M.sub_mem (le_sup_right.trans hm2 <| subset_span rfl) (M.mul_mem_left _ hxm),
    fun hx => mem_sInf.2 fun M ⟨him, hm⟩ => by_contradiction fun hxm =>
      let ⟨y, i, hi, df⟩ := hm.exists_inv hxm
      let ⟨z, hz⟩ := hx (-y)
hm.1.1 (eq_top_iff_one _).2 sub_sub_cancel (z * -y * x + z) 1 ▸
        M.sub_mem (by
          rw [mul_assoc]; rw [← mul_add_one]; rw [neg_mul]; rw [← sub_eq_iff_eq_add.mpr df.symm]; rw [neg_sub]; rw [sub_add_cancel]
          exact M.mul_mem_left _ hi) <| him hz⟩

/--
theorem `exists_mul_add_sub_mem_of_mem_jacobson` / 定理 `exists_mul_add_sub_mem_of_mem_jacobson`

English:
theorem exists_mul_add_sub_mem_of_mem_jacobson
  given: {I : Ideal R} (r : R) (h : r in jacobson I)
  proof: by
  obtain ⟨s, hs⟩ := mem_jacobson_iff.1 h 1
  use s
  rw [mul_add]; rw [mul_one]
  simpa using hs

中文:
定理 exists_mul_add_sub_mem_of_mem_jacobson
  条件: {I : Ideal R} (r : R) (h : r in jacobson I)
  证明: by
  obtain ⟨s, hs⟩ := mem_jacobson_iff.1 h 1
  use s
  rw [mul_add]; rw [mul_one]
  simpa using hs

Depends on / 依赖: mem_jacobson_iff, mul_add, mul_one
-/
theorem exists_mul_add_sub_mem_of_mem_jacobson {I : Ideal R} (r : R) (h : r in jacobson I) :
    exists s, s * (r + 1) - 1 in I := by
  obtain ⟨s, hs⟩ := mem_jacobson_iff.1 h 1
  use s
  rw [mul_add]; rw [mul_one]
  simpa using hs

/--
theorem `exists_mul_sub_mem_of_sub_one_mem_jacobson` / 定理 `exists_mul_sub_mem_of_sub_one_mem_jacobson`

English:
theorem exists_mul_sub_mem_of_sub_one_mem_jacobson
  given: {I : Ideal R} (r : R) (h : r - 1 in jacobson I)
  proof: by
  convert! exists_mul_add_sub_mem_of_mem_jacobson _ h
  simp

中文:
定理 exists_mul_sub_mem_of_sub_one_mem_jacobson
  条件: {I : Ideal R} (r : R) (h : r - 1 in jacobson I)
  证明: by
  convert! exists_mul_add_sub_mem_of_mem_jacobson _ h
  simp

Depends on / 依赖: convert, exists_mul_add_sub_mem_of_mem_jacobson
-/
theorem exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 in jacobson I) :
    exists s, s * r - 1 in I := by
  convert! exists_mul_add_sub_mem_of_mem_jacobson _ h
  simp

/--
theorem `eq_jacobson_iff_sInf_maximal` / 定理 `eq_jacobson_iff_sInf_maximal`

English:
theorem eq_jacobson_iff_sInf_maximal
  proof: by
  use fun hI => ⟨{ J : Ideal R | I <= J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine le_antisymm (fun x hx => ?_) le_jacobson
  rw [hInf]; rw [mem_sInf]
  intro I hI
  rcases hM I hI with is_max | is_top
  · exact (mem_sInf.1 hx) ⟨le_sInf_iff.1 (le_of_e

中文:
定理 eq_jacobson_iff_sInf_maximal
  证明: by
  use fun hI => ⟨{ J : Ideal R | I <= J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine le_antisymm (fun x hx => ?_) le_jacobson
  rw [hInf]; rw [mem_sInf]
  intro I hI
  rcases hM I hI with is_max | is_top
  · exact (mem_sInf.1 hx) ⟨le_sInf_iff.1 (le_of_e

Depends on / 依赖: IsMaximal, J.IsMaximal, Or.inl, Submodule, Submodule.mem_top, hI.symm, hJ.right, is_max, is_top, is_top.symm, le_antisymm, le_jacobson, le_of_eq, le_sInf_iff, mem_sInf, mem_top
-/
theorem eq_jacobson_iff_sInf_maximal :
    I.jacobson = I ↔ exists M : Set (Ideal R), (forall J in M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M := by
  use fun hI => ⟨{ J : Ideal R | I <= J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine le_antisymm (fun x hx => ?_) le_jacobson
  rw [hInf]; rw [mem_sInf]
  intro I hI
  rcases hM I hI with is_max | is_top
  · exact (mem_sInf.1 hx) ⟨le_sInf_iff.1 (le_of_eq hInf) I hI, is_max⟩
  · exact is_top.symm ▸ Submodule.mem_top

/--
theorem `eq_jacobson_iff_sInf_maximal'` / 定理 `eq_jacobson_iff_sInf_maximal'`

English:
theorem eq_jacobson_iff_sInf_maximal'
  proof: eq_jacobson_iff_sInf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK =>
          Or.recOn (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_lt (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ =>
         

中文:
定理 eq_jacobson_iff_sInf_maximal'
  证明: eq_jacobson_iff_sInf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK =>
          Or.recOn (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_lt (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ =>
         

Depends on / 依赖: Classical, Classical.em, Or.inl, Or.inr, Or.recOn, eq_jacobson_iff_sInf_maximal, eq_jacobson_iff_sInf_maximal.trans, eq_top_iff, le_of_lt
-/
theorem eq_jacobson_iff_sInf_maximal' :
    I.jacobson = I ↔ exists M : Set (Ideal R), (forall J in M, forall (K : Ideal R), J < K -> K = ⊤) ∧ I = sInf M :=
  eq_jacobson_iff_sInf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK =>
          Or.recOn (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_lt (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ =>
          Or.recOn (Classical.em (J = ⊤)) (fun h => Or.inr h) fun h => Or.inl ⟨⟨h, hM.1 J hJ⟩⟩,
          hM.2⟩⟩⟩

/--
theorem `eq_jacobson_iff_notMem` / 定理 `eq_jacobson_iff_notMem`

English:
theorem eq_jacobson_iff_notMem
  proof: by
  constructor
  · intro h x hx
    rw [← h]; rw [Ideal.jacobson]; rw [mem_sInf] at hx
    push Not at hx
    exact hx
  · refine fun h => le_antisymm (fun x hx => ?_) le_jacobson
    contrapose hx
    rw [Ideal.jacobson]; rw [mem_sInf]
    push Not
    exact h x hx

中文:
定理 eq_jacobson_iff_notMem
  证明: by
  constructor
  · intro h x hx
    rw [← h]; rw [Ideal.jacobson]; rw [mem_sInf] at hx
    push Not at hx
    exact hx
  · refine fun h => le_antisymm (fun x hx => ?_) le_jacobson
    contrapose hx
    rw [Ideal.jacobson]; rw [mem_sInf]
    push Not
    exact h x hx

Depends on / 依赖: Ideal.jacobson, contrapose, jacobson, le_antisymm, le_jacobson, mem_sInf
-/
theorem eq_jacobson_iff_notMem :
    I.jacobson = I ↔ forall x ∉ I, exists M : Ideal R, (I <= M ∧ M.IsMaximal) ∧ x ∉ M := by
  constructor
  · intro h x hx
    rw [← h]; rw [Ideal.jacobson]; rw [mem_sInf] at hx
    push Not at hx
    exact hx
  · refine fun h => le_antisymm (fun x hx => ?_) le_jacobson
    contrapose hx
    rw [Ideal.jacobson]; rw [mem_sInf]
    push Not
    exact h x hx

/--
theorem `map_jacobson_of_surjective` / 定理 `map_jacobson_of_surjective`

English:
theorem map_jacobson_of_surjective
  given: {f : R ->+* S} (hf : Function.Surjective f)
  proof: by
  intro h
  unfold Ideal.jacobson
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): dot notation for `RingHom.ker` does not work
  have : forall J in { J : Ideal R | I <= J ∧ J.IsMaximal }, RingHom.ker f <= J :=
    fun J hJ => le_trans h hJ.left
  refine Trans.tr

中文:
定理 map_jacobson_of_surjective
  条件: {f : R ->+* S} (hf : Function.Surjective f)
  证明: by
  intro h
  unfold Ideal.jacobson
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): dot notation for `RingHom.ker` does not work
  have : forall J in { J : Ideal R | I <= J ∧ J.IsMaximal }, RingHom.ker f <= J :=
    fun J hJ => le_trans h hJ.left
  refine Trans.tr

Depends on / 依赖: Ideal.jacobson, jacobson
-/
theorem map_jacobson_of_surjective {f : R ->+* S} (hf : Function.Surjective f) :
    RingHom.ker f <= I -> map f I.jacobson = (map f I).jacobson := by
  intro h
  unfold Ideal.jacobson
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): dot notation for `RingHom.ker` does not work
  have : forall J in { J : Ideal R | I <= J ∧ J.IsMaximal }, RingHom.ker f <= J :=
    fun J hJ => le_trans h hJ.left
  refine Trans.trans (map_sInf hf this) (le_antisymm ?_ ?_)
  · refine
      sInf_le_sInf fun J hJ =>
        ⟨comap f J, ⟨⟨le_comap_of_map_le hJ.1, ?_⟩, map_comap_of_surjective f hf J⟩⟩
    have : J.IsMaximal := hJ.right
    exact comap_isMaximal_of_surjective f hf
  · refine sInf_le_sInf_of_subset_insert_top fun j hj => hj.recOn fun J hJ => ?_
    rw [← hJ.2]
    rcases map_eq_top_or_isMaximal_of_surjective f hf hJ.left.right with htop | hmax
    · exact htop.symm ▸ Set.mem_insert ⊤ _
    · exact Set.mem_insert_of_mem ⊤ ⟨map_mono hJ.1.1, hmax⟩

/--
theorem `map_jacobson_of_bijective` / 定理 `map_jacobson_of_bijective`

English:
theorem map_jacobson_of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  proof: map_jacobson_of_surjective hf.right
    (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot f).1 hf.left)) bot_le)

中文:
定理 map_jacobson_of_bijective
  条件: {f : R ->+* S} (hf : Function.Bijective f)
  证明: map_jacobson_of_surjective hf.right
    (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot f).1 hf.left)) bot_le)

Depends on / 依赖: RingHom, RingHom.injective_iff_ker_eq_bot, bot_le, hf.left, hf.right, injective_iff_ker_eq_bot, le_of_eq, le_trans, map_jacobson_of_surjective
-/
theorem map_jacobson_of_bijective {f : R ->+* S} (hf : Function.Bijective f) :
    map f I.jacobson = (map f I).jacobson :=
  map_jacobson_of_surjective hf.right
    (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot f).1 hf.left)) bot_le)

/--
theorem `comap_jacobson` / 定理 `comap_jacobson`

English:
theorem comap_jacobson
  given: {f : R ->+* S} {K : Ideal S}
  proof: Trans.trans (comap_sInf' f _) sInf_eq_iInf.symm

中文:
定理 comap_jacobson
  条件: {f : R ->+* S} {K : Ideal S}
  证明: Trans.trans (comap_sInf' f _) sInf_eq_iInf.symm

Depends on / 依赖: Trans.trans, comap_sInf, sInf_eq_iInf, sInf_eq_iInf.symm
-/
theorem comap_jacobson {f : R ->+* S} {K : Ideal S} :
    comap f K.jacobson = sInf (comap f '' { J : Ideal S | K <= J ∧ J.IsMaximal }) :=
  Trans.trans (comap_sInf' f _) sInf_eq_iInf.symm

/--
theorem `comap_jacobson_of_surjective` / 定理 `comap_jacobson_of_surjective`

English:
theorem comap_jacobson_of_surjective
  given: {f : R ->+* S} (hf : Function.Surjective f) {K : Ideal S}
  proof: by
  unfold Ideal.jacobson
  refine le_antisymm ?_ ?_
  · rw [← top_inf_eq (sInf _), ← sInf_insert, comap_sInf', sInf_eq_iInf]
    refine iInf_le_iInf_of_subset fun J hJ => ?_
    have : comap f (map f J) = J :=
      Trans.trans (comap_map_of_surjective f hf J)
        (le_antisymm (sup_le_iff.2 ⟨l

中文:
定理 comap_jacobson_of_surjective
  条件: {f : R ->+* S} (hf : Function.Surjective f) {K : Ideal S}
  证明: by
  unfold Ideal.jacobson
  refine le_antisymm ?_ ?_
  · rw [← top_inf_eq (sInf _), ← sInf_insert, comap_sInf', sInf_eq_iInf]
    refine iInf_le_iInf_of_subset fun J hJ => ?_
    have : comap f (map f J) = J :=
      Trans.trans (comap_map_of_surjective f hf J)
        (le_antisymm (sup_le_iff.2 ⟨l

Depends on / 依赖: Ideal.jacobson, Set.mem_insert, Set.mem_insert_of_mem, Trans.trans, bot_le, comap_map_of_surjective, comap_mono, comap_sInf, hJ.left, hJ.right, iInf_le_iInf_of_subset, jacobson, le_antisymm, le_of_eq, le_sup_left, le_trans, map_eq_top_or_isMaximal_of_surjective, mem_insert, mem_insert_of_mem, sInf_eq_iInf
-/
theorem comap_jacobson_of_surjective {f : R ->+* S} (hf : Function.Surjective f) {K : Ideal S} :
    comap f K.jacobson = (comap f K).jacobson := by
  unfold Ideal.jacobson
  refine le_antisymm ?_ ?_
  · rw [← top_inf_eq (sInf _), ← sInf_insert, comap_sInf', sInf_eq_iInf]
    refine iInf_le_iInf_of_subset fun J hJ => ?_
    have : comap f (map f J) = J :=
      Trans.trans (comap_map_of_surjective f hf J)
        (le_antisymm (sup_le_iff.2 ⟨le_of_eq rfl, le_trans (comap_mono bot_le) hJ.left⟩)
          le_sup_left)
    rcases map_eq_top_or_isMaximal_of_surjective _ hf hJ.right with htop | hmax
    · exact ⟨⊤, Set.mem_insert ⊤ _, htop ▸ this⟩
    · exact ⟨map f J, Set.mem_insert_of_mem _ ⟨le_map_of_comap_le_of_surjective f hf hJ.1, hmax⟩,
        this⟩
  · simp_rw [comap_sInf, le_iInf_iff]
    intro J hJ
    have : J.IsMaximal := hJ.right
    exact sInf_le ⟨comap_mono hJ.left, comap_isMaximal_of_surjective _ hf⟩

@[gcongr, mono]
/--
theorem `jacobson_mono` / 定理 `jacobson_mono`

English:
theorem jacobson_mono
  given: {I J : Ideal R}
  statement: I <= J -> I.jacobson <= J.jacobson
  proof: by
  intro h x hx
  rw [jacobson]; rw [mem_sInf] at hx ⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨Trans.trans h hK, hK_max⟩

中文:
定理 jacobson_mono
  条件: {I J : Ideal R}
  结论: I <= J -> I.jacobson <= J.jacobson
  证明: by
  intro h x hx
  rw [jacobson]; rw [mem_sInf] at hx ⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨Trans.trans h hK, hK_max⟩

Depends on / 依赖: Trans.trans, hK_max, jacobson, mem_sInf
-/
theorem jacobson_mono {I J : Ideal R} : I <= J -> I.jacobson <= J.jacobson := by
  intro h x hx
  rw [jacobson]; rw [mem_sInf] at hx ⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨Trans.trans h hK, hK_max⟩

/--
theorem `ringJacobson_le_jacobson` / 定理 `ringJacobson_le_jacobson`

English:
theorem ringJacobson_le_jacobson
  given: {I : Ideal R}
  statement: Ring.jacobson R <= I.jacobson
  proof: jacobson_bot.symm.trans_le (jacobson_mono bot_le)

中文:
定理 ringJacobson_le_jacobson
  条件: {I : Ideal R}
  结论: Ring.jacobson R <= I.jacobson
  证明: jacobson_bot.symm.trans_le (jacobson_mono bot_le)

Depends on / 依赖: bot_le, jacobson_bot, jacobson_bot.symm.trans_le, jacobson_mono, trans_le
-/
theorem ringJacobson_le_jacobson {I : Ideal R} : Ring.jacobson R <= I.jacobson :=
  jacobson_bot.symm.trans_le (jacobson_mono bot_le)

/-- The Jacobson radical of a two-sided ideal is two-sided. -/
instance {I : Ideal R} [I.IsTwoSided] : I.jacobson.IsTwoSided where
  -- Proof generalized from
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-definition-and-basic-results/
  mul_mem_of_left {x} r xJ := by
    apply mem_sInf.mpr
    intro 𝔪 𝔪_mem
    by_cases r𝔪 : r in 𝔪
    · apply 𝔪.smul_mem _ r𝔪
    -- 𝔪₀ := { a : R | a*r ∈ 𝔪 }
    let 𝔪₀ : Ideal R := Submodule.comap (DistribSMul.toLinearMap R (S := Rᵐᵒᵖ) R (.op r)) 𝔪
    suffices x in 𝔪₀ by simpa [𝔪₀] using this
    have I𝔪₀ : I <= 𝔪₀ := fun i iI =>
      𝔪_mem.left (I.mul_mem_right _ iI)
    have 𝔪₀_maximal : IsMaximal 𝔪₀ := by
      refine isMaximal_iff.mpr ⟨
        fun h => r𝔪 (by simpa [𝔪₀] using h),
        fun J b 𝔪₀J b𝔪₀ bJ => ?_⟩
      let K : Ideal R := Ideal.span {b*r} ⊔ 𝔪
      have ⟨s, y, y𝔪, sbyr⟩ :=
mem_span_singleton_sup.mp
mul_mem_left _ r
            (isMaximal_iff.mp 𝔪_mem.right).right K (b * r)
            le_sup_right b𝔪₀
            (mem_sup_left <| mem_span_singleton_self _)
      have : 1 - s * b in 𝔪₀ := by
        rw [mul_one]; rw [add_comm]; rw [← eq_sub_iff_add_eq] at sbyr
        rw [sbyr]; rw [← mul_assoc] at y𝔪
        simp [𝔪₀, sub_mul, y𝔪]
      have : 1 - s * b + s * b in J := by
        apply add_mem (𝔪₀J this) (J.mul_mem_left _ bJ)
      simpa using this
    exact mem_sInf.mp xJ ⟨I𝔪₀, 𝔪₀_maximal⟩

end Ring

section CommRing

variable [CommRing R] [CommRing S] {I : Ideal R}

/--
theorem `radical_le_jacobson` / 定理 `radical_le_jacobson`

English:
theorem radical_le_jacobson
  statement: radical I <= jacobson I
  proof: le_sInf fun _ hJ => (radical_eq_sInf I).symm ▸ sInf_le ⟨hJ.left, IsMaximal.isPrime hJ.right⟩

中文:
定理 radical_le_jacobson
  结论: radical I <= jacobson I
  证明: le_sInf fun _ hJ => (radical_eq_sInf I).symm ▸ sInf_le ⟨hJ.left, IsMaximal.isPrime hJ.right⟩

Depends on / 依赖: IsMaximal, IsMaximal.isPrime, hJ.left, hJ.right, isPrime, le_sInf, radical_eq_sInf, sInf_le
-/
theorem radical_le_jacobson : radical I <= jacobson I :=
  le_sInf fun _ hJ => (radical_eq_sInf I).symm ▸ sInf_le ⟨hJ.left, IsMaximal.isPrime hJ.right⟩

/--
theorem `isRadical_of_eq_jacobson` / 定理 `isRadical_of_eq_jacobson`

English:
theorem isRadical_of_eq_jacobson
  given: (h : jacobson I = I)
  statement: I.IsRadical
  proof: radical_le_jacobson.trans h.le

中文:
定理 isRadical_of_eq_jacobson
  条件: (h : jacobson I = I)
  结论: I.IsRadical
  证明: radical_le_jacobson.trans h.le

Depends on / 依赖: h.le, radical_le_jacobson, radical_le_jacobson.trans
-/
theorem isRadical_of_eq_jacobson (h : jacobson I = I) : I.IsRadical :=
  radical_le_jacobson.trans h.le

/--
lemma `isRadical_jacobson` / 引理 `isRadical_jacobson`

English:
lemma isRadical_jacobson
  given: (I : Ideal R)
  statement: I.jacobson.IsRadical
  proof: isRadical_of_eq_jacobson jacobson_idem

中文:
引理 isRadical_jacobson
  条件: (I : Ideal R)
  结论: I.jacobson.IsRadical
  证明: isRadical_of_eq_jacobson jacobson_idem

Depends on / 依赖: isRadical_of_eq_jacobson, jacobson_idem
-/
lemma isRadical_jacobson (I : Ideal R) : I.jacobson.IsRadical :=
  isRadical_of_eq_jacobson jacobson_idem

/--
theorem `isUnit_of_sub_one_mem_jacobson_bot` / 定理 `isUnit_of_sub_one_mem_jacobson_bot`

English:
theorem isUnit_of_sub_one_mem_jacobson_bot
  given: (r : R) (h : r - 1 in jacobson (⊥ : Ideal R))
  proof: by
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r h
  rw [mem_bot]; rw [sub_eq_zero]; rw [mul_comm] at hs
  exact .of_mul_eq_one _ hs

中文:
定理 isUnit_of_sub_one_mem_jacobson_bot
  条件: (r : R) (h : r - 1 in jacobson (⊥ : Ideal R))
  证明: by
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r h
  rw [mem_bot]; rw [sub_eq_zero]; rw [mul_comm] at hs
  exact .of_mul_eq_one _ hs

Depends on / 依赖: exists_mul_sub_mem_of_sub_one_mem_jacobson, mem_bot, mul_comm, of_mul_eq_one, sub_eq_zero
-/
theorem isUnit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 in jacobson (⊥ : Ideal R)) :
    IsUnit r := by
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r h
  rw [mem_bot]; rw [sub_eq_zero]; rw [mul_comm] at hs
  exact .of_mul_eq_one _ hs

/--
theorem `mem_jacobson_bot` / 定理 `mem_jacobson_bot`

English:
theorem mem_jacobson_bot
  given: {x : R}
  statement: x in jacobson (⊥ : Ideal R) ↔ forall y, IsUnit (x * y + 1)
  proof: ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    isUnit_iff_exists_inv.2
      ⟨z, by rwa [add_mul, one_mul, ← sub_eq_zero, mul_right_comm, mul_comm _ z, mul_right_comm]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (h y)
      ⟨b, (Submod

中文:
定理 mem_jacobson_bot
  条件: {x : R}
  结论: x in jacobson (⊥ : Ideal R) ↔ 对任意 y, IsUnit (x * y + 1)
  证明: ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    isUnit_iff_exists_inv.2
      ⟨z, by rwa [add_mul, one_mul, ← sub_eq_zero, mul_right_comm, mul_comm _ z, mul_right_comm]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (h y)
      ⟨b, (Submod

Depends on / 依赖: Submodule, Submodule.mem_bot, add_mul, isUnit_iff_exists_inv, mem_bot, mem_jacobson_iff, mem_jacobson_iff.mpr, mul_comm, mul_right_comm, one_mul, sub_eq_zero
-/
theorem mem_jacobson_bot {x : R} : x in jacobson (⊥ : Ideal R) ↔ forall y, IsUnit (x * y + 1) :=
  ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    isUnit_iff_exists_inv.2
      ⟨z, by rwa [add_mul, one_mul, ← sub_eq_zero, mul_right_comm, mul_comm _ z, mul_right_comm]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (h y)
      ⟨b, (Submodule.mem_bot R).2 (hb ▸ by ring)⟩⟩

/--
theorem `jacobson_eq_iff_jacobson_quotient_eq_bot` / 定理 `jacobson_eq_iff_jacobson_quotient_eq_bot`

English:
theorem jacobson_eq_iff_jacobson_quotient_eq_bot
  proof: by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_arg (Ideal.map (Ideal.Quotient.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at h
    simpa using h
  · intro h
    replace h := congr_a

中文:
定理 jacobson_eq_iff_jacobson_quotient_eq_bot
  证明: by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_arg (Ideal.map (Ideal.Quotient.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at h
    simpa using h
  · intro h
    replace h := congr_a

Depends on / 依赖: Function, Function.Surjective, Ideal.Quotient.mk, Ideal.map, Quotient, RingHom, RingHom.ker_eq_comap_bot, Submodule, Submodule.Quotient.mk_surjective, Surjective, comap_jacobson_of_surjective, congr_arg, ker_eq_comap_bot, le_of_eq, map_jacobson_of_surjective, mk_ker, mk_surjective, replace
-/
theorem jacobson_eq_iff_jacobson_quotient_eq_bot :
    I.jacobson = I ↔ jacobson (⊥ : Ideal (R ⧸ I)) = ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_arg (Ideal.map (Ideal.Quotient.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at h
    simpa using h
  · intro h
    replace h := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_jacobson_of_surjective hf]; rw [← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at h
    simpa using h

/--
theorem `radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot` / 定理 `radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot`

English:
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot
  proof: by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_arg (map (Ideal.Quotient.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eq mk_ker)]; rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this
    simpa

中文:
定理 radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot
  证明: by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_arg (map (Ideal.Quotient.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eq mk_ker)]; rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this
    simpa

Depends on / 依赖: Function, Function.Surjective, Ideal.Quotient.mk, Quotient, RingHom, RingHom.ker_eq_comap_bot, Submodule, Submodule.Quotient.mk_surjective, Surjective, comap_jacobson_of_surjective, comap_radical, congr_arg, ker_eq_comap_bot, le_of_eq, map_jacobson_of_surjective, map_radical_of_surjective, mk_ker, mk_surjective
-/
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
    I.radical = I.jacobson ↔ radical (⊥ : Ideal (R ⧸ I)) = jacobson ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_arg (map (Ideal.Quotient.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eq mk_ker)]; rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this
    simpa using this
  · intro h
    have := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_radical]; rw [comap_jacobson_of_surjective hf]; rw [← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at this
    simpa using this

/--
theorem `jacobson_radical_eq_jacobson` / 定理 `jacobson_radical_eq_jacobson`

English:
theorem jacobson_radical_eq_jacobson
  statement: I.radical.jacobson = I.jacobson
  proof: le_antisymm
    (le_trans (le_of_eq (congr_arg jacobson (radical_eq_sInf I)))
      (sInf_le_sInf fun _ hJ => ⟨sInf_le ⟨hJ.1, hJ.2.isPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

中文:
定理 jacobson_radical_eq_jacobson
  结论: I.radical.jacobson = I.jacobson
  证明: le_antisymm
    (le_trans (le_of_eq (congr_arg jacobson (radical_eq_sInf I)))
      (sInf_le_sInf fun _ hJ => ⟨sInf_le ⟨hJ.1, hJ.2.isPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

Depends on / 依赖: congr_arg, isPrime, jacobson, jacobson_mono, le_antisymm, le_of_eq, le_radical, le_trans, radical_eq_sInf, sInf_le, sInf_le_sInf
-/
theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
  le_antisymm
    (le_trans (le_of_eq (congr_arg jacobson (radical_eq_sInf I)))
      (sInf_le_sInf fun _ hJ => ⟨sInf_le ⟨hJ.1, hJ.2.isPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

end CommRing

end Jacobson

section IsLocal

variable [CommRing R]

/--
Definition of `IsLocal` / `IsLocal` 的定义

English:
class IsLocal
  parameters: (I : Ideal R)
  axioms and operations (1):
    - out : IsMaximal (jacobson I)

中文:
类 IsLocal
  参数: (I : Ideal R)
  公理与运算 (1 个):
    - out : IsMaximal (jacobson I)
-/
class IsLocal (I : Ideal R) : Prop where
  /-- A ring `R` is local if and only if its Jacobson radical is maximal -/
  out : IsMaximal (jacobson I)

/--
theorem `isLocal_iff` / 定理 `isLocal_iff`

English:
theorem isLocal_iff
  given: {I : Ideal R}
  statement: IsLocal I ↔ IsMaximal (jacobson I)
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 isLocal_iff
  条件: {I : Ideal R}
  结论: IsLocal I ↔ IsMaximal (jacobson I)
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem isLocal_iff {I : Ideal R} : IsLocal I ↔ IsMaximal (jacobson I) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `isLocal_of_isMaximal_radical` / 定理 `isLocal_of_isMaximal_radical`

English:
theorem isLocal_of_isMaximal_radical
  given: {I : Ideal R} (hi : IsMaximal (radical I))
  statement: IsLocal I
  proof: ⟨have : radical I = jacobson I :=
      le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
        (sInf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩

中文:
定理 isLocal_of_isMaximal_radical
  条件: {I : Ideal R} (hi : IsMaximal (radical I))
  结论: IsLocal I
  证明: ⟨have : radical I = jacobson I :=
      le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
        (sInf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩

Depends on / 依赖: IsMaximal, hm.isPrime.radical_le_iff, isPrime, jacobson, le_antisymm, le_radical, le_sInf, radical, radical_le_iff, sInf_le
-/
theorem isLocal_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsLocal I :=
  ⟨have : radical I = jacobson I :=
      le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
        (sInf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩

/--
theorem `IsLocal.le_jacobson` / 定理 `IsLocal.le_jacobson`

English:
theorem IsLocal.le_jacobson
  given: {I J : Ideal R} (hi : IsLocal I) (hij : I <= J) (hj : J != ⊤)
  proof: let ⟨_, hm, hjm⟩ := exists_le_maximal J hj
le_trans hjm le_of_eq Eq.symm hi.1.eq_of_le hm.1.1 sInf_le ⟨le_trans hij hjm, hm⟩

中文:
定理 IsLocal.le_jacobson
  条件: {I J : Ideal R} (hi : IsLocal I) (hij : I <= J) (hj : J != ⊤)
  证明: let ⟨_, hm, hjm⟩ := exists_le_maximal J hj
le_trans hjm le_of_eq Eq.symm hi.1.eq_of_le hm.1.1 sInf_le ⟨le_trans hij hjm, hm⟩

Depends on / 依赖: Eq.symm, eq_of_le, exists_le_maximal, le_of_eq, le_trans, sInf_le
-/
theorem IsLocal.le_jacobson {I J : Ideal R} (hi : IsLocal I) (hij : I <= J) (hj : J != ⊤) :
    J <= jacobson I :=
  let ⟨_, hm, hjm⟩ := exists_le_maximal J hj
le_trans hjm le_of_eq Eq.symm hi.1.eq_of_le hm.1.1 sInf_le ⟨le_trans hij hjm, hm⟩

/--
theorem `IsLocal.mem_jacobson_or_exists_inv` / 定理 `IsLocal.mem_jacobson_or_exists_inv`

English:
theorem IsLocal.mem_jacobson_or_exists_inv
  given: {I : Ideal R} (hi : IsLocal I) (x : R)
  proof: by_cases
    (fun h : I ⊔ span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr ⟨r, by
        rw [← hpq]; rw [mul_comm]; rw [← hr]; rw [← neg_sub]; rw [add_sub_cancel_right]; exact I.neg_mem hpi⟩)
   

中文:
定理 IsLocal.mem_jacobson_or_exists_inv
  条件: {I : Ideal R} (hi : IsLocal I) (x : R)
  证明: by_cases
    (fun h : I ⊔ span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr ⟨r, by
        rw [← hpq]; rw [mul_comm]; rw [← hr]; rw [← neg_sub]; rw [add_sub_cancel_right]; exact I.neg_mem hpi⟩)
   

Depends on / 依赖: I.neg_mem, Or.inl, Or.inr, Submodule, Submodule.mem_sup, add_sub_cancel_right, dvd_refl, eq_top_iff_one, hi.le_jacobson, le_jacobson, le_sup_left, le_sup_right, le_trans, mem_span_singleton, mem_sup, mul_comm, neg_mem, neg_sub
-/
theorem IsLocal.mem_jacobson_or_exists_inv {I : Ideal R} (hi : IsLocal I) (x : R) :
    x in jacobson I ∨ exists y, y * x - 1 in I :=
  by_cases
    (fun h : I ⊔ span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr ⟨r, by
        rw [← hpq]; rw [mul_comm]; rw [← hr]; rw [← neg_sub]; rw [add_sub_cancel_right]; exact I.neg_mem hpi⟩)
    fun h : I ⊔ span {x} != ⊤ =>
Or.inl
le_trans le_sup_right (hi.le_jacobson le_sup_left h) mem_span_singleton.2 dvd_refl x

end IsLocal

end Ideal

namespace TwoSidedIdeal

variable {R : Type u} [Ring R]

/--
Definition of `jacobson` / `jacobson` 的定义

English:
definition jacobson
  signature: (I : TwoSidedIdeal R)
  body: (asIdeal I).jacobson.toTwoSided

中文:
定义 jacobson
  签名: (I : TwoSidedIdeal R)
  定义体: (asIdeal I).jacobson.toTwoSided

Depends on / 依赖: asIdeal, jacobson, jacobson.toTwoSided, toTwoSided
-/
def jacobson (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  (asIdeal I).jacobson.toTwoSided

/--
lemma `asIdeal_jacobson` / 引理 `asIdeal_jacobson`

English:
lemma asIdeal_jacobson
  given: (I : TwoSidedIdeal R)
  statement: asIdeal I.jacobson = (asIdeal I).jacobson
  proof: by
  ext; simp [jacobson]

中文:
引理 asIdeal_jacobson
  条件: (I : TwoSidedIdeal R)
  结论: asIdeal I.jacobson = (asIdeal I).jacobson
  证明: by
  ext; simp [jacobson]

Depends on / 依赖: jacobson
-/
lemma asIdeal_jacobson (I : TwoSidedIdeal R) : asIdeal I.jacobson = (asIdeal I).jacobson := by
  ext; simp [jacobson]

/--
theorem `mem_jacobson_iff` / 定理 `mem_jacobson_iff`

English:
theorem mem_jacobson_iff
  given: {x : R} {I : TwoSidedIdeal R}
  proof: by
  simp [jacobson, Ideal.mem_jacobson_iff]

中文:
定理 mem_jacobson_iff
  条件: {x : R} {I : TwoSidedIdeal R}
  证明: by
  simp [jacobson, Ideal.mem_jacobson_iff]

Depends on / 依赖: Ideal.mem_jacobson_iff, jacobson, mem_jacobson_iff
-/
theorem mem_jacobson_iff {x : R} {I : TwoSidedIdeal R} :
    x in jacobson I ↔ forall y, exists z, z * y * x + z - 1 in I := by
  simp [jacobson, Ideal.mem_jacobson_iff]

end TwoSidedIdeal
