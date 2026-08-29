/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Adjoin.FG

/-!
# Adjoining elements and being finitely generated in an algebra tower

## Main results

* `Algebra.fg_trans'`: if `S` is finitely generated as `R`-algebra and `A` as `S`-algebra,
  then `A` is finitely generated as `R`-algebra
* `fg_of_fg_of_fg`: **Artin--Tate lemma**: if C/B/A is a tower of rings, and A is Noetherian, and
  C is algebra-finite over A, and C is module-finite over B, then B is algebra-finite over A.
-/

public section


open scoped Pointwise

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace Algebra

/--
theorem `adjoin_restrictScalars` / 定理 `adjoin_restrictScalars`

English:
theorem adjoin_restrictScalars
  statement: (C D E : Type*) [CommSemiring C] [CommSemiring D] [CommSemiring E]
  proof: by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x in Subsemiring.closure (_ union S) ↔ x in Subsemiring.closure (_ union S)
    rw [this]
  simp

中文:
定理 adjoin_restrictScalars
  结论: (C D E : 类型) [交换半环 C] [交换半环 D] [交换半环 E]
  证明: by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x in Subsemiring.closure (_ union S) ↔ x in Subsemiring.closure (_ union S)
    rw [this]
  simp

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, Set.range, Subalgebra, Subsemiring, Subsemiring.closure, algebraMap, closure, toAlgHom
-/
theorem adjoin_restrictScalars (C D E : Type*) [CommSemiring C] [CommSemiring D] [CommSemiring E]
    [Algebra C D] [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
    (Algebra.adjoin D S).restrictScalars C =
      (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars
        C := by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x in Subsemiring.closure (_ union S) ↔ x in Subsemiring.closure (_ union S)
    rw [this]
  simp

/--
theorem `adjoin_res_eq_adjoin_res` / 定理 `adjoin_res_eq_adjoin_res`

English:
theorem adjoin_res_eq_adjoin_res
  statement: (C D E F : Type*) [CommSemiring C] [CommSemiring D]
  proof: by
  rw [adjoin_restrictScalars C E]; rw [adjoin_restrictScalars C D]; rw [← hS]; rw [← hT]; rw [← Algebra.adjoin_image]; rw [← Algebra.adjoin_image]; rw [← AlgHom.coe_toRingHom]; rw [← AlgHom.coe_toRingHom]; rw [IsScalarTower.coe_toAlgHom]; rw [IsScalarTower.coe_toAlgHom]; rw [← adjoin_union_eq_adj

中文:
定理 adjoin_res_eq_adjoin_res
  结论: (C D E F : 类型) [交换半环 C] [交换半环 D]
  证明: by
  rw [adjoin_restrictScalars C E]; rw [adjoin_restrictScalars C D]; rw [← hS]; rw [← hT]; rw [← Algebra.adjoin_image]; rw [← Algebra.adjoin_image]; rw [← AlgHom.coe_toRingHom]; rw [← AlgHom.coe_toRingHom]; rw [IsScalarTower.coe_toAlgHom]; rw [IsScalarTower.coe_toAlgHom]; rw [← adjoin_union_eq_adj

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, Algebra, Algebra.adjoin_image, IsScalarTower, IsScalarTower.coe_toAlgHom, Set.union_comm, adjoin_image, adjoin_restrictScalars, adjoin_union_eq_adjoin_adjoin, coe_toAlgHom, coe_toRingHom, union_comm
-/
theorem adjoin_res_eq_adjoin_res (C D E F : Type*) [CommSemiring C] [CommSemiring D]
    [CommSemiring E] [CommSemiring F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F]
    [Algebra E F] [IsScalarTower C D F] [IsScalarTower C E F] {S : Set D} {T : Set E}
    (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
    (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
      (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C := by
  rw [adjoin_restrictScalars C E]; rw [adjoin_restrictScalars C D]; rw [← hS]; rw [← hT]; rw [← Algebra.adjoin_image]; rw [← Algebra.adjoin_image]; rw [← AlgHom.coe_toRingHom]; rw [← AlgHom.coe_toRingHom]; rw [IsScalarTower.coe_toAlgHom]; rw [IsScalarTower.coe_toAlgHom]; rw [← adjoin_union_eq_adjoin_adjoin]; rw [←
    adjoin_union_eq_adjoin_adjoin]; rw [Set.union_comm]

end Algebra

section

/--
theorem `Algebra.fg_trans'` / 定理 `Algebra.fg_trans'`

English:
theorem Algebra.fg_trans'
  statement: {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  proof: by
  classical
  rcases hRS with ⟨s, hs⟩
  rcases hSA with ⟨t, ht⟩
  exact ⟨s.image (algebraMap S A) union t, by
    rw [Finset.coe_union]; rw [Finset.coe_image]; rw [Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin]; rw [hs]; rw [Algebra.adjoin_top]; rw [ht]; rw [Subalgebra.restrictScalars_to

中文:
定理 代数.fg_trans'
  结论: {R S A : 类型} [交换半环 R] [交换半环 S] [半环 A]
  证明: by
  classical
  rcases hRS with ⟨s, hs⟩
  rcases hSA with ⟨t, ht⟩
  exact ⟨s.image (algebraMap S A) union t, by
    rw [Finset.coe_union]; rw [Finset.coe_image]; rw [Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin]; rw [hs]; rw [Algebra.adjoin_top]; rw [ht]; rw [Subalgebra.restrictScalars_to

Depends on / 依赖: Algebra, Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin, Algebra.adjoin_top, Finset, Finset.coe_image, Finset.coe_union, Subalgebra, Subalgebra.restrictScalars_top, adjoin_algebraMap_image_union_eq_adjoin_adjoin, adjoin_top, algebraMap, classical, coe_image, coe_union, restrictScalars_top, s.image
-/
theorem Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).FG)
    (hSA : (⊤ : Subalgebra S A).FG) : (⊤ : Subalgebra R A).FG := by
  classical
  rcases hRS with ⟨s, hs⟩
  rcases hSA with ⟨t, ht⟩
  exact ⟨s.image (algebraMap S A) union t, by
    rw [Finset.coe_union]; rw [Finset.coe_image]; rw [Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin]; rw [hs]; rw [Algebra.adjoin_top]; rw [ht]; rw [Subalgebra.restrictScalars_top]; rw [Subalgebra.restrictScalars_top]
    ⟩
end

section ArtinTate

variable (C : Type*)

section Semiring

variable [CommSemiring A] [CommSemiring B] [Semiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

open Finset Submodule

/--
theorem `exists_subalgebra_of_fg` / 定理 `exists_subalgebra_of_fg`

English:
theorem exists_subalgebra_of_fg
  given: (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG)
  proof: by
  obtain ⟨x, hx⟩ := hAC
  obtain ⟨y, hy⟩ := hBC
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f _ hf using this
  classical
  let s : Finset B := Finset.image₂ f (x union y * y) y
  have hxy :
    forall xi in x, xi in span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : 

中文:
定理 存在_subalgebra_of_fg
  条件: (hAC : (⊤ : 子代数 A C).FG) (hBC : (⊤ : 子模 B C).FG)
  证明: by
  obtain ⟨x, hx⟩ := hAC
  obtain ⟨y, hy⟩ := hBC
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f _ hf using this
  classical
  let s : Finset B := Finset.image₂ f (x union y * y) y
  have hxy :
    forall xi in x, xi in span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : 

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, Finset, Finset.image, adjoin, classical, eq_top_iff, insert, mem_span_finset, mem_union_left, simp_rw, smul_mem, subset_adjoin, sum_mem
-/
theorem exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG) :
    exists B₀ : Subalgebra A B, B₀.FG ∧ (⊤ : Submodule B₀ C).FG := by
  obtain ⟨x, hx⟩ := hAC
  obtain ⟨y, hy⟩ := hBC
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f _ hf using this
  classical
  let s : Finset B := Finset.image₂ f (x union y * y) y
  have hxy :
    forall xi in x, xi in span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    fun xi hxi =>
    hf xi ▸
      sum_mem fun yj hyj =>
        smul_mem (span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C))
⟨f xi yj, Algebra.subset_adjoin mem_image₂_of_mem (mem_union_left _ hxi) hyj⟩
          (subset_span <| mem_insert_of_mem hyj)
  have hyy :
    span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) *
        span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) <=
      span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) := by
    rw [span_mul_span]; rw [span_le]; rw [coe_insert]
    rintro _ ⟨yi, rfl | hyi, yj, rfl | hyj, rfl⟩ <;> dsimp
    · rw [mul_one]
      exact subset_span (Set.mem_insert _ _)
    · rw [one_mul]
      exact subset_span (Set.mem_insert_of_mem _ hyj)
    · rw [mul_one]
      exact subset_span (Set.mem_insert_of_mem _ hyi)
    · rw [← hf (yi * yj)]
      exact
        SetLike.mem_coe.2
          (sum_mem fun yk hyk =>
            smul_mem (span (Algebra.adjoin A (↑s : Set B)) (insert 1 ↑y : Set C))
              ⟨f (yi * yj) yk,
Algebra.subset_adjoin
                  mem_image₂_of_mem (mem_union_right _ <| mul_mem_mul hyi hyj) hyk⟩
              (subset_span <| Set.mem_insert_of_mem _ hyk : yk in _))
  refine ⟨Algebra.adjoin A (↑s : Set B), Subalgebra.fg_adjoin_finset _, insert 1 y, ?_⟩
  convert! restrictScalars_injective A (Algebra.adjoin A (s : Set B)) C _
  rw [restrictScalars_top]; rw [eq_top_iff]; rw [← Algebra.top_toSubmodule]; rw [← hx]; rw [Algebra.adjoin_eq_span]; rw [span_le]
  refine fun r hr =>
    Submonoid.closure_induction (fun c hc => hxy c hc) (subset_span <| mem_insert_self _ _)
      (fun p q _ _ hp hq => hyy <| Submodule.mul_mem_mul hp hq) hr

end Semiring

section Ring

variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is Noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Altman--Kleiman 16.17. -/
@[stacks 00IS]
/--
theorem `fg_of_fg_of_fg` / 定理 `fg_of_fg_of_fg`

English:
theorem fg_of_fg_of_fg
  statement: [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
  proof: let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
Algebra.fg_trans' (B₀.fg_top.2 hAB₀)
Subalgebra.fg_of_submodule_fg
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap

中文:
定理 fg_of_fg_of_fg
  结论: [是Noether环 A] (hAC : (⊤ : 子代数 A C).FG)
  证明: let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
Algebra.fg_trans' (B₀.fg_top.2 hAB₀)
Subalgebra.fg_of_submodule_fg
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap

Depends on / 依赖: Algebra, Algebra.fg_trans, Finite, IsNoetherianRing, IsScalarTower, IsScalarTower.toAlgHom, Module, Module.Finite, Subalgebra, Subalgebra.fg_of_submodule_fg, exists_subalgebra_of_fg, fg_of_injective, fg_of_submodule_fg, fg_top, fg_trans, isNoetherianRing_of_fg, toAlgHom, toLinearMap
-/
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
Algebra.fg_trans' (B₀.fg_top.2 hAB₀)
Subalgebra.fg_of_submodule_fg
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi

end Ring

end ArtinTate
