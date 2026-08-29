/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic

/-!

# Lemmas for ideal in polynomial span by monic polynomial

-/

@[expose] public section

variable (R : Type*) [CommRing R]

open Ideal

namespace Polynomial

/--
lemma `exists_monic_span` / 引理 `exists_monic_span`

English:
lemma exists_monic_span
  given: {k : Type*} [Field k] (I : Ideal k[X]) (ne : I != ⊥)
  proof: by
  classical
  obtain ⟨x, h, spanx⟩ := Ideal.exists_normalized_span_of_isPrincipal I
  refine ⟨x, (Polynomial.normalize_eq_self_iff_monic ?_).mp h, spanx⟩
  by_contra eq0
  simp [eq0, spanx] at ne

中文:
引理 exists_monic_span
  条件: {k : 类型} [Field k] (I : Ideal k[X]) (ne : I != ⊥)
  证明: by
  classical
  obtain ⟨x, h, spanx⟩ := Ideal.exists_normalized_span_of_isPrincipal I
  refine ⟨x, (Polynomial.normalize_eq_self_iff_monic ?_).mp h, spanx⟩
  by_contra eq0
  simp [eq0, spanx] at ne

Depends on / 依赖: Ideal.exists_normalized_span_of_isPrincipal, Polynomial, Polynomial.normalize_eq_self_iff_monic, classical, exists_normalized_span_of_isPrincipal, normalize_eq_self_iff_monic
-/
lemma exists_monic_span {k : Type*} [Field k] (I : Ideal k[X]) (ne : I != ⊥) :
    exists f, f.Monic ∧ I = Ideal.span {f} := by
  classical
  obtain ⟨x, h, spanx⟩ := Ideal.exists_normalized_span_of_isPrincipal I
  refine ⟨x, (Polynomial.normalize_eq_self_iff_monic ?_).mp h, spanx⟩
  by_contra eq0
  simp [eq0, spanx] at ne

/--
lemma `exists_monic_span_sup_map_eq` / 引理 `exists_monic_span_sup_map_eq`

English:
lemma exists_monic_span_sup_map_eq
  statement: (p : Ideal R[X])
  proof: by
  let q := p.comap C
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  have ne' : Ideal.map (mapRingHom (Ideal.Quotient.mk q)) p != ⊥ := by
    simp only [ne_eq, map_eq_bot_iff_le_ker, Polynomial.ker_mapRingHom, q, mk_ker]
    exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le ne.symm)
  rcase

中文:
引理 exists_monic_span_sup_map_eq
  结论: (p : Ideal R[X])
  证明: by
  let q := p.comap C
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  have ne' : Ideal.map (mapRingHom (Ideal.Quotient.mk q)) p != ⊥ := by
    simp only [ne_eq, map_eq_bot_iff_le_ker, Polynomial.ker_mapRingHom, q, mk_ker]
    exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le ne.symm)
  rcase

Depends on / 依赖: Ideal.Quotient.field, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.map, Ideal.map_comap_le, Polynomial, Polynomial.exists_monic_span, Polynomial.ker_mapRingHom, Polynomial.lifts_and_natDegree_eq_and_monic, Quotient, exists_monic_span, ker_mapRingHom, lifts_and_natDegree_eq_and_monic, lt_of_le_of_ne, mapRingHom, map_comap_le, map_eq_bot_iff_le_ker, map_surjective, mk_ker, mk_surjective
-/
lemma exists_monic_span_sup_map_eq (p : Ideal R[X])
    (ism : (p.comap C).IsMaximal) (ne : p != (p.comap C).map C) :
    exists f : R[X], f.Monic ∧ p = (p.comap C).map C ⊔ Ideal.span {f} := by
  let q := p.comap C
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  have ne' : Ideal.map (mapRingHom (Ideal.Quotient.mk q)) p != ⊥ := by
    simp only [ne_eq, map_eq_bot_iff_le_ker, Polynomial.ker_mapRingHom, q, mk_ker]
    exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le ne.symm)
  rcases Polynomial.exists_monic_span _ ne' with ⟨y, mony, hy⟩
  have : y in lifts (Ideal.Quotient.mk q) := map_surjective _ Ideal.Quotient.mk_surjective _
  rcases Polynomial.lifts_and_natDegree_eq_and_monic this mony with ⟨f, hf, deg, monf⟩
  use f, monf
  trans comap (mapRingHom (Ideal.Quotient.mk q)) ((span {f}).map (mapRingHom (Ideal.Quotient.mk q)))
  · rw [Ideal.map_span, coe_mapRingHom, Set.image_singleton, hf, ← hy,
      Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective)]
    simpa [Polynomial.ker_mapRingHom, q] using Ideal.map_comap_le
  · rw [Ideal.comap_map_of_surjective' _ (map_surjective _ Ideal.Quotient.mk_surjective),
      sup_comm, Polynomial.ker_mapRingHom, mk_ker]

end Polynomial
