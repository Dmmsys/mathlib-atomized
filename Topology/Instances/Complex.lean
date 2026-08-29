/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Some results about the topology of ℂ
-/

public section


section ComplexSubfield

open Complex Set

open ComplexConjugate

/--
theorem `Complex.subfield_eq_of_closed` / 定理 `Complex.subfield_eq_of_closed`

English:
theorem Complex.subfield_eq_of_closed
  given: {K : Subfield Complex} (hc : IsClosed (K : Set Complex))
  proof: by
  suffices range (ofReal : Real -> Complex) subseteq K by
    rw [range_subset_iff]; rw [← coe_algebraMap] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_se

中文:
定理 Complex.subfield_eq_of_closed
  条件: {K : Subfield Complex} (hc : IsClosed (K : Set Complex))
  证明: by
  suffices range (ofReal : Real -> Complex) subseteq K by
    rw [range_subset_iff]; rw [← coe_algebraMap] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_se

Depends on / 依赖: IntermediateField, IntermediateField.coe_toSubalgebra, IsClos, Set.range, SetLike, SetLike.coe_set_eq, Subalgebra, Subalgebra.isSimpleOrder_of_finrank, Subfield, Subfield.toIntermediateField, closure, coe_algebraMap, coe_set_eq, coe_toSubalgebra, eq_bot_or_eq_top, finrank_real_complex, isSimpleOrder_of_finrank, ofReal, range_subset_iff, simp_rw
-/
theorem Complex.subfield_eq_of_closed {K : Subfield Complex} (hc : IsClosed (K : Set Complex)) :
    K = ofRealHom.fieldRange ∨ K = ⊤ := by
  suffices range (ofReal : Real -> Complex) subseteq K by
    rw [range_subset_iff]; rw [← coe_algebraMap] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_set_eq, IntermediateField.coe_toSubalgebra] at this ⊢
    exact this
  suffices range (ofReal : Real -> Complex) subseteq closure (Set.range ((ofReal : Real -> Complex) ∘ ((↑) : Rat -> Real))) by
    refine subset_trans this ?_
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [Function.comp_apply, ofReal_ratCast, SetLike.mem_coe, SubfieldClass.ratCast_mem]
  nth_rw 1 [range_comp]
  refine subset_trans ?_ (image_closure_subset_closure_image continuous_ofReal)
  rw [DenseRange.closure_range Rat.isDenseEmbedding_coe_real.dense]
  simp only [image_univ]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Complex.uniformContinuous_ringHom_eq_id_or_conj` / 定理 `Complex.uniformContinuous_ringHom_eq_id_or_conj`

English:
theorem Complex.uniformContinuous_ringHom_eq_id_or_conj
  statement: (K : Subfield Complex) {ψ : K ->+* Complex}
  proof: by
  let : IsTopologicalDivisionRing Complex := IsTopologicalDivisionRing.mk
  let : IsTopologicalRing K.topologicalClosure :=
    Subring.instIsTopologicalRing K.topologicalClosure.toSubring
  set ι : K -> K.topologicalClosure := ⇑(Subfield.inclusion K.le_topologicalClosure)
  have ui : IsUniformIn

中文:
定理 Complex.uniformContinuous_ringHom_eq_id_or_conj
  结论: (K : Subfield Complex) {ψ : K ->+* Complex}
  证明: by
  let : IsTopologicalDivisionRing Complex := IsTopologicalDivisionRing.mk
  let : IsTopologicalRing K.topologicalClosure :=
    Subring.instIsTopologicalRing K.topologicalClosure.toSubring
  set ι : K -> K.topologicalClosure := ⇑(Subfield.inclusion K.le_topologicalClosure)
  have ui : IsUniformIn

Depends on / 依赖: DenseRange, Filter, Filter.comap_comap, IsTopologicalDivisionRing, IsTopologicalDivisionRing.mk, IsTopologicalRing, IsUniformInducing, K.le_topologicalClosure, K.topologicalClosure, K.topologicalClosure.toSubring, Subfield, Subfield.inclusion, Subring, Subring.instIsTopologicalRing, closure, comap_comap, extension, inclusion, instIsTopologicalRing, isDenseInducing
-/
theorem Complex.uniformContinuous_ringHom_eq_id_or_conj (K : Subfield Complex) {ψ : K ->+* Complex}
    (hc : UniformContinuous ψ) : ψ.toFun = K.subtype ∨ ψ.toFun = conj ∘ K.subtype := by
  let : IsTopologicalDivisionRing Complex := IsTopologicalDivisionRing.mk
  let : IsTopologicalRing K.topologicalClosure :=
    Subring.instIsTopologicalRing K.topologicalClosure.toSubring
  set ι : K -> K.topologicalClosure := ⇑(Subfield.inclusion K.le_topologicalClosure)
  have ui : IsUniformInducing ι :=
    ⟨by
      rw [uniformity_subtype]; rw [uniformity_subtype]; rw [Filter.comap_comap]
      congr ⟩
  let di := ui.isDenseInducing (?_ : DenseRange ι)
  · -- extψ : closure(K) →+* ℂ is the extension of ψ : K →+* ℂ
    let extψ := IsDenseInducing.extendRingHom ui di.dense hc
    have hψ := (uniformContinuous_uniformly_extend ui di.dense hc).continuous
    rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure K) with h | h
    · left
      let j := RingEquiv.subfieldCongr h
      -- ψ₁ is the continuous ring hom `ℝ →+* ℂ` constructed from `j : closure (K) ≃+* ℝ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ := RingHom.comp extψ (RingHom.comp j.symm.toRingHom ofRealHom.rangeRestrictField)
      -- Porting note: was `by continuity!` and was used inline
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using! hψ.comp ((continuous_algebraMap Real Complex).subtype_mk _)
      ext1 x
      rsuffices ⟨r, hr⟩ : exists r : Real, ofRealHom.rangeRestrictField r = j (ι x)
      · have := RingHom.congr_fun (ringHom_eq_ofReal_of_continuous hψ₁) r
        rw [RingHom.comp_apply]; rw [RingHom.comp_apply]; rw [hr]; rw [RingEquiv.toRingHom_eq_coe] at this
        convert! this using 1
        · exact (IsDenseInducing.extend_eq di hc.continuous _).symm
        · rw [← ofRealHom.coe_rangeRestrictField, hr]
          rfl
      obtain ⟨r, hr⟩ := SetLike.coe_mem (j (ι x))
      exact ⟨r, Subtype.ext hr⟩
    · -- ψ₁ is the continuous ring hom `ℂ →+* ℂ` constructed from `closure (K) ≃+* ℂ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ :=
        RingHom.comp extψ
          (RingHom.comp (RingEquiv.subfieldCongr h).symm.toRingHom
            (@Subfield.topEquiv Complex _).symm.toRingHom)
      -- Porting note: was `by continuity!` and was used inline
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using! hψ.comp (continuous_id.subtype_mk _)
      rcases ringHom_eq_id_or_conj_of_continuous hψ₁ with h | h
      · left
        ext1 z
        convert! RingHom.congr_fun h z using 1
        exact (IsDenseInducing.extend_eq di hc.continuous z).symm
      · right
        ext1 z
        convert! RingHom.congr_fun h z using 1
        exact (IsDenseInducing.extend_eq di hc.continuous z).symm
  · let j : { x // x in closure (id '' K) } -> (K.topologicalClosure : Set Complex) :=
      fun x =>
      ⟨x, by
        convert! x.prop
        simp only [id, Set.image_id']
        rfl ⟩
    convert!
      DenseRange.comp (Function.Surjective.denseRange _) (IsDenseEmbedding.id.subtype (· in K)).dense
        (by fun_prop : Continuous j)
    rintro ⟨y, hy⟩
    use
      ⟨y, by
        convert! hy
        simp only [id, Set.image_id']
        rfl ⟩

end ComplexSubfield
