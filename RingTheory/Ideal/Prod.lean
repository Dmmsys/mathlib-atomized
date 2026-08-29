/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `Ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form. Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/

@[expose] public section


universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S] (I : Ideal R) (J : Ideal S)

namespace Ideal

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : Ideal (R × S)
  body: I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)

@[simp]

中文:
定义 乘积
  签名: : 理想 (R × S)
  定义体: I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)

@[simp]

Depends on / 依赖: I.comap, J.comap, RingHom, RingHom.fst, RingHom.snd
-/
def prod : Ideal (R × S) := I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (I : Ideal R) (J : Ideal S)
  statement: ↑(prod I J) = (I ×ˢ J : Set (R × S))
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (I : 理想 R) (J : 理想 S)
  结论: ↑(乘积 I J) = (I ×ˢ J : 集合 (R × S))
  证明: rfl

@[simp]
-/
theorem coe_prod (I : Ideal R) (J : Ideal S) : ↑(prod I J) = (I ×ˢ J : Set (R × S)) :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {x : R × S}
  statement: x in prod I J ↔ x.1 in I ∧ x.2 in J
  proof: Iff.rfl

@[simp]

中文:
定理 mem_prod
  条件: {x : R × S}
  结论: x in 乘积 I J ↔ x.1 in I ∧ x.2 in J
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {x : R × S} : x in prod I J ↔ x.1 in I ∧ x.2 in J :=
  Iff.rfl

@[simp]
/--
theorem `_root_.RingHom.ker_prodMap` / 定理 `_root_.RingHom.ker_prodMap`

English:
theorem _root_.RingHom.ker_prodMap
  statement: {T U : Type*} [Semiring T] [Semiring U] (f : R ->+* S)
  proof: by
  ext ⟨⟩; simp

@[simp]

中文:
定理 _root_.环态射.ker_prodMap
  结论: {T U : 类型} [半环 T] [半环 U] (f : R ->+* S)
  证明: by
  ext ⟨⟩; simp

@[simp]
-/
theorem _root_.RingHom.ker_prodMap {T U : Type*} [Semiring T] [Semiring U] (f : R ->+* S)
    (g : T ->+* U) : RingHom.ker (f.prodMap g) = (RingHom.ker f).prod (RingHom.ker g) := by
  ext ⟨⟩; simp

@[simp]
/--
theorem `prod_top_top` / 定理 `prod_top_top`

English:
theorem prod_top_top
  statement: prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤
  proof: Ideal.ext by simp

@[simp]

中文:
定理 prod_top_top
  结论: 乘积 (⊤ : 理想 R) (⊤ : 理想 S) = ⊤
  证明: Ideal.ext by simp

@[simp]

Depends on / 依赖: Ideal.ext
-/
theorem prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤ :=
Ideal.ext by simp

@[simp]
/--
theorem `prod_bot_bot` / 定理 `prod_bot_bot`

English:
theorem prod_bot_bot
  statement: prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥
  proof: SetLike.coe_injective Set.singleton_prod_singleton

@[gcongr]

中文:
定理 prod_bot_bot
  结论: 乘积 (⊥ : 理想 R) (⊥ : 理想 S) = ⊥
  证明: SetLike.coe_injective Set.singleton_prod_singleton

@[gcongr]

Depends on / 依赖: Set.singleton_prod_singleton, SetLike, SetLike.coe_injective, coe_injective, singleton_prod_singleton
-/
theorem prod_bot_bot : prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥ :=
SetLike.coe_injective Set.singleton_prod_singleton

@[gcongr]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ <= I₂) (hJ : J₁ <= J₂)
  proof: Set.prod_mono hI hJ

中文:
定理 prod_mono
  条件: {I₁ I₂ : 理想 R} {J₁ J₂ : 理想 S} (hI : I₁ <= I₂) (hJ : J₁ <= J₂)
  证明: Set.prod_mono hI hJ

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ <= I₂) (hJ : J₁ <= J₂) :
    prod I₁ J₁ <= prod I₂ J₂ :=
  Set.prod_mono hI hJ

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: {I₁ I₂ : Ideal R} {J : Ideal S} (hI : I₁ <= I₂)
  statement: prod I₁ J <= prod I₂ J
  proof: Set.prod_mono_left hI

中文:
定理 prod_mono_left
  条件: {I₁ I₂ : 理想 R} {J : 理想 S} (hI : I₁ <= I₂)
  结论: 乘积 I₁ J <= 乘积 I₂ J
  证明: Set.prod_mono_left hI

Depends on / 依赖: Set.prod_mono_left, prod_mono_left
-/
theorem prod_mono_left {I₁ I₂ : Ideal R} {J : Ideal S} (hI : I₁ <= I₂) : prod I₁ J <= prod I₂ J :=
  Set.prod_mono_left hI

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: {I : Ideal R} {J₁ J₂ : Ideal S} (hJ : J₁ <= J₂)
  statement: prod I J₁ <= prod I J₂
  proof: Set.prod_mono_right hJ

中文:
定理 prod_mono_right
  条件: {I : 理想 R} {J₁ J₂ : 理想 S} (hJ : J₁ <= J₂)
  结论: 乘积 I J₁ <= 乘积 I J₂
  证明: Set.prod_mono_right hJ

Depends on / 依赖: Set.prod_mono_right, prod_mono_right
-/
theorem prod_mono_right {I : Ideal R} {J₁ J₂ : Ideal S} (hJ : J₁ <= J₂) : prod I J₁ <= prod I J₂ :=
  Set.prod_mono_right hJ

/--
theorem `ideal_prod_eq` / 定理 `ideal_prod_eq`

English:
theorem ideal_prod_eq
  given: (I : Ideal (R × S))
  proof: by
  apply Ideal.ext
  rintro ⟨r, s⟩
  rw [mem_prod]; rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]; rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, ?_⟩
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩

中文:
定理 ideal_prod_eq
  条件: (I : 理想 (R × S))
  证明: by
  apply Ideal.ext
  rintro ⟨r, s⟩
  rw [mem_prod]; rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]; rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, ?_⟩
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩

Depends on / 依赖: I.add_mem, I.mul_mem_left, Ideal.ext, Prod.fst_surjective, Prod.snd_surjective, RingHom, RingHom.fst, RingHom.snd, add_mem, fst_surjective, mem_map_iff_of_surjective, mem_prod, mul_mem_left, snd_surjective
-/
theorem ideal_prod_eq (I : Ideal (R × S)) :
    I = Ideal.prod (map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I) := by
  apply Ideal.ext
  rintro ⟨r, s⟩
  rw [mem_prod]; rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]; rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, ?_⟩
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩
  simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂)

@[simp]
/--
theorem `map_fst_prod` / 定理 `map_fst_prod`

English:
theorem map_fst_prod
  given: (I : Ideal R) (J : Ideal S)
  statement: map (RingHom.fst R S) (prod I J) = I
  proof: by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.1, fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩

@[simp]

中文:
定理 map_fst_prod
  条件: (I : 理想 R) (J : 理想 S)
  结论: map (环态射.fst R S) (乘积 I J) = I
  证明: by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.1, fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩

@[simp]

Depends on / 依赖: Ideal.zero_mem, Prod.fst_surjective, RingHom, RingHom.fst, fst_surjective, mem_map_iff_of_surjective, zero_mem
-/
theorem map_fst_prod (I : Ideal R) (J : Ideal S) : map (RingHom.fst R S) (prod I J) = I := by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.1, fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩

@[simp]
/--
theorem `map_snd_prod` / 定理 `map_snd_prod`

English:
theorem map_snd_prod
  given: (I : Ideal R) (J : Ideal S)
  statement: map (RingHom.snd R S) (prod I J) = J
  proof: by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.2, fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩

@[simp]

中文:
定理 map_snd_prod
  条件: (I : 理想 R) (J : 理想 S)
  结论: map (环态射.snd R S) (乘积 I J) = J
  证明: by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.2, fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩

@[simp]

Depends on / 依赖: Ideal.zero_mem, Prod.snd_surjective, RingHom, RingHom.snd, mem_map_iff_of_surjective, snd_surjective, zero_mem
-/
theorem map_snd_prod (I : Ideal R) (J : Ideal S) : map (RingHom.snd R S) (prod I J) = J := by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.2, fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩

@[simp]
/--
theorem `map_prodComm_prod` / 定理 `map_prodComm_prod`

English:
theorem map_prodComm_prod
  proof: by
  refine Trans.trans (ideal_prod_eq _) ?_
  simp [map_map]

中文:
定理 map_prodComm_prod
  证明: by
  refine Trans.trans (ideal_prod_eq _) ?_
  simp [map_map]

Depends on / 依赖: Trans.trans, ideal_prod_eq, map_map
-/
theorem map_prodComm_prod :
    map ((RingEquiv.prodComm : R × S ≃+* S × R) : R × S ->+* S × R) (prod I J) = prod J I := by
  refine Trans.trans (ideal_prod_eq _) ?_
  simp [map_map]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `idealProdEquiv` / `idealProdEquiv` 的定义

English:
definition idealProdEquiv
  signature: : Ideal (R × S) ≃o Ideal R × Ideal S where
  body: ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
  map_rel_iff' {I J} := by
    simp only [Equiv.coe_fn_mk, Prod.mk_le_mk]
    refine ⟨fun h => ?_, fun h => ⟨map_mono h, map_mono h⟩⟩
    rw [idea

中文:
定义 idealProdEquiv
  签名: : 理想 (R × S) ≃o 理想 R × 理想 S where
  定义体: ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
  map_rel_iff' {I J} := by
    simp only [Equiv.coe_fn_mk, Prod.mk_le_mk]
    refine ⟨fun h => ?_, fun h => ⟨map_mono h, map_mono h⟩⟩
    rw [idea

Depends on / 依赖: RingHom, RingHom.fst, RingHom.snd
-/
def idealProdEquiv : Ideal (R × S) ≃o Ideal R × Ideal S where
  toFun I := ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
  map_rel_iff' {I J} := by
    simp only [Equiv.coe_fn_mk, Prod.mk_le_mk]
    refine ⟨fun h => ?_, fun h => ⟨map_mono h, map_mono h⟩⟩
    rw [ideal_prod_eq I]; rw [ideal_prod_eq J]
    exact inf_le_inf (comap_mono h.1) (comap_mono h.2)

@[simp]
/--
theorem `idealProdEquiv_symm_apply` / 定理 `idealProdEquiv_symm_apply`

English:
theorem idealProdEquiv_symm_apply
  given: (I : Ideal R) (J : Ideal S)
  proof: rfl

中文:
定理 idealProdEquiv_symm_apply
  条件: (I : 理想 R) (J : 理想 S)
  证明: rfl
-/
theorem idealProdEquiv_symm_apply (I : Ideal R) (J : Ideal S) :
    idealProdEquiv.symm ⟨I, J⟩ = prod I J :=
  rfl

/--
theorem `span_prod_le` / 定理 `span_prod_le`

English:
theorem span_prod_le
  given: {s : Set R} {t : Set S}
  proof: by
  rw [ideal_prod_eq (span (s ×ˢ t))]; rw [map_span]; rw [map_span]
  gcongr
  · exact Set.fst_image_prod_subset _ _
  · exact Set.snd_image_prod_subset _ _

中文:
定理 span_prod_le
  条件: {s : 集合 R} {t : 集合 S}
  证明: by
  rw [ideal_prod_eq (span (s ×ˢ t))]; rw [map_span]; rw [map_span]
  gcongr
  · exact Set.fst_image_prod_subset _ _
  · exact Set.snd_image_prod_subset _ _

Depends on / 依赖: Set.fst_image_prod_subset, Set.snd_image_prod_subset, fst_image_prod_subset, ideal_prod_eq, map_span, snd_image_prod_subset
-/
theorem span_prod_le {s : Set R} {t : Set S} :
    span (s ×ˢ t) <= prod (span s) (span t) := by
  rw [ideal_prod_eq (span (s ×ˢ t))]; rw [map_span]; rw [map_span]
  gcongr
  · exact Set.fst_image_prod_subset _ _
  · exact Set.snd_image_prod_subset _ _

/--
theorem `span_prod` / 定理 `span_prod`

English:
theorem span_prod
  given: {s : Set R} {t : Set S} (hst : s.Nonempty ↔ t.Nonempty)
  proof: by
  simp_rw [iff_iff_and_or_not_and_not, Set.not_nonempty_iff_eq_empty] at hst
  obtain ⟨hs, ht⟩ | ⟨rfl, rfl⟩ := hst
  · conv_lhs => rw [Ideal.ideal_prod_eq (Ideal.span (s ×ˢ t))]
    congr 1
    · rw [Ideal.map_span]
      simp [Set.fst_image_prod _ ht]
    · rw [Ideal.map_span]
      simp [Set.sn

中文:
定理 span_prod
  条件: {s : 集合 R} {t : 集合 S} (hst : s.非空 ↔ t.非空)
  证明: by
  simp_rw [iff_iff_and_or_not_and_not, Set.not_nonempty_iff_eq_empty] at hst
  obtain ⟨hs, ht⟩ | ⟨rfl, rfl⟩ := hst
  · conv_lhs => rw [Ideal.ideal_prod_eq (Ideal.span (s ×ˢ t))]
    congr 1
    · rw [Ideal.map_span]
      simp [Set.fst_image_prod _ ht]
    · rw [Ideal.map_span]
      simp [Set.sn

Depends on / 依赖: Ideal.ideal_prod_eq, Ideal.map_span, Ideal.span, Set.fst_image_prod, Set.not_nonempty_iff_eq_empty, Set.snd_image_prod, conv_lhs, fst_image_prod, ideal_prod_eq, iff_iff_and_or_not_and_not, map_span, not_nonempty_iff_eq_empty, simp_rw, snd_image_prod
-/
theorem span_prod {s : Set R} {t : Set S} (hst : s.Nonempty ↔ t.Nonempty) :
    span (s ×ˢ t) = prod (span s) (span t) := by
  simp_rw [iff_iff_and_or_not_and_not, Set.not_nonempty_iff_eq_empty] at hst
  obtain ⟨hs, ht⟩ | ⟨rfl, rfl⟩ := hst
  · conv_lhs => rw [Ideal.ideal_prod_eq (Ideal.span (s ×ˢ t))]
    congr 1
    · rw [Ideal.map_span]
      simp [Set.fst_image_prod _ ht]
    · rw [Ideal.map_span]
      simp [Set.snd_image_prod hs]
  · simp

@[simp]
/--
theorem `prod_inj` / 定理 `prod_inj`

English:
theorem prod_inj
  given: {I I' : Ideal R} {J J' : Ideal S}
  proof: by
  simp only [← idealProdEquiv_symm_apply, idealProdEquiv.symm.injective.eq_iff, Prod.mk_inj]

@[simp]

中文:
定理 prod_inj
  条件: {I I' : 理想 R} {J J' : 理想 S}
  证明: by
  simp only [← idealProdEquiv_symm_apply, idealProdEquiv.symm.injective.eq_iff, Prod.mk_inj]

@[simp]

Depends on / 依赖: Prod.mk_inj, eq_iff, idealProdEquiv, idealProdEquiv.symm.injective.eq_iff, idealProdEquiv_symm_apply, injective, mk_inj
-/
theorem prod_inj {I I' : Ideal R} {J J' : Ideal S} :
    prod I J = prod I' J' ↔ I = I' ∧ J = J' := by
  simp only [← idealProdEquiv_symm_apply, idealProdEquiv.symm.injective.eq_iff, Prod.mk_inj]

@[simp]
/--
theorem `prod_eq_bot_iff` / 定理 `prod_eq_bot_iff`

English:
theorem prod_eq_bot_iff
  given: {I : Ideal R} {J : Ideal S}
  proof: by
  rw [← prod_inj]; rw [prod_bot_bot]

@[simp]

中文:
定理 prod_eq_bot_iff
  条件: {I : 理想 R} {J : 理想 S}
  证明: by
  rw [← prod_inj]; rw [prod_bot_bot]

@[simp]

Depends on / 依赖: prod_bot_bot, prod_inj
-/
theorem prod_eq_bot_iff {I : Ideal R} {J : Ideal S} :
    prod I J = ⊥ ↔ I = ⊥ ∧ J = ⊥ := by
  rw [← prod_inj]; rw [prod_bot_bot]

@[simp]
/--
theorem `prod_eq_top_iff` / 定理 `prod_eq_top_iff`

English:
theorem prod_eq_top_iff
  given: {I : Ideal R} {J : Ideal S}
  proof: by
  rw [← prod_inj]; rw [prod_top_top]

中文:
定理 prod_eq_top_iff
  条件: {I : 理想 R} {J : 理想 S}
  证明: by
  rw [← prod_inj]; rw [prod_top_top]

Depends on / 依赖: prod_inj, prod_top_top
-/
theorem prod_eq_top_iff {I : Ideal R} {J : Ideal S} :
    prod I J = ⊤ ↔ I = ⊤ ∧ J = ⊤ := by
  rw [← prod_inj]; rw [prod_top_top]

/--
theorem `isPrime_of_isPrime_prod_top` / 定理 `isPrime_of_isPrime_prod_top`

English:
theorem isPrime_of_isPrime_prod_top
  given: {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime)
  proof: by
  constructor
  · contrapose h
    rw [h]; rw [prod_top_top]; rw [isPrime_iff]
    simp
  · intro x y hxy
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ in prod I ⊤ := by
      rw [Prod.mk_mul_mk]; rw [mul_one]; rw [mem_prod]
      exact ⟨hxy, trivial⟩
    simpa using h.mem_or_mem this

中文:
定理 isPrime_of_isPrime_prod_top
  条件: {I : 理想 R} (h : (理想.乘积 I (⊤ : 理想 S)).是素)
  证明: by
  constructor
  · contrapose h
    rw [h]; rw [prod_top_top]; rw [isPrime_iff]
    simp
  · intro x y hxy
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ in prod I ⊤ := by
      rw [Prod.mk_mul_mk]; rw [mul_one]; rw [mem_prod]
      exact ⟨hxy, trivial⟩
    simpa using h.mem_or_mem this

Depends on / 依赖: Prod.mk_mul_mk, contrapose, h.mem_or_mem, isPrime_iff, mem_or_mem, mem_prod, mk_mul_mk, mul_one, prod_top_top
-/
theorem isPrime_of_isPrime_prod_top {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) :
    I.IsPrime := by
  constructor
  · contrapose h
    rw [h]; rw [prod_top_top]; rw [isPrime_iff]
    simp
  · intro x y hxy
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ in prod I ⊤ := by
      rw [Prod.mk_mul_mk]; rw [mul_one]; rw [mem_prod]
      exact ⟨hxy, trivial⟩
    simpa using h.mem_or_mem this

/--
theorem `isPrime_of_isPrime_prod_top'` / 定理 `isPrime_of_isPrime_prod_top'`

English:
theorem isPrime_of_isPrime_prod_top'
  given: {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime)
  proof: by
  apply isPrime_of_isPrime_prod_top (S := R)
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := R) (S := S))

中文:
定理 isPrime_of_isPrime_prod_top'
  条件: {I : 理想 S} (h : (理想.乘积 (⊤ : 理想 R) I).是素)
  证明: by
  apply isPrime_of_isPrime_prod_top (S := R)
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := R) (S := S))

Depends on / 依赖: isPrime_of_isPrime_prod_top, map_prodComm_prod
-/
theorem isPrime_of_isPrime_prod_top' {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime) :
    I.IsPrime := by
  apply isPrime_of_isPrime_prod_top (S := R)
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := R) (S := S))

/--
theorem `isPrime_ideal_prod_top` / 定理 `isPrime_ideal_prod_top`

English:
theorem isPrime_ideal_prod_top
  given: {I : Ideal R} [h : I.IsPrime]
  statement: (prod I (⊤ : Ideal S)).IsPrime where
  proof: by simpa using h.ne_top
  mem_or_mem' {x y} := by simpa using h.mem_or_mem

中文:
定理 isPrime_ideal_prod_top
  条件: {I : 理想 R} [h : I.是素]
  结论: (乘积 I (⊤ : 理想 S)).是素 where
  证明: by simpa using h.ne_top
  mem_or_mem' {x y} := by simpa using h.mem_or_mem

Depends on / 依赖: h.mem_or_mem, h.ne_top, mem_or_mem, ne_top
-/
theorem isPrime_ideal_prod_top {I : Ideal R} [h : I.IsPrime] : (prod I (⊤ : Ideal S)).IsPrime where
  ne_top' := by simpa using h.ne_top
  mem_or_mem' {x y} := by simpa using h.mem_or_mem

/--
theorem `isPrime_ideal_prod_top'` / 定理 `isPrime_ideal_prod_top'`

English:
theorem isPrime_ideal_prod_top'
  given: {I : Ideal S} [h : I.IsPrime]
  statement: (prod (⊤ : Ideal R) I).IsPrime
  proof: by
  let : IsPrime (prod I (⊤ : Ideal R)) := isPrime_ideal_prod_top
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := S) (S := R))

中文:
定理 isPrime_ideal_prod_top'
  条件: {I : 理想 S} [h : I.是素]
  结论: (乘积 (⊤ : 理想 R) I).是素
  证明: by
  let : IsPrime (prod I (⊤ : Ideal R)) := isPrime_ideal_prod_top
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := S) (S := R))

Depends on / 依赖: IsPrime, isPrime_ideal_prod_top, map_prodComm_prod
-/
theorem isPrime_ideal_prod_top' {I : Ideal S} [h : I.IsPrime] : (prod (⊤ : Ideal R) I).IsPrime := by
  let : IsPrime (prod I (⊤ : Ideal R)) := isPrime_ideal_prod_top
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := S) (S := R))

/--
theorem `ideal_prod_prime_aux` / 定理 `ideal_prod_prime_aux`

English:
theorem ideal_prod_prime_aux
  given: {I : Ideal R} {J : Ideal S}
  proof: by
  contrapose!
  simp only [ne_top_iff_one, isPrime_iff, not_and, not_forall, not_or]
  exact fun ⟨hI, hJ⟩ _ => ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩

中文:
定理 ideal_prod_prime_aux
  条件: {I : 理想 R} {J : 理想 S}
  证明: by
  contrapose!
  simp only [ne_top_iff_one, isPrime_iff, not_and, not_forall, not_or]
  exact fun ⟨hI, hJ⟩ _ => ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩

Depends on / 依赖: contrapose, isPrime_iff, ne_top_iff_one, not_and, not_forall, not_or
-/
theorem ideal_prod_prime_aux {I : Ideal R} {J : Ideal S} :
    (Ideal.prod I J).IsPrime -> I = ⊤ ∨ J = ⊤ := by
  contrapose!
  simp only [ne_top_iff_one, isPrime_iff, not_and, not_forall, not_or]
  exact fun ⟨hI, hJ⟩ _ => ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩

/--
theorem `ideal_prod_prime` / 定理 `ideal_prod_prime`

English:
theorem ideal_prod_prime
  given: (I : Ideal (R × S))
  proof: by
  constructor
  · rw [ideal_prod_eq I]
    intro hI
    rcases ideal_prod_prime_aux hI with (h | h)
    · right
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top' hI, rfl⟩⟩
    · left
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top hI, rfl⟩⟩
  · rintro (⟨p, ⟨h, r

中文:
定理 ideal_prod_prime
  条件: (I : 理想 (R × S))
  证明: by
  constructor
  · rw [ideal_prod_eq I]
    intro hI
    rcases ideal_prod_prime_aux hI with (h | h)
    · right
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top' hI, rfl⟩⟩
    · left
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top hI, rfl⟩⟩
  · rintro (⟨p, ⟨h, r

Depends on / 依赖: ideal_prod_eq, ideal_prod_prime_aux, isPrime_ideal_prod_top, isPrime_of_isPrime_prod_top
-/
theorem ideal_prod_prime (I : Ideal (R × S)) :
    I.IsPrime ↔
      (exists p : Ideal R, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨
        exists p : Ideal S, p.IsPrime ∧ I = Ideal.prod ⊤ p := by
  constructor
  · rw [ideal_prod_eq I]
    intro hI
    rcases ideal_prod_prime_aux hI with (h | h)
    · right
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top' hI, rfl⟩⟩
    · left
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top hI, rfl⟩⟩
  · rintro (⟨p, ⟨h, rfl⟩⟩ | ⟨p, ⟨h, rfl⟩⟩)
    · exact isPrime_ideal_prod_top
    · exact isPrime_ideal_prod_top'

end Ideal

open Submodule.IsPrincipal in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPrincipalIdealRing
  signature: R] [IsPrincipalIdealRing S] : IsPrincipalIdealRing (R × S) where
  body: by
    rw [I.ideal_prod_eq]; rw [← span_singleton_generator (I.map _)]; rw [← span_singleton_generator (I.map (RingHom.snd R S))]; rw [← Ideal.span]; rw [← Ideal.span]; rw [← Ideal.span_prod (iff_of_true (by simp) (by simp))]; rw [Set.singleton_prod_singleton]
    exact ⟨_, rfl⟩

中文:
实例 [是主理想环
  签名: R] [是主理想环 S] : 是主理想环 (R × S) where
  定义体: by
    rw [I.ideal_prod_eq]; rw [← span_singleton_generator (I.map _)]; rw [← span_singleton_generator (I.map (RingHom.snd R S))]; rw [← Ideal.span]; rw [← Ideal.span]; rw [← Ideal.span_prod (iff_of_true (by simp) (by simp))]; rw [Set.singleton_prod_singleton]
    exact ⟨_, rfl⟩

Depends on / 依赖: I.ideal_prod_eq, I.map, Ideal.span, Ideal.span_prod, RingHom, RingHom.snd, Set.singleton_prod_singleton, ideal_prod_eq, iff_of_true, singleton_prod_singleton, span_prod, span_singleton_generator
-/
instance [IsPrincipalIdealRing R] [IsPrincipalIdealRing S] : IsPrincipalIdealRing (R × S) where
  principal I := by
    rw [I.ideal_prod_eq]; rw [← span_singleton_generator (I.map _)]; rw [← span_singleton_generator (I.map (RingHom.snd R S))]; rw [← Ideal.span]; rw [← Ideal.span]; rw [← Ideal.span_prod (iff_of_true (by simp) (by simp))]; rw [Set.singleton_prod_singleton]
    exact ⟨_, rfl⟩
