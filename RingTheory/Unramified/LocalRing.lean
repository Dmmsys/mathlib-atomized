/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramified algebras over local rings

## Main results
- `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`:
  Let `R` be a local ring, `A` be a local `R`-algebra essentially of finite type.
  Then `A/R` is unramified if and only if `κA/κR` is separable, and `m_R S = m_S`.
- `Algebra.isUnramifiedAt_iff_map_eq`:
  Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
  Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q = qS_q`.

Let `S` be an `R` algebra, `p` be a prime of `R`, and suppose `q` is the unique prime of `S`
lying over `R`, then
- `Localization.localRingHom_injective_of_primesOver_eq_singleton`:
  If `R ⊆ S` is integral, then `R_p → S_q` is injective.
- `Localization.localRingHom_surjective_of_primesOver_eq_singleton`:
  Suppose `S` is `R`-finite and unramified at `q`. If `κ(p) = κ(q)` then `R_p → S_q` is surjective.
- `Localization.exists_awayMap_bijective_of_residueField_surjective`:
  Suppose `R ⊆ S` is finite and unramified at `q`.
  If `κ(p) = κ(q)` then there exists `r ∉ p` such that `R[1/f] = S[1/f]`.
-/

@[expose] public section

open IsLocalRing

namespace Algebra

section IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FormallyUnramified S (ResidueField S)
  body: .quotient _

中文:
实例 :
  签名: 形式非分歧 S (ResidueField S)
  定义体: .quotient _

Depends on / 依赖: quotient
-/
instance : FormallyUnramified S (ResidueField S) := .quotient _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallyUnramified
  signature: R S] :
  body: have : FormallyUnramified R (ResidueField S) := .comp _ S _
  .of_restrictScalars R _ _

中文:
实例 [形式非分歧
  签名: R S] :
  定义体: have : FormallyUnramified R (ResidueField S) := .comp _ S _
  .of_restrictScalars R _ _

Depends on / 依赖: FormallyUnramified, ResidueField, of_restrictScalars
-/
instance [FormallyUnramified R S] :
    FormallyUnramified (ResidueField R) (ResidueField S) :=
  have : FormallyUnramified R (ResidueField S) := .comp _ S _
  .of_restrictScalars R _ _

variable [EssFiniteType R S]

@[stacks 00UW "(2)"]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallyUnramified
  signature: R S] :
  body: have : EssFiniteType R (ResidueField S) := .comp _ S _
  have : EssFiniteType (ResidueField R) (ResidueField S) := .of_comp R _ _
  FormallyUnramified.finite_of_free _ _

@[stacks 00UW "(2)"]

中文:
实例 [形式非分歧
  签名: R S] :
  定义体: have : EssFiniteType R (ResidueField S) := .comp _ S _
  have : EssFiniteType (ResidueField R) (ResidueField S) := .of_comp R _ _
  FormallyUnramified.finite_of_free _ _

@[stacks 00UW "(2)"]

Depends on / 依赖: EssFiniteType, FormallyUnramified, FormallyUnramified.finite_of_free, ResidueField, finite_of_free, of_comp
-/
instance [FormallyUnramified R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  have : EssFiniteType R (ResidueField S) := .comp _ S _
  have : EssFiniteType (ResidueField R) (ResidueField S) := .of_comp R _ _
  FormallyUnramified.finite_of_free _ _

@[stacks 00UW "(2)"]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallyUnramified
  signature: R S] :
  body: FormallyUnramified.isSeparable _ _

中文:
实例 [形式非分歧
  签名: R S] :
  定义体: FormallyUnramified.isSeparable _ _

Depends on / 依赖: FormallyUnramified, FormallyUnramified.isSeparable, isSeparable
-/
instance [FormallyUnramified R S] :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
  FormallyUnramified.isSeparable _ _

set_option backward.inferInstanceAs.wrap.data false in
/--
lemma `FormallyUnramified.isField_quotient_map_maximalIdeal` / 引理 `FormallyUnramified.isField_quotient_map_maximalIdeal`

English:
lemma FormallyUnramified.isField_quotient_map_maximalIdeal
  given: [FormallyUnramified R S]
  proof: by
  let mR := (maximalIdeal R).map (algebraMap R S)
  have hmR : mR <= maximalIdeal S := ((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp ‹_›
  let : Algebra (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| Algebra (R ⧸ _) _)
  have : IsScalarTower R (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| IsScalarTower R (R ⧸ _) _)
  have : FormallyUnramified (ResidueField R) (S ⧸ mR) := .of_restrictScalars R _ _
  have : EssFiniteType (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  have : Module.Finite (ResidueField R) (S ⧸ mR) := FormallyUnramified.finite_of_free _ _
  have : IsReduced (S ⧸ mR) := FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)
  have : IsArtinianRing (S ⧸ mR) := isArtinian_of_tower (ResidueField R) inferInstance
  have : Nontrivial (S ⧸ mR) :=
Ideal.Quotient.nontrivial_iff.mpr ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hmR
  have : IsLocalRing (S ⧸ mR) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : maximalIdeal (S ⧸ mR) = ⊥ := by
    rw [← jacobson_eq_maximalIdeal _ bot_ne_top]; rw [IsArtinianRing.jacobson_eq_radical]; rw [← Ideal.zero_eq_bot]; rw [← nilradical]; rw [nilradical_eq_zero]
  rwa [← isField_iff_maximalIdeal_eq] at this

@[stacks 00UW "(1)"]

中文:
引理 形式非分歧.isField_quotient_map_maximalIdeal
  条件: [形式非分歧 R S]
  证明: by
  let mR := (maximalIdeal R).map (algebraMap R S)
  have hmR : mR <= maximalIdeal S := ((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp ‹_›
  let : Algebra (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| Algebra (R ⧸ _) _)
  have : IsScalarTower R (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| IsScalarTower R (R ⧸ _) _)
  have : FormallyUnramified (ResidueField R) (S ⧸ mR) := .of_restrictScalars R _ _
  have : EssFiniteType (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  have : Module.Finite (ResidueField R) (S ⧸ mR) := FormallyUnramified.finite_of_free _ _
  have : IsReduced (S ⧸ mR) := FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)
  have : IsArtinianRing (S ⧸ mR) := isArtinian_of_tower (ResidueField R) inferInstance
  have : Nontrivial (S ⧸ mR) :=
Ideal.Quotient.nontrivial_iff.mpr ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hmR
  have : IsLocalRing (S ⧸ mR) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : maximalIdeal (S ⧸ mR) = ⊥ := by
    rw [← jacobson_eq_maximalIdeal _ bot_ne_top]; rw [IsArtinianRing.jacobson_eq_radical]; rw [← Ideal.zero_eq_bot]; rw [← nilradical]; rw [nilradical_eq_zero]
  rwa [← isField_iff_maximalIdeal_eq] at this

@[stacks 00UW "(1)"]

Depends on / 依赖: Algebra, EssFiniteType, Finite, FormallyUnramified, IsScalarTower, Module, Module.Finite, Residu, ResidueField, algebraMap, local_hom_TFAE, maximalIdeal, of_comp, of_restrictScalars
-/
lemma FormallyUnramified.isField_quotient_map_maximalIdeal [FormallyUnramified R S] :
    IsField (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  let mR := (maximalIdeal R).map (algebraMap R S)
  have hmR : mR <= maximalIdeal S := ((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp ‹_›
  let : Algebra (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| Algebra (R ⧸ _) _)
  have : IsScalarTower R (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| IsScalarTower R (R ⧸ _) _)
  have : FormallyUnramified (ResidueField R) (S ⧸ mR) := .of_restrictScalars R _ _
  have : EssFiniteType (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  have : Module.Finite (ResidueField R) (S ⧸ mR) := FormallyUnramified.finite_of_free _ _
  have : IsReduced (S ⧸ mR) := FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)
  have : IsArtinianRing (S ⧸ mR) := isArtinian_of_tower (ResidueField R) inferInstance
  have : Nontrivial (S ⧸ mR) :=
Ideal.Quotient.nontrivial_iff.mpr ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hmR
  have : IsLocalRing (S ⧸ mR) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : maximalIdeal (S ⧸ mR) = ⊥ := by
    rw [← jacobson_eq_maximalIdeal _ bot_ne_top]; rw [IsArtinianRing.jacobson_eq_radical]; rw [← Ideal.zero_eq_bot]; rw [← nilradical]; rw [nilradical_eq_zero]
  rwa [← isField_iff_maximalIdeal_eq] at this

@[stacks 00UW "(1)"]
/--
lemma `FormallyUnramified.map_maximalIdeal` / 引理 `FormallyUnramified.map_maximalIdeal`

English:
lemma FormallyUnramified.map_maximalIdeal
  given: [FormallyUnramified R S]
  proof: by
  apply eq_maximalIdeal
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_quotient_map_maximalIdeal

@[stacks 02FM]

中文:
引理 形式非分歧.map_maximalIdeal
  条件: [形式非分歧 R S]
  证明: by
  apply eq_maximalIdeal
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_quotient_map_maximalIdeal

@[stacks 02FM]

Depends on / 依赖: Ideal.Quotient.maximal_ideal_iff_isField_quotient, Quotient, eq_maximalIdeal, isField_quotient_map_maximalIdeal, maximal_ideal_iff_isField_quotient
-/
lemma FormallyUnramified.map_maximalIdeal [FormallyUnramified R S] :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  apply eq_maximalIdeal
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_quotient_map_maximalIdeal

@[stacks 02FM]
/--
lemma `FormallyUnramified.of_map_maximalIdeal` / 引理 `FormallyUnramified.of_map_maximalIdeal`

English:
lemma FormallyUnramified.of_map_maximalIdeal
  proof: by
  constructor
  have : FormallyUnramified (ResidueField R) (ResidueField S) := .of_isSeparable _ _
  have : FormallyUnramified R (ResidueField S) := .comp _ (ResidueField R) _
  rw [← subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x in Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

中文:
引理 形式非分歧.of_map_maximalIdeal
  证明: by
  constructor
  have : FormallyUnramified (ResidueField R) (ResidueField S) := .of_isSeparable _ _
  have : FormallyUnramified R (ResidueField S) := .comp _ (ResidueField R) _
  rw [← subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x in Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: FormallyUnramified, Ideal.Quotient.mk_surjective, Ideal.toCotangent_surjective, Kaehler, KaehlerDifferential, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange, Quotient, ResidueField, Subsingleton, Subsingleton.elim, exact_kerCotangentToTensor_mapBaseChange, mk_surjective, of_isSeparable, subsingleton_of_forall_eq, subsingleton_tensorProduct, toCotangent_surjective
-/
lemma FormallyUnramified.of_map_maximalIdeal
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallyUnramified R S := by
  constructor
  have : FormallyUnramified (ResidueField R) (ResidueField S) := .of_isSeparable _ _
  have : FormallyUnramified R (ResidueField S) := .comp _ (ResidueField R) _
  rw [← subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x in Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

/--
lemma `FormallyUnramified.iff_map_maximalIdeal_eq` / 引理 `FormallyUnramified.iff_map_maximalIdeal_eq`

English:
lemma FormallyUnramified.iff_map_maximalIdeal_eq
  proof: ⟨fun _ => ⟨inferInstance, map_maximalIdeal⟩, fun ⟨_, e⟩ => of_map_maximalIdeal e⟩

中文:
引理 形式非分歧.iff_map_maximalIdeal_eq
  证明: ⟨fun _ => ⟨inferInstance, map_maximalIdeal⟩, fun ⟨_, e⟩ => of_map_maximalIdeal e⟩

Depends on / 依赖: map_maximalIdeal, of_map_maximalIdeal
-/
lemma FormallyUnramified.iff_map_maximalIdeal_eq :
    Algebra.FormallyUnramified R S ↔
      Algebra.IsSeparable (ResidueField R) (ResidueField S) ∧
      (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  ⟨fun _ => ⟨inferInstance, map_maximalIdeal⟩, fun ⟨_, e⟩ => of_map_maximalIdeal e⟩

end IsLocalRing

section IsUnramifiedAt

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/--
lemma `isUnramifiedAt_iff_map_eq` / 引理 `isUnramifiedAt_iff_map_eq`

English:
lemma isUnramifiedAt_iff_map_eq
  proof: by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · exact ⟨fun _ => .of_restrictScalars R _ _,
      fun _ => Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩
  rw [FormallyUnramified.iff_map_maximalIdeal_eq]
  congr!
  rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_map]; rw [Localization.localRingHom]; rw [IsLocalization.map_comp]; rw [← IsScalarTower.algebraMap_eq]

中文:
引理 isUnramifiedAt_iff_map_eq
  证明: by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · exact ⟨fun _ => .of_restrictScalars R _ _,
      fun _ => Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩
  rw [FormallyUnramified.iff_map_maximalIdeal_eq]
  congr!
  rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_map]; rw [Localization.localRingHom]; rw [IsLocalization.map_comp]; rw [← IsScalarTower.algebraMap_eq]

Depends on / 依赖: Algebra, Algebra.FormallyUnramified, Algebra.FormallyUnramified.comp, AtPrime, EssFiniteType, FormallyUnramified, FormallyUnramified.iff_map_maximalIdeal_eq, Ideal.map_map, IsLiesOverAlgebra, Localization, Localization.AtPrime, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq, Localization.AtPrime.map_eq_maximalIdeal, Localization.localRing, algebraMap_eq, iff_map_maximalIdeal_eq, localRing, map_eq_maximalIdeal, map_map, of_comp
-/
lemma isUnramifiedAt_iff_map_eq :
    Algebra.IsUnramifiedAt R q ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _ := by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · exact ⟨fun _ => .of_restrictScalars R _ _,
      fun _ => Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩
  rw [FormallyUnramified.iff_map_maximalIdeal_eq]
  congr!
  rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_map]; rw [Localization.localRingHom]; rw [IsLocalization.map_comp]; rw [← IsScalarTower.algebraMap_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsUnramifiedAt
  signature: R q] : Algebra.IsSeparable p.ResidueField q.ResidueField
  body: ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

中文:
实例 [代数.IsUnramifiedAt
  签名: R q] : 代数.是可分 p.ResidueField q.ResidueField
  定义体: ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

Depends on / 依赖: Algebra, Algebra.isUnramifiedAt_iff_map_eq, isUnramifiedAt_iff_map_eq
-/
instance [Algebra.IsUnramifiedAt R q] : Algebra.IsSeparable p.ResidueField q.ResidueField :=
  ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsUnramifiedAt
  signature: R q] : Module.Finite p.ResidueField q.ResidueField
  body: Algebra.FormallyUnramified.finite_of_free _ _

中文:
实例 [代数.IsUnramifiedAt
  签名: R q] : 模.有限 p.ResidueField q.ResidueField
  定义体: Algebra.FormallyUnramified.finite_of_free _ _

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.finite_of_free, FormallyUnramified, finite_of_free
-/
instance [Algebra.IsUnramifiedAt R q] : Module.Finite p.ResidueField q.ResidueField :=
  Algebra.FormallyUnramified.finite_of_free _ _

end IsUnramifiedAt

end Algebra

section UniquePrimeOver

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} [p.IsPrime]
  {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q})

include hq

namespace Localization

/--
lemma `localRingHom_injective_of_primesOver_eq_singleton` / 引理 `localRingHom_injective_of_primesOver_eq_singleton`

English:
lemma localRingHom_injective_of_primesOver_eq_singleton
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  obtain ⟨a, haq, e⟩ : exists a ∉ q, a * (algebraMap R S) x = 0 := by
    simpa [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] using hx
  obtain ⟨r, hrp, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ haq
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
    ⟨⟨r, hrp⟩, FaithfulSMul.algebraMap_injective R S ?_⟩
  grind

中文:
引理 localRingHom_injective_of_primesOver_eq_singleton
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  obtain ⟨a, haq, e⟩ : exists a ∉ q, a * (algebraMap R S) x = 0 := by
    simpa [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] using hx
  obtain ⟨r, hrp, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ haq
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
    ⟨⟨r, hrp⟩, FaithfulSMul.algebraMap_injective R S ?_⟩
  grind

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton, IsLocalization, IsLocalization.exists_mk, IsLocalization.mk, Localization, Localization.localRingHom_mk, _eq_zero_iff, algebraMap, algebraMap_injective, exists_mk, exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton, injective_iff_map_eq_zero, localRingHom_mk, p.primeCompl, primeCompl
-/
lemma localRingHom_injective_of_primesOver_eq_singleton
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    Function.Injective (localRingHom p q (algebraMap R S) (hq.ge rfl).2.1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  obtain ⟨a, haq, e⟩ : exists a ∉ q, a * (algebraMap R S) x = 0 := by
    simpa [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] using hx
  obtain ⟨r, hrp, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ haq
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
    ⟨⟨r, hrp⟩, FaithfulSMul.algebraMap_injective R S ?_⟩
  grind

/--
lemma `finite_of_primesOver_eq_singleton` / 引理 `finite_of_primesOver_eq_singleton`

English:
lemma finite_of_primesOver_eq_singleton
  statement: [Module.Finite R S] [q.LiesOver p]
  proof: by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap, ?_⟩
  rw [Finset.coe_image]; rw [← Submodule.span_span_of_tower R]; rw [← Submodule.map_span]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.coe_range]; rw [AlgHom.coe_toLinearMap]; rw [IsScalarTower.coe_toAlgHom']; rw [← top_le_iff]
  rintro x -
  obtain ⟨x, ⟨s, hsq⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨r, hr, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hsq
  rw [← Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M := p.primeCompl) _ ⟨r]; rw [hr⟩)]; rw [Algebra.smul_def]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply _ S]; rw [e']; rw [map_mul]; rw [mul_assoc]; rw [mul_left_comm]; rw [IsLocalization.mk'_spec'_mk]; rw [← map_mul]
  exact Submodule.subset_span ⟨_, rfl⟩

中文:
引理 finite_of_primesOver_eq_singleton
  结论: [模.有限 R S] [q.LiesOver p]
  证明: by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap, ?_⟩
  rw [Finset.coe_image]; rw [← Submodule.span_span_of_tower R]; rw [← Submodule.map_span]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.coe_range]; rw [AlgHom.coe_toLinearMap]; rw [IsScalarTower.coe_toAlgHom']; rw [← top_le_iff]
  rintro x -
  obtain ⟨x, ⟨s, hsq⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨r, hr, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hsq
  rw [← Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M := p.primeCompl) _ ⟨r]; rw [hr⟩)]; rw [Algebra.smul_def]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply _ S]; rw [e']; rw [map_mul]; rw [mul_assoc]; rw [mul_left_comm]; rw [IsLocalization.mk'_spec'_mk]; rw [← map_mul]
  exact Submodule.subset_span ⟨_, rfl⟩

Depends on / 依赖: AlgHom, AlgHom.coe_toLinearMap, Finite, Finset, Finset.coe_image, Ideal.exists_notMem_dvd_alge, IsLocalization, IsLocalization.exists_mk, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, LinearMap, LinearMap.coe_range, Module, Module.Finite.fg_top, Submodule, Submodule.map_span, Submodule.map_top, Submodule.span_span_of_tower, classical
-/
lemma finite_of_primesOver_eq_singleton [Module.Finite R S] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap, ?_⟩
  rw [Finset.coe_image]; rw [← Submodule.span_span_of_tower R]; rw [← Submodule.map_span]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.coe_range]; rw [AlgHom.coe_toLinearMap]; rw [IsScalarTower.coe_toAlgHom']; rw [← top_le_iff]
  rintro x -
  obtain ⟨x, ⟨s, hsq⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨r, hr, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hsq
  rw [← Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M := p.primeCompl) _ ⟨r]; rw [hr⟩)]; rw [Algebra.smul_def]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply _ S]; rw [e']; rw [map_mul]; rw [mul_assoc]; rw [mul_left_comm]; rw [IsLocalization.mk'_spec'_mk]; rw [← map_mul]
  exact Submodule.subset_span ⟨_, rfl⟩

/--
lemma `localRingHom_surjective_of_primesOver_eq_singleton` / 引理 `localRingHom_surjective_of_primesOver_eq_singleton`

English:
lemma localRingHom_surjective_of_primesOver_eq_singleton
  proof: by
  have := Localization.finite_of_primesOver_eq_singleton hq
  rw [← Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
  change Function.Surjective (Algebra.linearMap _ _)
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map]; rw [Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [← ResidueField.algebraMap_eq]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime q)]; rw [ResidueField.algebraMap_eq]; rw [← sub_eq_zero]; rw [← map_sub]; rw [residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  refine sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ha)

omit hq in

中文:
引理 localRingHom_surjective_of_primesOver_eq_singleton
  证明: by
  have := Localization.finite_of_primesOver_eq_singleton hq
  rw [← Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
  change Function.Surjective (Algebra.linearMap _ _)
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map]; rw [Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [← ResidueField.algebraMap_eq]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime q)]; rw [ResidueField.algebraMap_eq]; rw [← sub_eq_zero]; rw [← map_sub]; rw [residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  refine sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ha)

omit hq in

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.map_maximalIdeal, Algebra.linearMap, AtPrime, Finite, FormallyUnramified, Function, Function.Surjective, Ideal.smul_top_eq_map, IsLiesOverAlgebra, LinearMap, LinearMap.range_eq_top, Localization, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq, Localization.finite_of_primesOver_eq_singleton, Module, Module.Finite.fg_top, Residue, Submodule, Submodule.le_of_le_smul_of_le_jacobson_bot
-/
lemma localRingHom_surjective_of_primesOver_eq_singleton
    [Module.Finite R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    Function.Surjective (localRingHom p q (algebraMap R S) (q.over_def p)) := by
  have := Localization.finite_of_primesOver_eq_singleton hq
  rw [← Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
  change Function.Surjective (Algebra.linearMap _ _)
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map]; rw [Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [← ResidueField.algebraMap_eq]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime q)]; rw [ResidueField.algebraMap_eq]; rw [← sub_eq_zero]; rw [← map_sub]; rw [residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  refine sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ha)

omit hq in
/--
lemma `exists_awayMap_injective_of_localRingHom_injective` / 引理 `exists_awayMap_injective_of_localRingHom_injective`

English:
lemma exists_awayMap_injective_of_localRingHom_injective
  proof: by
  classical
  obtain ⟨s, hs⟩ := hRS
  have (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply H
    simp [localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
      show algebraMap R S _ = 0 from hs.le (Ideal.subset_span x.2)]
  choose m hm using fun x => (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
  have H : RingHom.ker (algebraMap R S) <= RingHom.ker
      (algebraMap R (Localization.Away (∏ i, m i).1)) := by
    rw [← hs]; rw [Ideal.span_le]
    intro x hxs
    refine (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mpr ⟨⟨_, 1, rfl⟩, ?_⟩
    simp only [pow_one]
    rw [Fintype.prod_eq_mul_prod_compl ⟨x]; rw [hxs⟩]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_left_comm]; rw [hm]; rw [mul_zero]
  refine ⟨_, (∏ i : s, m i).2, ?_⟩
  rintro r' ⟨s, e⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, _, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r') x
  simp only [awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  simp only [← map_pow, ← map_mul] at hn
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mp (H hn)
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, k + n, rfl⟩, ?_⟩
  dsimp only at hk ⊢
  rw [pow_add]; rw [mul_assoc]; rw [e]; rw [mul_pow]; rw [← e]; rw [mul_assoc]; rw [mul_left_comm]; rw [hk]; rw [mul_zero]

中文:
引理 存在_awayMap_injective_of_localRingHom_injective
  证明: by
  classical
  obtain ⟨s, hs⟩ := hRS
  have (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply H
    simp [localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
      show algebraMap R S _ = 0 from hs.le (Ideal.subset_span x.2)]
  choose m hm using fun x => (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
  have H : RingHom.ker (algebraMap R S) <= RingHom.ker
      (algebraMap R (Localization.Away (∏ i, m i).1)) := by
    rw [← hs]; rw [Ideal.span_le]
    intro x hxs
    refine (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mpr ⟨⟨_, 1, rfl⟩, ?_⟩
    simp only [pow_one]
    rw [Fintype.prod_eq_mul_prod_compl ⟨x]; rw [hxs⟩]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_left_comm]; rw [hm]; rw [mul_zero]
  refine ⟨_, (∏ i : s, m i).2, ?_⟩
  rintro r' ⟨s, e⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, _, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r') x
  simp only [awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  simp only [← map_pow, ← map_mul] at hn
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mp (H hn)
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, k + n, rfl⟩, ?_⟩
  dsimp only at hk ⊢
  rw [pow_add]; rw [mul_assoc]; rw [e]; rw [mul_pow]; rw [← e]; rw [mul_assoc]; rw [mul_left_comm]; rw [hk]; rw [mul_zero]

Depends on / 依赖: AtPrime, FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, Ideal.span_le, Ideal.subset_span, IsLocalization, IsLocalization.ma, IsLocalization.map_eq_zero_iff, Localization, Localization.AtPrime, Localization.Away, RingHom, RingHom.ker, algebraMap, algebraMap_eq_zero_iff, classical, hs.le, localRingHom_to_map, map_eq_zero_iff, p.primeCompl
-/
lemma exists_awayMap_injective_of_localRingHom_injective
    (hRS : (RingHom.ker (algebraMap R S)).FG) [q.LiesOver p]
    (H : Function.Injective (localRingHom p q (algebraMap R S) (q.over_def p))) :
    exists r ∉ p, forall r', r ∣ r' -> Function.Injective (awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := hRS
  have (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply H
    simp [localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
      show algebraMap R S _ = 0 from hs.le (Ideal.subset_span x.2)]
  choose m hm using fun x => (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
  have H : RingHom.ker (algebraMap R S) <= RingHom.ker
      (algebraMap R (Localization.Away (∏ i, m i).1)) := by
    rw [← hs]; rw [Ideal.span_le]
    intro x hxs
    refine (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mpr ⟨⟨_, 1, rfl⟩, ?_⟩
    simp only [pow_one]
    rw [Fintype.prod_eq_mul_prod_compl ⟨x]; rw [hxs⟩]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_left_comm]; rw [hm]; rw [mul_zero]
  refine ⟨_, (∏ i : s, m i).2, ?_⟩
  rintro r' ⟨s, e⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, _, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r') x
  simp only [awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  simp only [← map_pow, ← map_mul] at hn
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mp (H hn)
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, k + n, rfl⟩, ?_⟩
  dsimp only at hk ⊢
  rw [pow_add]; rw [mul_assoc]; rw [e]; rw [mul_pow]; rw [← e]; rw [mul_assoc]; rw [mul_left_comm]; rw [hk]; rw [mul_zero]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_awayMap_bijective_of_localRingHom_bijective` / 引理 `exists_awayMap_bijective_of_localRingHom_bijective`

English:
lemma exists_awayMap_bijective_of_localRingHom_bijective
  proof: by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : exists a, exists b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
      IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  obtain ⟨r, hrp, hr⟩ := Localization.exists_awayMap_injective_of_localRingHom_injective hRS H.1
  refine ⟨r * ∏ i in s, b i, mul_mem (s := p.primeCompl) hrp (prod_mem fun _ _ => hbp _), ?_⟩
  refine fun r' hr' => ⟨hr _ (.trans ⟨_, rfl⟩ hr'), ?_⟩
  have H : (IsScalarTower.toAlgHom R S _).range <= (awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top]; rw [Subalgebra.map_le]; rw [← hs]; rw [Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * r * (∏ i in s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr']; rw [← Finset.prod_erase_mul s b hxs]; rw [map_mul]; rw [map_mul]; rw [map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Away.invSelf, Localization.mk_eq_mk', awayMap, IsLocalization.Away.map,
    IsLocalization.map_mk', ← Algebra.smul_def, IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

中文:
引理 存在_awayMap_bijective_of_localRingHom_bijective
  证明: by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : exists a, exists b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
      IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  obtain ⟨r, hrp, hr⟩ := Localization.exists_awayMap_injective_of_localRingHom_injective hRS H.1
  refine ⟨r * ∏ i in s, b i, mul_mem (s := p.primeCompl) hrp (prod_mem fun _ _ => hbp _), ?_⟩
  refine fun r' hr' => ⟨hr _ (.trans ⟨_, rfl⟩ hr'), ?_⟩
  have H : (IsScalarTower.toAlgHom R S _).range <= (awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top]; rw [Subalgebra.map_le]; rw [← hs]; rw [Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * r * (∏ i in s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr']; rw [← Finset.prod_erase_mul s b hxs]; rw [map_mul]; rw [map_mul]; rw [map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Away.invSelf, Localization.mk_eq_mk', awayMap, IsLocalization.Away.map,
    IsLocalization.map_mk', ← Algebra.smul_def, IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

Depends on / 依赖: Algebra, Algebra.FiniteType.out, FiniteType, Ideal.mem_primeCompl_iff, IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.mk, Prod.exists, Subtype, Subtype.exists, _eq_iff_eq_mul, _surjective, algebraMap, classical, eq_iff_exists, exists.mp, exists_prop, localRingHom_mk, map_mul, mem_primeCompl_iff
-/
lemma exists_awayMap_bijective_of_localRingHom_bijective
    [Module.Finite R S] [q.LiesOver p] (hRS : (RingHom.ker (algebraMap R S)).FG)
    (H : Function.Bijective (localRingHom p q (algebraMap R S) (q.over_def p))) :
    exists r ∉ p, forall r', r ∣ r' -> Function.Bijective (awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : exists a, exists b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
      IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  obtain ⟨r, hrp, hr⟩ := Localization.exists_awayMap_injective_of_localRingHom_injective hRS H.1
  refine ⟨r * ∏ i in s, b i, mul_mem (s := p.primeCompl) hrp (prod_mem fun _ _ => hbp _), ?_⟩
  refine fun r' hr' => ⟨hr _ (.trans ⟨_, rfl⟩ hr'), ?_⟩
  have H : (IsScalarTower.toAlgHom R S _).range <= (awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top]; rw [Subalgebra.map_le]; rw [← hs]; rw [Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * r * (∏ i in s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr']; rw [← Finset.prod_erase_mul s b hxs]; rw [map_mul]; rw [map_mul]; rw [map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Away.invSelf, Localization.mk_eq_mk', awayMap, IsLocalization.Away.map,
    IsLocalization.map_mk', ← Algebra.smul_def, IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

/--
lemma `exists_awayMap_bijective_of_residueField_surjective` / 引理 `exists_awayMap_bijective_of_residueField_surjective`

English:
lemma exists_awayMap_bijective_of_residueField_surjective
  proof: exists_awayMap_bijective_of_localRingHom_bijective hq (by simpa using! Submodule.fg_bot)
    ⟨localRingHom_injective_of_primesOver_eq_singleton hq,
      localRingHom_surjective_of_primesOver_eq_singleton hq H⟩

中文:
引理 存在_awayMap_bijective_of_residueField_surjective
  证明: exists_awayMap_bijective_of_localRingHom_bijective hq (by simpa using! Submodule.fg_bot)
    ⟨localRingHom_injective_of_primesOver_eq_singleton hq,
      localRingHom_surjective_of_primesOver_eq_singleton hq H⟩

Depends on / 依赖: Submodule, Submodule.fg_bot, exists_awayMap_bijective_of_localRingHom_bijective, fg_bot, localRingHom_injective_of_primesOver_eq_singleton, localRingHom_surjective_of_primesOver_eq_singleton
-/
lemma exists_awayMap_bijective_of_residueField_surjective
    [Module.Finite R S] [FaithfulSMul R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    exists r ∉ p, forall r', r ∣ r' -> Function.Bijective (awayMap (algebraMap R S) r') :=
  exists_awayMap_bijective_of_localRingHom_bijective hq (by simpa using! Submodule.fg_bot)
    ⟨localRingHom_injective_of_primesOver_eq_singleton hq,
      localRingHom_surjective_of_primesOver_eq_singleton hq H⟩

end Localization

end UniquePrimeOver
