/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `Ideal.cotangentEquivIdeal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

@[expose] public section


namespace Ideal

-- Universes need to be explicit to avoid bad universe levels in `quotCotangent`
universe u v w

variable {R : Type u} {S : Type v} {S' : Type w} [CommRing R] [CommSemiring S] [Algebra S R]
variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

/--
Definition of `Cotangent` / `Cotangent` 的定义

English:
definition Cotangent
  signature: : Type _
  body: I ⧸ (I • ⊤ : Submodule R I)
deriving Inhabited

中文:
定义 余切
  签名: : 类型 _
  定义体: I ⧸ (I • ⊤ : Submodule R I)
deriving Inhabited

Depends on / 依赖: Submodule
-/
def Cotangent : Type _ := I ⧸ (I • ⊤ : Submodule R I)
deriving Inhabited

-- The `SMul` instance exists to avoid nsmul and zsmul diamonds.
deriving instance SMul S, AddCommGroup, Module (R ⧸ I), Module S, IsScalarTower S S',
  IsScalarTower R (R ⧸ I) for Cotangent I

variable [IsNoetherian R I] in
deriving instance IsNoetherian R for Cotangent I

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps! -isSimp apply]
/--
Definition of `toCotangent` / `toCotangent` 的定义

English:
definition toCotangent
  signature: : I ->ₗ[R] I.Cotangent
  body: Submodule.mkQ _

中文:
定义 toCotangent
  签名: : I ->ₗ[R] I.余切
  定义体: Submodule.mkQ _

Depends on / 依赖: Submodule, Submodule.mkQ
-/
def toCotangent : I ->ₗ[R] I.Cotangent := Submodule.mkQ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_toCotangent_ker` / 定理 `map_toCotangent_ker`

English:
theorem map_toCotangent_ker
  statement: (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2
  proof: by
  rw [Ideal.toCotangent]; rw [Submodule.ker_mkQ]; rw [pow_two]; rw [Submodule.map_smul'' I ⊤ (Submodule.subtype I)]; rw [smul_eq_mul]; rw [Submodule.map_subtype_top]

中文:
定理 map_toCotangent_ker
  结论: (线性映射.ker I.toCotangent).map I.subtype = I ^ 2
  证明: by
  rw [Ideal.toCotangent]; rw [Submodule.ker_mkQ]; rw [pow_two]; rw [Submodule.map_smul'' I ⊤ (Submodule.subtype I)]; rw [smul_eq_mul]; rw [Submodule.map_subtype_top]

Depends on / 依赖: Ideal.toCotangent, Submodule, Submodule.ker_mkQ, Submodule.map_smul, Submodule.map_subtype_top, Submodule.subtype, ker_mkQ, map_smul, map_subtype_top, pow_two, smul_eq_mul, subtype, toCotangent
-/
theorem map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2 := by
  rw [Ideal.toCotangent]; rw [Submodule.ker_mkQ]; rw [pow_two]; rw [Submodule.map_smul'' I ⊤ (Submodule.subtype I)]; rw [smul_eq_mul]; rw [Submodule.map_subtype_top]

/--
theorem `mem_toCotangent_ker` / 定理 `mem_toCotangent_ker`

English:
theorem mem_toCotangent_ker
  given: {x : I}
  statement: x in LinearMap.ker I.toCotangent ↔ (x : R) in I ^ 2
  proof: by
  rw [← I.map_toCotangent_ker]
  simp

中文:
定理 mem_toCotangent_ker
  条件: {x : I}
  结论: x in 线性映射.ker I.toCotangent ↔ (x : R) in I ^ 2
  证明: by
  rw [← I.map_toCotangent_ker]
  simp

Depends on / 依赖: I.map_toCotangent_ker, map_toCotangent_ker
-/
theorem mem_toCotangent_ker {x : I} : x in LinearMap.ker I.toCotangent ↔ (x : R) in I ^ 2 := by
  rw [← I.map_toCotangent_ker]
  simp

/--
theorem `toCotangent_eq` / 定理 `toCotangent_eq`

English:
theorem toCotangent_eq
  given: {x y : I}
  statement: I.toCotangent x = I.toCotangent y ↔ (x - y : R) in I ^ 2
  proof: by
  rw [← sub_eq_zero]
  exact I.mem_toCotangent_ker

中文:
定理 toCotangent_eq
  条件: {x y : I}
  结论: I.toCotangent x = I.toCotangent y ↔ (x - y : R) in I ^ 2
  证明: by
  rw [← sub_eq_zero]
  exact I.mem_toCotangent_ker

Depends on / 依赖: I.mem_toCotangent_ker, mem_toCotangent_ker, sub_eq_zero
-/
theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) in I ^ 2 := by
  rw [← sub_eq_zero]
  exact I.mem_toCotangent_ker

/--
theorem `toCotangent_eq_zero` / 定理 `toCotangent_eq_zero`

English:
theorem toCotangent_eq_zero
  given: (x : I)
  statement: I.toCotangent x = 0 ↔ (x : R) in I ^ 2
  proof: I.mem_toCotangent_ker

中文:
定理 toCotangent_eq_zero
  条件: (x : I)
  结论: I.toCotangent x = 0 ↔ (x : R) in I ^ 2
  证明: I.mem_toCotangent_ker

Depends on / 依赖: I.mem_toCotangent_ker, mem_toCotangent_ker
-/
theorem toCotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) in I ^ 2 := I.mem_toCotangent_ker

/--
theorem `toCotangent_surjective` / 定理 `toCotangent_surjective`

English:
theorem toCotangent_surjective
  statement: Function.Surjective I.toCotangent
  proof: Submodule.mkQ_surjective _

中文:
定理 toCotangent_surjective
  结论: 函数.满射 I.toCotangent
  证明: Submodule.mkQ_surjective _

Depends on / 依赖: Submodule, Submodule.mkQ_surjective, mkQ_surjective
-/
theorem toCotangent_surjective : Function.Surjective I.toCotangent := Submodule.mkQ_surjective _

/--
theorem `toCotangent_range` / 定理 `toCotangent_range`

English:
theorem toCotangent_range
  statement: LinearMap.range I.toCotangent = ⊤
  proof: Submodule.range_mkQ _

中文:
定理 toCotangent_range
  结论: 线性映射.range I.toCotangent = ⊤
  证明: Submodule.range_mkQ _

Depends on / 依赖: Submodule, Submodule.range_mkQ, range_mkQ
-/
theorem toCotangent_range : LinearMap.range I.toCotangent = ⊤ := Submodule.range_mkQ _

/--
theorem `cotangent_subsingleton_iff` / 定理 `cotangent_subsingleton_iff`

English:
theorem cotangent_subsingleton_iff
  statement: Subsingleton I.Cotangent ↔ IsIdempotentElem I
  proof: by
  constructor
  · intro H
    refine (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) ?_)
    exact fun x hx => (I.toCotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  · exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
I.toCotangent_eq.mpr ((p

中文:
定理 cotangent_subsingleton_iff
  结论: 子单例 I.余切 ↔ IsIdempotentElem I
  证明: by
  constructor
  · intro H
    refine (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) ?_)
    exact fun x hx => (I.toCotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  · exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
I.toCotangent_eq.mpr ((p

Depends on / 依赖: I.sub_mem, I.toCotangent_eq.mpr, I.toCotangent_eq_zero, Ideal.pow_le_self, Quotient, Quotient.inductionOn, Subsingleton, Subsingleton.elim, le_antisymm, pow_le_self, pow_two, sub_mem, symm.trans, toCotangent_eq, toCotangent_eq_zero, two_ne_zero, x.prop, y.prop
-/
theorem cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I := by
  constructor
  · intro H
    refine (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) ?_)
    exact fun x hx => (I.toCotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  · exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
I.toCotangent_eq.mpr ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩

/--
Definition of `cotangentToQuotientSquare` / `cotangentToQuotientSquare` 的定义

English:
definition cotangentToQuotientSquare
  signature: : I.Cotangent ->ₗ[R] R ⧸ I ^ 2
  body: Submodule.mapQ (I • ⊤) (I ^ 2) I.subtype
    (by
      rw [← Submodule.map_le_iff_le_comap]; rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [Submodule.range_subtype]; rw [smul_eq_mul]; rw [pow_two])

中文:
定义 cotangentToQuotientSquare
  签名: : I.余切 ->ₗ[R] R ⧸ I ^ 2
  定义体: Submodule.mapQ (I • ⊤) (I ^ 2) I.subtype
    (by
      rw [← Submodule.map_le_iff_le_comap]; rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [Submodule.range_subtype]; rw [smul_eq_mul]; rw [pow_two])

Depends on / 依赖: I.subtype, Submodule, Submodule.mapQ, Submodule.map_le_iff_le_comap, Submodule.map_smul, Submodule.map_top, Submodule.range_subtype, map_le_iff_le_comap, map_smul, map_top, pow_two, range_subtype, smul_eq_mul, subtype
-/
def cotangentToQuotientSquare : I.Cotangent ->ₗ[R] R ⧸ I ^ 2 :=
  Submodule.mapQ (I • ⊤) (I ^ 2) I.subtype
    (by
      rw [← Submodule.map_le_iff_le_comap]; rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [Submodule.range_subtype]; rw [smul_eq_mul]; rw [pow_two])

/--
theorem `to_quotient_square_comp_toCotangent` / 定理 `to_quotient_square_comp_toCotangent`

English:
theorem to_quotient_square_comp_toCotangent
  proof: LinearMap.ext fun _ => rfl

@[simp]

中文:
定理 to_quotient_square_comp_toCotangent
  证明: LinearMap.ext fun _ => rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem to_quotient_square_comp_toCotangent :
    I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkQ.comp (Submodule.subtype I) :=
  LinearMap.ext fun _ => rfl

@[simp]
/--
theorem `toCotangent_to_quotient_square` / 定理 `toCotangent_to_quotient_square`

English:
theorem toCotangent_to_quotient_square
  given: (x : I)
  proof: rfl

中文:
定理 toCotangent_to_quotient_square
  条件: (x : I)
  证明: rfl
-/
theorem toCotangent_to_quotient_square (x : I) :
    I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x := rfl

/--
lemma `cotangentToQuotientSquare_injective` / 引理 `cotangentToQuotientSquare_injective`

English:
lemma cotangentToQuotientSquare_injective
  statement: Function.Injective I.cotangentToQuotientSquare
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [toCotangent_to_quotient_square] at hx
  rwa [Ideal.toCotangent_eq_zero, ← Submodule.Quotient.mk_eq_zero (I ^ 2)]

中文:
引理 cotangentToQuotientSquare_injective
  结论: 函数.单射 I.cotangentToQuotientSquare
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [toCotangent_to_quotient_square] at hx
  rwa [Ideal.toCotangent_eq_zero, ← Submodule.Quotient.mk_eq_zero (I ^ 2)]

Depends on / 依赖: I.toCotangent_surjective, Ideal.toCotangent_eq_zero, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, injective_iff_map_eq_zero, mk_eq_zero, toCotangent_eq_zero, toCotangent_surjective, toCotangent_to_quotient_square
-/
lemma cotangentToQuotientSquare_injective : Function.Injective I.cotangentToQuotientSquare := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [toCotangent_to_quotient_square] at hx
  rwa [Ideal.toCotangent_eq_zero, ← Submodule.Quotient.mk_eq_zero (I ^ 2)]

/--
lemma `Cotangent.smul_eq_zero_of_mem` / 引理 `Cotangent.smul_eq_zero_of_mem`

English:
lemma Cotangent.smul_eq_zero_of_mem
  statement: {I : Ideal R}
  proof: by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul]; rw [Ideal.toCotangent_eq_zero]; rw [pow_two]
  exact Ideal.mul_mem_mul hx m.2

中文:
引理 余切.smul_eq_zero_of_mem
  结论: {I : 理想 R}
  证明: by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul]; rw [Ideal.toCotangent_eq_zero]; rw [pow_two]
  exact Ideal.mul_mem_mul hx m.2
-/
lemma Cotangent.smul_eq_zero_of_mem {I : Ideal R}
    {x} (hx : x in I) (m : I.Cotangent) : x • m = 0 := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul]; rw [Ideal.toCotangent_eq_zero]; rw [pow_two]
  exact Ideal.mul_mem_mul hx m.2

/--
lemma `isTorsionBySet_cotangent` / 引理 `isTorsionBySet_cotangent`

English:
lemma isTorsionBySet_cotangent
  proof: fun m x => m.smul_eq_zero_of_mem x.2

中文:
引理 isTorsionBySet_cotangent
  证明: fun m x => m.smul_eq_zero_of_mem x.2

Depends on / 依赖: m.smul_eq_zero_of_mem, smul_eq_zero_of_mem
-/
lemma isTorsionBySet_cotangent :
    Module.IsTorsionBySet R I.Cotangent I :=
  fun m x => m.smul_eq_zero_of_mem x.2

/--
Definition of `cotangentIdeal` / `cotangentIdeal` 的定义

English:
definition cotangentIdeal
  signature: (I : Ideal R)
  body: Submodule.map (Quotient.mk (I ^ 2) |>.toSemilinearMap) I

中文:
定义 cotangentIdeal
  签名: (I : 理想 R)
  定义体: Submodule.map (Quotient.mk (I ^ 2) |>.toSemilinearMap) I

Depends on / 依赖: Quotient, Quotient.mk, Submodule, Submodule.map, toSemilinearMap
-/
def cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2) :=
  Submodule.map (Quotient.mk (I ^ 2) |>.toSemilinearMap) I

/--
theorem `cotangentIdeal_square` / 定理 `cotangentIdeal_square`

English:
theorem cotangentIdeal_square
  given: (I : Ideal R)
  statement: I.cotangentIdeal ^ 2 = ⊥
  proof: by
  rw [eq_bot_iff]; rw [pow_two I.cotangentIdeal]; rw [← smul_eq_mul]
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero]; rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact

中文:
定理 cotangentIdeal_square
  条件: (I : 理想 R)
  结论: I.cotangentIdeal ^ 2 = ⊥
  证明: by
  rw [eq_bot_iff]; rw [pow_two I.cotangentIdeal]; rw [← smul_eq_mul]
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero]; rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact

Depends on / 依赖: I.cotangentIdeal, Ideal.mul_mem_mul, Quotient, Submodule, Submodule.Quotient.eq, Submodule.smul_induction_on, add_mem, cotangentIdeal, eq_bot_iff, mul_mem_mul, pow_two, smul_eq_mul, smul_induction_on, sub_zero
-/
theorem cotangentIdeal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥ := by
  rw [eq_bot_iff]; rw [pow_two I.cotangentIdeal]; rw [← smul_eq_mul]
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero]; rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact add_mem hx hy

/--
lemma `mk_mem_cotangentIdeal` / 引理 `mk_mem_cotangentIdeal`

English:
lemma mk_mem_cotangentIdeal
  given: {I : Ideal R} {x : R}
  proof: by
  refine ⟨fun ⟨y, hy, e⟩ => ?_, fun h => ⟨x, h, rfl⟩⟩
  simpa using sub_mem hy (Ideal.pow_le_self two_ne_zero
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp e))

中文:
引理 mk_mem_cotangentIdeal
  条件: {I : 理想 R} {x : R}
  证明: by
  refine ⟨fun ⟨y, hy, e⟩ => ?_, fun h => ⟨x, h, rfl⟩⟩
  simpa using sub_mem hy (Ideal.pow_le_self two_ne_zero
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp e))

Depends on / 依赖: Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.pow_le_self, Quotient, mk_eq_mk_iff_sub_mem, pow_le_self, sub_mem, two_ne_zero
-/
lemma mk_mem_cotangentIdeal {I : Ideal R} {x : R} :
    Quotient.mk (I ^ 2) x in I.cotangentIdeal ↔ x in I := by
  refine ⟨fun ⟨y, hy, e⟩ => ?_, fun h => ⟨x, h, rfl⟩⟩
  simpa using sub_mem hy (Ideal.pow_le_self two_ne_zero
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp e))

/--
lemma `comap_cotangentIdeal` / 引理 `comap_cotangentIdeal`

English:
lemma comap_cotangentIdeal
  given: (I : Ideal R)
  proof: Ideal.ext fun _ => mk_mem_cotangentIdeal

中文:
引理 comap_cotangentIdeal
  条件: (I : 理想 R)
  证明: Ideal.ext fun _ => mk_mem_cotangentIdeal

Depends on / 依赖: Ideal.ext, mk_mem_cotangentIdeal
-/
lemma comap_cotangentIdeal (I : Ideal R) :
    I.cotangentIdeal.comap (Quotient.mk (I ^ 2)) = I :=
  Ideal.ext fun _ => mk_mem_cotangentIdeal

/--
theorem `range_cotangentToQuotientSquare` / 定理 `range_cotangentToQuotientSquare`

English:
theorem range_cotangentToQuotientSquare
  proof: by
  trans LinearMap.range (I.cotangentToQuotientSquare.comp I.toCotangent)
  · rw [LinearMap.range_comp, I.toCotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_toCotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl

中文:
定理 range_cotangentToQuotientSquare
  证明: by
  trans LinearMap.range (I.cotangentToQuotientSquare.comp I.toCotangent)
  · rw [LinearMap.range_comp, I.toCotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_toCotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl

Depends on / 依赖: I.cotangentToQuotientSquare.comp, I.range_subtype, I.toCotangent, I.toCotangent_range, LinearMap, LinearMap.range, LinearMap.range_comp, Submodule, Submodule.map_top, cotangentToQuotientSquare, map_top, range_comp, range_subtype, toCotangent, toCotangent_range, to_quotient_square_comp_toCotangent
-/
theorem range_cotangentToQuotientSquare :
    LinearMap.range I.cotangentToQuotientSquare = I.cotangentIdeal.restrictScalars R := by
  trans LinearMap.range (I.cotangentToQuotientSquare.comp I.toCotangent)
  · rw [LinearMap.range_comp, I.toCotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_toCotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl

/--
Definition of `cotangentEquivIdeal` / `cotangentEquivIdeal` 的定义

English:
definition cotangentEquivIdeal
  signature: : I.Cotangent ≃ₗ[R] I.cotangentIdeal
  body: by
  refine
  { LinearMap.codRestrict (I.cotangentIdeal.restrictScalars R) I.cotangentToQuotientSquare
      fun x => by rw [← range_cotangentToQuotientSquare]; exact LinearMap.mem_range_self _ _,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    o

中文:
定义 cotangentEquivIdeal
  签名: : I.余切 ≃ₗ[R] I.cotangentIdeal
  定义体: by
  refine
  { LinearMap.codRestrict (I.cotangentIdeal.restrictScalars R) I.cotangentToQuotientSquare
      fun x => by rw [← range_cotangentToQuotientSquare]; exact LinearMap.mem_range_self _ _,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    o

Depends on / 依赖: Equiv.ofBijective, I.cotangentIdeal.restrictScalars, I.cotangentToQuotientSquare, I.toCotangent_eq, I.toCotangent_surjective, LinearMap, LinearMap.codRestrict, LinearMap.mem_range_self, Quotient, Submodule, Submodule.Quotient.eq, Submodule.mkQ_apply, Subtype, Subtype.val, codRestrict, congr_arg, cotangentIdeal, cotangentToQuotientSquare, mem_range_self, mkQ_apply
-/
noncomputable def cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal := by
  refine
  { LinearMap.codRestrict (I.cotangentIdeal.restrictScalars R) I.cotangentToQuotientSquare
      fun x => by rw [← range_cotangentToQuotientSquare]; exact LinearMap.mem_range_self _ _,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
    rw [I.toCotangent_eq]
    dsimp only [toCotangent_to_quotient_square, Submodule.mkQ_apply] at e
    rwa [Submodule.Quotient.eq] at e
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨I.toCotangent ⟨x, hx⟩, Subtype.ext rfl⟩

@[simp]
/--
theorem `cotangentEquivIdeal_apply` / 定理 `cotangentEquivIdeal_apply`

English:
theorem cotangentEquivIdeal_apply
  given: (x : I.Cotangent)
  proof: rfl

中文:
定理 cotangentEquivIdeal_apply
  条件: (x : I.余切)
  证明: rfl
-/
theorem cotangentEquivIdeal_apply (x : I.Cotangent) :
    ↑(I.cotangentEquivIdeal x) = I.cotangentToQuotientSquare x := rfl

/--
theorem `cotangentEquivIdeal_symm_apply` / 定理 `cotangentEquivIdeal_symm_apply`

English:
theorem cotangentEquivIdeal_symm_apply
  given: (x : R) (hx : x in I)
  proof: by
  simp [I.cotangentEquivIdeal.symm_apply_eq, Subtype.ext_iff]

中文:
定理 cotangentEquivIdeal_symm_apply
  条件: (x : R) (hx : x in I)
  证明: by
  simp [I.cotangentEquivIdeal.symm_apply_eq, Subtype.ext_iff]

Depends on / 依赖: I.cotangentEquivIdeal.symm_apply_eq, Subtype, Subtype.ext_iff, cotangentEquivIdeal, ext_iff, symm_apply_eq
-/
theorem cotangentEquivIdeal_symm_apply (x : R) (hx : x in I) :
    I.cotangentEquivIdeal.symm ⟨(I ^ 2).mkQ x, Submodule.mem_map_of_mem hx⟩ =
      I.toCotangent ⟨x, hx⟩ := by
  simp [I.cotangentEquivIdeal.symm_apply_eq, Subtype.ext_iff]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `_root_.AlgHom.kerSquareLift` / `_root_.AlgHom.kerSquareLift` 的定义

English:
definition _root_.AlgHom.kerSquareLift
  signature: (f : A ->ₐ[R] B)
  body: by
  refine { Ideal.Quotient.lift (RingHom.ker f.toRingHom ^ 2) f.toRingHom ?_ with commutes' := ?_ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r
    rw [IsScalarTower.algebraMap_apply R A]; rw [RingHom.toFun_eq_coe]; rw [Ideal.Quotient.algebraMap_eq]; rw [Ideal.Quotient.lift_

中文:
定义 _root_.代数态射.kerSquareLift
  签名: (f : A ->ₐ[R] B)
  定义体: by
  refine { Ideal.Quotient.lift (RingHom.ker f.toRingHom ^ 2) f.toRingHom ?_ with commutes' := ?_ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r
    rw [IsScalarTower.algebraMap_apply R A]; rw [RingHom.toFun_eq_coe]; rw [Ideal.Quotient.algebraMap_eq]; rw [Ideal.Quotient.lift_

Depends on / 依赖: Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift, Ideal.Quotient.lift_mk, Ideal.pow_le_self, IsScalarTower, IsScalarTower.algebraMap_apply, Quotient, RingHom, RingHom.ker, RingHom.toFun_eq_coe, algebraMap_apply, algebraMap_eq, commutes, f.map_algebraMap, f.toRingHom, lift_mk, map_algebraMap, pow_le_self, toFun_eq_coe, toRingHom
-/
def _root_.AlgHom.kerSquareLift (f : A ->ₐ[R] B) : A ⧸ RingHom.ker f.toRingHom ^ 2 ->ₐ[R] B := by
  refine { Ideal.Quotient.lift (RingHom.ker f.toRingHom ^ 2) f.toRingHom ?_ with commutes' := ?_ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r
    rw [IsScalarTower.algebraMap_apply R A]; rw [RingHom.toFun_eq_coe]; rw [Ideal.Quotient.algebraMap_eq]; rw [Ideal.Quotient.lift_mk]
    exact f.map_algebraMap r

-- Can't be `simp`, because `RingHom.ker f.toRingHom` in the definition of `AlgHom.kerSquareLift`
-- is not simp NF. Will be fixed by removing `RingHomClass` in the definition of `RingHom.ker`.
-- (#25138)
/--
lemma `_root_.AlgHom.kerSquareLift_mk` / 引理 `_root_.AlgHom.kerSquareLift_mk`

English:
lemma _root_.AlgHom.kerSquareLift_mk
  given: (f : A ->ₐ[R] B) (x : A)
  statement: f.kerSquareLift x = f x
  proof: rfl

中文:
引理 _root_.代数态射.kerSquareLift_mk
  条件: (f : A ->ₐ[R] B) (x : A)
  结论: f.kerSquareLift x = f x
  证明: rfl
-/
lemma _root_.AlgHom.kerSquareLift_mk (f : A ->ₐ[R] B) (x : A) : f.kerSquareLift x = f x :=
  rfl

/--
theorem `_root_.AlgHom.ker_kerSquareLift` / 定理 `_root_.AlgHom.ker_kerSquareLift`

English:
theorem _root_.AlgHom.ker_kerSquareLift
  given: (f : A ->ₐ[R] B)
  proof: by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx

中文:
定理 _root_.代数态射.ker_kerSquareLift
  条件: (f : A ->ₐ[R] B)
  证明: by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, le_antisymm, mk_surjective
-/
theorem _root_.AlgHom.ker_kerSquareLift (f : A ->ₐ[R] B) :
    RingHom.ker f.kerSquareLift.toRingHom = (RingHom.ker f.toRingHom).cotangentIdeal := by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx

/--
Instance `Algebra.kerSquareLift` / 实例 `Algebra.kerSquareLift`

English:
instance Algebra.kerSquareLift
  signature: : Algebra (R ⧸ (RingHom.ker (algebraMap R A) ^ 2)) A
  body: (Algebra.ofId R A).kerSquareLift.toAlgebra

中文:
实例 代数.kerSquareLift
  签名: : 代数 (R ⧸ (环态射.ker (algebraMap R A) ^ 2)) A
  定义体: (Algebra.ofId R A).kerSquareLift.toAlgebra

Depends on / 依赖: Algebra, Algebra.ofId, kerSquareLift, kerSquareLift.toAlgebra, toAlgebra
-/
instance Algebra.kerSquareLift : Algebra (R ⧸ (RingHom.ker (algebraMap R A) ^ 2)) A :=
  (Algebra.ofId R A).kerSquareLift.toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: A B] [IsScalarTower R A B] :
  body: IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R A B).kerSquareLift.comp_algebraMap.symm

中文:
实例 [代数
  签名: A B] [标量塔 R A B] :
  定义体: IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R A B).kerSquareLift.comp_algebraMap.symm

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, IsScalarTower.toAlgHom, comp_algebraMap, kerSquareLift, kerSquareLift.comp_algebraMap.symm, of_algebraMap_eq, toAlgHom
-/
instance [Algebra A B] [IsScalarTower R A B] :
    IsScalarTower R (A ⧸ (RingHom.ker (algebraMap A B) ^ 2)) B :=
  IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R A B).kerSquareLift.comp_algebraMap.symm

/--
Definition of `quotCotangent` / `quotCotangent` 的定义

English:
definition quotCotangent
  signature: : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I
  body: by
  refine (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)

中文:
定义 quotCotangent
  签名: : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I
  定义体: by
  refine (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)

Depends on / 依赖: DoubleQuot, DoubleQuot.quotQuotEquivQuotSup, Ideal.map_eq_submodule_map, Ideal.pow_le_self, Ideal.quotEquivOfEq, map_eq_submodule_map, pow_le_self, quotEquivOfEq, quotQuotEquivQuotSup, sup_eq_right, sup_eq_right.mpr, two_ne_zero
-/
def quotCotangent : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I := by
  refine (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapCotangent` / `mapCotangent` 的定义

English:
definition mapCotangent
  signature: (I₁ : Ideal A) (I₂ : Ideal B) (f : A ->ₐ[R] B) (h : I₁ <= I₂.comap f)
  body: by
  refine Submodule.mapQ ((I₁ • ⊤ : Submodule A I₁).restrictScalars R)
    ((I₂ • ⊤ : Submodule B I₂).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := I₁.restrictScalars R) (q := I₂.restrictScalars R) h
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule

中文:
定义 mapCotangent
  签名: (I₁ : 理想 A) (I₂ : 理想 B) (f : A ->ₐ[R] B) (h : I₁ <= I₂.comap f)
  定义体: by
  refine Submodule.mapQ ((I₁ • ⊤ : Submodule A I₁).restrictScalars R)
    ((I₂ • ⊤ : Submodule B I₂).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := I₁.restrictScalars R) (q := I₂.restrictScalars R) h
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule

Depends on / 依赖: SetLike, SetLike.mk_smul_mk, Submodule, Submodule.mapQ, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.smul_induction_on, Submodule.smul_mem_smul, add_mem, convert, f.toLinearMap.restrict, mem_comap, mk_smul_mk, restrict, restrictScalars, restrictScalars_mem, smul_eq_mul, smul_induction_on, smul_mem_smul, toLinearMap
-/
def mapCotangent (I₁ : Ideal A) (I₂ : Ideal B) (f : A ->ₐ[R] B) (h : I₁ <= I₂.comap f) :
    I₁.Cotangent ->ₗ[R] I₂.Cotangent := by
  refine Submodule.mapQ ((I₁ • ⊤ : Submodule A I₁).restrictScalars R)
    ((I₂ • ⊤ : Submodule B I₂).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := I₁.restrictScalars R) (q := I₂.restrictScalars R) h
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ (fun _ _ => add_mem)
    rintro a ha ⟨b, hb⟩ -
    simp only [SetLike.mk_smul_mk, smul_eq_mul, Submodule.mem_comap, Submodule.restrictScalars_mem]
    convert!
      (Submodule.smul_mem_smul (M := I₂) (r := f a) (n := ⟨f b, h hb⟩) (h ha)
        (Submodule.mem_top)) using 1
    ext
    exact map_mul f a b

@[simp]
/--
lemma `mapCotangent_toCotangent` / 引理 `mapCotangent_toCotangent`

English:
lemma mapCotangent_toCotangent
  proof: rfl

中文:
引理 mapCotangent_toCotangent
  证明: rfl
-/
lemma mapCotangent_toCotangent
    (I₁ : Ideal A) (I₂ : Ideal B) (f : A ->ₐ[R] B) (h : I₁ <= I₂.comap f) (x : I₁) :
    Ideal.mapCotangent I₁ I₂ f h (Ideal.toCotangent I₁ x) = Ideal.toCotangent I₂ ⟨f x, h x.2⟩ := rfl

namespace Cotangent

section Lift

variable {S : Type*} [CommRing S] [Algebra R S] {I : Ideal S}
variable {M : Type*} [AddCommGroup M] [Module R M]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0)
  body: QuotientAddGroup.lift _ f.toAddMonoidHom fun x hx => by
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    refine Submodule.smul_induction_on hx (fun r hr y _ => hf ⟨r, hr⟩ y) fun x y hx hy => ?_
    simp only [map_add, hx, hy, add_zero]
  map_smul' r x := by
    obtain ⟨x

中文:
定义 lift
  签名: (f : I ->ₗ[R] M) (hf : 对任意 (x y : I), f (x * y) = 0)
  定义体: QuotientAddGroup.lift _ f.toAddMonoidHom fun x hx => by
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    refine Submodule.smul_induction_on hx (fun r hr y _ => hf ⟨r, hr⟩ y) fun x y hx hy => ?_
    simp only [map_add, hx, hy, add_zero]
  map_smul' r x := by
    obtain ⟨x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, I.toCotangent_surjective, QuotientAddGroup, QuotientAddGroup.lift, Submodule, Submodule.mem_toAddSubgroup, Submodule.smul_induction_on, add_zero, f.toAddMonoidHom, map_add, map_smul, mem_ker, mem_toAddSubgroup, smul_induction_on, toAddMonoidHom, toCotangent_surjective
-/
def lift (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) :
    I.Cotangent ->ₗ[R] M where
__ := QuotientAddGroup.lift _ f.toAddMonoidHom fun x hx => by
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    refine Submodule.smul_induction_on hx (fun r hr y _ => hf ⟨r, hr⟩ y) fun x y hx hy => ?_
    simp only [map_add, hx, hy, add_zero]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    exact map_smul f _ _

@[simp]
/--
lemma `lift_toCotangent` / 引理 `lift_toCotangent`

English:
lemma lift_toCotangent
  given: (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) (x : I)
  proof: rfl

@[simp]

中文:
引理 lift_toCotangent
  条件: (f : I ->ₗ[R] M) (hf : 对任意 (x y : I), f (x * y) = 0) (x : I)
  证明: rfl

@[simp]
-/
lemma lift_toCotangent (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) (x : I) :
    Cotangent.lift f hf (I.toCotangent x) = f x :=
  rfl

@[simp]
/--
lemma `lift_comp_toCotangent` / 引理 `lift_comp_toCotangent`

English:
lemma lift_comp_toCotangent
  given: (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0)
  proof: rfl

中文:
引理 lift_comp_toCotangent
  条件: (f : I ->ₗ[R] M) (hf : 对任意 (x y : I), f (x * y) = 0)
  证明: rfl
-/
lemma lift_comp_toCotangent (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) :
    Cotangent.lift f hf ∘ₗ I.toCotangent = f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `lift_surjective_iff` / 引理 `lift_surjective_iff`

English:
lemma lift_surjective_iff
  given: (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Cotangent.lift_comp_toCotangent f hf, LinearMap.coe_comp]
    exact Function.Surjective.comp h (toCotangent_surjective I)
  · dsimp [Cotangent.lift]
    exact QuotientAddGroup.lift_surjective_of_surjective _ _ h _

中文:
引理 lift_surjective_iff
  条件: (f : I ->ₗ[R] M) (hf : 对任意 (x y : I), f (x * y) = 0)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Cotangent.lift_comp_toCotangent f hf, LinearMap.coe_comp]
    exact Function.Surjective.comp h (toCotangent_surjective I)
  · dsimp [Cotangent.lift]
    exact QuotientAddGroup.lift_surjective_of_surjective _ _ h _

Depends on / 依赖: Cotangent, Cotangent.lift, Cotangent.lift_comp_toCotangent, Function, Function.Surjective.comp, LinearMap, LinearMap.coe_comp, QuotientAddGroup, QuotientAddGroup.lift_surjective_of_surjective, Surjective, coe_comp, lift_comp_toCotangent, lift_surjective_of_surjective, toCotangent_surjective
-/
lemma lift_surjective_iff (f : I ->ₗ[R] M) (hf : forall (x y : I), f (x * y) = 0) :
    Function.Surjective (Cotangent.lift f hf) ↔ Function.Surjective f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Cotangent.lift_comp_toCotangent f hf, LinearMap.coe_comp]
    exact Function.Surjective.comp h (toCotangent_surjective I)
  · dsimp [Cotangent.lift]
    exact QuotientAddGroup.lift_surjective_of_surjective _ _ h _

end Lift

/--
Definition of `equivOfEq` / `equivOfEq` 的定义

English:
definition equivOfEq
  signature: (I J : Ideal R) (hIJ : I = J)
  body: Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) fun x y => by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) fun x y => by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    subst hI

中文:
定义 equivOfEq
  签名: (I J : 理想 R) (hIJ : I = J)
  定义体: Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) fun x y => by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) fun x y => by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    subst hI

Depends on / 依赖: Cotangent, Cotangent.lift, I.toCotangent, I.toCotangent_surjective, J.toCotangent, LinearEquiv, LinearEquiv.ofEq, hIJ.symm, invFun, left_inv, mul_mem_mul, right_inv, toCotangent, toCotangent_eq_zero, toCotangent_surjective
-/
def equivOfEq (I J : Ideal R) (hIJ : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent where
__ := Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) fun x y => by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) fun x y => by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    subst hIJ
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp
  right_inv x := by
    subst hIJ
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp

@[simp]
/--
lemma `equivOfEq_toCotangent` / 引理 `equivOfEq_toCotangent`

English:
lemma equivOfEq_toCotangent
  given: (I J : Ideal R) (hIJ : I = J) (x : I)
  proof: rfl

@[simp]

中文:
引理 equivOfEq_toCotangent
  条件: (I J : 理想 R) (hIJ : I = J) (x : I)
  证明: rfl

@[simp]
-/
lemma equivOfEq_toCotangent (I J : Ideal R) (hIJ : I = J) (x : I) :
    Cotangent.equivOfEq I J hIJ (I.toCotangent x) = J.toCotangent (LinearEquiv.ofEq I J hIJ x) :=
  rfl

@[simp]
/--
lemma `equivOfEq_symm` / 引理 `equivOfEq_symm`

English:
lemma equivOfEq_symm
  given: (I J : Ideal R) (hIJ : I = J)
  proof: rfl

中文:
引理 equivOfEq_symm
  条件: (I J : 理想 R) (hIJ : I = J)
  证明: rfl
-/
lemma equivOfEq_symm (I J : Ideal R) (hIJ : I = J) :
    (Cotangent.equivOfEq I J hIJ).symm = Cotangent.equivOfEq J I hIJ.symm :=
  rfl

end Ideal.Cotangent

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/--
Definition of `CotangentSpace` / `CotangentSpace` 的定义

English:
abbreviation CotangentSpace
  signature: : Type _
  body: (maximalIdeal R).Cotangent

中文:
缩写 CotangentSpace
  签名: : 类型 _
  定义体: (maximalIdeal R).Cotangent

Depends on / 依赖: Cotangent, maximalIdeal
-/
abbrev CotangentSpace : Type _ := (maximalIdeal R).Cotangent

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (ResidueField R) (CotangentSpace R)
  body: inferInstanceAs Module (R ⧸ maximalIdeal R) _

中文:
实例 :
  签名: 模 (ResidueField R) (CotangentSpace R)
  定义体: inferInstanceAs Module (R ⧸ maximalIdeal R) _

Depends on / 依赖: Module, maximalIdeal
-/
instance : Module (ResidueField R) (CotangentSpace R) :=
inferInstanceAs Module (R ⧸ maximalIdeal R) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R (ResidueField R) (CotangentSpace R)
  body: inferInstanceAs IsScalarTower R (R ⧸ maximalIdeal R) _

中文:
实例 :
  签名: 标量塔 R (ResidueField R) (CotangentSpace R)
  定义体: inferInstanceAs IsScalarTower R (R ⧸ maximalIdeal R) _

Depends on / 依赖: IsScalarTower, maximalIdeal
-/
instance : IsScalarTower R (ResidueField R) (CotangentSpace R) :=
inferInstanceAs IsScalarTower R (R ⧸ maximalIdeal R) _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherianRing
  signature: R] : FiniteDimensional (ResidueField R) (CotangentSpace R)
  body: Module.Finite.of_restrictScalars_finite R _ _

中文:
实例 [是Noether环
  签名: R] : 有限维 (ResidueField R) (CotangentSpace R)
  定义体: Module.Finite.of_restrictScalars_finite R _ _

Depends on / 依赖: Finite, Module, Module.Finite.of_restrictScalars_finite, of_restrictScalars_finite
-/
instance [IsNoetherianRing R] : FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_restrictScalars_finite R _ _

variable {R}

/--
lemma `subsingleton_cotangentSpace_iff` / 引理 `subsingleton_cotangentSpace_iff`

English:
lemma subsingleton_cotangentSpace_iff
  given: [IsNoetherianRing R]
  proof: by
  refine (maximalIdeal R).cotangent_subsingleton_iff.trans ?_
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]; rw [Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing]
  simp [(maximalIdeal.isMaximal R).ne_top]

中文:
引理 subsingleton_cotangentSpace_iff
  条件: [是Noether环 R]
  证明: by
  refine (maximalIdeal R).cotangent_subsingleton_iff.trans ?_
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]; rw [Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing]
  simp [(maximalIdeal.isMaximal R).ne_top]

Depends on / 依赖: Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing, IsLocalRing, IsLocalRing.isField_iff_maximalIdeal_eq, cotangent_subsingleton_iff, cotangent_subsingleton_iff.trans, isField_iff_maximalIdeal_eq, isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing, isMaximal, maximalIdeal, maximalIdeal.isMaximal, ne_top
-/
lemma subsingleton_cotangentSpace_iff [IsNoetherianRing R] :
    Subsingleton (CotangentSpace R) ↔ IsField R := by
  refine (maximalIdeal R).cotangent_subsingleton_iff.trans ?_
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]; rw [Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing]
  simp [(maximalIdeal.isMaximal R).ne_top]

/--
lemma `CotangentSpace.map_eq_top_iff` / 引理 `CotangentSpace.map_eq_top_iff`

English:
lemma CotangentSpace.map_eq_top_iff
  given: [IsNoetherianRing R] {M : Submodule R (maximalIdeal R)}
  proof: by
  refine ⟨fun H => eq_top_iff.mpr ?_, by rintro rfl; simp [Ideal.toCotangent_range]⟩
  refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _).mp ?_
  rw [Submodule.map_top]; rw [Submodule.range_subtype]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.n

中文:
引理 CotangentSpace.map_eq_top_iff
  条件: [是Noether环 R] {M : 子模 R (maximalIdeal R)}
  证明: by
  refine ⟨fun H => eq_top_iff.mpr ?_, by rintro rfl; simp [Ideal.toCotangent_range]⟩
  refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _).mp ?_
  rw [Submodule.map_top]; rw [Submodule.range_subtype]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.n

Depends on / 依赖: Ideal.map_toCotangent_ker, Ideal.toCotangent_range, IsLocalRing, IsLocalRing.jacobson_eq_maximalIdeal, IsNoetherian, IsNoetherian.noetherian, Submodule, Submodule.comap_map_eq, Submodule.injective_subtype, Submodule.le_of_le_smul_of_le_jacobson_bot, Submodule.map_le_map_iff_of_injective, Submodule.map_sup, Submodule.map_top, Submodule.range_subtype, bot_ne_top, comap_map_eq, eq_top_iff, eq_top_iff.mpr, injective_subtype, jacobson_eq_maximalIdeal
-/
lemma CotangentSpace.map_eq_top_iff [IsNoetherianRing R] {M : Submodule R (maximalIdeal R)} :
    M.map (maximalIdeal R).toCotangent = ⊤ ↔ M = ⊤ := by
  refine ⟨fun H => eq_top_iff.mpr ?_, by rintro rfl; simp [Ideal.toCotangent_range]⟩
  refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _).mp ?_
  rw [Submodule.map_top]; rw [Submodule.range_subtype]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
  rw [smul_eq_mul]; rw [← pow_two]; rw [← Ideal.map_toCotangent_ker]; rw [← Submodule.map_sup]; rw [← Submodule.comap_map_eq]; rw [H]; rw [Submodule.comap_top]; rw [Submodule.map_top]; rw [Submodule.range_subtype]

/--
lemma `CotangentSpace.span_image_eq_top_iff` / 引理 `CotangentSpace.span_image_eq_top_iff`

English:
lemma CotangentSpace.span_image_eq_top_iff
  given: [IsNoetherianRing R] {s : Set (maximalIdeal R)}
  proof: by
  rw [← map_eq_top_iff]; rw [← (Submodule.restrictScalars_injective R ..).eq_iff]; rw [Submodule.restrictScalars_span]
  · simp
  · exact Ideal.Quotient.mk_surjective

中文:
引理 CotangentSpace.span_image_eq_top_iff
  条件: [是Noether环 R] {s : 集合 (maximalIdeal R)}
  证明: by
  rw [← map_eq_top_iff]; rw [← (Submodule.restrictScalars_injective R ..).eq_iff]; rw [Submodule.restrictScalars_span]
  · simp
  · exact Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, Submodule, Submodule.restrictScalars_injective, Submodule.restrictScalars_span, eq_iff, map_eq_top_iff, mk_surjective, restrictScalars_injective, restrictScalars_span
-/
lemma CotangentSpace.span_image_eq_top_iff [IsNoetherianRing R] {s : Set (maximalIdeal R)} :
    Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s) = ⊤ ↔
      Submodule.span R s = ⊤ := by
  rw [← map_eq_top_iff]; rw [← (Submodule.restrictScalars_injective R ..).eq_iff]; rw [Submodule.restrictScalars_span]
  · simp
  · exact Ideal.Quotient.mk_surjective

/--
theorem `rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg` / 定理 `rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg`

English:
theorem rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg
  given: (fg : (maximalIdeal R).FG)
  proof: by
  rw [Submodule.rank_eq_spanRank_of_free]; rw [← Submodule.spanRank_top (maximalIdeal R)]
  apply le_antisymm
  · obtain ⟨s, hs_card, hs_span⟩ :=
      (⊤ : Submodule R (maximalIdeal R)).exists_span_set_card_eq_spanRank
    have hs_span' : Submodule.span (ResidueField R) ((maximalIdeal R).toCotan

中文:
定理 rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg
  条件: (fg : (maximalIdeal R).FG)
  证明: by
  rw [Submodule.rank_eq_spanRank_of_free]; rw [← Submodule.spanRank_top (maximalIdeal R)]
  apply le_antisymm
  · obtain ⟨s, hs_card, hs_span⟩ :=
      (⊤ : Submodule R (maximalIdeal R)).exists_span_set_card_eq_spanRank
    have hs_span' : Submodule.span (ResidueField R) ((maximalIdeal R).toCotan

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, ResidueField, Submodule, Submodule.map_span, Submodule.map_top, Submodule.rank_eq_spanRank_of_free, Submodule.restrictScalars_eq_top_iff, Submodule.restrictScalars_span, Submodule.span, Submodule.spanRank_top, exists_span_set_card_eq_spanRank, hs_card, hs_span, le_antisymm, map_span, map_top, maximalIdeal, mk_surjective, rank_eq_spanRank_of_free
-/
theorem rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg (fg : (maximalIdeal R).FG) :
    Module.rank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanRank := by
  rw [Submodule.rank_eq_spanRank_of_free]; rw [← Submodule.spanRank_top (maximalIdeal R)]
  apply le_antisymm
  · obtain ⟨s, hs_card, hs_span⟩ :=
      (⊤ : Submodule R (maximalIdeal R)).exists_span_set_card_eq_spanRank
    have hs_span' : Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s) = ⊤ := by
      rw [← Submodule.restrictScalars_eq_top_iff R]; rw [Submodule.restrictScalars_span R (ResidueField R) Ideal.Quotient.mk_surjective]; rw [← Submodule.map_span]; rw [hs_span]; rw [Submodule.map_top]; rw [Ideal.toCotangent_range]
    rw [← hs_card]; rw [← hs_span']
    grw [Submodule.spanRank_span_le_card, Cardinal.mk_image_le]
  · obtain ⟨s, hs_card, hs_span⟩ :=
      (⊤ : Submodule (ResidueField R) (CotangentSpace R)).exists_span_set_card_eq_spanRank
    have hs_span' : Submodule.span R s =
        Submodule.map (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R (maximalIdeal R)))) ⊤ := by
      rw [Submodule.map_top]; rw [Submodule.range_mkQ]
      change Submodule.span R s = ⊤
      rw [← Submodule.restrictScalars_span R (ResidueField R)
        Ideal.Quotient.mk_surjective]; rw [hs_span]; rw [Submodule.restrictScalars_top]
    obtain ⟨t, ht_inj, ht_image, ht_span⟩ :=
      Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot s
        ((Submodule.fg_top (maximalIdeal R)).mpr fg)
        (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
        hs_span'
    rw [← hs_card]; rw [← ht_span]; rw [← ht_image]
    exact le_of_le_of_eq (Submodule.spanRank_span_le_card t)
      (Cardinal.mk_image_eq_of_injOn _ _ ht_inj).symm

/--
theorem `rank_cotangentSpace_eq_spanrank_maximalIdeal` / 定理 `rank_cotangentSpace_eq_spanrank_maximalIdeal`

English:
theorem rank_cotangentSpace_eq_spanrank_maximalIdeal
  given: [IsNoetherianRing R]
  proof: rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg (maximalIdeal R).fg_of_isNoetherianRing

中文:
定理 rank_cotangentSpace_eq_spanrank_maximalIdeal
  条件: [是Noether环 R]
  证明: rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg (maximalIdeal R).fg_of_isNoetherianRing

Depends on / 依赖: fg_of_isNoetherianRing, maximalIdeal, rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg
-/
theorem rank_cotangentSpace_eq_spanrank_maximalIdeal [IsNoetherianRing R] :
    Module.rank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanRank :=
  rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg (maximalIdeal R).fg_of_isNoetherianRing

open Module

/--
lemma `finrank_cotangentSpace_eq_zero_iff` / 引理 `finrank_cotangentSpace_eq_zero_iff`

English:
lemma finrank_cotangentSpace_eq_zero_iff
  given: [IsNoetherianRing R]
  proof: by
  rw [finrank_zero_iff]; rw [subsingleton_cotangentSpace_iff]

中文:
引理 finrank_cotangentSpace_eq_zero_iff
  条件: [是Noether环 R]
  证明: by
  rw [finrank_zero_iff]; rw [subsingleton_cotangentSpace_iff]

Depends on / 依赖: finrank_zero_iff, subsingleton_cotangentSpace_iff
-/
lemma finrank_cotangentSpace_eq_zero_iff [IsNoetherianRing R] :
    finrank (ResidueField R) (CotangentSpace R) = 0 ↔ IsField R := by
  rw [finrank_zero_iff]; rw [subsingleton_cotangentSpace_iff]

/--
lemma `finrank_cotangentSpace_eq_zero` / 引理 `finrank_cotangentSpace_eq_zero`

English:
lemma finrank_cotangentSpace_eq_zero
  given: (R) [Field R]
  proof: finrank_cotangentSpace_eq_zero_iff.mpr (Field.toIsField R)

中文:
引理 finrank_cotangentSpace_eq_zero
  条件: (R) [域 R]
  证明: finrank_cotangentSpace_eq_zero_iff.mpr (Field.toIsField R)

Depends on / 依赖: Field.toIsField, finrank_cotangentSpace_eq_zero_iff, finrank_cotangentSpace_eq_zero_iff.mpr, toIsField
-/
lemma finrank_cotangentSpace_eq_zero (R) [Field R] :
    finrank (ResidueField R) (CotangentSpace R) = 0 :=
  finrank_cotangentSpace_eq_zero_iff.mpr (Field.toIsField R)

open Submodule in
/--
theorem `finrank_cotangentSpace_le_one_iff` / 定理 `finrank_cotangentSpace_le_one_iff`

English:
theorem finrank_cotangentSpace_le_one_iff
  given: [IsNoetherianRing R]
  proof: by
  rw [Module.finrank_le_one_iff_top_isPrincipal]; rw [isPrincipal_iff]; rw [(maximalIdeal R).toCotangent_surjective.exists]; rw [isPrincipal_iff]
  simp_rw [← Set.image_singleton, eq_comm (a := ⊤), CotangentSpace.span_image_eq_top_iff,
    ← (map_injective_of_injective (injective_subtype _)).eq_i

中文:
定理 finrank_cotangentSpace_le_one_iff
  条件: [是Noether环 R]
  证明: by
  rw [Module.finrank_le_one_iff_top_isPrincipal]; rw [isPrincipal_iff]; rw [(maximalIdeal R).toCotangent_surjective.exists]; rw [isPrincipal_iff]
  simp_rw [← Set.image_singleton, eq_comm (a := ⊤), CotangentSpace.span_image_eq_top_iff,
    ← (map_injective_of_injective (injective_subtype _)).eq_i

Depends on / 依赖: CotangentSpace, CotangentSpace.span_image_eq_top_iff, Module, Module.finrank_le_one_iff_top_isPrincipal, Set.image_singleton, Set.mem_singleton, Submodule, Submodule.map_top, eq_comm, eq_iff, finrank_le_one_iff_top_isPrincipal, image_singleton, injective_subtype, isPrincipal_iff, map_injective_of_injective, map_span, map_top, maximalIdeal, mem_singleton, range_subtype
-/
theorem finrank_cotangentSpace_le_one_iff [IsNoetherianRing R] :
    finrank (ResidueField R) (CotangentSpace R) <= 1 ↔ (maximalIdeal R).IsPrincipal := by
  rw [Module.finrank_le_one_iff_top_isPrincipal]; rw [isPrincipal_iff]; rw [(maximalIdeal R).toCotangent_surjective.exists]; rw [isPrincipal_iff]
  simp_rw [← Set.image_singleton, eq_comm (a := ⊤), CotangentSpace.span_image_eq_top_iff,
    ← (map_injective_of_injective (injective_subtype _)).eq_iff, map_span, Set.image_singleton,
    Submodule.map_top, range_subtype, eq_comm (a := maximalIdeal R)]
  exact ⟨fun ⟨x, h⟩ => ⟨_, h⟩, fun ⟨x, h⟩ => ⟨⟨x, h ▸ subset_span (Set.mem_singleton x)⟩, h⟩⟩

end IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/--
lemma `Ideal.mapCotangent_surjective_of_comap_eq` / 引理 `Ideal.mapCotangent_surjective_of_comap_eq`

English:
lemma Ideal.mapCotangent_surjective_of_comap_eq
  statement: (surj : Function.Surjective (algebraMap A B))
  proof: by
  intro x
  rcases I.toCotangent_surjective x with ⟨x', rfl⟩
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq x'.2 with ⟨y', mem, hy'⟩
  use J.toCotangent ⟨y', mem⟩
  simpa using I.toCotangent.congr_arg (SetCoe.ext hy')

中文:
引理 理想.mapCotangent_surjective_of_comap_eq
  结论: (surj : 函数.满射 (algebraMap A B))
  证明: by
  intro x
  rcases I.toCotangent_surjective x with ⟨x', rfl⟩
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq x'.2 with ⟨y', mem, hy'⟩
  use J.toCotangent ⟨y', mem⟩
  simpa using I.toCotangent.congr_arg (SetCoe.ext hy')

Depends on / 依赖: I.toCotangent.congr_arg, I.toCotangent_surjective, Ideal.exists_of_comap_eq_ker_sup, J.toCotangent, SetCoe, SetCoe.ext, congr_arg, exists_of_comap_eq_ker_sup, toCotangent, toCotangent_surjective
-/
lemma Ideal.mapCotangent_surjective_of_comap_eq (surj : Function.Surjective (algebraMap A B))
    {I : Ideal B} {J : Ideal A} (eq : I.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ J) :
    Function.Surjective (Ideal.mapCotangent J I (Algebra.ofId A B)
      (le_of_le_of_eq le_sup_right eq.symm)) := by
  intro x
  rcases I.toCotangent_surjective x with ⟨x', rfl⟩
  rcases Ideal.exists_of_comap_eq_ker_sup _ surj eq x'.2 with ⟨y', mem, hy'⟩
  use J.toCotangent ⟨y', mem⟩
  simpa using I.toCotangent.congr_arg (SetCoe.ext hy')

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Ideal.mapCotangent_ker_of_surjective` / 引理 `Ideal.mapCotangent_ker_of_surjective`

English:
lemma Ideal.mapCotangent_ker_of_surjective
  statement: (surj : Function.Surjective (algebraMap A B))
  proof: by
  have eqmap := Ideal.eq_map_of_comap_eq_ker_sup _ surj eq
  refine le_antisymm (fun x hx => ?_) ?_
  · rcases J.toCotangent_surjective x with ⟨x', hx'⟩
    have : Function.Surjective (Algebra.ofId A B) := surj
    simp only [← hx', LinearMap.mem_ker, Ideal.mapCotangent_toCotangent,
      Ideal.t

中文:
引理 理想.mapCotangent_ker_of_surjective
  结论: (surj : 函数.满射 (algebraMap A B))
  证明: by
  have eqmap := Ideal.eq_map_of_comap_eq_ker_sup _ surj eq
  refine le_antisymm (fun x hx => ?_) ?_
  · rcases J.toCotangent_surjective x with ⟨x', hx'⟩
    have : Function.Surjective (Algebra.ofId A B) := surj
    simp only [← hx', LinearMap.mem_ker, Ideal.mapCotangent_toCotangent,
      Ideal.t

Depends on / 依赖: Algebra, Algebra.ofId, Algebra.ofId_apply, Function, Function.Surjective, Ideal.comap_map_of_surjective, Ideal.eq_map_of_comap_eq_ker_sup, Ideal.mapCotangent_toCotangent, Ideal.map_pow, Ideal.mem_comap, Ideal.toCotangent_eq_zero, J.toCotangent_surjective, LinearMap, LinearMap.mem_ker, Submodule, Submodule.mem_sup.mp, Surjective, comap_map_of_surjective, eq_map_of_comap_eq_ker_sup, le_antisymm
-/
lemma Ideal.mapCotangent_ker_of_surjective (surj : Function.Surjective (algebraMap A B))
    {I : Ideal B} {J : Ideal A} (eq : I.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ J) :
    (Ideal.mapCotangent J I (Algebra.ofId A B) (le_of_le_of_eq le_sup_right eq.symm)).ker =
      (Submodule.comap J.subtype ((RingHom.ker (algebraMap A B)) ⊓ J)).map J.toCotangent := by
  have eqmap := Ideal.eq_map_of_comap_eq_ker_sup _ surj eq
  refine le_antisymm (fun x hx => ?_) ?_
  · rcases J.toCotangent_surjective x with ⟨x', hx'⟩
    have : Function.Surjective (Algebra.ofId A B) := surj
    simp only [← hx', LinearMap.mem_ker, Ideal.mapCotangent_toCotangent,
      Ideal.toCotangent_eq_zero, eqmap, Algebra.ofId_apply] at hx
    rw [← Ideal.map_pow]; rw [← Ideal.mem_comap]; rw [Ideal.comap_map_of_surjective' _ surj] at hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
    have : y + z in J := by simp [hyz]
    have zmemJ := (Ideal.add_mem_iff_right J (Ideal.pow_le_self (by omega) hy)).mp this
    have xeq : x = J.toCotangent ⟨z, zmemJ⟩ := by simpa [← hx', J.toCotangent_eq, ← hyz] using hy
    rw [xeq]
    exact Submodule.mem_map_of_mem (Submodule.mem_comap.mpr (Ideal.mem_inf.mpr ⟨hz, zmemJ⟩))
  · rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp]
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Ideal.mapCotangent_toCotangent]
    convert! map_zero I.toCotangent
    exact (Ideal.mem_inf.mp hx).1
