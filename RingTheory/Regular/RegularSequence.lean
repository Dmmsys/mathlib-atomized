/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regular sequences and weakly regular sequences

The notion of a regular sequence is fundamental in commutative algebra.
Properties of regular sequences encode information about singularities of a
ring and regularity of a sequence can be tested homologically.
However the notion of a regular sequence is only really sensible for Noetherian local rings.

TODO: Koszul regular sequences, `H_1`-regular sequences, quasi-regular sequences, depth.

## Tags

module, regular element, regular sequence, commutative algebra
-/

@[expose] public section

universe u v

open scoped Pointwise

variable {R S M M₂ M₃ M₄ : Type*}

namespace Ideal

variable [Semiring R] [Semiring S]

/--
Definition of `ofList` / `ofList` 的定义

English:
abbreviation ofList
  signature: (rs : List R)
  body: span { r | r in rs }

中文:
缩写 ofList
  签名: (rs : 列表 R)
  定义体: span { r | r in rs }
-/
abbrev ofList (rs : List R) := span { r | r in rs }

/--
lemma `ofList_nil` / 引理 `ofList_nil`

English:
lemma ofList_nil
  statement: (ofList [] : Ideal R) = ⊥
  proof: have : { r | r in [] } = ∅ := Set.eq_empty_of_forall_notMem (fun _ => List.not_mem_nil)
  Eq.trans (congrArg span this) span_empty

中文:
引理 ofList_nil
  结论: (ofList [] : 理想 R) = ⊥
  证明: have : { r | r in [] } = ∅ := Set.eq_empty_of_forall_notMem (fun _ => List.not_mem_nil)
  Eq.trans (congrArg span this) span_empty
-/
@[simp] lemma ofList_nil : (ofList [] : Ideal R) = ⊥ :=
  have : { r | r in [] } = ∅ := Set.eq_empty_of_forall_notMem (fun _ => List.not_mem_nil)
  Eq.trans (congrArg span this) span_empty

/--
lemma `ofList_append` / 引理 `ofList_append`

English:
lemma ofList_append
  given: (rs₁ rs₂ : List R)
  proof: have : { r | r in rs₁ ++ rs₂ } = _ := Set.ext (fun _ => List.mem_append)
  Eq.trans (congrArg span this) (span_union _ _)

中文:
引理 ofList_append
  条件: (rs₁ rs₂ : 列表 R)
  证明: have : { r | r in rs₁ ++ rs₂ } = _ := Set.ext (fun _ => List.mem_append)
  Eq.trans (congrArg span this) (span_union _ _)
-/
@[simp] lemma ofList_append (rs₁ rs₂ : List R) :
    ofList (rs₁ ++ rs₂) = ofList rs₁ ⊔ ofList rs₂ :=
  have : { r | r in rs₁ ++ rs₂ } = _ := Set.ext (fun _ => List.mem_append)
  Eq.trans (congrArg span this) (span_union _ _)

/--
lemma `ofList_singleton` / 引理 `ofList_singleton`

English:
lemma ofList_singleton
  given: (r : R)
  statement: ofList [r] = span {r}
  proof: congrArg span (Set.ext fun _ => List.mem_singleton)

中文:
引理 ofList_singleton
  条件: (r : R)
  结论: ofList [r] = span {r}
  证明: congrArg span (Set.ext fun _ => List.mem_singleton)

Depends on / 依赖: List.mem_singleton, Set.ext, mem_singleton
-/
lemma ofList_singleton (r : R) : ofList [r] = span {r} :=
  congrArg span (Set.ext fun _ => List.mem_singleton)

/--
lemma `ofList_cons` / 引理 `ofList_cons`

English:
lemma ofList_cons
  given: (r : R) (rs : List R)
  proof: Eq.trans (ofList_append [r] rs) (congrArg (· ⊔ _) (ofList_singleton r))

中文:
引理 ofList_cons
  条件: (r : R) (rs : 列表 R)
  证明: Eq.trans (ofList_append [r] rs) (congrArg (· ⊔ _) (ofList_singleton r))
-/
@[simp] lemma ofList_cons (r : R) (rs : List R) :
    ofList (r::rs) = span {r} ⊔ ofList rs :=
  Eq.trans (ofList_append [r] rs) (congrArg (· ⊔ _) (ofList_singleton r))

/--
lemma `map_ofList` / 引理 `map_ofList`

English:
lemma map_ofList
  given: (f : R ->+* S) (rs : List R)
  proof: Eq.trans (map_span f { r | r in rs }) congrArg span
    Set.ext (fun _ => List.mem_map.symm)

中文:
引理 map_ofList
  条件: (f : R ->+* S) (rs : 列表 R)
  证明: Eq.trans (map_span f { r | r in rs }) congrArg span
    Set.ext (fun _ => List.mem_map.symm)
-/
@[simp] lemma map_ofList (f : R ->+* S) (rs : List R) :
    map f (ofList rs) = ofList (rs.map f) :=
Eq.trans (map_span f { r | r in rs }) congrArg span
    Set.ext (fun _ => List.mem_map.symm)

/--
lemma `ofList_cons_smul` / 引理 `ofList_cons_smul`

English:
lemma ofList_cons_smul
  statement: {R} [CommSemiring R] (r : R) (rs : List R) {M}
  proof: by
  rw [ofList_cons]; rw [Submodule.sup_smul]; rw [Submodule.ideal_span_singleton_smul]

中文:
引理 ofList_cons_smul
  结论: {R} [交换半环 R] (r : R) (rs : 列表 R) {M}
  证明: by
  rw [ofList_cons]; rw [Submodule.sup_smul]; rw [Submodule.ideal_span_singleton_smul]

Depends on / 依赖: Submodule, Submodule.ideal_span_singleton_smul, Submodule.sup_smul, ideal_span_singleton_smul, ofList_cons, sup_smul
-/
lemma ofList_cons_smul {R} [CommSemiring R] (r : R) (rs : List R) {M}
    [AddCommMonoid M] [Module R M] (N : Submodule R M) :
    ofList (r :: rs) • N = r • N ⊔ ofList rs • N := by
  rw [ofList_cons]; rw [Submodule.sup_smul]; rw [Submodule.ideal_span_singleton_smul]

end Ideal

namespace Submodule

variable (M) [CommRing R] [AddCommGroup M] [AddCommGroup M₂]
    [Module R M] [Module R M₂] (r : R) (rs : List R)

/--
Definition of `quotOfListConsSMulTopEquivQuotSMulTopInner` / `quotOfListConsSMulTopEquivQuotSMulTopInner` 的定义

English:
definition quotOfListConsSMulTopEquivQuotSMulTopInner
  signature: :
  body: quotEquivOfEq _ _ (Ideal.ofList_cons_smul r rs ⊤) ≪≫ₗ
    (quotientQuotientEquivQuotientSup (r • ⊤) (Ideal.ofList rs • ⊤)).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_smul'', map_top, range_mkQ])

中文:
定义 quotOfListConsSMulTopEquivQuotSMulTopInner
  签名: :
  定义体: quotEquivOfEq _ _ (Ideal.ofList_cons_smul r rs ⊤) ≪≫ₗ
    (quotientQuotientEquivQuotientSup (r • ⊤) (Ideal.ofList rs • ⊤)).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_smul'', map_top, range_mkQ])

Depends on / 依赖: Ideal.ofList, Ideal.ofList_cons_smul, map_smul, map_top, ofList, ofList_cons_smul, quotEquivOfEq, quotientQuotientEquivQuotientSup, range_mkQ
-/
def quotOfListConsSMulTopEquivQuotSMulTopInner :
    (M ⧸ (Ideal.ofList (r :: rs) • ⊤ : Submodule R M)) ≃ₗ[R]
      QuotSMulTop r M ⧸ (Ideal.ofList rs • ⊤ : Submodule R (QuotSMulTop r M)) :=
  quotEquivOfEq _ _ (Ideal.ofList_cons_smul r rs ⊤) ≪≫ₗ
    (quotientQuotientEquivQuotientSup (r • ⊤) (Ideal.ofList rs • ⊤)).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_smul'', map_top, range_mkQ])

/--
Definition of `quotOfListConsSMulTopEquivQuotSMulTopOuter` / `quotOfListConsSMulTopEquivQuotSMulTopOuter` 的定义

English:
definition quotOfListConsSMulTopEquivQuotSMulTopOuter
  signature: :
  body: quotEquivOfEq _ _ (Eq.trans (Ideal.ofList_cons_smul r rs ⊤) (sup_comm _ _)) ≪≫ₗ
    (quotientQuotientEquivQuotientSup (Ideal.ofList rs • ⊤) (r • ⊤)).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_pointwise_smul, map_top, range_mkQ])

中文:
定义 quotOfListConsSMulTopEquivQuotSMulTopOuter
  签名: :
  定义体: quotEquivOfEq _ _ (Eq.trans (Ideal.ofList_cons_smul r rs ⊤) (sup_comm _ _)) ≪≫ₗ
    (quotientQuotientEquivQuotientSup (Ideal.ofList rs • ⊤) (r • ⊤)).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_pointwise_smul, map_top, range_mkQ])

Depends on / 依赖: Eq.trans, Ideal.ofList, Ideal.ofList_cons_smul, map_pointwise_smul, map_top, ofList, ofList_cons_smul, quotEquivOfEq, quotientQuotientEquivQuotientSup, range_mkQ, sup_comm
-/
def quotOfListConsSMulTopEquivQuotSMulTopOuter :
    (M ⧸ (Ideal.ofList (r :: rs) • ⊤ : Submodule R M)) ≃ₗ[R]
      QuotSMulTop r (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) :=
  quotEquivOfEq _ _ (Eq.trans (Ideal.ofList_cons_smul r rs ⊤) (sup_comm _ _)) ≪≫ₗ
    (quotientQuotientEquivQuotientSup (Ideal.ofList rs • ⊤) (r • ⊤)).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_pointwise_smul, map_top, range_mkQ])

variable {M}

/--
lemma `quotOfListConsSMulTopEquivQuotSMulTopInner_naturality` / 引理 `quotOfListConsSMulTopEquivQuotSMulTopInner_naturality`

English:
lemma quotOfListConsSMulTopEquivQuotSMulTopInner_naturality
  given: (f : M ->ₗ[R] M₂)
  proof: quot_hom_ext _ _ _ fun _ => rfl

中文:
引理 quotOfListConsSMulTopEquivQuotSMulTopInner_naturality
  条件: (f : M ->ₗ[R] M₂)
  证明: quot_hom_ext _ _ _ fun _ => rfl

Depends on / 依赖: quot_hom_ext
-/
lemma quotOfListConsSMulTopEquivQuotSMulTopInner_naturality (f : M ->ₗ[R] M₂) :
    (quotOfListConsSMulTopEquivQuotSMulTopInner M₂ r rs).toLinearMap ∘ₗ
        mapQ _ _ _ (smul_top_le_comap_smul_top (Ideal.ofList (r :: rs)) f) =
      mapQ _ _ _ (smul_top_le_comap_smul_top _ (QuotSMulTop.map r f)) ∘ₗ
        (quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).toLinearMap :=
  quot_hom_ext _ _ _ fun _ => rfl

/--
lemma `top_eq_ofList_cons_smul_iff` / 引理 `top_eq_ofList_cons_smul_iff`

English:
lemma top_eq_ofList_cons_smul_iff
  proof: by
  conv => congr <;> rw [eq_comm, ← Quotient.subsingleton_iff]
  exact (quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).toEquiv.subsingleton_congr

中文:
引理 top_eq_ofList_cons_smul_iff
  证明: by
  conv => congr <;> rw [eq_comm, ← Quotient.subsingleton_iff]
  exact (quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).toEquiv.subsingleton_congr

Depends on / 依赖: Quotient, Quotient.subsingleton_iff, eq_comm, quotOfListConsSMulTopEquivQuotSMulTopInner, subsingleton_congr, subsingleton_iff, toEquiv, toEquiv.subsingleton_congr
-/
lemma top_eq_ofList_cons_smul_iff :
    (⊤ : Submodule R M) = Ideal.ofList (r :: rs) • ⊤ ↔
      (⊤ : Submodule R (QuotSMulTop r M)) = Ideal.ofList rs • ⊤ := by
  conv => congr <;> rw [eq_comm, ← Quotient.subsingleton_iff]
  exact (quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).toEquiv.subsingleton_congr

end Submodule

namespace RingTheory.Sequence

open scoped TensorProduct List
open Function Submodule QuotSMulTop

variable (S M)

section Definitions

/-
In theory, regularity of `rs : List α` on `M` makes sense as soon as
`[Monoid α]`, `[AddCommGroup M]`, and `[DistribMulAction α M]`.
Instead of `Ideal.ofList (rs.take i) • (⊤ : Submodule R M)` we use
`⨆ (j : Fin i), rs[j] • (⊤ : AddSubgroup M)`.
However it's not clear that this is a useful generalization.
If we add the assumption `[SMulCommClass α α M]` this is essentially the same
as focusing on the commutative ring case, by passing to the monoid ring
`ℤ[abelianization of α]`.
-/
variable [CommRing R] [AddCommGroup M] [Module R M]

open Ideal

/-- A sequence `[r₁, …, rₙ]` is weakly regular on `M` iff `rᵢ` is regular on
`M⧸(r₁, …, rᵢ₋₁)M` for all `1 ≤ i ≤ n`. -/
@[mk_iff]
/--
Definition of `IsWeaklyRegular` / `IsWeaklyRegular` 的定义

English:
structure IsWeaklyRegular
  parameters: (rs : List R)
  axioms and operations (1):
    - regular_mod_prev : forall i (h : i < rs.length), IsSMulRegular (M ⧸ (ofList (rs.take i) • ⊤ : Submodule R M)) rs[i]

中文:
结构 是WeaklyRegular
  参数: (rs : 列表 R)
  公理与运算 (1 个):
    - regular_mod_prev : 对任意 i (h : i < rs.length), IsSMulRegular (M ⧸ (ofList (rs.take i) • ⊤ : 子模 R M)) rs[i]
-/
structure IsWeaklyRegular (rs : List R) : Prop where
  regular_mod_prev : forall i (h : i < rs.length),
    IsSMulRegular (M ⧸ (ofList (rs.take i) • ⊤ : Submodule R M)) rs[i]

/--
lemma `isWeaklyRegular_iff_Fin` / 引理 `isWeaklyRegular_iff_Fin`

English:
lemma isWeaklyRegular_iff_Fin
  given: (rs : List R)
  proof: Iff.trans (isWeaklyRegular_iff M rs) (Iff.symm Fin.forall_iff)

中文:
引理 isWeaklyRegular_iff_Fin
  条件: (rs : 列表 R)
  证明: Iff.trans (isWeaklyRegular_iff M rs) (Iff.symm Fin.forall_iff)

Depends on / 依赖: Fin.forall_iff, Iff.symm, Iff.trans, forall_iff, isWeaklyRegular_iff
-/
lemma isWeaklyRegular_iff_Fin (rs : List R) :
    IsWeaklyRegular M rs ↔ forall (i : Fin rs.length),
      IsSMulRegular (M ⧸ (ofList (rs.take i) • ⊤ : Submodule R M)) rs[i] :=
  Iff.trans (isWeaklyRegular_iff M rs) (Iff.symm Fin.forall_iff)

/-- A weakly regular sequence `rs` on `M` is regular if also `M/rsM ≠ 0`. -/
@[mk_iff]
/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
structure IsRegular
  parameters: (rs : List R)
  extends: IsWeaklyRegular M rs
  axioms and operations (1):
    - top_ne_smul : (⊤ : Submodule R M) != Ideal.ofList rs • ⊤

中文:
结构 是正则
  参数: (rs : 列表 R)
  继承: 是WeaklyRegular M rs
  公理与运算 (1 个):
    - top_ne_smul : (⊤ : 子模 R M) != 理想.ofList rs • ⊤
-/
structure IsRegular (rs : List R) : Prop extends IsWeaklyRegular M rs where
  top_ne_smul : (⊤ : Submodule R M) != Ideal.ofList rs • ⊤

end Definitions

section Congr

variable {S M} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup M₂]
    [Module R M] [Module S M₂]
    {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

set_option backward.isDefEq.respectTransparency.types false in
open DistribMulAction AddSubgroup in
/--
lemma `_root_.AddHom.map_smul_top_toAddSubgroup_of_surjective` / 引理 `_root_.AddHom.map_smul_top_toAddSubgroup_of_surjective`

English:
lemma _root_.AddHom.map_smul_top_toAddSubgroup_of_surjective
  proof: by
  induction h with
  | nil =>
    convert! AddSubgroup.map_bot f using 1 <;>
      rw [Ideal.ofList_nil]; rw [bot_smul]; rw [bot_toAddSubgroup]
  | @cons r s _ _ h _ ih =>
    conv => congr <;> rw [Ideal.ofList_cons, sup_smul, sup_toAddSubgroup,
      ideal_span_singleton_smul, pointwise_smul_toA

中文:
引理 _root_.加法半群态射.map_smul_top_toAddSubgroup_of_surjective
  证明: by
  induction h with
  | nil =>
    convert! AddSubgroup.map_bot f using 1 <;>
      rw [Ideal.ofList_nil]; rw [bot_smul]; rw [bot_toAddSubgroup]
  | @cons r s _ _ h _ ih =>
    conv => congr <;> rw [Ideal.ofList_cons, sup_smul, sup_toAddSubgroup,
      ideal_span_singleton_smul, pointwise_smul_toA
-/
private lemma _root_.AddHom.map_smul_top_toAddSubgroup_of_surjective
    {f : M ->+ M₂} {as : List R} {bs : List S} (hf : Function.Surjective f)
    (h : List.Forall₂ (fun r s => forall x, f (r • x) = s • f x) as bs) :
    (Ideal.ofList as • ⊤ : Submodule R M).toAddSubgroup.map f =
      (Ideal.ofList bs • ⊤ : Submodule S M₂).toAddSubgroup := by
  induction h with
  | nil =>
    convert! AddSubgroup.map_bot f using 1 <;>
      rw [Ideal.ofList_nil]; rw [bot_smul]; rw [bot_toAddSubgroup]
  | @cons r s _ _ h _ ih =>
    conv => congr <;> rw [Ideal.ofList_cons, sup_smul, sup_toAddSubgroup,
      ideal_span_singleton_smul, pointwise_smul_toAddSubgroup,
      top_toAddSubgroup, AddSubgroup.pointwise_smul_def]
    apply DFunLike.ext (f.comp (toAddMonoidEnd R M r))
      ((toAddMonoidEnd S M₂ s).comp f) at h
    rw [AddSubgroup.map_sup]; rw [ih]; rw [map_map]; rw [h]; rw [← map_map]; rw [map_top_of_surjective f hf]

/--
lemma `_root_.AddEquiv.isWeaklyRegular_congr` / 引理 `_root_.AddEquiv.isWeaklyRegular_congr`

English:
lemma _root_.AddEquiv.isWeaklyRegular_congr
  statement: {e : M ≃+ M₂} {as bs}
  proof: by
  conv => congr <;> rw [isWeaklyRegular_iff_Fin]
  let e' i : (M ⧸ (Ideal.ofList (as.take i) • ⊤ : Submodule R M)) ≃+
      M₂ ⧸ (Ideal.ofList (bs.take i) • ⊤ : Submodule S M₂) :=
QuotientAddGroup.congr _ _ e
AddHom.map_smul_top_toAddSubgroup_of_surjective e.surjective
        List.forall₂_take i

中文:
引理 _root_.加法等价.isWeaklyRegular_congr
  结论: {e : M ≃+ M₂} {as bs}
  证明: by
  conv => congr <;> rw [isWeaklyRegular_iff_Fin]
  let e' i : (M ⧸ (Ideal.ofList (as.take i) • ⊤ : Submodule R M)) ≃+
      M₂ ⧸ (Ideal.ofList (bs.take i) • ⊤ : Submodule S M₂) :=
QuotientAddGroup.congr _ _ e
AddHom.map_smul_top_toAddSubgroup_of_surjective e.surjective
        List.forall₂_take i

Depends on / 依赖: AddHom, AddHom.map_smul_top_toAddSubgroup_of_surjective, Ideal.ofList, List.forall, QuotientAddGroup, QuotientAddGroup.congr, Submodule, as.take, bs.take, e.surjective, finCongr, forall.mpr, forall_congr, h.get, h.length_eq, isSMulRegular_congr, isWeaklyRegular_iff_Fin, length_eq, map_smul_top_toAddSubgroup_of_surjective, mkQ_surjective
-/
lemma _root_.AddEquiv.isWeaklyRegular_congr {e : M ≃+ M₂} {as bs}
    (h : List.Forall₂ (fun (r : R) (s : S) => forall x, e (r • x) = s • e x) as bs) :
    IsWeaklyRegular M as ↔ IsWeaklyRegular M₂ bs := by
  conv => congr <;> rw [isWeaklyRegular_iff_Fin]
  let e' i : (M ⧸ (Ideal.ofList (as.take i) • ⊤ : Submodule R M)) ≃+
      M₂ ⧸ (Ideal.ofList (bs.take i) • ⊤ : Submodule S M₂) :=
QuotientAddGroup.congr _ _ e
AddHom.map_smul_top_toAddSubgroup_of_surjective e.surjective
        List.forall₂_take i h
  refine (finCongr h.length_eq).forall_congr @fun _ => (e' _).isSMulRegular_congr ?_
  exact (mkQ_surjective _).forall.mpr fun _ => congrArg (mkQ _) (h.get _ _ _)

/--
lemma `_root_.LinearEquiv.isWeaklyRegular_congr'` / 引理 `_root_.LinearEquiv.isWeaklyRegular_congr'`

English:
lemma _root_.LinearEquiv.isWeaklyRegular_congr'
  given: (e : M ≃ₛₗ[σ] M₂) (rs : List R)
  proof: e.toAddEquiv.isWeaklyRegular_congr List.forall₂_map_right_iff.mpr
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

中文:
引理 _root_.线性等价.isWeaklyRegular_congr'
  条件: (e : M ≃ₛₗ[σ] M₂) (rs : 列表 R)
  证明: e.toAddEquiv.isWeaklyRegular_congr List.forall₂_map_right_iff.mpr
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

Depends on / 依赖: List.forall, _map_right_iff.mpr, _same.mpr, e.map_smul, e.toAddEquiv.isWeaklyRegular_congr, isWeaklyRegular_congr, map_smul, toAddEquiv
-/
lemma _root_.LinearEquiv.isWeaklyRegular_congr' (e : M ≃ₛₗ[σ] M₂) (rs : List R) :
    IsWeaklyRegular M rs ↔ IsWeaklyRegular M₂ (rs.map σ) :=
e.toAddEquiv.isWeaklyRegular_congr List.forall₂_map_right_iff.mpr
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

/--
lemma `_root_.LinearEquiv.isWeaklyRegular_congr` / 引理 `_root_.LinearEquiv.isWeaklyRegular_congr`

English:
lemma _root_.LinearEquiv.isWeaklyRegular_congr
  given: [Module R M₂] (e : M ≃ₗ[R] M₂) (rs : List R)
  proof: Iff.trans (e.isWeaklyRegular_congr' rs) iff_of_eq congrArg _ rs.map_id

中文:
引理 _root_.线性等价.isWeaklyRegular_congr
  条件: [模 R M₂] (e : M ≃ₗ[R] M₂) (rs : 列表 R)
  证明: Iff.trans (e.isWeaklyRegular_congr' rs) iff_of_eq congrArg _ rs.map_id

Depends on / 依赖: Iff.trans, e.isWeaklyRegular_congr, iff_of_eq, isWeaklyRegular_congr, map_id, rs.map_id
-/
lemma _root_.LinearEquiv.isWeaklyRegular_congr [Module R M₂] (e : M ≃ₗ[R] M₂) (rs : List R) :
    IsWeaklyRegular M rs ↔ IsWeaklyRegular M₂ rs :=
Iff.trans (e.isWeaklyRegular_congr' rs) iff_of_eq congrArg _ rs.map_id

/--
lemma `_root_.AddEquiv.isRegular_congr` / 引理 `_root_.AddEquiv.isRegular_congr`

English:
lemma _root_.AddEquiv.isRegular_congr
  statement: {e : M ≃+ M₂} {as bs}
  proof: by
  conv => congr <;> rw [isRegular_iff, ne_comm, ← Quotient.nontrivial_iff]
let e' := QuotientAddGroup.congr _ _ e
    AddHom.map_smul_top_toAddSubgroup_of_surjective e.surjective h
  exact and_congr (e.isWeaklyRegular_congr h) e'.nontrivial_congr

中文:
引理 _root_.加法等价.isRegular_congr
  结论: {e : M ≃+ M₂} {as bs}
  证明: by
  conv => congr <;> rw [isRegular_iff, ne_comm, ← Quotient.nontrivial_iff]
let e' := QuotientAddGroup.congr _ _ e
    AddHom.map_smul_top_toAddSubgroup_of_surjective e.surjective h
  exact and_congr (e.isWeaklyRegular_congr h) e'.nontrivial_congr

Depends on / 依赖: AddHom, AddHom.map_smul_top_toAddSubgroup_of_surjective, Quotient, Quotient.nontrivial_iff, QuotientAddGroup, QuotientAddGroup.congr, and_congr, e.isWeaklyRegular_congr, e.surjective, isRegular_iff, isWeaklyRegular_congr, map_smul_top_toAddSubgroup_of_surjective, ne_comm, nontrivial_congr, nontrivial_iff, surjective
-/
lemma _root_.AddEquiv.isRegular_congr {e : M ≃+ M₂} {as bs}
    (h : List.Forall₂ (fun (r : R) (s : S) => forall x, e (r • x) = s • e x) as bs) :
    IsRegular M as ↔ IsRegular M₂ bs := by
  conv => congr <;> rw [isRegular_iff, ne_comm, ← Quotient.nontrivial_iff]
let e' := QuotientAddGroup.congr _ _ e
    AddHom.map_smul_top_toAddSubgroup_of_surjective e.surjective h
  exact and_congr (e.isWeaklyRegular_congr h) e'.nontrivial_congr

/--
lemma `_root_.LinearEquiv.isRegular_congr'` / 引理 `_root_.LinearEquiv.isRegular_congr'`

English:
lemma _root_.LinearEquiv.isRegular_congr'
  given: (e : M ≃ₛₗ[σ] M₂) (rs : List R)
  proof: e.toAddEquiv.isRegular_congr List.forall₂_map_right_iff.mpr
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

中文:
引理 _root_.线性等价.isRegular_congr'
  条件: (e : M ≃ₛₗ[σ] M₂) (rs : 列表 R)
  证明: e.toAddEquiv.isRegular_congr List.forall₂_map_right_iff.mpr
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

Depends on / 依赖: List.forall, _map_right_iff.mpr, _same.mpr, e.map_smul, e.toAddEquiv.isRegular_congr, isRegular_congr, map_smul, toAddEquiv
-/
lemma _root_.LinearEquiv.isRegular_congr' (e : M ≃ₛₗ[σ] M₂) (rs : List R) :
    IsRegular M rs ↔ IsRegular M₂ (rs.map σ) :=
e.toAddEquiv.isRegular_congr List.forall₂_map_right_iff.mpr
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

/--
lemma `_root_.LinearEquiv.isRegular_congr` / 引理 `_root_.LinearEquiv.isRegular_congr`

English:
lemma _root_.LinearEquiv.isRegular_congr
  given: [Module R M₂] (e : M ≃ₗ[R] M₂) (rs : List R)
  proof: Iff.trans (e.isRegular_congr' rs) iff_of_eq congrArg _ rs.map_id

中文:
引理 _root_.线性等价.isRegular_congr
  条件: [模 R M₂] (e : M ≃ₗ[R] M₂) (rs : 列表 R)
  证明: Iff.trans (e.isRegular_congr' rs) iff_of_eq congrArg _ rs.map_id

Depends on / 依赖: Iff.trans, e.isRegular_congr, iff_of_eq, isRegular_congr, map_id, rs.map_id
-/
lemma _root_.LinearEquiv.isRegular_congr [Module R M₂] (e : M ≃ₗ[R] M₂) (rs : List R) :
    IsRegular M rs ↔ IsRegular M₂ rs :=
Iff.trans (e.isRegular_congr' rs) iff_of_eq congrArg _ rs.map_id

end Congr

/--
lemma `isWeaklyRegular_map_algebraMap_iff` / 引理 `isWeaklyRegular_map_algebraMap_iff`

English:
lemma isWeaklyRegular_map_algebraMap_iff
  statement: [CommRing R] [CommRing S]
  proof: (AddEquiv.refl M).isWeaklyRegular_congr List.forall₂_map_left_iff.mpr
    List.forall₂_same.mpr fun r _ => algebraMap_smul S r

中文:
引理 isWeaklyRegular_map_algebraMap_iff
  结论: [交换环 R] [交换环 S]
  证明: (AddEquiv.refl M).isWeaklyRegular_congr List.forall₂_map_left_iff.mpr
    List.forall₂_same.mpr fun r _ => algebraMap_smul S r

Depends on / 依赖: AddEquiv, AddEquiv.refl, List.forall, _map_left_iff.mpr, _same.mpr, algebraMap_smul, isWeaklyRegular_congr
-/
lemma isWeaklyRegular_map_algebraMap_iff [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (rs : List R) :
    IsWeaklyRegular M (rs.map (algebraMap R S)) ↔ IsWeaklyRegular M rs :=
(AddEquiv.refl M).isWeaklyRegular_congr List.forall₂_map_left_iff.mpr
    List.forall₂_same.mpr fun r _ => algebraMap_smul S r

variable [CommRing R] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
    [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

@[simp]
/--
lemma `isWeaklyRegular_cons_iff` / 引理 `isWeaklyRegular_cons_iff`

English:
lemma isWeaklyRegular_cons_iff
  given: (r : R) (rs : List R)
  proof: have := Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
  let e i := quotOfListConsSMulTopEquivQuotSMulTopInner M r (rs.take i)
Iff.trans (isWeaklyRegular_iff_Fin _ _) Iff.trans Fin.forall_iff_succ
and_congr ((quotEquivOfEqBot _ this).isSMulRegular_congr r)
      Iff.trans (forall_congr' f

中文:
引理 isWeaklyRegular_cons_iff
  条件: (r : R) (rs : 列表 R)
  证明: have := Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
  let e i := quotOfListConsSMulTopEquivQuotSMulTopInner M r (rs.take i)
Iff.trans (isWeaklyRegular_iff_Fin _ _) Iff.trans Fin.forall_iff_succ
and_congr ((quotEquivOfEqBot _ this).isSMulRegular_congr r)
      Iff.trans (forall_congr' f

Depends on / 依赖: Eq.trans, Fin.forall_iff_succ, Ideal.ofList_nil, Iff.trans, and_congr, bot_smul, forall_congr, forall_iff_succ, isSMulRegular_congr, isWeaklyRegular_iff_Fin, ofList_nil, quotEquivOfEqBot, quotOfListConsSMulTopEquivQuotSMulTopInner, rs.get, rs.take
-/
lemma isWeaklyRegular_cons_iff (r : R) (rs : List R) :
    IsWeaklyRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsWeaklyRegular (QuotSMulTop r M) rs :=
  have := Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
  let e i := quotOfListConsSMulTopEquivQuotSMulTopInner M r (rs.take i)
Iff.trans (isWeaklyRegular_iff_Fin _ _) Iff.trans Fin.forall_iff_succ
and_congr ((quotEquivOfEqBot _ this).isSMulRegular_congr r)
      Iff.trans (forall_congr' fun i => (e i).isSMulRegular_congr (rs.get i))
        (isWeaklyRegular_iff_Fin _ _).symm

/--
lemma `isWeaklyRegular_cons_iff'` / 引理 `isWeaklyRegular_cons_iff'`

English:
lemma isWeaklyRegular_cons_iff'
  given: (r : R) (rs : List R)
  proof: Iff.trans (isWeaklyRegular_cons_iff M r rs) and_congr_right'
Iff.symm isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {r}) _ rs

@[simp]

中文:
引理 isWeaklyRegular_cons_iff'
  条件: (r : R) (rs : 列表 R)
  证明: Iff.trans (isWeaklyRegular_cons_iff M r rs) and_congr_right'
Iff.symm isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {r}) _ rs

@[simp]

Depends on / 依赖: Ideal.span, Iff.symm, Iff.trans, and_congr_right, isWeaklyRegular_cons_iff, isWeaklyRegular_map_algebraMap_iff
-/
lemma isWeaklyRegular_cons_iff' (r : R) (rs : List R) :
    IsWeaklyRegular M (r :: rs) ↔
      IsSMulRegular M r ∧
        IsWeaklyRegular (QuotSMulTop r M)
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) :=
Iff.trans (isWeaklyRegular_cons_iff M r rs) and_congr_right'
Iff.symm isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {r}) _ rs

@[simp]
/--
lemma `isRegular_cons_iff` / 引理 `isRegular_cons_iff`

English:
lemma isRegular_cons_iff
  given: (r : R) (rs : List R)
  proof: by
  rw [isRegular_iff]; rw [isRegular_iff]; rw [isWeaklyRegular_cons_iff M r rs]; rw [ne_eq]; rw [top_eq_ofList_cons_smul_iff]; rw [and_assoc]

中文:
引理 isRegular_cons_iff
  条件: (r : R) (rs : 列表 R)
  证明: by
  rw [isRegular_iff]; rw [isRegular_iff]; rw [isWeaklyRegular_cons_iff M r rs]; rw [ne_eq]; rw [top_eq_ofList_cons_smul_iff]; rw [and_assoc]

Depends on / 依赖: and_assoc, isRegular_iff, isWeaklyRegular_cons_iff, ne_eq, top_eq_ofList_cons_smul_iff
-/
lemma isRegular_cons_iff (r : R) (rs : List R) :
    IsRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsRegular (QuotSMulTop r M) rs := by
  rw [isRegular_iff]; rw [isRegular_iff]; rw [isWeaklyRegular_cons_iff M r rs]; rw [ne_eq]; rw [top_eq_ofList_cons_smul_iff]; rw [and_assoc]

/--
lemma `isRegular_cons_iff'` / 引理 `isRegular_cons_iff'`

English:
lemma isRegular_cons_iff'
  given: (r : R) (rs : List R)
  proof: by
  conv => congr <;> rw [isRegular_iff, ne_eq]
  rw [isWeaklyRegular_cons_iff']; rw [← restrictScalars_inj R (R ⧸ _)]; rw [← Ideal.map_ofList]; rw [← Ideal.Quotient.algebraMap_eq]; rw [Ideal.smul_restrictScalars]; rw [restrictScalars_top]; rw [top_eq_ofList_cons_smul_iff]; rw [and_assoc]

中文:
引理 isRegular_cons_iff'
  条件: (r : R) (rs : 列表 R)
  证明: by
  conv => congr <;> rw [isRegular_iff, ne_eq]
  rw [isWeaklyRegular_cons_iff']; rw [← restrictScalars_inj R (R ⧸ _)]; rw [← Ideal.map_ofList]; rw [← Ideal.Quotient.algebraMap_eq]; rw [Ideal.smul_restrictScalars]; rw [restrictScalars_top]; rw [top_eq_ofList_cons_smul_iff]; rw [and_assoc]

Depends on / 依赖: Ideal.Quotient.algebraMap_eq, Ideal.map_ofList, Ideal.smul_restrictScalars, Quotient, algebraMap_eq, and_assoc, isRegular_iff, isWeaklyRegular_cons_iff, map_ofList, ne_eq, restrictScalars_inj, restrictScalars_top, smul_restrictScalars, top_eq_ofList_cons_smul_iff
-/
lemma isRegular_cons_iff' (r : R) (rs : List R) :
    IsRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsRegular (QuotSMulTop r M)
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  conv => congr <;> rw [isRegular_iff, ne_eq]
  rw [isWeaklyRegular_cons_iff']; rw [← restrictScalars_inj R (R ⧸ _)]; rw [← Ideal.map_ofList]; rw [← Ideal.Quotient.algebraMap_eq]; rw [Ideal.smul_restrictScalars]; rw [restrictScalars_top]; rw [top_eq_ofList_cons_smul_iff]; rw [and_assoc]

variable {M}

namespace IsWeaklyRegular

variable (R M) in
/--
lemma `nil` / 引理 `nil`

English:
lemma nil
  statement: IsWeaklyRegular M ([] : List R)
  proof: .mk (False.elim <| Nat.not_lt_zero · ·)

中文:
引理 nil
  结论: 是WeaklyRegular M ([] : 列表 R)
  证明: .mk (False.elim <| Nat.not_lt_zero · ·)
-/
@[simp] lemma nil : IsWeaklyRegular M ([] : List R) :=
  .mk (False.elim <| Nat.not_lt_zero · ·)

/--
lemma `cons` / 引理 `cons`

English:
lemma cons
  statement: {r : R} {rs : List R} (h1 : IsSMulRegular M r)
  proof: (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

中文:
引理 cons
  结论: {r : R} {rs : 列表 R} (h1 : IsSMulRegular M r)
  证明: (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

Depends on / 依赖: isWeaklyRegular_cons_iff
-/
lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (QuotSMulTop r M) rs) : IsWeaklyRegular M (r :: rs) :=
  (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

/--
lemma `cons'` / 引理 `cons'`

English:
lemma cons'
  statement: {r : R} {rs : List R} (h1 : IsSMulRegular M r)
  proof: (isWeaklyRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

中文:
引理 cons'
  结论: {r : R} {rs : 列表 R} (h1 : IsSMulRegular M r)
  证明: (isWeaklyRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

Depends on / 依赖: isWeaklyRegular_cons_iff
-/
lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (QuotSMulTop r M)
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsWeaklyRegular M (r :: rs) :=
  (isWeaklyRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

/-- Weakly regular sequences can be inductively characterized by:
* The empty sequence is weakly regular on any module.
* If `r` is regular on `M` and `rs` is a weakly regular sequence on `M⧸rM` then
  the sequence obtained from `rs` by prepending `r` is weakly regular on `M`.

This is the induction principle produced by the inductive definition above.
The motive will usually be valued in `Prop`, but `Sort*` works too. -/
@[induction_eliminator]
/--
Definition of `recIterModByRegular` / `recIterModByRegular` 的定义

English:
definition recIterModByRegular
  body: (isWeaklyRegular_cons_iff M r rs).mp h
    cons r rs h1 h2 (recIterModByRegular nil cons h2)

中文:
定义 recIterModByRegular
  定义体: (isWeaklyRegular_cons_iff M r rs).mp h
    cons r rs h1 h2 (recIterModByRegular nil cons h2)

Depends on / 依赖: isWeaklyRegular_cons_iff
-/
def recIterModByRegular
    {motive : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> (rs : List R) ->
      IsWeaklyRegular M rs -> Sort*}
    (nil : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> motive M [] (nil R M))
    (cons : {M : Type v} -> [AddCommGroup M] -> [Module R M] -> (r : R) ->
      (rs : List R) -> (h1 : IsSMulRegular M r) ->
      (h2 : IsWeaklyRegular (QuotSMulTop r M) rs) ->
      (ih : motive (QuotSMulTop r M) rs h2) -> motive M (r :: rs) (cons h1 h2)) :
    {M : Type v} -> [AddCommGroup M] -> [Module R M] -> {rs : List R} ->
    (h : IsWeaklyRegular M rs) -> motive M rs h
  | M, _, _, [], _ => nil M
  | M, _, _, r :: rs, h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff M r rs).mp h
    cons r rs h1 h2 (recIterModByRegular nil cons h2)

/--
Definition of `ndrecIterModByRegular` / `ndrecIterModByRegular` 的定义

English:
definition ndrecIterModByRegular
  body: recIterModByRegular (motive := fun M _ _ rs _ => motive M rs) nil cons

中文:
定义 ndrecIterModByRegular
  定义体: recIterModByRegular (motive := fun M _ _ rs _ => motive M rs) nil cons

Depends on / 依赖: motive, recIterModByRegular
-/
def ndrecIterModByRegular
    {motive : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> (rs : List R) -> Sort*}
    (nil : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> motive M [])
    (cons : {M : Type v} -> [AddCommGroup M] -> [Module R M] -> (r : R) ->
      (rs : List R) -> IsSMulRegular M r -> IsWeaklyRegular (QuotSMulTop r M) rs ->
      motive (QuotSMulTop r M) rs -> motive M (r :: rs))
    {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs -> motive M rs :=
  recIterModByRegular (motive := fun M _ _ rs _ => motive M rs) nil cons

/--
Definition of `recIterModByRegularWithRing` / `recIterModByRegularWithRing` 的定义

English:
definition recIterModByRegularWithRing
  body: (isWeaklyRegular_cons_iff' M r rs).mp h
    cons r rs h1 h2 (recIterModByRegularWithRing nil cons h2)
  termination_by _ _ _ _ _ rs => List.length rs

中文:
定义 recIterModByRegularWithRing
  定义体: (isWeaklyRegular_cons_iff' M r rs).mp h
    cons r rs h1 h2 (recIterModByRegularWithRing nil cons h2)
  termination_by _ _ _ _ _ rs => List.length rs

Depends on / 依赖: isWeaklyRegular_cons_iff
-/
def recIterModByRegularWithRing
    {motive : (R : Type u) -> [CommRing R] -> (M : Type v) -> [AddCommGroup M] ->
      [Module R M] -> (rs : List R) -> IsWeaklyRegular M rs -> Sort*}
    (nil : (R : Type u) -> [CommRing R] -> (M : Type v) -> [AddCommGroup M] ->
      [Module R M] -> motive R M [] (nil R M))
    (cons : {R : Type u} -> [CommRing R] -> {M : Type v} -> [AddCommGroup M] ->
      [Module R M] -> (r : R) -> (rs : List R) -> (h1 : IsSMulRegular M r) ->
      (h2 : IsWeaklyRegular (QuotSMulTop r M)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) ->
      (ih : motive (R ⧸ Ideal.span {r}) (QuotSMulTop r M)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) h2) ->
            motive R M (r :: rs) (cons' h1 h2)) :
    {R : Type u} -> [CommRing R] -> {M : Type v} -> [AddCommGroup M] ->
    [Module R M] -> {rs : List R} -> (h : IsWeaklyRegular M rs) -> motive R M rs h
  | R, _, M, _, _, [], _ => nil R M
  | _, _, M, _, _, r :: rs, h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff' M r rs).mp h
    cons r rs h1 h2 (recIterModByRegularWithRing nil cons h2)
  termination_by _ _ _ _ _ rs => List.length rs

/--
Definition of `ndrecWithRing` / `ndrecWithRing` 的定义

English:
definition ndrecWithRing
  body: recIterModByRegularWithRing (motive := fun R _ M _ _ rs _ => motive R M rs)
    nil cons

中文:
定义 ndrecWithRing
  定义体: recIterModByRegularWithRing (motive := fun R _ M _ _ rs _ => motive R M rs)
    nil cons

Depends on / 依赖: motive, recIterModByRegularWithRing
-/
def ndrecWithRing
    {motive : (R : Type u) -> [CommRing R] -> (M : Type v) ->
      [AddCommGroup M] -> [Module R M] -> (rs : List R) -> Sort*}
    (nil : (R : Type u) -> [CommRing R] -> (M : Type v) ->
      [AddCommGroup M] -> [Module R M] -> motive R M [])
    (cons : {R : Type u} -> [CommRing R] -> {M : Type v} -> [AddCommGroup M] ->
      [Module R M] -> (r : R) -> (rs : List R) -> IsSMulRegular M r ->
      IsWeaklyRegular (QuotSMulTop r M)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) ->
      motive (R ⧸ Ideal.span {r}) (QuotSMulTop r M)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) -> motive R M (r :: rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs -> motive R M rs :=
  recIterModByRegularWithRing (motive := fun R _ M _ _ rs _ => motive R M rs)
    nil cons

end IsWeaklyRegular

section

variable (M)

/--
lemma `isWeaklyRegular_singleton_iff` / 引理 `isWeaklyRegular_singleton_iff`

English:
lemma isWeaklyRegular_singleton_iff
  given: (r : R)
  proof: Iff.trans (isWeaklyRegular_cons_iff M r []) (and_iff_left (.nil R _))

中文:
引理 isWeaklyRegular_singleton_iff
  条件: (r : R)
  证明: Iff.trans (isWeaklyRegular_cons_iff M r []) (and_iff_left (.nil R _))

Depends on / 依赖: Iff.trans, and_iff_left, isWeaklyRegular_cons_iff
-/
lemma isWeaklyRegular_singleton_iff (r : R) :
    IsWeaklyRegular M [r] ↔ IsSMulRegular M r :=
  Iff.trans (isWeaklyRegular_cons_iff M r []) (and_iff_left (.nil R _))

/--
lemma `isWeaklyRegular_append_iff` / 引理 `isWeaklyRegular_append_iff`

English:
lemma isWeaklyRegular_append_iff
  given: (rs₁ rs₂ : List R)
  proof: by
  induction rs₁ generalizing M with
  | nil =>
refine Iff.symm Iff.trans (and_iff_right (.nil R M)) ?_
    refine (quotEquivOfEqBot _ ?_).isWeaklyRegular_congr rs₂
    rw [Ideal.ofList_nil]; rw [bot_smul]
  | cons r rs₁ ih =>
    let e := quotOfListConsSMulTopEquivQuotSMulTopInner M r rs₁
    rw 

中文:
引理 isWeaklyRegular_append_iff
  条件: (rs₁ rs₂ : 列表 R)
  证明: by
  induction rs₁ generalizing M with
  | nil =>
refine Iff.symm Iff.trans (and_iff_right (.nil R M)) ?_
    refine (quotEquivOfEqBot _ ?_).isWeaklyRegular_congr rs₂
    rw [Ideal.ofList_nil]; rw [bot_smul]
  | cons r rs₁ ih =>
    let e := quotOfListConsSMulTopEquivQuotSMulTopInner M r rs₁
    rw 

Depends on / 依赖: Ideal.ofList_nil, Iff.symm, Iff.trans, List.cons_append, and_assoc, and_iff_right, bot_smul, cons_append, e.isWeaklyRegular_congr, generalizing, isWeaklyRegular_congr, isWeaklyRegular_cons_iff, ofList_nil, quotEquivOfEqBot, quotOfListConsSMulTopEquivQuotSMulTopInner
-/
lemma isWeaklyRegular_append_iff (rs₁ rs₂ : List R) :
    IsWeaklyRegular M (rs₁ ++ rs₂) ↔
      IsWeaklyRegular M rs₁ ∧
        IsWeaklyRegular (M ⧸ (Ideal.ofList rs₁ • ⊤ : Submodule R M)) rs₂ := by
  induction rs₁ generalizing M with
  | nil =>
refine Iff.symm Iff.trans (and_iff_right (.nil R M)) ?_
    refine (quotEquivOfEqBot _ ?_).isWeaklyRegular_congr rs₂
    rw [Ideal.ofList_nil]; rw [bot_smul]
  | cons r rs₁ ih =>
    let e := quotOfListConsSMulTopEquivQuotSMulTopInner M r rs₁
    rw [List.cons_append]; rw [isWeaklyRegular_cons_iff]; rw [isWeaklyRegular_cons_iff]; rw [ih]; rw [← and_assoc]; rw [← e.isWeaklyRegular_congr rs₂]

/--
lemma `isWeaklyRegular_append_iff'` / 引理 `isWeaklyRegular_append_iff'`

English:
lemma isWeaklyRegular_append_iff'
  given: (rs₁ rs₂ : List R)
  proof: Iff.trans (isWeaklyRegular_append_iff M rs₁ rs₂) and_congr_right'
Iff.symm isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.ofList rs₁) _ rs₂

中文:
引理 isWeaklyRegular_append_iff'
  条件: (rs₁ rs₂ : 列表 R)
  证明: Iff.trans (isWeaklyRegular_append_iff M rs₁ rs₂) and_congr_right'
Iff.symm isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.ofList rs₁) _ rs₂

Depends on / 依赖: Ideal.ofList, Iff.symm, Iff.trans, and_congr_right, isWeaklyRegular_append_iff, isWeaklyRegular_map_algebraMap_iff, ofList
-/
lemma isWeaklyRegular_append_iff' (rs₁ rs₂ : List R) :
    IsWeaklyRegular M (rs₁ ++ rs₂) ↔
      IsWeaklyRegular M rs₁ ∧
        IsWeaklyRegular (M ⧸ (Ideal.ofList rs₁ • ⊤ : Submodule R M))
          (rs₂.map (Ideal.Quotient.mk (Ideal.ofList rs₁))) :=
Iff.trans (isWeaklyRegular_append_iff M rs₁ rs₂) and_congr_right'
Iff.symm isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.ofList rs₁) _ rs₂

end

namespace IsRegular

variable (R M) in
/--
lemma `nil` / 引理 `nil`

English:
lemma nil
  given: [Nontrivial M]
  statement: IsRegular M ([] : List R) where
  proof: IsWeaklyRegular.nil R M
  top_ne_smul h := by
    rw [Ideal.ofList_nil]; rw [bot_smul]; rw [eq_comm]; rw [subsingleton_iff_bot_eq_top] at h
    exact not_subsingleton M ((Submodule.subsingleton_iff _).mp h)

中文:
引理 nil
  条件: [非平凡 M]
  结论: 是正则 M ([] : 列表 R) where
  证明: IsWeaklyRegular.nil R M
  top_ne_smul h := by
    rw [Ideal.ofList_nil]; rw [bot_smul]; rw [eq_comm]; rw [subsingleton_iff_bot_eq_top] at h
    exact not_subsingleton M ((Submodule.subsingleton_iff _).mp h)

Depends on / 依赖: IsWeaklyRegular, IsWeaklyRegular.nil
-/
lemma nil [Nontrivial M] : IsRegular M ([] : List R) where
  toIsWeaklyRegular := IsWeaklyRegular.nil R M
  top_ne_smul h := by
    rw [Ideal.ofList_nil]; rw [bot_smul]; rw [eq_comm]; rw [subsingleton_iff_bot_eq_top] at h
    exact not_subsingleton M ((Submodule.subsingleton_iff _).mp h)

/--
lemma `cons` / 引理 `cons`

English:
lemma cons
  statement: {r : R} {rs : List R} (h1 : IsSMulRegular M r)
  proof: (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

中文:
引理 cons
  结论: {r : R} {rs : 列表 R} (h1 : IsSMulRegular M r)
  证明: (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

Depends on / 依赖: isRegular_cons_iff
-/
lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (QuotSMulTop r M) rs) : IsRegular M (r :: rs) :=
  (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

/--
lemma `cons'` / 引理 `cons'`

English:
lemma cons'
  statement: {r : R} {rs : List R} (h1 : IsSMulRegular M r)
  proof: (isRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

中文:
引理 cons'
  结论: {r : R} {rs : 列表 R} (h1 : IsSMulRegular M r)
  证明: (isRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

Depends on / 依赖: isRegular_cons_iff
-/
lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (QuotSMulTop r M) (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsRegular M (r :: rs) :=
  (isRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

/-- Regular sequences can be inductively characterized by:
* The empty sequence is regular on any nonzero module.
* If `r` is regular on `M` and `rs` is a regular sequence on `M⧸rM` then the
  sequence obtained from `rs` by prepending `r` is regular on `M`.

This is the induction principle produced by the inductive definition above.
The motive will usually be valued in `Prop`, but `Sort*` works too. -/
@[induction_eliminator]
/--
Definition of `recIterModByRegular` / `recIterModByRegular` 的定义

English:
definition recIterModByRegular
  body: h.toIsWeaklyRegular.recIterModByRegular
    (motive := fun N _ _ rs' h' => forall h'', motive N rs' ⟨h', h''⟩)
    (fun N _ _ h' =>
      haveI := (nontrivial_iff R).mp (nontrivial_of_ne _ _ h'); nil N)
    (fun r rs' h1 h2 h3 h4 =>
      have ⟨h5, h6⟩ := (isRegular_cons_iff _ _ _).mp ⟨h2.cons h1, h

中文:
定义 recIterModByRegular
  定义体: h.toIsWeaklyRegular.recIterModByRegular
    (motive := fun N _ _ rs' h' => forall h'', motive N rs' ⟨h', h''⟩)
    (fun N _ _ h' =>
      haveI := (nontrivial_iff R).mp (nontrivial_of_ne _ _ h'); nil N)
    (fun r rs' h1 h2 h3 h4 =>
      have ⟨h5, h6⟩ := (isRegular_cons_iff _ _ _).mp ⟨h2.cons h1, h

Depends on / 依赖: h.toIsWeaklyRegular.recIterModByRegular, h.top_ne_smul, h2.cons, h6.top_ne_smul, isRegular_cons_iff, motive, nontrivial_iff, nontrivial_of_ne, recIterModByRegular, toIsWeaklyRegular, top_ne_smul
-/
def recIterModByRegular
    {motive : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> (rs : List R) ->
      IsRegular M rs -> Sort*}
    (nil : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> [Nontrivial M] ->
      motive M [] (nil R M))
    (cons : {M : Type v} -> [AddCommGroup M] -> [Module R M] -> (r : R) ->
      (rs : List R) -> (h1 : IsSMulRegular M r) -> (h2 : IsRegular (QuotSMulTop r M) rs) ->
      (ih : motive (QuotSMulTop r M) rs h2) -> motive M (r :: rs) (cons h1 h2))
    {M} [AddCommGroup M] [Module R M] {rs} (h : IsRegular M rs) : motive M rs h :=
  h.toIsWeaklyRegular.recIterModByRegular
    (motive := fun N _ _ rs' h' => forall h'', motive N rs' ⟨h', h''⟩)
    (fun N _ _ h' =>
      haveI := (nontrivial_iff R).mp (nontrivial_of_ne _ _ h'); nil N)
    (fun r rs' h1 h2 h3 h4 =>
      have ⟨h5, h6⟩ := (isRegular_cons_iff _ _ _).mp ⟨h2.cons h1, h4⟩
      cons r rs' h5 h6 (h3 h6.top_ne_smul))
    h.top_ne_smul

/--
Definition of `ndrecIterModByRegular` / `ndrecIterModByRegular` 的定义

English:
definition ndrecIterModByRegular
  body: recIterModByRegular (motive := fun M _ _ rs _ => motive M rs) nil cons

中文:
定义 ndrecIterModByRegular
  定义体: recIterModByRegular (motive := fun M _ _ rs _ => motive M rs) nil cons

Depends on / 依赖: motive, recIterModByRegular
-/
def ndrecIterModByRegular
    {motive : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> (rs : List R) -> Sort*}
    (nil : (M : Type v) -> [AddCommGroup M] -> [Module R M] -> [Nontrivial M] -> motive M [])
    (cons : {M : Type v} -> [AddCommGroup M] -> [Module R M] -> (r : R) ->
      (rs : List R) -> IsSMulRegular M r -> IsRegular (QuotSMulTop r M) rs ->
      motive (QuotSMulTop r M) rs -> motive M (r :: rs))
    {M} [AddCommGroup M] [Module R M] {rs} : IsRegular M rs -> motive M rs :=
  recIterModByRegular (motive := fun M _ _ rs _ => motive M rs) nil cons

/--
Definition of `recIterModByRegularWithRing` / `recIterModByRegularWithRing` 的定义

English:
definition recIterModByRegularWithRing
  body: h.toIsWeaklyRegular.recIterModByRegularWithRing
    (motive := fun R _ N _ _ rs' h' => forall h'', motive R N rs' ⟨h', h''⟩)
    (fun R _ N _ _ h' =>
      haveI := (nontrivial_iff R).mp (nontrivial_of_ne _ _ h'); nil R N)
    (fun r rs' h1 h2 h3 h4 =>
      have ⟨h5, h6⟩ := (isRegular_cons_iff' _ _

中文:
定义 recIterModByRegularWithRing
  定义体: h.toIsWeaklyRegular.recIterModByRegularWithRing
    (motive := fun R _ N _ _ rs' h' => forall h'', motive R N rs' ⟨h', h''⟩)
    (fun R _ N _ _ h' =>
      haveI := (nontrivial_iff R).mp (nontrivial_of_ne _ _ h'); nil R N)
    (fun r rs' h1 h2 h3 h4 =>
      have ⟨h5, h6⟩ := (isRegular_cons_iff' _ _

Depends on / 依赖: h.toIsWeaklyRegular.recIterModByRegularWithRing, h.top_ne_smul, h2.cons, h6.top_ne_smul, isRegular_cons_iff, motive, nontrivial_iff, nontrivial_of_ne, recIterModByRegularWithRing, toIsWeaklyRegular, top_ne_smul
-/
def recIterModByRegularWithRing
    {motive : (R : Type u) -> [CommRing R] -> (M : Type v) -> [AddCommGroup M] ->
      [Module R M] -> (rs : List R) -> IsRegular M rs -> Sort*}
    (nil : (R : Type u) -> [CommRing R] -> (M : Type v) -> [AddCommGroup M] ->
      [Module R M] -> [Nontrivial M] -> motive R M [] (nil R M))
    (cons : {R : Type u} -> [CommRing R] -> {M : Type v} -> [AddCommGroup M] ->
      [Module R M] -> (r : R) -> (rs : List R) -> (h1 : IsSMulRegular M r) ->
      (h2 : IsRegular (QuotSMulTop r M)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) ->
      (ih : motive (R ⧸ Ideal.span {r}) (QuotSMulTop r M)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) h2) ->
            motive R M (r :: rs) (cons' h1 h2))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs}
    (h : IsRegular M rs) : motive R M rs h :=
  h.toIsWeaklyRegular.recIterModByRegularWithRing
    (motive := fun R _ N _ _ rs' h' => forall h'', motive R N rs' ⟨h', h''⟩)
    (fun R _ N _ _ h' =>
      haveI := (nontrivial_iff R).mp (nontrivial_of_ne _ _ h'); nil R N)
    (fun r rs' h1 h2 h3 h4 =>
      have ⟨h5, h6⟩ := (isRegular_cons_iff' _ _ _).mp ⟨h2.cons' h1, h4⟩
cons r rs' h5 h6 h3 h6.top_ne_smul)
    h.top_ne_smul

/--
Definition of `ndrecIterModByRegularWithRing` / `ndrecIterModByRegularWithRing` 的定义

English:
definition ndrecIterModByRegularWithRing
  body: recIterModByRegularWithRing (motive := fun R _ M _ _ rs _ => motive R M rs)
    nil cons

中文:
定义 ndrecIterModByRegularWithRing
  定义体: recIterModByRegularWithRing (motive := fun R _ M _ _ rs _ => motive R M rs)
    nil cons

Depends on / 依赖: Subtype, Subtype.coe_preimage_self, coe_preimage_self, motive, recIterModByRegularWithRing
-/
def ndrecIterModByRegularWithRing
    {motive : (R : Type u) -> [CommRing R] -> (M : Type v) ->
      [AddCommGroup M] -> [Module R M] -> (rs : List R) -> Sort*}
    (nil : (R : Type u) -> [CommRing R] -> (M : Type v) ->
      [AddCommGroup M] -> [Module R M] -> [Nontrivial M] -> motive R M [])
    (cons : {R : Type u} -> [CommRing R] -> {M : Type v} ->
      [AddCommGroup M] -> [Module R M] -> (r : R) -> (rs : List R) ->
      IsSMulRegular M r ->
      IsRegular (QuotSMulTop r M)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) ->
      motive (R ⧸ Ideal.span {r}) (QuotSMulTop r M)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) ->
      motive R M (r :: rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsRegular M rs -> motive R M rs :=
  recIterModByRegularWithRing (motive := fun R _ M _ _ rs _ => motive R M rs)
    nil cons

/--
lemma `quot_ofList_smul_nontrivial` / 引理 `quot_ofList_smul_nontrivial`

English:
lemma quot_ofList_smul_nontrivial
  statement: {rs : List R} (h : IsRegular M rs)
  proof: Submodule.Quotient.nontrivial_iff.mpr
    ne_top_of_le_ne_top h.top_ne_smul.symm (smul_mono_right _ le_top)

中文:
引理 quot_ofList_smul_nontrivial
  结论: {rs : 列表 R} (h : 是正则 M rs)
  证明: Submodule.Quotient.nontrivial_iff.mpr
    ne_top_of_le_ne_top h.top_ne_smul.symm (smul_mono_right _ le_top)

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.nontrivial_iff.mpr, h.top_ne_smul.symm, le_top, ne_top_of_le_ne_top, nontrivial_iff, smul_mono_right, top_ne_smul
-/
lemma quot_ofList_smul_nontrivial {rs : List R} (h : IsRegular M rs)
    (N : Submodule R M) : Nontrivial (M ⧸ Ideal.ofList rs • N) :=
Submodule.Quotient.nontrivial_iff.mpr
    ne_top_of_le_ne_top h.top_ne_smul.symm (smul_mono_right _ le_top)

/--
lemma `nontrivial` / 引理 `nontrivial`

English:
lemma nontrivial
  given: {rs : List R} (h : IsRegular M rs)
  statement: Nontrivial M
  proof: haveI := quot_ofList_smul_nontrivial h ⊤
  (mkQ_surjective (Ideal.ofList rs • ⊤ : Submodule R M)).nontrivial

中文:
引理 nontrivial
  条件: {rs : 列表 R} (h : 是正则 M rs)
  结论: 非平凡 M
  证明: haveI := quot_ofList_smul_nontrivial h ⊤
  (mkQ_surjective (Ideal.ofList rs • ⊤ : Submodule R M)).nontrivial

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.ext, Functor, Ideal.ofList, Submodule, mkQ_surjective, nontrivial, ofList, quot_ofList_smul_nontrivial, subsingleton
-/
lemma nontrivial {rs : List R} (h : IsRegular M rs) : Nontrivial M :=
  haveI := quot_ofList_smul_nontrivial h ⊤
  (mkQ_surjective (Ideal.ofList rs • ⊤ : Submodule R M)).nontrivial

end IsRegular

/--
lemma `isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator` / 引理 `isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator`

English:
lemma isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator
  proof: Iff.trans (isRegular_iff M rs) and_iff_left
top_ne_ideal_smul_of_le_jacobson_annihilator Ideal.span_le.mpr h

中文:
引理 isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator
  证明: Iff.trans (isRegular_iff M rs) and_iff_left
top_ne_ideal_smul_of_le_jacobson_annihilator Ideal.span_le.mpr h

Depends on / 依赖: Ideal.span_le.mpr, Iff.trans, and_iff_left, isRegular_iff, span_le, top_ne_ideal_smul_of_le_jacobson_annihilator
-/
lemma isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator
    [Nontrivial M] [Module.Finite R M] {rs : List R}
    (h : forall r in rs, r in Ideal.jacobson (Module.annihilator R M)) :
    IsRegular M rs ↔ IsWeaklyRegular M rs :=
Iff.trans (isRegular_iff M rs) and_iff_left
top_ne_ideal_smul_of_le_jacobson_annihilator Ideal.span_le.mpr h

/--
lemma `_root_.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal` / 引理 `_root_.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`

English:
lemma _root_.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
  proof: have H h' := bot_ne_top.symm annihilator_eq_top_iff.mp
    Eq.trans annihilator_top h'
  isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator fun r hr =>
    IsLocalRing.jacobson_eq_maximalIdeal (Module.annihilator R M) H ▸ h r hr

中文:
引理 _root_.是局部环.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
  证明: have H h' := bot_ne_top.symm annihilator_eq_top_iff.mp
    Eq.trans annihilator_top h'
  isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator fun r hr =>
    IsLocalRing.jacobson_eq_maximalIdeal (Module.annihilator R M) H ▸ h r hr

Depends on / 依赖: Eq.trans, IsLocalRing, IsLocalRing.jacobson_eq_maximalIdeal, Module, Module.annihilator, annihilator, annihilator_eq_top_iff, annihilator_eq_top_iff.mp, annihilator_top, bot_ne_top, bot_ne_top.symm, isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator, jacobson_eq_maximalIdeal
-/
lemma _root_.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    [IsLocalRing R] [Nontrivial M] [Module.Finite R M] {rs : List R}
    (h : forall r in rs, r in IsLocalRing.maximalIdeal R) :
    IsRegular M rs ↔ IsWeaklyRegular M rs :=
have H h' := bot_ne_top.symm annihilator_eq_top_iff.mp
    Eq.trans annihilator_top h'
  isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator fun r hr =>
    IsLocalRing.jacobson_eq_maximalIdeal (Module.annihilator R M) H ▸ h r hr

open IsWeaklyRegular IsArtinian in
/--
lemma `eq_nil_of_isRegular_on_artinian` / 引理 `eq_nil_of_isRegular_on_artinian`

English:
lemma eq_nil_of_isRegular_on_artinian
  given: [IsArtinian R M]

中文:
引理 eq_nil_of_isRegular_on_artinian
  条件: [是Artin R M]
-/
lemma eq_nil_of_isRegular_on_artinian [IsArtinian R M] :
    {rs : List R} -> IsRegular M rs -> rs = []
  | [], _ => rfl
  | r :: rs, h => by
    rw [isRegular_iff]; rw [ne_comm]; rw [← lt_top_iff_ne_top]; rw [Ideal.ofList_cons]; rw [sup_smul]; rw [ideal_span_singleton_smul]; rw [isWeaklyRegular_cons_iff] at h
    refine absurd ?_ (ne_of_lt (lt_of_le_of_lt le_sup_left h.right))
exact Eq.trans (Submodule.map_top _) LinearMap.range_eq_top.mpr
      surjective_of_injective_endomorphism (LinearMap.lsmul R M r) h.left.left

/--
lemma `IsWeaklyRegular.isWeaklyRegular_lTensor` / 引理 `IsWeaklyRegular.isWeaklyRegular_lTensor`

English:
lemma IsWeaklyRegular.isWeaklyRegular_lTensor
  statement: [Module.Flat R M₂]
  proof: by
  induction h with
  | nil N => exact nil R (M₂ otimes[R] N)
  | @cons N _ _ r rs' h1 _ ih =>
    let e := tensorQuotSMulTopEquivQuotSMulTop r M₂ N
    exact ((e.isWeaklyRegular_congr rs').mp ih).cons (h1.lTensor M₂)

中文:
引理 是WeaklyRegular.isWeaklyRegular_lTensor
  结论: [模.平坦 R M₂]
  证明: by
  induction h with
  | nil N => exact nil R (M₂ otimes[R] N)
  | @cons N _ _ r rs' h1 _ ih =>
    let e := tensorQuotSMulTopEquivQuotSMulTop r M₂ N
    exact ((e.isWeaklyRegular_congr rs').mp ih).cons (h1.lTensor M₂)

Depends on / 依赖: e.isWeaklyRegular_congr, h1.lTensor, isWeaklyRegular_congr, lTensor, otimes, tensorQuotSMulTopEquivQuotSMulTop
-/
lemma IsWeaklyRegular.isWeaklyRegular_lTensor [Module.Flat R M₂]
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M₂ otimes[R] M) rs := by
  induction h with
  | nil N => exact nil R (M₂ otimes[R] N)
  | @cons N _ _ r rs' h1 _ ih =>
    let e := tensorQuotSMulTopEquivQuotSMulTop r M₂ N
    exact ((e.isWeaklyRegular_congr rs').mp ih).cons (h1.lTensor M₂)

/--
lemma `IsWeaklyRegular.isWeaklyRegular_rTensor` / 引理 `IsWeaklyRegular.isWeaklyRegular_rTensor`

English:
lemma IsWeaklyRegular.isWeaklyRegular_rTensor
  statement: [Module.Flat R M₂]
  proof: by
  induction h with
  | nil N => exact nil R (N otimes[R] M₂)
  | @cons N _ _ r rs' h1 _ ih =>
    let e := quotSMulTopTensorEquivQuotSMulTop r M₂ N
    exact ((e.isWeaklyRegular_congr rs').mp ih).cons (h1.rTensor M₂)

中文:
引理 是WeaklyRegular.isWeaklyRegular_rTensor
  结论: [模.平坦 R M₂]
  证明: by
  induction h with
  | nil N => exact nil R (N otimes[R] M₂)
  | @cons N _ _ r rs' h1 _ ih =>
    let e := quotSMulTopTensorEquivQuotSMulTop r M₂ N
    exact ((e.isWeaklyRegular_congr rs').mp ih).cons (h1.rTensor M₂)

Depends on / 依赖: e.isWeaklyRegular_congr, h1.rTensor, isWeaklyRegular_congr, otimes, quotSMulTopTensorEquivQuotSMulTop, rTensor
-/
lemma IsWeaklyRegular.isWeaklyRegular_rTensor [Module.Flat R M₂]
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M otimes[R] M₂) rs := by
  induction h with
  | nil N => exact nil R (N otimes[R] M₂)
  | @cons N _ _ r rs' h1 _ ih =>
    let e := quotSMulTopTensorEquivQuotSMulTop r M₂ N
    exact ((e.isWeaklyRegular_congr rs').mp ih).cons (h1.rTensor M₂)
-- TODO: apply the above to localization and completion (Corollary 1.1.3 in B&H)

/--
lemma `map_first_exact_on_four_term_right_exact_of_isSMulRegular_last` / 引理 `map_first_exact_on_four_term_right_exact_of_isSMulRegular_last`

English:
lemma map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
  proof: by
  induction h₄ generalizing M M₂ M₃ with
  | nil =>
    apply (Exact.iff_of_ladder_linearEquiv ?_ ?_).mp h₁₂
any_goals exact quotEquivOfEqBot _
      Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
    all_goals exact quot_hom_ext _ _ _ fun _ => rfl
  | cons r rs h₄ _ ih =>
    speciali

中文:
引理 map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
  证明: by
  induction h₄ generalizing M M₂ M₃ with
  | nil =>
    apply (Exact.iff_of_ladder_linearEquiv ?_ ?_).mp h₁₂
any_goals exact quotEquivOfEqBot _
      Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
    all_goals exact quot_hom_ext _ _ _ fun _ => rfl
  | cons r rs h₄ _ ih =>
    speciali

Depends on / 依赖: Eq.trans, Exact.iff_of_ladder_linearEquiv, Ideal.ofList_nil, all_goals, any_goals, bot_smul, generalizing, iff_of_ladder_linearEquiv, map_exact, map_first_exact_on_four_term_exact_of_isSMulRegular_last, map_surjective, ofList_nil, quotEquivOfEqBot, quotOfListConsSMulTop, quotOfListConsSMulTopEquivQuotSMulTopInner_naturality, quot_hom_ext, specialize
-/
lemma map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    {rs : List R} {f₁ : M ->ₗ[R] M₂} {f₂ : M₂ ->ₗ[R] M₃} {f₃ : M₃ ->ₗ[R] M₄}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h₃ : Surjective f₃)
    (h₄ : IsWeaklyRegular M₄ rs) :
    Exact (mapQ _ _ _ (smul_top_le_comap_smul_top (Ideal.ofList rs) f₁))
          (mapQ _ _ _ (smul_top_le_comap_smul_top (Ideal.ofList rs) f₂)) := by
  induction h₄ generalizing M M₂ M₃ with
  | nil =>
    apply (Exact.iff_of_ladder_linearEquiv ?_ ?_).mp h₁₂
any_goals exact quotEquivOfEqBot _
      Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
    all_goals exact quot_hom_ext _ _ _ fun _ => rfl
  | cons r rs h₄ _ ih =>
    specialize ih
      (map_first_exact_on_four_term_exact_of_isSMulRegular_last h₁₂ h₂₃ h₄)
      (map_exact r h₂₃ h₃) (map_surjective r h₃)
    have H₁ := quotOfListConsSMulTopEquivQuotSMulTopInner_naturality r rs f₁
    have H₂ := quotOfListConsSMulTopEquivQuotSMulTopInner_naturality r rs f₂
    exact (Exact.iff_of_ladder_linearEquiv H₁.symm H₂.symm).mp ih

-- todo: modding out a complex by a regular sequence (prop 1.1.5 in B&H)

section Perm

set_option backward.isDefEq.respectTransparency.types false in
open _root_.LinearMap in
/--
lemma `IsWeaklyRegular.swap` / 引理 `IsWeaklyRegular.swap`

English:
lemma IsWeaklyRegular.swap
  statement: {a b : R} (h1 : IsWeaklyRegular M [a, b])
  proof: by
  rw [isWeaklyRegular_cons_iff]; rw [isWeaklyRegular_singleton_iff] at h1 ⊢
  obtain ⟨ha, hb⟩ := h1
  rw [← isSMulRegular_iff_torsionBy_eq_bot] at h2
  specialize h2 (le_antisymm ?_ (smul_le_self_of_tower a (torsionBy R M b)))
· refine le_of_eq_of_le ?_ smul_top_inf_eq_smul_of_isSMulRegular_on_qu

中文:
引理 是WeaklyRegular.swap
  结论: {a b : R} (h1 : 是WeaklyRegular M [a, b])
  证明: by
  rw [isWeaklyRegular_cons_iff]; rw [isWeaklyRegular_singleton_iff] at h1 ⊢
  obtain ⟨ha, hb⟩ := h1
  rw [← isSMulRegular_iff_torsionBy_eq_bot] at h2
  specialize h2 (le_antisymm ?_ (smul_le_self_of_tower a (torsionBy R M b)))
· refine le_of_eq_of_le ?_ smul_top_inf_eq_smul_of_isSMulRegular_on_qu

Depends on / 依赖: Discrete, Discrete.range_functor, Fan.mk_pt, Limits, Limits.Fan.isLimitMapConeEquiv, Preorder, Preorder.isLimitIInf, Preorder.isLimitOfIsGLB, allowSynthFailures, functor_obj_iInf, hf.functor_obj_iInf, homOfLE_leOfHom, isGLB_iInf, isLimitIInf, isLimitMapConeEquiv, isLimitOfIsGLB, mk_pt, preservesLimit_of_preserves_limit_cone, preservesLimitsOfShape_of_discrete, range_functor
-/
private lemma IsWeaklyRegular.swap {a b : R} (h1 : IsWeaklyRegular M [a, b])
    (h2 : torsionBy R M b = a • torsionBy R M b -> torsionBy R M b = ⊥) :
    IsWeaklyRegular M [b, a] := by
  rw [isWeaklyRegular_cons_iff]; rw [isWeaklyRegular_singleton_iff] at h1 ⊢
  obtain ⟨ha, hb⟩ := h1
  rw [← isSMulRegular_iff_torsionBy_eq_bot] at h2
  specialize h2 (le_antisymm ?_ (smul_le_self_of_tower a (torsionBy R M b)))
· refine le_of_eq_of_le ?_ smul_top_inf_eq_smul_of_isSMulRegular_on_quot
ha.of_injective _ ker_eq_bot.mp ker_liftQ_eq_bot' _ (lsmul R M b) rfl
    rw [← (isSMulRegular_on_quot_iff_lsmul_comap_eq _ _).mp hb]
    exact (inf_eq_right.mpr (ker_le_comap _)).symm
  · rwa [ha.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul, inf_comm, smul_comm,
      ← h2.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul, and_iff_left hb]

-- TODO: Equivalence of permutability of regular sequences to regularity of
-- subsequences and regularity on poly ring. See [07DW] in stacks project
-- We need a theory of multivariate polynomial modules first

/--
lemma `IsWeaklyRegular.prototype_perm` / 引理 `IsWeaklyRegular.prototype_perm`

English:
lemma IsWeaklyRegular.prototype_perm
  statement: {rs : List R} (h : IsWeaklyRegular M rs)
  proof: have H := LinearEquiv.isWeaklyRegular_congr quotEquivOfEqBot _
    Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
(H rs').mp (aux [] h'' (.refl rs) (h''.symm.subperm)) (H rs).mpr h
  where aux {rs₁ rs₂} (rs₀ : List R)
    (h₁₂ : rs₁ ~ rs₂) (H₁ : rs₀ ++ rs₁ <+~ rs) (H₃ : rs₀ ++ rs₂ <+~ rs)

中文:
引理 是WeaklyRegular.prototype_perm
  结论: {rs : 列表 R} (h : 是WeaklyRegular M rs)
  证明: have H := LinearEquiv.isWeaklyRegular_congr quotEquivOfEqBot _
    Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
(H rs').mp (aux [] h'' (.refl rs) (h''.symm.subperm)) (H rs).mpr h
  where aux {rs₁ rs₂} (rs₀ : List R)
    (h₁₂ : rs₁ ~ rs₂) (H₁ : rs₀ ++ rs₁ <+~ rs) (H₃ : rs₀ ++ rs₂ <+~ rs)

Depends on / 依赖: Ideal.ofList, Submodule, ofList, torsionBy
-/
lemma IsWeaklyRegular.prototype_perm {rs : List R} (h : IsWeaklyRegular M rs)
    {rs'} (h'' : rs ~ rs') (h' : forall a b rs', (a :: b :: rs') <+~ rs ->
      let K := torsionBy R (M ⧸ (Ideal.ofList rs' • ⊤ : Submodule R M)) b
      K = a • K -> K = ⊥) : IsWeaklyRegular M rs' :=
have H := LinearEquiv.isWeaklyRegular_congr quotEquivOfEqBot _
    Eq.trans (congrArg (· • ⊤) Ideal.ofList_nil) (bot_smul ⊤)
(H rs').mp (aux [] h'' (.refl rs) (h''.symm.subperm)) (H rs).mpr h
  where aux {rs₁ rs₂} (rs₀ : List R)
    (h₁₂ : rs₁ ~ rs₂) (H₁ : rs₀ ++ rs₁ <+~ rs) (H₃ : rs₀ ++ rs₂ <+~ rs)
    (h : IsWeaklyRegular (M ⧸ (Ideal.ofList rs₀ • ⊤ : Submodule R M)) rs₁) :
    IsWeaklyRegular (M ⧸ (Ideal.ofList rs₀ • ⊤ : Submodule R M)) rs₂ := by {
  induction h₁₂ generalizing rs₀ with
  | nil => exact .nil R _
  | cons r _ ih =>
    let e := quotOfListConsSMulTopEquivQuotSMulTopOuter M r rs₀
    rw [isWeaklyRegular_cons_iff]; rw [← e.isWeaklyRegular_congr] at h ⊢
    refine h.imp_right (ih (r :: rs₀) ?_ ?_) <;>
      exact List.perm_middle.subperm_right.mp ‹_›
  | swap a b t =>
    rw [show forall x y z]; rw [x :: y :: z = [x]; rw [y] ++ z from fun _ _ _ => rfl,
      isWeaklyRegular_append_iff] at h ⊢
    have : Ideal.ofList [b, a] = Ideal.ofList [a, b] :=
congrArg Ideal.span Set.ext fun _ => (List.Perm.swap a b []).mem_iff
    rw [(quotEquivOfEq _ _ (congrArg₂ _ this rfl)).isWeaklyRegular_congr] at h
    rw [List.append_cons]; rw [List.append_cons]; rw [List.append_assoc _ [b] [a]] at H₁
    apply (List.sublist_append_left (rs₀ ++ [b, a]) _).subperm.trans at H₁
    apply List.perm_append_comm.subperm.trans at H₁
    exact h.imp_left (swap · (h' b a rs₀ H₁))
  | trans h₁₂ _ ih₁₂ ih₂₃ =>
    have H₂ := (h₁₂.append_left rs₀).subperm_right.mp H₁
    exact ih₂₃ rs₀ H₂ H₃ (ih₁₂ rs₀ H₁ H₂ h) }

-- putting `{rs' : List R}` and `h2` after `h3` would be better for partial
-- application, but this argument order seems nicer overall
/--
lemma `IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator` / 引理 `IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator`

English:
lemma IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator
  statement: [IsNoetherian R M]
  proof: h1.prototype_perm h2 fun r _ _ h h' =>
    eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
      (IsNoetherian.noetherian _) h'
      (Ideal.jacobson_mono
        (le_trans
          -- The named argument `(R := R)` below isn't necessary, but
          -- typechecking is much slower without 

中文:
引理 是WeaklyRegular.of_perm_of_subset_jacobson_annihilator
  结论: [是Noether R M]
  证明: h1.prototype_perm h2 fun r _ _ h h' =>
    eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
      (IsNoetherian.noetherian _) h'
      (Ideal.jacobson_mono
        (le_trans
          -- The named argument `(R := R)` below isn't necessary, but
          -- typechecking is much slower without 

Depends on / 依赖: Ideal.jacobson_mono, IsNoetherian, IsNoetherian.noetherian, eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator, h1.prototype_perm, jacobson_mono, le_trans, noetherian, prototype_perm
-/
lemma IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsWeaklyRegular M rs) (h2 : List.Perm rs rs')
    (h3 : forall r in rs, r in (Module.annihilator R M).jacobson) :
    IsWeaklyRegular M rs' :=
  h1.prototype_perm h2 fun r _ _ h h' =>
    eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
      (IsNoetherian.noetherian _) h'
      (Ideal.jacobson_mono
        (le_trans
          -- The named argument `(R := R)` below isn't necessary, but
          -- typechecking is much slower without it
          (LinearMap.annihilator_le_of_surjective (R := R) _ (mkQ_surjective _))
          (LinearMap.annihilator_le_of_injective _ (injective_subtype _)))
        (h3 r (h.subset List.mem_cons_self)))

end Perm

/--
lemma `IsRegular.of_perm_of_subset_jacobson_annihilator` / 引理 `IsRegular.of_perm_of_subset_jacobson_annihilator`

English:
lemma IsRegular.of_perm_of_subset_jacobson_annihilator
  statement: [IsNoetherian R M]
  proof: ⟨h1.toIsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h2 h3,
    letI := h1.nontrivial
top_ne_ideal_smul_of_le_jacobson_annihilator
      Ideal.span_le.mpr (h3 · <| h2.mem_iff.mpr ·)⟩

中文:
引理 是正则.of_perm_of_subset_jacobson_annihilator
  结论: [是Noether R M]
  证明: ⟨h1.toIsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h2 h3,
    letI := h1.nontrivial
top_ne_ideal_smul_of_le_jacobson_annihilator
      Ideal.span_le.mpr (h3 · <| h2.mem_iff.mpr ·)⟩

Depends on / 依赖: Ideal.span_le.mpr, h1.nontrivial, h1.toIsWeaklyRegular.of_perm_of_subset_jacobson_annihilator, h2.mem_iff.mpr, mem_iff, nontrivial, of_perm_of_subset_jacobson_annihilator, span_le, toIsWeaklyRegular, top_ne_ideal_smul_of_le_jacobson_annihilator
-/
lemma IsRegular.of_perm_of_subset_jacobson_annihilator [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsRegular M rs) (h2 : List.Perm rs rs')
    (h3 : forall r in rs, r in (Module.annihilator R M).jacobson) : IsRegular M rs' :=
  ⟨h1.toIsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h2 h3,
    letI := h1.nontrivial
top_ne_ideal_smul_of_le_jacobson_annihilator
      Ideal.span_le.mpr (h3 · <| h2.mem_iff.mpr ·)⟩

/--
lemma `_root_.IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal` / 引理 `_root_.IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal`

English:
lemma _root_.IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal
  proof: IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h1 h2 fun r hr =>
    IsLocalRing.maximalIdeal_le_jacobson _ (h3 r hr)

中文:
引理 _root_.是局部环.isWeaklyRegular_of_perm_of_subset_maximalIdeal
  证明: IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h1 h2 fun r hr =>
    IsLocalRing.maximalIdeal_le_jacobson _ (h3 r hr)

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal_le_jacobson, IsWeaklyRegular, IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator, maximalIdeal_le_jacobson, of_perm_of_subset_jacobson_annihilator
-/
lemma _root_.IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal
    [IsLocalRing R] [IsNoetherian R M] {rs rs' : List R}
    (h1 : IsWeaklyRegular M rs) (h2 : List.Perm rs rs')
    (h3 : forall r in rs, r in IsLocalRing.maximalIdeal R) : IsWeaklyRegular M rs' :=
  IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h1 h2 fun r hr =>
    IsLocalRing.maximalIdeal_le_jacobson _ (h3 r hr)

/--
lemma `_root_.IsLocalRing.isRegular_of_perm` / 引理 `_root_.IsLocalRing.isRegular_of_perm`

English:
lemma _root_.IsLocalRing.isRegular_of_perm
  statement: [IsLocalRing R] [IsNoetherian R M]
  proof: by
  obtain ⟨h3, h4⟩ := h1
  refine ⟨IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h3 h2 ?_, ?_⟩
  · intro x (h6 : x in { r | r in rs })
    refine IsLocalRing.le_maximalIdeal ?_ (Ideal.subset_span h6)
    exact h4 ∘ Eq.trans (top_smul _).symm ∘ Eq.symm ∘ congrArg (· • ⊤)
  · refine ne_

中文:
引理 _root_.是局部环.isRegular_of_perm
  结论: [是局部环 R] [是Noether R M]
  证明: by
  obtain ⟨h3, h4⟩ := h1
  refine ⟨IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h3 h2 ?_, ?_⟩
  · intro x (h6 : x in { r | r in rs })
    refine IsLocalRing.le_maximalIdeal ?_ (Ideal.subset_span h6)
    exact h4 ∘ Eq.trans (top_smul _).symm ∘ Eq.symm ∘ congrArg (· • ⊤)
  · refine ne_

Depends on / 依赖: Eq.symm, Eq.trans, Ideal.span, Ideal.subset_span, IsLocalRing, IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal, IsLocalRing.le_maximalIdeal, Set.ext, h2.mem_iff, isWeaklyRegular_of_perm_of_subset_maximalIdeal, le_maximalIdeal, mem_iff, ne_of_ne_of_eq, subset_span, top_smul
-/
lemma _root_.IsLocalRing.isRegular_of_perm [IsLocalRing R] [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsRegular M rs) (h2 : List.Perm rs rs') :
    IsRegular M rs' := by
  obtain ⟨h3, h4⟩ := h1
  refine ⟨IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h3 h2 ?_, ?_⟩
  · intro x (h6 : x in { r | r in rs })
    refine IsLocalRing.le_maximalIdeal ?_ (Ideal.subset_span h6)
    exact h4 ∘ Eq.trans (top_smul _).symm ∘ Eq.symm ∘ congrArg (· • ⊤)
  · refine ne_of_ne_of_eq h4 (congrArg (Ideal.span · • ⊤) ?_)
    exact Set.ext fun _ => h2.mem_iff

end RingTheory.Sequence

section IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L]

open IsLocalRing

/--
lemma `nontrivial_quotSMulTop_of_mem_maximalIdeal` / 引理 `nontrivial_quotSMulTop_of_mem_maximalIdeal`

English:
lemma nontrivial_quotSMulTop_of_mem_maximalIdeal
  given: {x : R} (mem : x in maximalIdeal R)
  proof: by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  exact Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator (maximalIdeal_le_jacobson _ mem)

中文:
引理 nontrivial_quotSMulTop_of_mem_maximalIdeal
  条件: {x : R} (mem : x in maximalIdeal R)
  证明: by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  exact Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator (maximalIdeal_le_jacobson _ mem)

Depends on / 依赖: Ne.symm, Quotient, Submodule, Submodule.Quotient.nontrivial_iff.mpr, Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator, maximalIdeal_le_jacobson, nontrivial_iff, top_ne_pointwise_smul_of_mem_jacobson_annihilator
-/
lemma nontrivial_quotSMulTop_of_mem_maximalIdeal {x : R} (mem : x in maximalIdeal R) :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  exact Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator (maximalIdeal_le_jacobson _ mem)

/--
lemma `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal` / 引理 `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`

English:
lemma RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
  statement: {rs : List R}
  proof: ⟨reg, Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    ((Ideal.span_le.mpr mem).trans (maximalIdeal_le_jacobson _))⟩

中文:
引理 RingTheory.序列.是正则.of_isWeaklyRegular_of_mem_maximalIdeal
  结论: {rs : 列表 R}
  证明: ⟨reg, Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    ((Ideal.span_le.mpr mem).trans (maximalIdeal_le_jacobson _))⟩

Depends on / 依赖: Homeomorph, Homeomorph.compactSpace, Homeomorph.ulift.symm, Ideal.span_le.mpr, Submodule, Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator, compactSpace, convert, infer_instance, maximalIdeal_le_jacobson, span_le, top_ne_ideal_smul_of_le_jacobson_annihilator
-/
lemma RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal {rs : List R}
    (mem : forall r in rs, r in maximalIdeal R) (reg : IsWeaklyRegular L rs) :
    IsRegular L rs :=
  ⟨reg, Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    ((Ideal.span_le.mpr mem).trans (maximalIdeal_le_jacobson _))⟩

end IsLocalRing
