/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvableByRad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* The Abel-Ruffini Theorem `isSolvable_gal_of_irreducible`: An irreducible polynomial with a root
  that is solvable by radicals has a solvable Galois group.
-/

public section

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/--
theorem `gal_zero_isSolvable` / 定理 `gal_zero_isSolvable`

English:
theorem gal_zero_isSolvable
  statement: Group.IsSolvable (0 : F[X]).Gal
  proof: by infer_instance

中文:
定理 gal_zero_isSolvable
  结论: 群.是可解 (0 : F[X]).Gal
  证明: by infer_instance

Depends on / 依赖: infer_instance
-/
theorem gal_zero_isSolvable : Group.IsSolvable (0 : F[X]).Gal := by infer_instance

/--
theorem `gal_one_isSolvable` / 定理 `gal_one_isSolvable`

English:
theorem gal_one_isSolvable
  statement: Group.IsSolvable (1 : F[X]).Gal
  proof: by infer_instance

中文:
定理 gal_one_isSolvable
  结论: 群.是可解 (1 : F[X]).Gal
  证明: by infer_instance

Depends on / 依赖: infer_instance
-/
theorem gal_one_isSolvable : Group.IsSolvable (1 : F[X]).Gal := by infer_instance

/--
theorem `gal_C_isSolvable` / 定理 `gal_C_isSolvable`

English:
theorem gal_C_isSolvable
  given: (x : F)
  statement: Group.IsSolvable (C x).Gal
  proof: by infer_instance

中文:
定理 gal_C_isSolvable
  条件: (x : F)
  结论: 群.是可解 (C x).Gal
  证明: by infer_instance

Depends on / 依赖: infer_instance
-/
theorem gal_C_isSolvable (x : F) : Group.IsSolvable (C x).Gal := by infer_instance

/--
theorem `gal_X_isSolvable` / 定理 `gal_X_isSolvable`

English:
theorem gal_X_isSolvable
  statement: Group.IsSolvable (X : F[X]).Gal
  proof: by infer_instance

中文:
定理 gal_X_isSolvable
  结论: 群.是可解 (X : F[X]).Gal
  证明: by infer_instance

Depends on / 依赖: infer_instance
-/
theorem gal_X_isSolvable : Group.IsSolvable (X : F[X]).Gal := by infer_instance

/--
theorem `gal_X_sub_C_isSolvable` / 定理 `gal_X_sub_C_isSolvable`

English:
theorem gal_X_sub_C_isSolvable
  given: (x : F)
  statement: Group.IsSolvable (X - C x).Gal
  proof: by infer_instance

中文:
定理 gal_X_sub_C_isSolvable
  条件: (x : F)
  结论: 群.是可解 (X - C x).Gal
  证明: by infer_instance

Depends on / 依赖: infer_instance
-/
theorem gal_X_sub_C_isSolvable (x : F) : Group.IsSolvable (X - C x).Gal := by infer_instance

/--
theorem `gal_X_pow_isSolvable` / 定理 `gal_X_pow_isSolvable`

English:
theorem gal_X_pow_isSolvable
  given: (n : Nat)
  statement: Group.IsSolvable (X ^ n : F[X]).Gal
  proof: by infer_instance

中文:
定理 gal_X_pow_isSolvable
  条件: (n : 自然数)
  结论: 群.是可解 (X ^ n : F[X]).Gal
  证明: by infer_instance

Depends on / 依赖: infer_instance
-/
theorem gal_X_pow_isSolvable (n : Nat) : Group.IsSolvable (X ^ n : F[X]).Gal := by infer_instance

/--
theorem `gal_mul_isSolvable` / 定理 `gal_mul_isSolvable`

English:
theorem gal_mul_isSolvable
  given: {p q : F[X]} (_ : Group.IsSolvable p.Gal) (_ : Group.IsSolvable q.Gal)
  proof: Group.isSolvable_of_isSolvable_injective (Gal.restrictProd_injective p q)

中文:
定理 gal_mul_isSolvable
  条件: {p q : F[X]} (_ : 群.是可解 p.Gal) (_ : 群.是可解 q.Gal)
  证明: Group.isSolvable_of_isSolvable_injective (Gal.restrictProd_injective p q)

Depends on / 依赖: Gal.restrictProd_injective, Group.isSolvable_of_isSolvable_injective, isSolvable_of_isSolvable_injective, restrictProd_injective
-/
theorem gal_mul_isSolvable {p q : F[X]} (_ : Group.IsSolvable p.Gal) (_ : Group.IsSolvable q.Gal) :
    Group.IsSolvable (p * q).Gal :=
  Group.isSolvable_of_isSolvable_injective (Gal.restrictProd_injective p q)

/--
theorem `gal_prod_isSolvable` / 定理 `gal_prod_isSolvable`

English:
theorem gal_prod_isSolvable
  given: {s : Multiset F[X]} (hs : forall p in s, Group.IsSolvable (Gal p))
  proof: by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons]; rw [Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht

中文:
定理 gal_prod_isSolvable
  条件: {s : Multiset F[X]} (hs : 对任意 p in s, 群.是可解 (Gal p))
  证明: by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons]; rw [Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.insert_eq_cons, Multiset.prod_cons, gal_mul_isSolvable, gal_one_isSolvable, induction_on, insert_eq_cons, prod_cons
-/
theorem gal_prod_isSolvable {s : Multiset F[X]} (hs : forall p in s, Group.IsSolvable (Gal p)) :
    Group.IsSolvable s.prod.Gal := by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons]; rw [Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht

/--
theorem `gal_isSolvable_of_splits` / 定理 `gal_isSolvable_of_splits`

English:
theorem gal_isSolvable_of_splits
  statement: {p q : F[X]}
  proof: haveI : Group.IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  Group.isSolvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)

中文:
定理 gal_isSolvable_of_splits
  结论: {p q : F[X]}
  证明: haveI : Group.IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  Group.isSolvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom_surjective, Group.IsSolvable, Group.isSolvable_of_surjective, IsSolvable, SplittingField, isSolvable_of_surjective, q.SplittingField, restrictNormalHom_surjective
-/
theorem gal_isSolvable_of_splits {p q : F[X]}
    (_ : Fact ((p.map (algebraMap F q.SplittingField)).Splits)) (hq : Group.IsSolvable q.Gal) :
    Group.IsSolvable p.Gal :=
  haveI : Group.IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  Group.isSolvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)

/--
theorem `gal_isSolvable_tower` / 定理 `gal_isSolvable_tower`

English:
theorem gal_isSolvable_tower
  statement: (p q : F[X]) (hpq : (p.map (algebraMap F q.SplittingField)).Splits)
  proof: by
  let K := p.SplittingField
  let L := q.SplittingField
  have : Fact ((p.map (algebraMap F L)).Splits) := ⟨hpq⟩
  let ϕ : Gal(L/K) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective

中文:
定理 gal_isSolvable_tower
  结论: (p q : F[X]) (hpq : (p.map (algebraMap F q.分裂域)).Splits)
  证明: by
  let K := p.SplittingField
  let L := q.SplittingField
  have : Fact ((p.map (algebraMap F L)).Splits) := ⟨hpq⟩
  let ϕ : Gal(L/K) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective

Depends on / 依赖: Function, Function.Injective, Group.IsSolvable, Group.isSolvable_of_isSolvable_injective, Injective, IsSolvable, IsSplittingField, IsSplittingField.algEquiv, Splits, SplittingField, algEquiv, algebraMap, autCongr, injective, isSolvable_of_isScalarTower, isSolvable_of_isSolvable_injective, p.SplittingField, p.map, q.SplittingField, q.map
-/
theorem gal_isSolvable_tower (p q : F[X]) (hpq : (p.map (algebraMap F q.SplittingField)).Splits)
    (hp : Group.IsSolvable p.Gal)
    (hq : Group.IsSolvable (q.map (algebraMap F p.SplittingField)).Gal) :
    Group.IsSolvable q.Gal := by
  let K := p.SplittingField
  let L := q.SplittingField
  have : Fact ((p.map (algebraMap F L)).Splits) := ⟨hpq⟩
  let ϕ : Gal(L/K) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective
  have : Group.IsSolvable Gal(K/F) := hp
  have : Group.IsSolvable Gal(L/K) := Group.isSolvable_of_isSolvable_injective ϕ_inj
  exact isSolvable_of_isScalarTower F p.SplittingField q.SplittingField

section GalXPowSubC

set_option backward.isDefEq.respectTransparency false in
/--
theorem `gal_X_pow_sub_one_isSolvable` / 定理 `gal_X_pow_sub_one_isSolvable`

English:
theorem gal_X_pow_sub_one_isSolvable
  given: (n : Nat)
  statement: Group.IsSolvable (X ^ n - 1 : F[X]).Gal
  proof: by
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact gal_zero_isSolvable
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) != 0 := X_pow_sub_C_ne_zero hn' 1
  apply Group.isSolvable_of_comm
  intro σ τ
  ext a ha
  simp only [mem_rootSet_of_ne hn'', map_sub,

中文:
定理 gal_X_pow_sub_one_isSolvable
  条件: (n : 自然数)
  结论: 群.是可解 (X ^ n - 1 : F[X]).Gal
  证明: by
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact gal_zero_isSolvable
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) != 0 := X_pow_sub_C_ne_zero hn' 1
  apply Group.isSolvable_of_comm
  intro σ τ
  ext a ha
  simp only [mem_rootSet_of_ne hn'', map_sub,

Depends on / 依赖: Group.isSolvable_of_comm, X_pow_sub_C_ne_zero, aeval_X_pow, aeval_one, gal_zero_isSolvable, isSolvable_of_comm, map_rootsOfUnity_eq_pow_self, map_sub, mem_rootSet_of_ne, pos_iff_ne_zero, pos_iff_ne_zero.mpr, pow_zero, rootsOfUnity, rootsOfUnity.mkO, sub_eq_zero, sub_self, toAlgHom
-/
theorem gal_X_pow_sub_one_isSolvable (n : Nat) : Group.IsSolvable (X ^ n - 1 : F[X]).Gal := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact gal_zero_isSolvable
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) != 0 := X_pow_sub_C_ne_zero hn' 1
  apply Group.isSolvable_of_comm
  intro σ τ
  ext a ha
  simp only [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha
  have key : forall σ : (X ^ n - 1 : F[X]).Gal, exists m : Nat, σ a = a ^ m := by
    intro σ
    lift n to Nat+ using hn'
    exact map_rootsOfUnity_eq_pow_self σ.toAlgHom (rootsOfUnity.mkOfPowEq a ha)
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply]; rw [τ.mul_apply]; rw [hc]; rw [map_pow]; rw [hd]; rw [map_pow]; rw [hc]; rw [← pow_mul]; rw [pow_mul']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `gal_X_pow_sub_C_isSolvable_aux` / 定理 `gal_X_pow_sub_C_isSolvable_aux`

English:
theorem gal_X_pow_sub_C_isSolvable_aux
  statement: (n : Nat) (a : F)
  proof: by
  by_cases ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  have ha' : algebraMap F (X ^ n - C a).SplittingField a != 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    exact gal_C_isSol

中文:
定理 gal_X_pow_sub_C_isSolvable_aux
  结论: (n : 自然数) (a : F)
  证明: by
  by_cases ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  have ha' : algebraMap F (X ^ n - C a).SplittingField a != 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    exact gal_C_isSol

Depends on / 依赖: C_sub, RingHom, RingHom.injective, SplittingField, X_pow_sub_C_ne_zero, algebraMap, gal_C_isSolvable, gal_X_pow_isSolvable, injective, injective_iff_map_eq_zero, mem_range, pos_iff_ne_zero, pos_iff_ne_zero.mpr, pow_zero, sub_zero
-/
theorem gal_X_pow_sub_C_isSolvable_aux (n : Nat) (a : F)
    (h : ((X ^ n - 1 : F[X]).map (RingHom.id F)).Splits) : Group.IsSolvable (X ^ n - C a).Gal := by
  by_cases ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  have ha' : algebraMap F (X ^ n - C a).SplittingField a != 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    exact gal_C_isSolvable (1 - a)
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : X ^ n - C a != 0 := X_pow_sub_C_ne_zero hn' a
  have hn''' : (X ^ n - 1 : F[X]) != 0 := X_pow_sub_C_ne_zero hn' 1
  have mem_range : forall {c : (X ^ n - C a).SplittingField},
      (c ^ n = 1 -> (exists d, algebraMap F (X ^ n - C a).SplittingField d = c)) := fun {c} hc =>
    RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c
      (Splits.degree_eq_one_of_irreducible (h.of_dvd (map_ne_zero hn''')
        (minpoly.dvd F c (by rwa [map_id, map_sub, sub_eq_zero, aeval_X_pow, aeval_one])))
          (minpoly.irreducible ((SplittingField.instNormal (X ^ n - C a)).isIntegral c))))
  apply Group.isSolvable_of_comm
  intro σ τ
  ext b hb
  rw [mem_rootSet_of_ne hn'']; rw [map_sub]; rw [aeval_X_pow]; rw [aeval_C]; rw [sub_eq_zero] at hb
  have hb' : b != 0 := by
    intro hb'
    rw [hb']; rw [zero_pow hn] at hb
    exact ha' hb.symm
  have key : forall σ : (X ^ n - C a).Gal, exists c, σ b = b * algebraMap F _ c := by
    intro σ
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ← map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc]; rw [mul_div_cancel₀ (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply]; rw [τ.mul_apply]; rw [hc]; rw [map_mul]; rw [τ.commutes]; rw [hd]; rw [map_mul]; rw [σ.commutes]; rw [hc]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_right_inj' hb']; rw [mul_comm]

/--
theorem `splits_X_pow_sub_one_of_X_pow_sub_C` / 定理 `splits_X_pow_sub_one_of_X_pow_sub_C`

English:
theorem splits_X_pow_sub_one_of_X_pow_sub_C
  statement: {F : Type*} [Field F] {E : Type*} [Field E]
  proof: by
  have ha' : i a != 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree != 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ 

中文:
定理 splits_X_pow_sub_one_of_X_pow_sub_C
  结论: {F : 类型} [域 F] {E : 类型} [域 E]
  证明: by
  have ha' : i a != 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree != 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ 

Depends on / 依赖: Splits, Splits.exists_eval_eq_zero, WithBot, WithBot.coe_eq_coe.mp, coe_eq_coe, degree, degree_X_pow_sub_C, degree_map, eval_map, exists_eval_eq_zero, i.injective, injective, injective_iff_map_eq_zero, ne_of_eq_of_ne, pos_iff_ne_zero, pos_iff_ne_zero.mpr, sub_eq_zero, zero_pow
-/
theorem splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [Field F] {E : Type*} [Field E]
    (i : F ->+* E) (n : Nat) {a : F} (ha : a != 0) (h : ((X ^ n - C a).map i).Splits) :
    ((X ^ n - 1 : F[X]).map i).Splits := by
  have ha' : i a != 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree != 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ := Splits.exists_eval_eq_zero h (by rwa [degree_map])
  rw [eval_map]; rw [eval₂_sub]; rw [eval₂_X_pow]; rw [eval₂_C]; rw [sub_eq_zero] at hb
  have hb' : b != 0 := by
    intro hb'
    rw [hb']; rw [zero_pow hn] at hb
    exact ha' hb.symm
  let s := ((X ^ n - C a).map i).roots
  have hs : _ = _ * (s.map _).prod := h.eq_prod_roots
  rw [leadingCoeff_map]; rw [leadingCoeff_X_pow_sub_C hn']; rw [RingHom.map_one]; rw [C_1]; rw [one_mul] at hs
  have hs' : Multiset.card s = n := by
    rw [← h.natDegree_eq_card_roots]; rw [natDegree_map]; rw [natDegree_X_pow_sub_C]
  rw [splits_iff_exists_multiset]; rw [leadingCoeff_map]
  use (s.map fun c => c / b)
  rw [leadingCoeff_X_pow_sub_one hn']; rw [map_one]; rw [C_1]; rw [one_mul]; rw [Multiset.map_map]
  have C_mul_C : C (i a⁻¹) * C (i a) = 1 := by
    rw [← C_mul]; rw [← i.map_mul]; rw [inv_mul_cancel₀ ha]; rw [i.map_one]; rw [C_1]
  have key1 : (X ^ n - 1 : F[X]).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X) := by
    rw [Polynomial.map_sub]; rw [Polynomial.map_sub]; rw [Polynomial.map_pow]; rw [map_X]; rw [map_C]; rw [Polynomial.map_one]; rw [sub_comp]; rw [pow_comp]; rw [X_comp]; rw [C_comp]; rw [mul_pow]; rw [← C_pow]; rw [hb]; rw [mul_sub]; rw [←
      mul_assoc]; rw [C_mul_C]; rw [one_mul]
  have key2 : ((fun q : E[X] => q.comp (C b * X)) ∘ fun c : E => X - C c) = fun c : E =>
      C b * (X - C (c / b)) := by
    ext1 c
    dsimp only [Function.comp_apply]
    rw [sub_comp]; rw [X_comp]; rw [C_comp]; rw [mul_sub]; rw [← C_mul]; rw [mul_div_cancel₀ c hb']
  rw [key1]; rw [hs]; rw [multiset_prod_comp]; rw [Multiset.map_map]; rw [key2]; rw [Multiset.prod_map_mul]; rw [Function.const_def (α := E) (y := C b)]; rw [Multiset.map_const]; rw [Multiset.prod_replicate]; rw [hs']; rw [← C_pow]; rw [hb]; rw [← mul_assoc]; rw [C_mul_C]; rw [one_mul]
  rfl

/--
theorem `gal_X_pow_sub_C_isSolvable` / 定理 `gal_X_pow_sub_C_isSolvable`

English:
theorem gal_X_pow_sub_C_isSolvable
  given: (n : Nat) (x : F)
  statement: Group.IsSolvable (X ^ n - C x).Gal
  proof: by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.m

中文:
定理 gal_X_pow_sub_C_isSolvable
  条件: (n : 自然数) (x : F)
  结论: 群.是可解 (X ^ n - C x).Gal
  证明: by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.m

Depends on / 依赖: Polynomial, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_sub, SplittingField, SplittingField.splits, gal_X_pow_isSolvable, gal_X_pow_sub_C_isSolvable_aux, gal_X_pow_sub_one_isSolvable, gal_isSolvable_tower, map_C, map_X, map_id, map_one, map_pow, map_sub, splits, splits_X_pow_sub_one_of_X_pow_sub_C, sub_zero
-/
theorem gal_X_pow_sub_C_isSolvable (n : Nat) (x : F) : Group.IsSolvable (X ^ n - C x).Gal := by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    apply gal_X_pow_sub_C_isSolvable_aux
    rw [map_id]
    have key := SplittingField.splits (X ^ n - 1 : F[X])
    rwa [Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one] at key

end GalXPowSubC

variable (F E) in
/--
Definition of `solvableByRad` / `solvableByRad` 的定义

English:
definition solvableByRad
  signature: : IntermediateField F E
  body: sInf {s | forall x, forall n != 0, x ^ n in s -> x in s}

中文:
定义 solvableByRad
  签名: : 中间域 F E
  定义体: sInf {s | forall x, forall n != 0, x ^ n in s -> x in s}
-/
def solvableByRad : IntermediateField F E :=
  sInf {s | forall x, forall n != 0, x ^ n in s -> x in s}

variable (F) in
/-- Inductive definition of solvable by radicals -/
@[deprecated solvableByRad (since := "2026-02-28")]
/--
Inductive type `IsSolvableByRad` / 归纳类型 `IsSolvableByRad`

English:
inductive IsSolvableByRad
  parameters: : E -> Prop
  constructors (6):
    - base: (α : F) : IsSolvableByRad (algebraMap F E α)
    - add: (α β : E) : IsSolvableByRad α -> IsSolvableByRad β -> IsSolvableByRad (α + β)
    - neg: (α : E) : IsSolvableByRad α -> IsSolvableByRad (-α)
    - mul: (α β : E) : IsSolvableByRad α -> IsSolvableByRad β -> IsSolvableByRad (α * β)
    - inv: (α : E) : IsSolvableByRad α -> IsSolvableByRad α⁻¹
    - rad: (α : E) (n : Nat) (hn : n != 0) : IsSolvableByRad (α ^ n) -> IsSolvableByRad α

中文:
归纳类型 是SolvableByRad
  参数: : E -> 命题
  构造子 (6 个):
    - base: (α : F) : 是SolvableByRad (algebraMap F E α)
    - add: (α β : E) : 是SolvableByRad α -> 是SolvableByRad β -> 是SolvableByRad (α + β)
    - neg: (α : E) : 是SolvableByRad α -> 是SolvableByRad (-α)
    - mul: (α β : E) : 是SolvableByRad α -> 是SolvableByRad β -> 是SolvableByRad (α * β)
    - inv: (α : E) : 是SolvableByRad α -> 是SolvableByRad α⁻¹
    - rad: (α : E) (n : 自然数) (hn : n != 0) : 是SolvableByRad (α ^ n) -> 是SolvableByRad α
-/
inductive IsSolvableByRad : E -> Prop
  | base (α : F) : IsSolvableByRad (algebraMap F E α)
  | add (α β : E) : IsSolvableByRad α -> IsSolvableByRad β -> IsSolvableByRad (α + β)
  | neg (α : E) : IsSolvableByRad α -> IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α -> IsSolvableByRad β -> IsSolvableByRad (α * β)
  | inv (α : E) : IsSolvableByRad α -> IsSolvableByRad α⁻¹
  | rad (α : E) (n : Nat) (hn : n != 0) : IsSolvableByRad (α ^ n) -> IsSolvableByRad α

/--
theorem `solvableByRad_le` / 定理 `solvableByRad_le`

English:
theorem solvableByRad_le
  given: {s : IntermediateField F E} (H : forall x, forall n != 0, x ^ n in s -> x in s)
  proof: sInf_le H

中文:
定理 solvableByRad_le
  条件: {s : 中间域 F E} (H : 对任意 x, 对任意 n != 0, x ^ n in s -> x in s)
  证明: sInf_le H

Depends on / 依赖: sInf_le
-/
theorem solvableByRad_le {s : IntermediateField F E} (H : forall x, forall n != 0, x ^ n in s -> x in s) :
    solvableByRad F E <= s :=
  sInf_le H

/--
theorem `solvableByRad.rad_mem` / 定理 `solvableByRad.rad_mem`

English:
theorem solvableByRad.rad_mem
  given: {x : E} {n : Nat} (hn : n != 0) (hx : x ^ n in solvableByRad F E)
  proof: by
  grind [solvableByRad]

中文:
定理 solvableByRad.rad_mem
  条件: {x : E} {n : 自然数} (hn : n != 0) (hx : x ^ n in solvableByRad F E)
  证明: by
  grind [solvableByRad]

Depends on / 依赖: solvableByRad
-/
theorem solvableByRad.rad_mem {x : E} {n : Nat} (hn : n != 0) (hx : x ^ n in solvableByRad F E) :
    x in solvableByRad F E := by
  grind [solvableByRad]

variable (F E) in
/--
theorem `solvableByRad_le_algClosure` / 定理 `solvableByRad_le_algClosure`

English:
theorem solvableByRad_le_algClosure
  statement: solvableByRad F E <= algebraicClosure F E
  proof: by
  refine solvableByRad_le fun x n hn hx => ?_
  rw [mem_algebraicClosure_iff] at hx ⊢
  obtain ⟨p, h1, h2⟩ := hx
  refine ⟨p.comp (X ^ n), ⟨fun h => h1 (leadingCoeff_eq_zero.mp ?_), ?_⟩⟩
  · rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    rwa [natDeg

中文:
定理 solvableByRad_le_algClosure
  结论: solvableByRad F E <= algebraicClosure F E
  证明: by
  refine solvableByRad_le fun x n hn hx => ?_
  rw [mem_algebraicClosure_iff] at hx ⊢
  obtain ⟨p, h1, h2⟩ := hx
  refine ⟨p.comp (X ^ n), ⟨fun h => h1 (leadingCoeff_eq_zero.mp ?_), ?_⟩⟩
  · rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    rwa [natDeg

Depends on / 依赖: aeval_comp, leadingCoeff_X_pow, leadingCoeff_comp, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, mem_algebraicClosure_iff, mul_one, natDegree_X_pow, one_pow, p.comp, solvableByRad_le
-/
theorem solvableByRad_le_algClosure : solvableByRad F E <= algebraicClosure F E := by
  refine solvableByRad_le fun x n hn hx => ?_
  rw [mem_algebraicClosure_iff] at hx ⊢
  obtain ⟨p, h1, h2⟩ := hx
  refine ⟨p.comp (X ^ n), ⟨fun h => h1 (leadingCoeff_eq_zero.mp ?_), ?_⟩⟩
  · rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    rwa [natDegree_X_pow]
  · simpa [aeval_comp]

/--
theorem `isAlgebraic_solvableByRad` / 定理 `isAlgebraic_solvableByRad`

English:
theorem isAlgebraic_solvableByRad
  statement: (solvableByRad F E).IsAlgebraic
  proof: fun _ hx => mem_algebraicClosure_iff.1 (solvableByRad_le_algClosure _ _ hx)

中文:
定理 isAlgebraic_solvableByRad
  结论: (solvableByRad F E).是代数
  证明: fun _ hx => mem_algebraicClosure_iff.1 (solvableByRad_le_algClosure _ _ hx)

Depends on / 依赖: mem_algebraicClosure_iff, solvableByRad_le_algClosure
-/
theorem isAlgebraic_solvableByRad : (solvableByRad F E).IsAlgebraic :=
  fun _ hx => mem_algebraicClosure_iff.1 (solvableByRad_le_algClosure _ _ hx)

/--
theorem `isIntegral_of_mem_solvableByRad` / 定理 `isIntegral_of_mem_solvableByRad`

English:
theorem isIntegral_of_mem_solvableByRad
  given: {x : E} (hx : x in solvableByRad F E)
  statement: IsIntegral F x
  proof: (isAlgebraic_solvableByRad _ hx).isIntegral

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isIntegral := isIntegral_of_mem_solvableByRad

中文:
定理 is整数egral_of_mem_solvableByRad
  条件: {x : E} (hx : x in solvableByRad F E)
  结论: 是整 F x
  证明: (isAlgebraic_solvableByRad _ hx).isIntegral

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isIntegral := isIntegral_of_mem_solvableByRad

Depends on / 依赖: isAlgebraic_solvableByRad, isIntegral
-/
theorem isIntegral_of_mem_solvableByRad {x : E} (hx : x in solvableByRad F E) : IsIntegral F x :=
  (isAlgebraic_solvableByRad _ hx).isIntegral

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isIntegral := isIntegral_of_mem_solvableByRad

/-- An induction principle for `solvableByRad`. -/
@[elab_as_elim]
/--
theorem `solvableByRad.induction` / 定理 `solvableByRad.induction`

English:
theorem solvableByRad.induction
  statement: (motive : forall x, x in solvableByRad F E -> Prop)
  proof: by
  let s : Subalgebra F E :=
  { carrier := {x | exists hx : x in solvableByRad F E, motive x hx}
    algebraMap_mem' a := ⟨algebraMap_mem _ a, mem a⟩
    add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨add_mem ha hb, add _ _ ha hb ha' hb'⟩
    mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨mul_mem ha hb, mul _ 

中文:
定理 solvableByRad.induction
  结论: (motive : 对任意 x, x in solvableByRad F E -> 命题)
  证明: by
  let s : Subalgebra F E :=
  { carrier := {x | exists hx : x in solvableByRad F E, motive x hx}
    algebraMap_mem' a := ⟨algebraMap_mem _ a, mem a⟩
    add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨add_mem ha hb, add _ _ ha hb ha' hb'⟩
    mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨mul_mem ha hb, mul _ 
-/
protected theorem solvableByRad.induction (motive : forall x, x in solvableByRad F E -> Prop)
    (mem : forall x, motive (algebraMap F E x) (algebraMap_mem _ _))
    (add : forall x y (hx : x in solvableByRad F E) (hy : y in solvableByRad F E),
      motive x hx -> motive y hy -> motive (x + y) (add_mem hx hy))
    (mul : forall x y (hx : x in solvableByRad F E) (hy : y in solvableByRad F E),
      motive x hx -> motive y hy -> motive (x * y) (mul_mem hx hy))
    (rad : forall n x (hn : n != 0) (hx : x ^ n in solvableByRad F E),
      motive (x ^ n) hx -> motive x (rad_mem hn hx))
    {x : E} (hx : x in solvableByRad F E) : motive x hx := by
  let s : Subalgebra F E :=
  { carrier := {x | exists hx : x in solvableByRad F E, motive x hx}
    algebraMap_mem' a := ⟨algebraMap_mem _ a, mem a⟩
    add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨add_mem ha hb, add _ _ ha hb ha' hb'⟩
    mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨mul_mem ha hb, mul _ _ ha hb ha' hb'⟩ }
let t : IntermediateField F E := Subalgebra.IsAlgebraic.toIntermediateField (S := s) by
    rintro x ⟨hx, hx'⟩
    apply isAlgebraic_solvableByRad
    exact hx
  have ht (x n) (hn : n != 0) : x ^ n in t -> x in t := by
    rintro ⟨hx, hx'⟩
    exact ⟨rad_mem hn hx, rad _ _ hn hx hx'⟩
  obtain ⟨_, h⟩ := solvableByRad_le (s := t) ht hx
  exact h

/--
theorem `induction_rad` / 定理 `induction_rad`

English:
theorem induction_rad
  statement: {x : E} (hx : x in solvableByRad F E) {n : Nat} (hn : n != 0)
  proof: by
  let p := minpoly F (x ^ n)
  have hp : p.comp (X ^ n) != 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h' | h'
    · exact minpoly.ne_zero (isIntegral_of_mem_solvableByRad (pow_mem hx n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of

中文:
定理 induction_rad
  结论: {x : E} (hx : x in solvableByRad F E) {n : 自然数} (hn : n != 0)
  证明: by
  let p := minpoly F (x ^ n)
  have hp : p.comp (X ^ n) != 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h' | h'
    · exact minpoly.ne_zero (isIntegral_of_mem_solvableByRad (pow_mem hx n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of
-/
private theorem induction_rad {x : E} (hx : x in solvableByRad F E) {n : Nat} (hn : n != 0)
    (hα : Group.IsSolvable (minpoly F (x ^ n)).Gal) : Group.IsSolvable (minpoly F x).Gal := by
  let p := minpoly F (x ^ n)
  have hp : p.comp (X ^ n) != 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h' | h'
    · exact minpoly.ne_zero (isIntegral_of_mem_solvableByRad (pow_mem hx n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of_splits
  · exact ⟨(SplittingField.splits (p.comp (X ^ n))).of_dvd (map_ne_zero hp)
      ((map_dvd_map' _).mpr (minpoly.dvd F x (by rw [aeval_comp, aeval_X_pow, minpoly.aeval])))⟩
  · refine gal_isSolvable_tower p (p.comp (X ^ n)) ?_ hα ?_
    · exact Gal.splits_in_splittingField_of_comp _ _ (by rwa [natDegree_X_pow])
    · obtain ⟨s, hs⟩ := splits_iff_exists_multiset.1 (SplittingField.splits p)
      rw [map_comp]; rw [Polynomial.map_pow]; rw [map_X]; rw [hs]; rw [mul_comp]; rw [C_comp]
      apply gal_mul_isSolvable (gal_C_isSolvable _)
      rw [multiset_prod_comp]
      apply gal_prod_isSolvable
      intro q hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, _, rfl⟩ := hq
      rw [sub_comp]; rw [X_comp]; rw [C_comp]
      exact gal_X_pow_sub_C_isSolvable n q

open IntermediateField

/--
theorem `induction_step` / 定理 `induction_step`

English:
theorem induction_step
  statement: {x y z : E}
  proof: by
  let p := minpoly F x
  let q := minpoly F y
  have hpq := SplittingField.splits (p * q)
  rw [Polynomial.map_mul]; rw [splits_mul (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hx)))
      (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hy)))] at hpq
  have f : ↥F

中文:
定理 induction_step
  结论: {x y z : E}
  证明: by
  let p := minpoly F x
  let q := minpoly F y
  have hpq := SplittingField.splits (p * q)
  rw [Polynomial.map_mul]; rw [splits_mul (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hx)))
      (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hy)))] at hpq
  have f : ↥F
-/
private theorem induction_step {x y z : E}
    (hx : x in solvableByRad F E) (hy : y in solvableByRad F E) (hz : z in solvableByRad F E)
    (hx' : Group.IsSolvable (minpoly F x).Gal) (hy' : Group.IsSolvable (minpoly F y).Gal)
    (hz' : z in F⟮x, y⟯) : Group.IsSolvable (minpoly F z).Gal := by
  let p := minpoly F x
  let q := minpoly F y
  have hpq := SplittingField.splits (p * q)
  rw [Polynomial.map_mul]; rw [splits_mul (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hx)))
      (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hy)))] at hpq
  have f : ↥F⟮x, y⟯ ->ₐ[F] (p * q).SplittingField :=
Classical.choice nonempty_algHom_adjoin_of_splits by
      rintro a (rfl | rfl)
      · exact ⟨isIntegral_of_mem_solvableByRad hx, hpq.1⟩
      · exact ⟨isIntegral_of_mem_solvableByRad hy, hpq.2⟩
  have key : minpoly F z = minpoly F (f ⟨z, hz'⟩) := by
    refine minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (isIntegral_of_mem_solvableByRad hz)) ?_
      (minpoly.monic (isIntegral_of_mem_solvableByRad hz))
    rw [aeval_algHom_apply]; rw [map_eq_zero]
    apply (algebraMap (↥F⟮x, y⟯) E).injective
    simp [← aeval_algebraMap_apply]
  rw [key]
  refine gal_isSolvable_of_splits ⟨Normal.splits ?_ (f ⟨z, hz'⟩)⟩ (gal_mul_isSolvable hx' hy')
  infer_instance

/--
theorem `isSolvable_gal_minpoly` / 定理 `isSolvable_gal_minpoly`

English:
theorem isSolvable_gal_minpoly
  given: {x : E} (hx : x in solvableByRad F E)
  proof: by
  induction hx using solvableByRad.induction with
  | mem y => rw [minpoly.eq_X_sub_C E]; infer_instance
  | add y z hy hz hy' hz' =>
    apply induction_step hy hz (add_mem hy hz) hy' hz' (add_mem ..) <;> apply subset_adjoin <;> simp
  | mul y z hy hz hy' hz' =>
    apply induction_step hy hz (m

中文:
定理 isSolvable_gal_minpoly
  条件: {x : E} (hx : x in solvableByRad F E)
  证明: by
  induction hx using solvableByRad.induction with
  | mem y => rw [minpoly.eq_X_sub_C E]; infer_instance
  | add y z hy hz hy' hz' =>
    apply induction_step hy hz (add_mem hy hz) hy' hz' (add_mem ..) <;> apply subset_adjoin <;> simp
  | mul y z hy hz hy' hz' =>
    apply induction_step hy hz (m

Depends on / 依赖: add_mem, eq_X_sub_C, induction_rad, induction_step, infer_instance, minpoly, minpoly.eq_X_sub_C, mul_mem, rad_mem, solvableByRad, solvableByRad.induction, solvableByRad.rad_mem, subset_adjoin
-/
theorem isSolvable_gal_minpoly {x : E} (hx : x in solvableByRad F E) :
    Group.IsSolvable (minpoly F x).Gal := by
  induction hx using solvableByRad.induction with
  | mem y => rw [minpoly.eq_X_sub_C E]; infer_instance
  | add y z hy hz hy' hz' =>
    apply induction_step hy hz (add_mem hy hz) hy' hz' (add_mem ..) <;> apply subset_adjoin <;> simp
  | mul y z hy hz hy' hz' =>
    apply induction_step hy hz (mul_mem hy hz) hy' hz' (mul_mem ..) <;> apply subset_adjoin <;> simp
  | rad n y hn hy hy' => exact induction_rad (solvableByRad.rad_mem hn hy) hn hy'

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isSolvable := isSolvable_gal_minpoly

/--
theorem `isSolvable_gal_of_irreducible` / 定理 `isSolvable_gal_of_irreducible`

English:
theorem isSolvable_gal_of_irreducible
  statement: {x : E} (hx : x in solvableByRad F E) {q : F[X]}
  proof: by
  have : Group.IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval]
    exact isSolvable_gal_minpoly hx
  refine Group.isSolvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ ?_)
  aesop

@[deprecated (since := "2026-02-28")]
alia

中文:
定理 isSolvable_gal_of_irreducible
  结论: {x : E} (hx : x in solvableByRad F E) {q : F[X]}
  证明: by
  have : Group.IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval]
    exact isSolvable_gal_minpoly hx
  refine Group.isSolvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ ?_)
  aesop

@[deprecated (since := "2026-02-28")]
alia

Depends on / 依赖: Gal.restrictDvd_surjective, Group.IsSolvable, Group.isSolvable_of_surjective, IsSolvable, eq_of_irreducible, isSolvable_gal_minpoly, isSolvable_of_surjective, leadingCoeff, minpoly, minpoly.eq_of_irreducible, q.leadingCoeff, q_aeval, q_irred, restrictDvd_surjective
-/
theorem isSolvable_gal_of_irreducible {x : E} (hx : x in solvableByRad F E) {q : F[X]}
    (q_irred : Irreducible q) (q_aeval : aeval x q = 0) : Group.IsSolvable q.Gal := by
  have : Group.IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval]
    exact isSolvable_gal_minpoly hx
  refine Group.isSolvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ ?_)
  aesop

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isSolvable' := isSolvable_gal_of_irreducible
