/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Structure of finite(ly generated) abelian groups

* `AddCommGroup.equiv_free_prod_directSum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `CommGroup.equiv_free_prod_prod_multiplicative_zmod` is a version for multiplicative groups.
* `AddCommGroup.equiv_directSum_zmod_of_finite` : Any finite abelian group is a direct sum of
  some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`.
* `CommGroup.equiv_prod_multiplicative_zmod_of_finite` is a version for multiplicative groups.
-/

@[expose] public section

open scoped DirectSum


/--
Definition of `directSumNeZeroMulHom` / `directSumNeZeroMulHom` 的定义

English:
definition directSumNeZeroMulHom
  signature: {ι : Type} [DecidableEq ι] (p : ι -> Nat) (n : ι -> Nat)
  body: DirectSum.toAddMonoid fun i => DirectSum.of (fun i => ZMod (p i ^ n i)) i

中文:
定义 directSumNeZeroMulHom
  签名: {ι : Type} [DecidableEq ι] (p : ι -> 自然数) (n : ι -> 自然数)
  定义体: DirectSum.toAddMonoid fun i => DirectSum.of (fun i => ZMod (p i ^ n i)) i
-/
private def directSumNeZeroMulHom {ι : Type} [DecidableEq ι] (p : ι -> Nat) (n : ι -> Nat) :
    (⨁ i : {i // n i != 0}, ZMod (p i ^ n i)) ->+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid fun i => DirectSum.of (fun i => ZMod (p i ^ n i)) i

/--
Definition of `directSumNeZeroMulEquiv` / `directSumNeZeroMulEquiv` 的定义

English:
definition directSumNeZeroMulEquiv
  signature: (ι : Type) [DecidableEq ι] (p : ι -> Nat) (n : ι -> Nat)
  body: directSumNeZeroMulHom p n
  invFun := DirectSum.toAddMonoid fun i =>
    if h : n i = 0 then 0 else DirectSum.of (fun j : {i // n i != 0} => ZMod (p j ^ n j)) ⟨i, h⟩
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [directSumNeZeroMulHo

中文:
定义 directSumNeZeroMulEquiv
  签名: (ι : Type) [DecidableEq ι] (p : ι -> 自然数) (n : ι -> 自然数)
  定义体: directSumNeZeroMulHom p n
  invFun := DirectSum.toAddMonoid fun i =>
    if h : n i = 0 then 0 else DirectSum.of (fun j : {i // n i != 0} => ZMod (p j ^ n j)) ⟨i, h⟩
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [directSumNeZeroMulHo
-/
private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι -> Nat) (n : ι -> Nat) :
    (⨁ i : {i // n i != 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) where
  toFun := directSumNeZeroMulHom p n
  invFun := DirectSum.toAddMonoid fun i =>
    if h : n i = 0 then 0 else DirectSum.of (fun j : {i // n i != 0} => ZMod (p j ^ n j)) ⟨i, h⟩
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [directSumNeZeroMulHom]; rw [DirectSum.toAddMonoid_of]; rw [DirectSum.toAddMonoid_of]; rw [dif_neg i.prop]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of i x =>
      rw [DirectSum.toAddMonoid_of]
      split_ifs with h
      · simp [(ZMod.subsingleton_iff.2 <| by rw [h, pow_zero]).elim x 0]
      · simp_rw [directSumNeZeroMulHom, DirectSum.toAddMonoid_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add (directSumNeZeroMulHom p n)

universe u

namespace Module

variable (M : Type u)

/--
theorem `finite_of_fg_torsion` / 定理 `finite_of_fg_torsion`

English:
theorem finite_of_fg_torsion
  statement: [AddCommGroup M] [Module Int M] [Module.Finite Int M]
  proof: by
  rcases Module.equiv_directSum_of_isTorsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  have : forall i : ι, NeZero (p i ^ e i).natAbs := fun i =>
⟨Int.natAbs_ne_zero.mpr pow_ne_zero (e i) (h i).ne_zero⟩
have : forall i : ι, _root_.Finite Int ⧸ Submodule.span Int {p i ^ e i} := fun i =>
    Finite.of_equiv _

中文:
定理 finite_of_fg_torsion
  结论: [AddCommGroup M] [Module 整数 M] [Module.Finite 整数 M]
  证明: by
  rcases Module.equiv_directSum_of_isTorsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  have : forall i : ι, NeZero (p i ^ e i).natAbs := fun i =>
⟨Int.natAbs_ne_zero.mpr pow_ne_zero (e i) (h i).ne_zero⟩
have : forall i : ι, _root_.Finite Int ⧸ Submodule.span Int {p i ^ e i} := fun i =>
    Finite.of_equiv _

Depends on / 依赖: DFinsupp, DFinsupp.equivFunOnFintype.symm, Finite, Finite.of_equi, Finite.of_equiv, Int.natAbs_ne_zero.mpr, Module, Module.equiv_directSum_of_isTorsion, NeZero, Submodule, Submodule.span, _root_, _root_.Finite, equivFunOnFintype, equiv_directSum_of_isTorsion, natAbs, natAbs_ne_zero, ne_zero, of_equi, of_equiv
-/
theorem finite_of_fg_torsion [AddCommGroup M] [Module Int M] [Module.Finite Int M]
    (hM : Module.IsTorsion Int M) : _root_.Finite M := by
  rcases Module.equiv_directSum_of_isTorsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  have : forall i : ι, NeZero (p i ^ e i).natAbs := fun i =>
⟨Int.natAbs_ne_zero.mpr pow_ne_zero (e i) (h i).ne_zero⟩
have : forall i : ι, _root_.Finite Int ⧸ Submodule.span Int {p i ^ e i} := fun i =>
    Finite.of_equiv _ (p i ^ e i).quotientSpanEquivZMod.symm.toEquiv
  have : _root_.Finite (⨁ i, Int ⧸ (Submodule.span Int {p i ^ e i} : Submodule Int Int)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact Finite.of_equiv _ l.symm.toEquiv

end Module

variable (G : Type u)

namespace AddCommGroup

variable [AddCommGroup G]

/--
theorem `equiv_free_prod_directSum_zmod` / 定理 `equiv_free_prod_directSum_zmod`

English:
theorem equiv_free_prod_directSum_zmod
  given: [hG : AddGroup.FG G]
  proof: by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_directSum _ _ _ _ _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG)
  refine ⟨n, ι, fι, fun i => (p i).natAbs, fun i => ?_, e, ⟨?_⟩⟩
  · rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]; exact hp i
  exact
    f.toAddEquiv.tra

中文:
定理 equiv_free_prod_directSum_zmod
  条件: [hG : AddGroup.FG G]
  证明: by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_directSum _ _ _ _ _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG)
  refine ⟨n, ι, fι, fun i => (p i).natAbs, fun i => ?_, e, ⟨?_⟩⟩
  · rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]; exact hp i
  exact
    f.toAddEquiv.tra

Depends on / 依赖: AddEquiv, AddEquiv.refl, DFinsupp, DFinsupp.mapRange.addEquiv, Finite, Int.prime_iff_natAbs_prime, Int.quotientSpanEquivZMod, Module, Module.Finite.iff_addGroup_fg.mpr, Module.equiv_free_prod_directSum, ZMod.ringEquivCongr, addEquiv, equiv_free_prod_directSum, f.toAddEquiv.trans, iff_addGroup_fg, irreducible_iff_prime, mapRange, natAbs, natAbs_pow, prime_iff_natAbs_prime
-/
theorem equiv_free_prod_directSum_zmod [hG : AddGroup.FG G] :
    exists (n : Nat) (ι : Type) (_ : Fintype ι) (p : ι -> Nat) (_ : forall i, Nat.Prime <| p i) (e : ι -> Nat),
Nonempty G ≃+ (Fin n ->₀ Int) × ⨁ i : ι, ZMod (p i ^ e i) := by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_directSum _ _ _ _ _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG)
  refine ⟨n, ι, fι, fun i => (p i).natAbs, fun i => ?_, e, ⟨?_⟩⟩
  · rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]; exact hp i
  exact
    f.toAddEquiv.trans
      ((AddEquiv.refl _).prodCongr <|
        DFinsupp.mapRange.addEquiv fun i =>
          ((Int.quotientSpanEquivZMod _).trans <|
ZMod.ringEquivCongr (p i).natAbs_pow _).toAddEquiv)

/--
theorem `equiv_directSum_zmod_of_finite` / 定理 `equiv_directSum_zmod_of_finite`

English:
theorem equiv_directSum_zmod_of_finite
  given: [Finite G]
  proof: by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_directSum_zmod G
  rcases n with - | n
  · have : Unique (Fin Nat.zero ->₀ Int) :=
      { uniq := by subsingleton }
    exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
  · have := @Fintype.prodLeft _ _ _ (Fin

中文:
定理 equiv_directSum_zmod_of_finite
  条件: [Finite G]
  证明: by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_directSum_zmod G
  rcases n with - | n
  · have : Unique (Fin Nat.zero ->₀ Int) :=
      { uniq := by subsingleton }
    exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
  · have := @Fintype.prodLeft _ _ _ (Fin

Depends on / 依赖: AddEquiv, AddEquiv.uniqueProd, Finsupp, Finsupp.single, Finsupp.single_eq_same, Fintype, Fintype.ofEquiv, Fintype.ofSurjective, Fintype.prodLeft, Nat.zero, Unique, equiv_free_prod_directSum_zmod, f.toEquiv, f.trans, false.elim, n.succ, nonempty_fintype, ofEquiv, ofSurjective, prodLeft
-/
theorem equiv_directSum_zmod_of_finite [Finite G] :
    exists (ι : Type) (_ : Fintype ι) (p : ι -> Nat) (_ : forall i, Nat.Prime <| p i) (e : ι -> Nat),
Nonempty G ≃+ ⨁ i : ι, ZMod (p i ^ e i) := by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_directSum_zmod G
  rcases n with - | n
  · have : Unique (Fin Nat.zero ->₀ Int) :=
      { uniq := by subsingleton }
    exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
  · have := @Fintype.prodLeft _ _ _ (Fintype.ofEquiv G f.toEquiv) _
    exact
      (Fintype.ofSurjective (fun f : Fin n.succ ->₀ Int => f 0) fun a =>
            ⟨Finsupp.single 0 a, Finsupp.single_eq_same⟩).false.elim

/--
lemma `equiv_directSum_zmod_of_finite'` / 引理 `equiv_directSum_zmod_of_finite'`

English:
lemma equiv_directSum_zmod_of_finite'
  given: (G : Type*) [AddCommGroup G] [Finite G]
  proof: by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  refine ⟨{i : ι // n i != 0}, inferInstance, fun i => p i ^ n i, ?_,
    ⟨e.trans (directSumNeZeroMulEquiv ι _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow₀ (hp _).one_lt hi

中文:
引理 equiv_directSum_zmod_of_finite'
  条件: (G : 类型) [AddCommGroup G] [Finite G]
  证明: by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  refine ⟨{i : ι // n i != 0}, inferInstance, fun i => p i ^ n i, ?_,
    ⟨e.trans (directSumNeZeroMulEquiv ι _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow₀ (hp _).one_lt hi

Depends on / 依赖: AddCommGroup, AddCommGroup.equiv_directSum_zmod_of_finite, classical, directSumNeZeroMulEquiv, e.trans, equiv_directSum_zmod_of_finite, one_lt
-/
lemma equiv_directSum_zmod_of_finite' (G : Type*) [AddCommGroup G] [Finite G] :
    exists (ι : Type) (_ : Fintype ι) (n : ι -> Nat),
      (forall i, 1 < n i) ∧ Nonempty (G ≃+ ⨁ i, ZMod (n i)) := by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  refine ⟨{i : ι // n i != 0}, inferInstance, fun i => p i ^ n i, ?_,
    ⟨e.trans (directSumNeZeroMulEquiv ι _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow₀ (hp _).one_lt hi

/--
theorem `finite_of_fg_isAddTorsion` / 定理 `finite_of_fg_isAddTorsion`

English:
theorem finite_of_fg_isAddTorsion
  given: [hG' : AddGroup.FG G] (hG : IsAddTorsion G)
  statement: Finite G
  proof: @Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG')
    isAddTorsion_iff_isTorsion_int.mp hG

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isAddTorsion

中文:
定理 finite_of_fg_isAddTorsion
  条件: [hG' : AddGroup.FG G] (hG : IsAddTorsion G)
  结论: Finite G
  证明: @Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG')
    isAddTorsion_iff_isTorsion_int.mp hG

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isAddTorsion

Depends on / 依赖: Finite, Module, Module.Finite.iff_addGroup_fg.mpr, Module.finite_of_fg_torsion, finite_of_fg_torsion, iff_addGroup_fg, isAddTorsion_iff_isTorsion_int, isAddTorsion_iff_isTorsion_int.mp
-/
theorem finite_of_fg_isAddTorsion [hG' : AddGroup.FG G] (hG : IsAddTorsion G) : Finite G :=
@Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG')
    isAddTorsion_iff_isTorsion_int.mp hG

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isAddTorsion

end AddCommGroup

namespace CommGroup

@[to_additive existing]
/--
theorem `finite_of_fg_isMulTorsion` / 定理 `finite_of_fg_isMulTorsion`

English:
theorem finite_of_fg_isMulTorsion
  given: [CommGroup G] [Group.FG G] (hG : IsMulTorsion G)
  statement: Finite G
  proof: @Finite.of_equiv _ _ (AddCommGroup.finite_of_fg_isAddTorsion (Additive G) hG) Multiplicative.ofAdd

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isMulTorsion

中文:
定理 finite_of_fg_isMulTorsion
  条件: [CommGroup G] [Group.FG G] (hG : IsMulTorsion G)
  结论: Finite G
  证明: @Finite.of_equiv _ _ (AddCommGroup.finite_of_fg_isAddTorsion (Additive G) hG) Multiplicative.ofAdd

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isMulTorsion

Depends on / 依赖: AddCommGroup, AddCommGroup.finite_of_fg_isAddTorsion, Additive, Finite, Finite.of_equiv, Multiplicative, Multiplicative.ofAdd, finite_of_fg_isAddTorsion, of_equiv
-/
theorem finite_of_fg_isMulTorsion [CommGroup G] [Group.FG G] (hG : IsMulTorsion G) : Finite G :=
  @Finite.of_equiv _ _ (AddCommGroup.finite_of_fg_isAddTorsion (Additive G) hG) Multiplicative.ofAdd

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isMulTorsion

/--
theorem `equiv_prod_multiplicative_zmod_of_finite` / 定理 `equiv_prod_multiplicative_zmod_of_finite`

English:
theorem equiv_prod_multiplicative_zmod_of_finite
  given: (G : Type*) [CommGroup G] [Finite G]
  proof: by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm h₂.some.trans
    (DirectSum.addEquivProd _).trans (MulEquiv.piMultiplicative _).toAdditiveRight⟩⟩

中文:
定理 equiv_prod_multiplicative_zmod_of_finite
  条件: (G : 类型) [CommGroup G] [Finite G]
  证明: by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm h₂.some.trans
    (DirectSum.addEquivProd _).trans (MulEquiv.piMultiplicative _).toAdditiveRight⟩⟩

Depends on / 依赖: AddCommGroup, AddCommGroup.equiv_directSum_zmod_of_finite, Additive, DirectSum, DirectSum.addEquivProd, MulEquiv, MulEquiv.piMultiplicative, MulEquiv.toAdditive.symm, addEquivProd, equiv_directSum_zmod_of_finite, piMultiplicative, some.trans, toAdditive, toAdditiveRight
-/
theorem equiv_prod_multiplicative_zmod_of_finite (G : Type*) [CommGroup G] [Finite G] :
    exists (ι : Type) (_ : Fintype ι) (n : ι -> Nat),
       (forall (i : ι), 1 < n i) ∧ Nonempty (G ≃* ((i : ι) -> Multiplicative (ZMod (n i)))) := by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm h₂.some.trans
    (DirectSum.addEquivProd _).trans (MulEquiv.piMultiplicative _).toAdditiveRight⟩⟩

/--
theorem `equiv_free_prod_prod_multiplicative_zmod` / 定理 `equiv_free_prod_prod_multiplicative_zmod`

English:
theorem equiv_free_prod_prod_multiplicative_zmod
  given: (G : Type*) [CommGroup G] [hG : Group.FG G]
  proof: by
  obtain ⟨n, ι, inst, x, p, e, equiv⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive G)
exact ⟨ι, Fin n, inst, inferInstance, x, p, e, ⟨MulEquiv.toAdditive.symm equiv.some.trans
    ((Finsupp.addEquivFunOnFinite.trans <| ((AddEquiv.piAdditive _).trans <|
        (AddEquiv.additiveMultip

中文:
定理 equiv_free_prod_prod_multiplicative_zmod
  条件: (G : 类型) [CommGroup G] [hG : Group.FG G]
  证明: by
  obtain ⟨n, ι, inst, x, p, e, equiv⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive G)
exact ⟨ι, Fin n, inst, inferInstance, x, p, e, ⟨MulEquiv.toAdditive.symm equiv.some.trans
    ((Finsupp.addEquivFunOnFinite.trans <| ((AddEquiv.piAdditive _).trans <|
        (AddEquiv.additiveMultip

Depends on / 依赖: AddCommGroup, AddCommGroup.equiv_free_prod_directSum_zmod, AddEquiv, AddEquiv.additiveMultiplicative, AddEquiv.piAdditive, AddEquiv.prodAdditive, Additive, DirectSum, DirectSum.addEquivProd, Equiv.refl, Finsupp, Finsupp.addEquivFunOnFinite.trans, MulEquiv, MulEquiv.toAdditive.symm, addEquivFunOnFinite, addEquivProd, additiveMultiplicative, arrowCongr, equiv.some.trans, equiv_free_prod_directSum_zmod
-/
theorem equiv_free_prod_prod_multiplicative_zmod (G : Type*) [CommGroup G] [hG : Group.FG G] :
    exists (ι j : Type) (_ : Fintype ι) (_ : Fintype j) (p : ι -> Nat)
    (_ : forall i, Nat.Prime <| p i) (e : ι -> Nat),
Nonempty G ≃* (j -> Multiplicative Int) × ((i : ι) -> Multiplicative (ZMod (p i ^ e i))) := by
  obtain ⟨n, ι, inst, x, p, e, equiv⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive G)
exact ⟨ι, Fin n, inst, inferInstance, x, p, e, ⟨MulEquiv.toAdditive.symm equiv.some.trans
    ((Finsupp.addEquivFunOnFinite.trans <| ((AddEquiv.piAdditive _).trans <|
        (AddEquiv.additiveMultiplicative Int).arrowCongr (Equiv.refl _)).symm).prodCongr
          (DirectSum.addEquivProd _ )).trans <| (AddEquiv.prodAdditive _ _).symm⟩⟩

end CommGroup

namespace Subgroup

@[to_additive]
/--
lemma `finiteIndex_range_powMonoidHom_of_fg` / 引理 `finiteIndex_range_powMonoidHom_of_fg`

English:
lemma finiteIndex_range_powMonoidHom_of_fg
  statement: (A : Type*) [CommGroup A] [Group.FG A] {n : Nat}
  proof: finiteIndex_iff_finite_quotient.mpr CommGroup.finite_of_fg_isMulTorsion _
    CommGroup.isMulTorsion_quotient_range_powMonoidHom A hn

@[to_additive]

中文:
引理 finiteIndex_range_powMonoidHom_of_fg
  结论: (A : 类型) [CommGroup A] [Group.FG A] {n : 自然数}
  证明: finiteIndex_iff_finite_quotient.mpr CommGroup.finite_of_fg_isMulTorsion _
    CommGroup.isMulTorsion_quotient_range_powMonoidHom A hn

@[to_additive]

Depends on / 依赖: FiniteIndex, range.FiniteIndex
-/
lemma finiteIndex_range_powMonoidHom_of_fg (A : Type*) [CommGroup A] [Group.FG A] {n : Nat}
    (hn : n != 0) :
    (powMonoidHom (α := A) n).range.FiniteIndex :=
finiteIndex_iff_finite_quotient.mpr CommGroup.finite_of_fg_isMulTorsion _
    CommGroup.isMulTorsion_quotient_range_powMonoidHom A hn

@[to_additive]
/--
lemma `isFiniteRelIndex_map_powMonoidHom_of_fg` / 引理 `isFiniteRelIndex_map_powMonoidHom_of_fg`

English:
lemma isFiniteRelIndex_map_powMonoidHom_of_fg
  statement: {A : Type*} [CommGroup A] {B : Subgroup A}
  proof: by B.map (powMonoidHom (α := A) n)
  rw [isFiniteRelIndex_iff_finiteIndex]
  have : (map (powMonoidHom (α := A) n) B).subgroupOf B = (powMonoidHom (α := B) n).range := by
    ext1
    simp [mem_subgroupOf, Subtype.ext_iff]
  rw [this]
  have := (Group.fg_iff_subgroup_fg B).mpr hB
  exact finiteIndex

中文:
引理 isFiniteRelIndex_map_powMonoidHom_of_fg
  结论: {A : 类型} [CommGroup A] {B : Subgroup A}
  证明: by B.map (powMonoidHom (α := A) n)
  rw [isFiniteRelIndex_iff_finiteIndex]
  have : (map (powMonoidHom (α := A) n) B).subgroupOf B = (powMonoidHom (α := B) n).range := by
    ext1
    simp [mem_subgroupOf, Subtype.ext_iff]
  rw [this]
  have := (Group.fg_iff_subgroup_fg B).mpr hB
  exact finiteIndex

Depends on / 依赖: B.map, Group.fg_iff_subgroup_fg, Subtype, Subtype.ext_iff, ext_iff, fg_iff_subgroup_fg, finiteIndex_range_powMonoidHom_of_fg, isFiniteRelIndex_iff_finiteIndex, mem_subgroupOf, powMonoidHom, subgroupOf
-/
lemma isFiniteRelIndex_map_powMonoidHom_of_fg {A : Type*} [CommGroup A] {B : Subgroup A}
    (hB : B.FG) {n : Nat} (hn : n != 0) :
.IsFiniteRelIndex B := by B.map (powMonoidHom (α := A) n)
  rw [isFiniteRelIndex_iff_finiteIndex]
  have : (map (powMonoidHom (α := A) n) B).subgroupOf B = (powMonoidHom (α := B) n).range := by
    ext1
    simp [mem_subgroupOf, Subtype.ext_iff]
  rw [this]
  have := (Group.fg_iff_subgroup_fg B).mpr hB
  exact finiteIndex_range_powMonoidHom_of_fg B hn

end Subgroup

namespace Submodule

variable {R K M : Type*} [CommRing R] [CommRing K] [Algebra R K] [Module.Finite Int R]
  [AddCommGroup M] [Module R M]

/--
lemma `fg_toAddSubgroup` / 引理 `fg_toAddSubgroup`

English:
lemma fg_toAddSubgroup
  given: {A : Submodule R M} (hfg : A.FG)
  statement: A.toAddSubgroup.FG
  proof: by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup A.toAddSubgroup]; rw [← fg_iff_addSubgroup_fg]
  exact FG.restrictScalars hfg

中文:
引理 fg_toAddSubgroup
  条件: {A : Submodule R M} (hfg : A.FG)
  结论: A.toAddSubgroup.FG
  证明: by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup A.toAddSubgroup]; rw [← fg_iff_addSubgroup_fg]
  exact FG.restrictScalars hfg

Depends on / 依赖: A.toAddSubgroup, AddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup, FG.restrictScalars, fg_iff_addSubgroup_fg, restrictScalars, toAddSubgroup, toIntSubmodule_toAddSubgroup
-/
lemma fg_toAddSubgroup {A : Submodule R M} (hfg : A.FG) : A.toAddSubgroup.FG := by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup A.toAddSubgroup]; rw [← fg_iff_addSubgroup_fg]
  exact FG.restrictScalars hfg

open AddSubgroup in
/--
lemma `isFiniteRelIndex_of_map_linearMapMulLeft_le` / 引理 `isFiniteRelIndex_of_map_linearMapMulLeft_le`

English:
lemma isFiniteRelIndex_of_map_linearMapMulLeft_le
  statement: {A B : Submodule R K} {n : Nat} (hn : n != 0)
  proof: by
  have := fg_toAddSubgroup hfg
  have := isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg this hn
  refine isFiniteRelIndex_of_le_left (H := A.toAddSubgroup.map (nsmulAddMonoidHom n))
    A.toAddSubgroup ?_
  rw [SetLike.le_def] at h ⊢
  simpa using h

中文:
引理 isFiniteRelIndex_of_map_linearMapMulLeft_le
  结论: {A B : Submodule R K} {n : 自然数} (hn : n != 0)
  证明: by
  have := fg_toAddSubgroup hfg
  have := isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg this hn
  refine isFiniteRelIndex_of_le_left (H := A.toAddSubgroup.map (nsmulAddMonoidHom n))
    A.toAddSubgroup ?_
  rw [SetLike.le_def] at h ⊢
  simpa using h

Depends on / 依赖: A.toAddSubgroup, A.toAddSubgroup.map, SetLike, SetLike.le_def, fg_toAddSubgroup, isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg, isFiniteRelIndex_of_le_left, le_def, nsmulAddMonoidHom, toAddSubgroup
-/
lemma isFiniteRelIndex_of_map_linearMapMulLeft_le {A B : Submodule R K} {n : Nat} (hn : n != 0)
    (hfg : A.FG) (h : A.map (LinearMap.mulLeft R (n : K)) <= B) :
    B.toAddSubgroup.IsFiniteRelIndex A.toAddSubgroup := by
  have := fg_toAddSubgroup hfg
  have := isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg this hn
  refine isFiniteRelIndex_of_le_left (H := A.toAddSubgroup.map (nsmulAddMonoidHom n))
    A.toAddSubgroup ?_
  rw [SetLike.le_def] at h ⊢
  simpa using h

end Submodule
