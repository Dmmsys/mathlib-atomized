/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Totally split algebras

An `R`-algebra `S` is finite (totally) split if it is isomorphic to `Fin n → R` for some `n`.
Geometrically, this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split.

## Main results

- `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`: If `S` is finite étale over `R` of
  some constant rank, there exists a faithfully flat, finite étale `R`-algebra `T` such that
  `T ⊗[R] S` is finite split.
-/

universe u

public section

open TensorProduct

/--
Definition of `Algebra.IsFiniteSplit` / `Algebra.IsFiniteSplit` 的定义

English:
class Algebra.IsFiniteSplit
  parameters: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  axioms and operations (1):
    - nonempty_algEquiv_fun((R S)) : exists n : Nat, Nonempty (S ≃ₐ[R] Fin n -> R)

中文:
类 代数.是FiniteSplit
  参数: (R S : 类型) [交换环 R] [交换环 S] [代数 R S]
  公理与运算 (1 个):
    - nonempty_algEquiv_fun((R S)) : 存在 n : 自然数, 非空 (S ≃ₐ[R] 有限集 n -> R)
-/
class Algebra.IsFiniteSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun (R S) : exists n : Nat, Nonempty (S ≃ₐ[R] Fin n -> R)

namespace Algebra.IsFiniteSplit

variable {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra R S]

instance {T : Type*} [CommRing T] [Algebra R T] [IsFiniteSplit R S] :
    IsFiniteSplit T (T otimes[R] S) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R S
  refine ⟨n, ⟨?_⟩⟩
  exact (TensorProduct.congr AlgEquiv.refl e).trans
    ((TensorProduct.piRight R T T (fun _ : Fin n => R)).trans <|
      AlgEquiv.piCongrRight fun i => TensorProduct.rid R T T)

instance {ι : Type*} [Finite ι] : IsFiniteSplit R (ι -> R) where
  nonempty_algEquiv_fun := by
    cases nonempty_fintype ι
    exact ⟨_, ⟨AlgEquiv.piCongrLeft' _ _ (Fintype.equivFin ι)⟩⟩

/--
lemma `of_algEquiv` / 引理 `of_algEquiv`

English:
lemma of_algEquiv
  given: {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S]
  proof: by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩

中文:
引理 of_algEquiv
  条件: {S' : 类型} [交换环 S'] [代数 R S'] (e : S ≃ₐ[R] S') [是FiniteSplit R S]
  证明: by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩

Depends on / 依赖: e.symm.trans, nonempty_algEquiv_fun
-/
lemma of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S] :
    IsFiniteSplit R S' := by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiniteSplit R R
  body: .of_algEquiv (AlgEquiv.funUnique (ι := Fin 1) _ _)

中文:
实例 :
  签名: 是FiniteSplit R R
  定义体: .of_algEquiv (AlgEquiv.funUnique (ι := Fin 1) _ _)

Depends on / 依赖: AlgEquiv, AlgEquiv.funUnique, funUnique, of_algEquiv
-/
instance : IsFiniteSplit R R :=
  .of_algEquiv (AlgEquiv.funUnique (ι := Fin 1) _ _)

/--
lemma `of_subsingleton_top` / 引理 `of_subsingleton_top`

English:
lemma of_subsingleton_top
  given: [Subsingleton S]
  statement: IsFiniteSplit R S
  proof: ⟨0, ⟨default⟩⟩

中文:
引理 of_subsingleton_top
  条件: [子单例 S]
  结论: 是FiniteSplit R S
  证明: ⟨0, ⟨default⟩⟩
-/
lemma of_subsingleton_top [Subsingleton S] : IsFiniteSplit R S :=
  ⟨0, ⟨default⟩⟩

/--
lemma `of_subsingleton` / 引理 `of_subsingleton`

English:
lemma of_subsingleton
  given: [Subsingleton R]
  statement: IsFiniteSplit R S
  proof: by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact of_subsingleton_top

中文:
引理 of_subsingleton
  条件: [子单例 R]
  结论: 是FiniteSplit R S
  证明: by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact of_subsingleton_top

Depends on / 依赖: RingHom, RingHom.codomain_trivial, Subsingleton, algebraMap, codomain_trivial, of_subsingleton_top
-/
lemma of_subsingleton [Subsingleton R] : IsFiniteSplit R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact of_subsingleton_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteSplit
  signature: R S] : Module.Free R S
  body: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

中文:
实例 [是FiniteSplit
  签名: R S] : 模.自由 R S
  定义体: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

Depends on / 依赖: Module, Module.Free.of_equiv, e.symm.toLinearEquiv, nonempty_algEquiv_fun, of_equiv, toLinearEquiv
-/
instance [IsFiniteSplit R S] : Module.Free R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteSplit
  signature: R S] : Module.FinitePresentation R S
  body: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

中文:
实例 [是FiniteSplit
  签名: R S] : 模.有限呈现 R S
  定义体: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

Depends on / 依赖: FinitePresentation, Module, Module.FinitePresentation.of_equiv, e.symm.toLinearEquiv, nonempty_algEquiv_fun, of_equiv, toLinearEquiv
-/
instance [IsFiniteSplit R S] : Module.FinitePresentation R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteSplit
  signature: R S] : Etale R S
  body: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact .of_equiv e.symm

中文:
实例 [是FiniteSplit
  签名: R S] : 平展 R S
  定义体: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact .of_equiv e.symm

Depends on / 依赖: e.symm, nonempty_algEquiv_fun, of_equiv
-/
instance [IsFiniteSplit R S] : Etale R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact .of_equiv e.symm

open Ideal in
variable (k) in
/--
lemma `bijective_algebraMap_quotient` / 引理 `bijective_algebraMap_quotient`

English:
lemma bijective_algebraMap_quotient
  given: [IsFiniteSplit k R] (p : Ideal R) [p.IsPrime]
  proof: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun k R
  let p' : Ideal (Fin n -> k) := p.comap e.symm
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', inferInstance⟩
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  let g : (R ⧸ p) ≃ₐ[k] k :=
(quotientEquivAlg _ p' e <| comap_symm e.t

中文:
引理 bijective_algebraMap_quotient
  条件: [是FiniteSplit k R] (p : 理想 R) [p.是素]
  证明: by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun k R
  let p' : Ideal (Fin n -> k) := p.comap e.symm
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', inferInstance⟩
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  let g : (R ⧸ p) ≃ₐ[k] k :=
(quotientEquivAlg _ p' e <| comap_symm e.t

Depends on / 依赖: Function, Function.surjective_eval, Pi.evalAlgHom, PrimeSpectrum, PrimeSpectrum.exists_comap_evalRingHom_eq, Subsingleton, Subsingleton.elim, asIdeal, comap_symm, comp_algebr, e.symm, e.toRingEquiv, evalAlgHom, exists_comap_evalRingHom_eq, g.symm.toAlgHom.comp_algebr, nonempty_algEquiv_fun, p.comap, quotientEquivAlg, quotientEquivAlgOfEq, quotientKerAlgEquivOfSurjective
-/
lemma bijective_algebraMap_quotient [IsFiniteSplit k R] (p : Ideal R) [p.IsPrime] :
    Function.Bijective (algebraMap k (R ⧸ p)) := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun k R
  let p' : Ideal (Fin n -> k) := p.comap e.symm
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', inferInstance⟩
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  let g : (R ⧸ p) ≃ₐ[k] k :=
(quotientEquivAlg _ p' e <| comap_symm e.toRingEquiv).trans
(quotientEquivAlgOfEq k congr($(hq).asIdeal).symm).trans
    quotientKerAlgEquivOfSurjective (f := Pi.evalAlgHom k (fun _ => k) i)
      (Function.surjective_eval _)
  simpa [← g.symm.toAlgHom.comp_algebraMap] using g.symm.bijective

set_option backward.isDefEq.respectTransparency.types false in
variable (k R) in
/-- If `R` is finite split over a field `k`, the `k`-rational points of `R`
are in one-to-one correspondence with its prime spectrum. -/
@[expose]
noncomputable
/--
Definition of `algHomEquivPrimeSpectrum` / `algHomEquivPrimeSpectrum` 的定义

English:
definition algHomEquivPrimeSpectrum
  signature: [IsFiniteSplit k R]
  body: ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId _ _) (bijective_algebraMap_quotient _ _)).symm.toAlgHom
    (Ideal.Quotient.mkₐ _ p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    a

中文:
定义 algHomEquivPrimeSpectrum
  签名: [是FiniteSplit k R]
  定义体: ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId _ _) (bijective_algebraMap_quotient _ _)).symm.toAlgHom
    (Ideal.Quotient.mkₐ _ p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    a

Depends on / 依赖: RingHom, RingHom.ker, RingHom.ker_isPrime, ker_isPrime
-/
def algHomEquivPrimeSpectrum [IsFiniteSplit k R] : (R ->ₐ[k] k) ≃ PrimeSpectrum R where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId _ _) (bijective_algebraMap_quotient _ _)).symm.toAlgHom
    (Ideal.Quotient.mkₐ _ p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    apply (AlgEquiv.ofBijective (ofId k (R ⧸ RingHom.ker f))
      (bijective_algebraMap_quotient _ _)).injective
    rw [AlgEquiv.apply_symm_apply]; rw [AlgEquiv.coe_ofBijective]; rw [ofId_apply]; rw [IsScalarTower.algebraMap_apply k R]
    simp [-Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  right_inv p := by
    ext : 1
    dsimp
    rw [← AlgHom.comap_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.ker_coe_equiv]; rw [← RingHom.ker_eq_comap_bot]; rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]

@[simp]
/--
lemma `coe_algHomEquivPrimeSpectrum` / 引理 `coe_algHomEquivPrimeSpectrum`

English:
lemma coe_algHomEquivPrimeSpectrum
  given: [IsFiniteSplit k R] (f : R ->ₐ[k] k)
  proof: rfl

中文:
引理 coe_algHomEquivPrimeSpectrum
  条件: [是FiniteSplit k R] (f : R ->ₐ[k] k)
  证明: rfl
-/
lemma coe_algHomEquivPrimeSpectrum [IsFiniteSplit k R] (f : R ->ₐ[k] k) :
    algHomEquivPrimeSpectrum k R f = RingHom.ker f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSepClosed
  signature: k] [EssFiniteType k R] [FormallyEtale k R] : IsFiniteSplit k R
  body: by
  have := FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  exact .of_algEquiv (Algebra.FormallyEtale.equivPiOfIsSepClosed k R).symm

中文:
实例 [是SepClosed
  签名: k] [EssFiniteType k R] [形式平展 k R] : 是FiniteSplit k R
  定义体: by
  have := FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  exact .of_algEquiv (Algebra.FormallyEtale.equivPiOfIsSepClosed k R).symm

Depends on / 依赖: Algebra, Algebra.FormallyEtale.equivPiOfIsSepClosed, FormallyEtale, FormallyUnramified, FormallyUnramified.finite_of_free, IsArtinianRing, equivPiOfIsSepClosed, finite_of_free, isArtinian_of_tower, of_algEquiv
-/
instance [IsSepClosed k] [EssFiniteType k R] [FormallyEtale k R] : IsFiniteSplit k R := by
  have := FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  exact .of_algEquiv (Algebra.FormallyEtale.equivPiOfIsSepClosed k R).symm

variable {n : Nat} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/--
lemma `exists_tensorProduct_of_etale` / 引理 `exists_tensorProduct_of_etale`

English:
lemma exists_tensorProduct_of_etale
  statement: [Etale R S] [Module.Finite R S] {n : Nat}
  proof: by
  induction n generalizing R S with
  | zero =>
    use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
    let e : R otimes[R] S ≃ₐ[R] S := TensorProduct.lid R S
    have : IsFiniteSplit R S := by
      rw [Nat.cast_zero]; rw [Module.rankAtStalk_eq_zero_iff_subsingle

中文:
引理 存在_tensorProduct_of_etale
  结论: [平展 R S] [模.有限 R S] {n : 自然数}
  证明: by
  induction n generalizing R S with
  | zero =>
    use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
    let e : R otimes[R] S ≃ₐ[R] S := TensorProduct.lid R S
    have : IsFiniteSplit R S := by
      rw [Nat.cast_zero]; rw [Module.rankAtStalk_eq_zero_iff_subsingle
-/
lemma exists_tensorProduct_of_etale [Etale R S] [Module.Finite R S] {n : Nat}
    (hn : Module.rankAtStalk (R := R) S = n) :
    exists (T : Type u) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.FaithfullyFlat R T) (_ : Module.Finite R T) (_ : Algebra.Etale R T),
      IsFiniteSplit T (T otimes[R] S) := by
  induction n generalizing R S with
  | zero =>
    use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
    let e : R otimes[R] S ≃ₐ[R] S := TensorProduct.lid R S
    have : IsFiniteSplit R S := by
      rw [Nat.cast_zero]; rw [Module.rankAtStalk_eq_zero_iff_subsingleton] at hn
      exact of_subsingleton_top
    apply IsFiniteSplit.of_algEquiv e.symm
  | succ n ih =>
    cases subsingleton_or_nontrivial R
    · use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
      have : IsFiniteSplit R S := .of_subsingleton
      exact .of_algEquiv (TensorProduct.lid R S).symm
    have : Nontrivial S := by
      apply Module.nontrivial_of_rankAtStalk_pos (R := R)
      simp [hn]
    /- Because `S` is unramified over `R`, there exists an `S`-algebra `U` such that
    `S ⊗[R] S ≃ₐ[S] S × U`. -/
    obtain ⟨U, _, _, ⟨e⟩⟩ := Algebra.FormallyUnramified.exists_algEquiv_prod R S
    algebraize [RingHom.snd S U]
    have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
    have : Etale S U := by
      have : Etale S (S × U) := Etale.of_equiv e
      exact .comp S (S × U) U
    have : Module.Finite S U := by
      have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
      have : Module.Finite (S × U) U :=
        Module.Finite.of_surjective (Algebra.linearMap (S × U) U) (RingHom.snd S U).surjective
      exact Module.Finite.trans (S × U) _
    have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
      simp [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv, Module.rankAtStalk_baseChange, hn]
    simp_rw [Module.rankAtStalk_prod , Module.rankAtStalk_self, Pi.add_apply, Pi.one_apply] at this
    /- Since the `S`-rank of `S × U = S ⊗[R] S` is `n + 1`, the `S`-rank of `U` is `n`,
    so we may apply the induction hypothesis on `U`. -/
    have : Module.rankAtStalk (R := S) U = n := by
      ext p
      simp only [Pi.natCast_def, Nat.cast_id]
      grind
    /- We obtain a finite étale, faithfully flat `S`-algebra `V` such that `V ⊗[S] U` is finite
    split. We claim that `V` viewed as an `R`-algebra works. -/
    obtain ⟨V, _, _, _, _, _, hV⟩ := ih this
    obtain ⟨n, ⟨f⟩⟩ := hV.nonempty_algEquiv_fun
    algebraize [(algebraMap S V).comp (algebraMap R S)]
    let e : V otimes[R] S ≃ₐ[V] Unit oplus Fin n -> V :=
(Algebra.TensorProduct.cancelBaseChange R S V V S).symm.trans
(TensorProduct.congr AlgEquiv.refl e).trans
(TensorProduct.prodRight S V V S U).trans
(AlgEquiv.prodCongr (TensorProduct.rid S V V) f).trans
        (AlgEquiv.prodCongr (AlgEquiv.funUnique _ _ _).symm AlgEquiv.refl).trans
        (AlgEquiv.sumArrowEquivProdArrow Unit (Fin n) V V).symm
    refine ⟨V, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
    · have : Module.FaithfullyFlat R S := by
        apply Module.FaithfullyFlat.of_comap_surjective
        rw [← PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]
        intro p
        simp [hn]
      exact Module.FaithfullyFlat.trans R S V
    · exact Module.Finite.trans S V
    · exact Algebra.Etale.comp R S V
    · exact .of_algEquiv e.symm

end IsFiniteSplit

end Algebra
