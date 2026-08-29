/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Properties of the module `α →₀ M`

* `Finsupp.linearEquivFunOnFinite`: `α →₀ β` and `a → β` are equivalent if `α` is finite
* `FunOnFinite.map`: the map `(X → M) → (Y → M)` induced by a map `f : X ⟶ Y` when
  `X` and `Y` are finite.
* `FunOnFinite.linearMmap`: the linear map `(X → M) →ₗ[R] (Y → M)` induced
  by a map `f : X ⟶ Y` when `X` and `Y` are finite.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section uniqueLinearEquiv

variable (R : Type*) {S α : Type*} (M : Type*)
variable [AddCommMonoid M] [Semiring R] [Module R M]

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
@[simps! apply symm_apply]
/--
Definition of `uniqueLinearEquiv` / `uniqueLinearEquiv` 的定义

English:
definition uniqueLinearEquiv
  signature: [Subsingleton α] (a : α)
  body: uniqueAddEquiv a
  map_smul' _ _ := rfl

中文:
定义 uniqueLinearEquiv
  签名: [子单例 α] (a : α)
  定义体: uniqueAddEquiv a
  map_smul' _ _ := rfl

Depends on / 依赖: uniqueAddEquiv
-/
noncomputable def uniqueLinearEquiv [Subsingleton α] (a : α) : (α ->₀ M) ≃ₗ[R] M where
  toAddEquiv := uniqueAddEquiv a
  map_smul' _ _ := rfl

-- We want this lemma to fire before `uniqueRingEquiv_symm_apply`.
/--
lemma `uniqueLinearEquiv_symm_apply_apply` / 引理 `uniqueLinearEquiv_symm_apply_apply`

English:
lemma uniqueLinearEquiv_symm_apply_apply
  given: (a : α) [Subsingleton α] (m : M) (b : α)
  proof: by simp [Subsingleton.elim b a]

中文:
引理 uniqueLinearEquiv_symm_apply_apply
  条件: (a : α) [子单例 α] (m : M) (b : α)
  证明: by simp [Subsingleton.elim b a]
-/
@[simp↓ high] lemma uniqueLinearEquiv_symm_apply_apply (a : α) [Subsingleton α] (m : M) (b : α) :
    (uniqueLinearEquiv R M a).symm m b = m := by simp [Subsingleton.elim b a]

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
@[deprecated uniqueLinearEquiv (since := "2026-05-06")]
/--
Definition of `LinearEquiv.finsuppUnique` / `LinearEquiv.finsuppUnique` 的定义

English:
definition LinearEquiv.finsuppUnique
  signature: (α : Type*) [Unique α]
  body: { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 线性等价.finsuppUnique
  签名: (α : 类型) [唯一 α]
  定义体: { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.funUnique, Finsupp, Finsupp.equivFunOnFinite.trans, equivFunOnFinite, funUnique, map_add, map_smul
-/
noncomputable def LinearEquiv.finsuppUnique (α : Type*) [Unique α] : (α ->₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable {R M}

@[deprecated uniqueLinearEquiv_apply (since := "2026-05-06")]
/--
theorem `LinearEquiv.finsuppUnique_apply` / 定理 `LinearEquiv.finsuppUnique_apply`

English:
theorem LinearEquiv.finsuppUnique_apply
  given: (α : Type*) [Unique α] (f : α ->₀ M)
  proof: rfl

中文:
定理 线性等价.finsuppUnique_apply
  条件: (α : 类型) [唯一 α] (f : α ->₀ M)
  证明: rfl
-/
theorem LinearEquiv.finsuppUnique_apply (α : Type*) [Unique α] (f : α ->₀ M) :
    LinearEquiv.finsuppUnique R M α f = f default :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated uniqueLinearEquiv_symm_apply (since := "2026-05-06")]
/--
theorem `LinearEquiv.finsuppUnique_symm_apply` / 定理 `LinearEquiv.finsuppUnique_symm_apply`

English:
theorem LinearEquiv.finsuppUnique_symm_apply
  given: (α : Type*) [Unique α] (m : M)
  proof: by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
    equivFunOnFinite, Function.update]

中文:
定理 线性等价.finsuppUnique_symm_apply
  条件: (α : 类型) [唯一 α] (m : M)
  证明: by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
    equivFunOnFinite, Function.update]

Depends on / 依赖: Equiv.funUnique, Function, Function.update, LinearEquiv, LinearEquiv.finsuppUnique, Pi.single, equivFunOnFinite, finsuppUnique, funUnique, single, update
-/
theorem LinearEquiv.finsuppUnique_symm_apply (α : Type*) [Unique α] (m : M) :
    (LinearEquiv.finsuppUnique R M α).symm m = Finsupp.single default m := by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
    equivFunOnFinite, Function.update]

end uniqueLinearEquiv

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/--
Definition of `lcoeFun` / `lcoeFun` 的定义

English:
definition lcoeFun
  signature: : (α ->₀ M) ->ₗ[R] α -> M where
  body: (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp

中文:
定义 lcoeFun
  签名: : (α ->₀ M) ->ₗ[R] α -> M where
  定义体: (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp
-/
def lcoeFun : (α ->₀ M) ->ₗ[R] α -> M where
  toFun := (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp

/--
theorem `lcoeFun_apply` / 定理 `lcoeFun_apply`

English:
theorem lcoeFun_apply
  given: (f : α ->₀ M)
  statement: lcoeFun (R := R) f = ⇑f
  proof: rfl

中文:
定理 lcoeFun_apply
  条件: (f : α ->₀ M)
  结论: lcoeFun (R := R) f = ⇑f
  证明: rfl
-/
@[simp] theorem lcoeFun_apply (f : α ->₀ M) : lcoeFun (R := R) f = ⇑f := rfl

/--
theorem `lcoeFun_comp_lsingle` / 定理 `lcoeFun_comp_lsingle`

English:
theorem lcoeFun_comp_lsingle
  given: [DecidableEq α] (x : α)
  proof: by
  ext; simp [single_eq_pi_single]

中文:
定理 lcoeFun_comp_lsingle
  条件: [DecidableEq α] (x : α)
  证明: by
  ext; simp [single_eq_pi_single]
-/
@[simp] theorem lcoeFun_comp_lsingle [DecidableEq α] (x : α) :
    lcoeFun ∘ₗ lsingle x = .single R (fun _ => M) x := by
  ext; simp [single_eq_pi_single]

end Finsupp

variable {R M N P : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

open Finsupp

namespace LinearMap

section prodOfFinsuppNat

open Function

variable (f : P × M ->ₗ[R] M)

/--
Definition of `prodOfFinsuppNat` / `prodOfFinsuppNat` 的定义

English:
definition prodOfFinsuppNat
  signature: : (Nat ->₀ P) ->ₗ[R] P × M
  body: Finsupp.lsum Nat fun n => ((.inr .. ∘ₗ f) ^ n) ∘ₗ .inl ..

中文:
定义 prodOfFinsupp自然数
  签名: : (自然数 ->₀ P) ->ₗ[R] P × M
  定义体: Finsupp.lsum Nat fun n => ((.inr .. ∘ₗ f) ^ n) ∘ₗ .inl ..

Depends on / 依赖: Finsupp, Finsupp.lsum
-/
def prodOfFinsuppNat : (Nat ->₀ P) ->ₗ[R] P × M :=
  Finsupp.lsum Nat fun n => ((.inr .. ∘ₗ f) ^ n) ∘ₗ .inl ..

/--
theorem `fst_prodOfFinsuppNat` / 定理 `fst_prodOfFinsuppNat`

English:
theorem fst_prodOfFinsuppNat
  given: (x : Nat ->₀ P)
  statement: (prodOfFinsuppNat f x).1 = x 0
  proof: by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.fst_sum]
  rw [Finset.sum_eq_single 0 (fun n _ hn => ?_) (by simp)]
  · simp
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn
  simp [pow_succ']

中文:
定理 fst_prodOfFinsupp自然数
  条件: (x : 自然数 ->₀ P)
  结论: (prodOfFinsupp自然数 f x).1 = x 0
  证明: by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.fst_sum]
  rw [Finset.sum_eq_single 0 (fun n _ hn => ?_) (by simp)]
  · simp
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn
  simp [pow_succ']

Depends on / 依赖: Finset, Finset.sum_eq_single, Prod.fst_sum, coe_lsum, exists_eq_succ_of_ne_zero, fst_sum, n.exists_eq_succ_of_ne_zero, pow_succ, prodOfFinsuppNat, simp_rw, sum_eq_single
-/
theorem fst_prodOfFinsuppNat (x : Nat ->₀ P) : (prodOfFinsuppNat f x).1 = x 0 := by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.fst_sum]
  rw [Finset.sum_eq_single 0 (fun n _ hn => ?_) (by simp)]
  · simp
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn
  simp [pow_succ']

/--
theorem `snd_prodOfFinsuppNat` / 定理 `snd_prodOfFinsuppNat`

English:
theorem snd_prodOfFinsuppNat
  given: (x : Nat ->₀ P)
  proof: by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.snd_sum]
  rw [← Finset.sum_preimage (· + 1) _ (add_left_injective 1).injOn _ (by simp_all)]
  simp [pow_succ']

中文:
定理 snd_prodOfFinsupp自然数
  条件: (x : 自然数 ->₀ P)
  证明: by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.snd_sum]
  rw [← Finset.sum_preimage (· + 1) _ (add_left_injective 1).injOn _ (by simp_all)]
  simp [pow_succ']

Depends on / 依赖: Finset, Finset.sum_preimage, Prod.snd_sum, add_left_injective, coe_lsum, pow_succ, prodOfFinsuppNat, simp_rw, snd_sum, sum_preimage
-/
theorem snd_prodOfFinsuppNat (x : Nat ->₀ P) :
    (prodOfFinsuppNat f x).2 =
    f (prodOfFinsuppNat f <| comapDomain.addMonoidHom (add_left_injective 1) x) := by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.snd_sum]
  rw [← Finset.sum_preimage (· + 1) _ (add_left_injective 1).injOn _ (by simp_all)]
  simp [pow_succ']

variable {f}

/--
theorem `prodOfFinsuppNat_injective` / 定理 `prodOfFinsuppNat_injective`

English:
theorem prodOfFinsuppNat_injective
  given: (inj : Injective f)
  statement: Injective (prodOfFinsuppNat f)
  proof: by
  intro x y
  let s := x.support union y.support
  obtain eq | ne := s.eq_empty_or_nonempty
  · simp_all [s]
  set n := s.max' ne with hn
  clear_value n; revert x y
  induction n using Nat.strong_induction_on with | h n ih =>
  intro x y s _ hn eq
  rw [← x.single_add_erase 0]; rw [← y.single_add_erase 0]
  simp_rw [← mapDomain_comapDomain_nat_add_one, ← f.fst_prodOfFinsuppNat, eq]
  congr 2
  by_contra ne
  apply ne (ih _ _ _ rfl (inj _))
  · contrapose! ne; simp_all [-comapDomain_support]
  · simp +contextual [hn, s, ← Nat.succ_le_iff, Finset.le_max']
  simp_rw [← snd_prodOfFinsuppNat, eq]

中文:
定理 prodOfFinsupp自然数_injective
  条件: (inj : 单射 f)
  结论: 单射 (prodOfFinsupp自然数 f)
  证明: by
  intro x y
  let s := x.support union y.support
  obtain eq | ne := s.eq_empty_or_nonempty
  · simp_all [s]
  set n := s.max' ne with hn
  clear_value n; revert x y
  induction n using Nat.strong_induction_on with | h n ih =>
  intro x y s _ hn eq
  rw [← x.single_add_erase 0]; rw [← y.single_add_erase 0]
  simp_rw [← mapDomain_comapDomain_nat_add_one, ← f.fst_prodOfFinsuppNat, eq]
  congr 2
  by_contra ne
  apply ne (ih _ _ _ rfl (inj _))
  · contrapose! ne; simp_all [-comapDomain_support]
  · simp +contextual [hn, s, ← Nat.succ_le_iff, Finset.le_max']
  simp_rw [← snd_prodOfFinsuppNat, eq]

Depends on / 依赖: Nat.strong_induction_on, clear_value, comapDomain_support, contextual, contrapose, eq_empty_or_nonempty, f.fst_prodOfFinsuppNat, fst_prodOfFinsuppNat, mapDomain_comapDomain_nat_add_one, revert, s.eq_empty_or_nonempty, s.max, simp_rw, single_add_erase, strong_induction_on, support, x.single_add_erase, x.support, y.single_add_erase, y.support
-/
theorem prodOfFinsuppNat_injective (inj : Injective f) : Injective (prodOfFinsuppNat f) := by
  intro x y
  let s := x.support union y.support
  obtain eq | ne := s.eq_empty_or_nonempty
  · simp_all [s]
  set n := s.max' ne with hn
  clear_value n; revert x y
  induction n using Nat.strong_induction_on with | h n ih =>
  intro x y s _ hn eq
  rw [← x.single_add_erase 0]; rw [← y.single_add_erase 0]
  simp_rw [← mapDomain_comapDomain_nat_add_one, ← f.fst_prodOfFinsuppNat, eq]
  congr 2
  by_contra ne
  apply ne (ih _ _ _ rfl (inj _))
  · contrapose! ne; simp_all [-comapDomain_support]
  · simp +contextual [hn, s, ← Nat.succ_le_iff, Finset.le_max']
  simp_rw [← snd_prodOfFinsuppNat, eq]

/--
theorem `exists_finsupp_nat_of_prod_injective` / 定理 `exists_finsupp_nat_of_prod_injective`

English:
theorem exists_finsupp_nat_of_prod_injective
  given: (inj : Injective f)
  proof: ⟨f ∘ₗ prodOfFinsuppNat f, inj.comp (prodOfFinsuppNat_injective inj)⟩

中文:
定理 存在_finsupp_nat_of_prod_injective
  条件: (inj : 单射 f)
  证明: ⟨f ∘ₗ prodOfFinsuppNat f, inj.comp (prodOfFinsuppNat_injective inj)⟩

Depends on / 依赖: inj.comp, prodOfFinsuppNat, prodOfFinsuppNat_injective
-/
theorem exists_finsupp_nat_of_prod_injective (inj : Injective f) :
    exists g : (Nat ->₀ P) ->ₗ[R] M, Injective g :=
  ⟨f ∘ₗ prodOfFinsuppNat f, inj.comp (prodOfFinsuppNat_injective inj)⟩

/--
theorem `exists_finsupp_nat_of_fin_fun_injective` / 定理 `exists_finsupp_nat_of_fin_fun_injective`

English:
theorem exists_finsupp_nat_of_fin_fun_injective
  statement: {n : Nat}
  proof: have e := LinearEquiv.piCongrLeft R (fun _ => P) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
exists_finsupp_nat_of_prod_injective (f := f ∘ₗ e.symm.toLinearMap) inj.comp e.symm.injective

中文:
定理 存在_finsupp_nat_of_fin_fun_injective
  结论: {n : 自然数}
  证明: have e := LinearEquiv.piCongrLeft R (fun _ => P) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
exists_finsupp_nat_of_prod_injective (f := f ∘ₗ e.symm.toLinearMap) inj.comp e.symm.injective

Depends on / 依赖: LinearEquiv, LinearEquiv.piCongrLeft, e.symm.injective, e.symm.toLinearMap, exists_finsupp_nat_of_prod_injective, finSuccEquiv, inj.comp, injective, piCongrLeft, piOptionEquivProd, toLinearMap
-/
theorem exists_finsupp_nat_of_fin_fun_injective {n : Nat}
    {f : (Fin (n + 1) -> P) ->ₗ[R] Fin n -> P} (inj : Injective f) :
    exists g : (Nat ->₀ P) ->ₗ[R] Fin n -> P, Injective g :=
  have e := LinearEquiv.piCongrLeft R (fun _ => P) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
exists_finsupp_nat_of_prod_injective (f := f ∘ₗ e.symm.toLinearMap) inj.comp e.symm.injective

end prodOfFinsuppNat

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFinsuppSurjective`
/--
Definition of `splittingOfFunOnFintypeSurjective` / `splittingOfFunOnFintypeSurjective` 的定义

English:
definition splittingOfFunOnFintypeSurjective
  signature: [Finite α] (f : M ->ₗ[R] α -> R) (s : Surjective f)
  body: (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap

中文:
定义 splittingOfFunOnFintypeSurjective
  签名: [有限 α] (f : M ->ₗ[R] α -> R) (s : 满射 f)
  定义体: (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap

Depends on / 依赖: Finsupp, Finsupp.lift, Finsupp.single, linearEquivFunOnFinite, single, symm.toLinearMap, toLinearMap
-/
def splittingOfFunOnFintypeSurjective [Finite α] (f : M ->ₗ[R] α -> R) (s : Surjective f) :
    (α -> R) ->ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap

/--
theorem `splittingOfFunOnFintypeSurjective_splits` / 定理 `splittingOfFunOnFintypeSurjective_splits`

English:
theorem splittingOfFunOnFintypeSurjective_splits
  statement: [Finite α] (f : M ->ₗ[R] α -> R)
  proof: by
  classical
  ext x y
  dsimp [splittingOfFunOnFintypeSurjective]
  rw [linearEquivFunOnFinite_symm_single]; rw [Finsupp.sum_single_index]; rw [one_smul]; rw [(s (Finsupp.single x 1)).choose_spec]; rw [Finsupp.single_eq_pi_single]
  rw [zero_smul]

中文:
定理 splittingOfFunOnFintypeSurjective_splits
  结论: [有限 α] (f : M ->ₗ[R] α -> R)
  证明: by
  classical
  ext x y
  dsimp [splittingOfFunOnFintypeSurjective]
  rw [linearEquivFunOnFinite_symm_single]; rw [Finsupp.sum_single_index]; rw [one_smul]; rw [(s (Finsupp.single x 1)).choose_spec]; rw [Finsupp.single_eq_pi_single]
  rw [zero_smul]

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.single_eq_pi_single, Finsupp.sum_single_index, choose_spec, classical, linearEquivFunOnFinite_symm_single, one_smul, single, single_eq_pi_single, splittingOfFunOnFintypeSurjective, sum_single_index, zero_smul
-/
theorem splittingOfFunOnFintypeSurjective_splits [Finite α] (f : M ->ₗ[R] α -> R)
    (s : Surjective f) : f.comp (splittingOfFunOnFintypeSurjective f s) = LinearMap.id := by
  classical
  ext x y
  dsimp [splittingOfFunOnFintypeSurjective]
  rw [linearEquivFunOnFinite_symm_single]; rw [Finsupp.sum_single_index]; rw [one_smul]; rw [(s (Finsupp.single x 1)).choose_spec]; rw [Finsupp.single_eq_pi_single]
  rw [zero_smul]

/--
theorem `leftInverse_splittingOfFunOnFintypeSurjective` / 定理 `leftInverse_splittingOfFunOnFintypeSurjective`

English:
theorem leftInverse_splittingOfFunOnFintypeSurjective
  statement: [Finite α] (f : M ->ₗ[R] α -> R)
  proof: fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g

中文:
定理 leftInverse_splittingOfFunOnFintypeSurjective
  结论: [有限 α] (f : M ->ₗ[R] α -> R)
  证明: fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g
-/
theorem leftInverse_splittingOfFunOnFintypeSurjective [Finite α] (f : M ->ₗ[R] α -> R)
    (s : Surjective f) : LeftInverse f (splittingOfFunOnFintypeSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g

/--
theorem `splittingOfFunOnFintypeSurjective_injective` / 定理 `splittingOfFunOnFintypeSurjective_injective`

English:
theorem splittingOfFunOnFintypeSurjective_injective
  statement: [Finite α] (f : M ->ₗ[R] α -> R)
  proof: (leftInverse_splittingOfFunOnFintypeSurjective f s).injective

中文:
定理 splittingOfFunOnFintypeSurjective_injective
  结论: [有限 α] (f : M ->ₗ[R] α -> R)
  证明: (leftInverse_splittingOfFunOnFintypeSurjective f s).injective

Depends on / 依赖: injective, leftInverse_splittingOfFunOnFintypeSurjective
-/
theorem splittingOfFunOnFintypeSurjective_injective [Finite α] (f : M ->ₗ[R] α -> R)
    (s : Surjective f) : Injective (splittingOfFunOnFintypeSurjective f s) :=
  (leftInverse_splittingOfFunOnFintypeSurjective f s).injective

end LinearMap

namespace Finsupp

variable {α : Type*}

/--
Definition of `submodule` / `submodule` 的定义

English:
definition submodule
  signature: (S : α -> Submodule R M)
  body: { x | forall i, x i in S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]

中文:
定义 submodule
  签名: (S : α -> 子模 R M)
  定义体: { x | forall i, x i in S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
-/
def submodule (S : α -> Submodule R M) : Submodule R (α ->₀ M) where
  carrier := { x | forall i, x i in S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
/--
lemma `mem_submodule_iff` / 引理 `mem_submodule_iff`

English:
lemma mem_submodule_iff
  given: (S : α -> Submodule R M) (x : α ->₀ M)
  proof: by
  rfl

@[simp]

中文:
引理 mem_submodule_iff
  条件: (S : α -> 子模 R M) (x : α ->₀ M)
  证明: by
  rfl

@[simp]
-/
lemma mem_submodule_iff (S : α -> Submodule R M) (x : α ->₀ M) :
    x in submodule S ↔ forall i, x i in S i := by
  rfl

@[simp]
/--
lemma `comap_lsingle_submodule` / 引理 `comap_lsingle_submodule`

English:
lemma comap_lsingle_submodule
  given: (p : α -> Submodule R M) (i : α)
  proof: by
  ext x
  refine ⟨fun hx => by simpa using hx i, fun hx j => ?_⟩
  rcases eq_or_ne i j with rfl|h <;> simp_all

中文:
引理 comap_lsingle_submodule
  条件: (p : α -> 子模 R M) (i : α)
  证明: by
  ext x
  refine ⟨fun hx => by simpa using hx i, fun hx j => ?_⟩
  rcases eq_or_ne i j with rfl|h <;> simp_all

Depends on / 依赖: eq_or_ne
-/
lemma comap_lsingle_submodule (p : α -> Submodule R M) (i : α) :
    Submodule.comap (lsingle i) (submodule p) = p i := by
  ext x
  refine ⟨fun hx => by simpa using hx i, fun hx j => ?_⟩
  rcases eq_or_ne i j with rfl|h <;> simp_all

/--
lemma `submodule_eq_iSup` / 引理 `submodule_eq_iSup`

English:
lemma submodule_eq_iSup
  given: (p : α -> Submodule R M)
  proof: by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← Finsupp.sum_single x]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hx i))
  · simp [iSup_le_iff, Submodule.map_le_iff_le_comap]

@[simp]

中文:
引理 submodule_eq_iSup
  条件: (p : α -> 子模 R M)
  证明: by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← Finsupp.sum_single x]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hx i))
  · simp [iSup_le_iff, Submodule.map_le_iff_le_comap]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_single, Submodule, Submodule.map_le_iff_le_comap, Submodule.mem_iSup_of_mem, Submodule.mem_map_of_mem, Submodule.sum_mem, iSup_le_iff, le_antisymm, map_le_iff_le_comap, mem_iSup_of_mem, mem_map_of_mem, sum_mem, sum_single
-/
lemma submodule_eq_iSup (p : α -> Submodule R M) :
    Finsupp.submodule p = ⨆ i, Submodule.map (Finsupp.lsingle i) (p i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← Finsupp.sum_single x]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hx i))
  · simp [iSup_le_iff, Submodule.map_le_iff_le_comap]

@[simp]
/--
lemma `submodule_top` / 引理 `submodule_top`

English:
lemma submodule_top
  statement: Finsupp.submodule (fun _ : α => (⊤ : Submodule R M)) = ⊤
  proof: by
  ext
  simp

中文:
引理 submodule_top
  结论: 有限支撑.submodule (fun _ : α => (⊤ : 子模 R M)) = ⊤
  证明: by
  ext
  simp
-/
lemma submodule_top : Finsupp.submodule (fun _ : α => (⊤ : Submodule R M)) = ⊤ := by
  ext
  simp

/--
theorem `ker_mapRange` / 定理 `ker_mapRange`

English:
theorem ker_mapRange
  given: (f : M ->ₗ[R] N) (I : Type*)
  proof: by
  ext x
  simp [Finsupp.ext_iff]

中文:
定理 ker_mapRange
  条件: (f : M ->ₗ[R] N) (I : 类型)
  证明: by
  ext x
  simp [Finsupp.ext_iff]

Depends on / 依赖: Finsupp, Finsupp.ext_iff, LinearMap, LinearMap.ker, ext_iff, submodule
-/
theorem ker_mapRange (f : M ->ₗ[R] N) (I : Type*) :
    LinearMap.ker (mapRange.linearMap (α := I) f) = submodule (fun _ => LinearMap.ker f) := by
  ext x
  simp [Finsupp.ext_iff]

/--
theorem `range_mapRange_linearMap` / 定理 `range_mapRange_linearMap`

English:
theorem range_mapRange_linearMap
  given: (f : M ->ₗ[R] N) (hf : LinearMap.ker f = ⊥) (I : Type*)
  proof: by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    simp [← hy]
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose
    <;> simp_all +contextual [← hy, map_zero, LinearMap.ker_eq_bot'.1 hf]

中文:
定理 range_mapRange_linearMap
  条件: (f : M ->ₗ[R] N) (hf : 线性映射.ker f = ⊥) (I : 类型)
  证明: by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    simp [← hy]
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose
    <;> simp_all +contextual [← hy, map_zero, LinearMap.ker_eq_bot'.1 hf]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, LinearMap.range, contextual, contrapose, ker_eq_bot, map_zero, submodule, support, x.support
-/
theorem range_mapRange_linearMap (f : M ->ₗ[R] N) (hf : LinearMap.ker f = ⊥) (I : Type*) :
    LinearMap.range (mapRange.linearMap (α := I) f) = submodule (fun _ => LinearMap.range f) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    simp [← hy]
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose
    <;> simp_all +contextual [← hy, map_zero, LinearMap.ker_eq_bot'.1 hf]

end Finsupp

namespace FunOnFinite

section

variable {M : Type*} [AddCommMonoid M] {X Y Z : Type*}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [Finite X] [Finite Y] (f : X -> Y) (s : X -> M)
  body: Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s))

中文:
定义 map
  签名: [有限 X] [有限 Y] (f : X -> Y) (s : X -> M)
  定义体: Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s))

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite, Finsupp.equivFunOnFinite.symm, Finsupp.mapDomain, equivFunOnFinite, mapDomain
-/
noncomputable def map [Finite X] [Finite Y] (f : X -> Y) (s : X -> M) : Y -> M :=
  Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s))

/--
lemma `map_apply_apply` / 引理 `map_apply_apply`

English:
lemma map_apply_apply
  given: [Fintype X] [Finite Y] [DecidableEq Y] (f : X -> Y) (s : X -> M) (y : Y)
  proof: by
  obtain ⟨s, rfl⟩ := Finsupp.equivFunOnFinite.surjective s
  dsimp [map]
  simp only [Equiv.symm_apply_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finsetSum]
  simp [Finset.sum_filter]
  congr
  aesop

@[simp]

中文:
引理 map_apply_apply
  条件: [有限类型 X] [有限 Y] [DecidableEq Y] (f : X -> Y) (s : X -> M) (y : Y)
  证明: by
  obtain ⟨s, rfl⟩ := Finsupp.equivFunOnFinite.surjective s
  dsimp [map]
  simp only [Equiv.symm_apply_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finsetSum]
  simp [Finset.sum_filter]
  congr
  aesop

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, Finset, Finset.sum_filter, Finsupp, Finsupp.equivFunOnFinite.surjective, Finsupp.mapDomain_finsetSum, Finsupp.univ_sum_single, equivFunOnFinite, mapDomain_finsetSum, nth_rw, sum_filter, surjective, symm_apply_apply, univ_sum_single
-/
lemma map_apply_apply [Fintype X] [Finite Y] [DecidableEq Y] (f : X -> Y) (s : X -> M) (y : Y) :
    map f s y = ∑ x with f x = y, s x := by
  obtain ⟨s, rfl⟩ := Finsupp.equivFunOnFinite.surjective s
  dsimp [map]
  simp only [Equiv.symm_apply_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finsetSum]
  simp [Finset.sum_filter]
  congr
  aesop

@[simp]
/--
lemma `map_piSingle` / 引理 `map_piSingle`

English:
lemma map_piSingle
  statement: [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
  proof: by
  simp [map]

中文:
引理 map_piSingle
  结论: [有限 X] [有限 Y] [DecidableEq X] [DecidableEq Y]
  证明: by
  simp [map]
-/
lemma map_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X -> Y) (x : X) (m : M) :
    map f (Pi.single x m) = Pi.single (f x) m := by
  simp [map]

variable (M) in
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: [Finite X]
  statement: map (_root_.id : X -> X) (M := M) = _root_.id
  proof: by
  ext s
  simp [map]

中文:
引理 map_id
  条件: [有限 X]
  结论: map (_root_.id : X -> X) (M := M) = _root_.id
  证明: by
  ext s
  simp [map]

Depends on / 依赖: _root_, _root_.id
-/
lemma map_id [Finite X] : map (_root_.id : X -> X) (M := M) = _root_.id := by
  ext s
  simp [map]

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: [Finite X] [Finite Y] [Finite Z] (g : Y -> Z) (f : X -> Y)
  proof: by
  ext s
  simp [map, Finsupp.mapDomain_comp]

中文:
引理 map_comp
  条件: [有限 X] [有限 Y] [有限 Z] (g : Y -> Z) (f : X -> Y)
  证明: by
  ext s
  simp [map, Finsupp.mapDomain_comp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_comp, mapDomain_comp
-/
lemma map_comp [Finite X] [Finite Y] [Finite Z] (g : Y -> Z) (f : X -> Y) :
    map (g.comp f) (M := M) = (map g).comp (map f) := by
  ext s
  simp [map, Finsupp.mapDomain_comp]

end

section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {X Y Z : Type*}

/--
Definition of `linearMap` / `linearMap` 的定义

English:
definition linearMap
  signature: [Finite X] [Finite Y] (f : X -> Y)
  body: (((Finsupp.linearEquivFunOnFinite R M Y)).comp (Finsupp.lmapDomain M R f)).comp
    (Finsupp.linearEquivFunOnFinite R M X).symm.toLinearMap

中文:
定义 linearMap
  签名: [有限 X] [有限 Y] (f : X -> Y)
  定义体: (((Finsupp.linearEquivFunOnFinite R M Y)).comp (Finsupp.lmapDomain M R f)).comp
    (Finsupp.linearEquivFunOnFinite R M X).symm.toLinearMap

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, Finsupp.lmapDomain, linearEquivFunOnFinite, lmapDomain, symm.toLinearMap, toLinearMap
-/
noncomputable def linearMap [Finite X] [Finite Y] (f : X -> Y) :
    (X -> M) ->ₗ[R] (Y -> M) :=
  (((Finsupp.linearEquivFunOnFinite R M Y)).comp (Finsupp.lmapDomain M R f)).comp
    (Finsupp.linearEquivFunOnFinite R M X).symm.toLinearMap

/--
lemma `linearMap_apply_apply` / 引理 `linearMap_apply_apply`

English:
lemma linearMap_apply_apply
  proof: by
  apply map_apply_apply

@[simp]

中文:
引理 linearMap_apply_apply
  证明: by
  apply map_apply_apply

@[simp]

Depends on / 依赖: map_apply_apply
-/
lemma linearMap_apply_apply
    [Fintype X] [Finite Y] [DecidableEq Y] (f : X -> Y) (s : X -> M) (y : Y) :
    linearMap R M f s y = (Finset.univ.filter (fun (x : X) => f x = y)).sum s := by
  apply map_apply_apply

@[simp]
/--
lemma `linearMap_piSingle` / 引理 `linearMap_piSingle`

English:
lemma linearMap_piSingle
  statement: [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
  proof: by
  apply map_piSingle

中文:
引理 linearMap_piSingle
  结论: [有限 X] [有限 Y] [DecidableEq X] [DecidableEq Y]
  证明: by
  apply map_piSingle

Depends on / 依赖: map_piSingle
-/
lemma linearMap_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X -> Y) (x : X) (m : M) :
    linearMap R M f (Pi.single x m) = Pi.single (f x) m := by
  apply map_piSingle

variable (X) in
@[simp]
/--
lemma `linearMap_id` / 引理 `linearMap_id`

English:
lemma linearMap_id
  given: [Finite X]
  statement: linearMap R M (_root_.id : X -> X) = .id
  proof: by
  classical
  aesop

中文:
引理 linearMap_id
  条件: [有限 X]
  结论: linearMap R M (_root_.id : X -> X) = .id
  证明: by
  classical
  aesop

Depends on / 依赖: classical
-/
lemma linearMap_id [Finite X] : linearMap R M (_root_.id : X -> X) = .id := by
  classical
  aesop

/--
lemma `linearMap_comp` / 引理 `linearMap_comp`

English:
lemma linearMap_comp
  given: [Finite X] [Finite Y] [Finite Z] (f : X -> Y) (g : Y -> Z)
  proof: by
  classical
  aesop

中文:
引理 linearMap_comp
  条件: [有限 X] [有限 Y] [有限 Z] (f : X -> Y) (g : Y -> Z)
  证明: by
  classical
  aesop

Depends on / 依赖: classical
-/
lemma linearMap_comp [Finite X] [Finite Y] [Finite Z] (f : X -> Y) (g : Y -> Z) :
    linearMap R M (g.comp f) = (linearMap R M g).comp (linearMap R M f) := by
  classical
  aesop

end

end FunOnFinite
